#!/usr/bin/env php
<?php
/**
 * Bitrix Encrypted Multi-Volume Backup CLI Utility
 * 
 * Allows listing, viewing (cat), and extracting arbitrary files (PHP, images, SQL, etc.)
 * directly from Bitrix encrypted multi-volume backup archives (*.enc.gz, *.enc.gz.*).
 */

error_reporting(E_ALL & ~E_DEPRECATED);
if (function_exists('mb_internal_encoding')) {
    mb_internal_encoding('ISO-8859-1');
}

class BitrixArchive
{
    const BX_SIGNATURE = 'Bitrix Encrypted File';
    const BUFFER_SIZE = 51200;

    protected string $firstFile = '';
    protected string $currentFile = '';
    protected string $password = '';
    protected ?string $md5Key = null;
    protected ?string $cryptoAlgorithm = null;
    protected bool $isGzip = true;
    protected $res = null;
    protected string $buffer = '';
    protected int $block = 0;
    protected int $blockHeader = 0;
    protected ?array $currentHeader = null;
    protected array $dataSizeCache = [];
    protected array $errors = [];

    public function __construct(string $filePath, string $password = '')
    {
        $this->firstFile = $filePath;
        $this->password = $password;
        if ($this->password !== '') {
            $this->md5Key = md5($this->password);
        }
    }

    public function getCryptoAlgorithm(): ?string
    {
        return $this->cryptoAlgorithm;
    }

    public function getCurrentFile(): string
    {
        return $this->currentFile;
    }

    public function getFirstFile(): string
    {
        return $this->firstFile;
    }

    public function getErrors(): array
    {
        return $this->errors;
    }

    public static function getVolumeList(string $firstFile): array
    {
        $base = preg_replace('#\.[0-9]+$#', '', $firstFile);
        $files = [];
        if (file_exists($base)) {
            $files[] = $base;
        }
        $i = 1;
        while (file_exists($base . '.' . $i)) {
            $files[] = $base . '.' . $i;
            $i++;
        }
        return $files;
    }

    public static function checkIsEncrypted(string $filePath): bool
    {
        if (!file_exists($filePath)) {
            return false;
        }
        $isGzip = (str_ends_with($filePath, '.gz') || preg_match('#\.gz\.[0-9]+$#', $filePath));
        $res = $isGzip ? @gzopen($filePath, 'rb') : @fopen($filePath, 'rb');
        if (!$res) {
            return false;
        }
        $str = $isGzip ? gzread($res, 512) : fread($res, 512);
        if ($isGzip) {
            @gzclose($res);
        } else {
            @fclose($res);
        }
        if ($str === false || strlen($str) < 512) {
            return false;
        }
        $data = unpack("a100empty/a90signature/a10version/a56tail/a256enc", $str);
        return (trim($data['signature'] ?? '') === self::BX_SIGNATURE);
    }

    public function open(): bool
    {
        $this->close();
        $this->currentFile = $this->firstFile;
        $this->block = 0;
        $this->buffer = '';
        $this->currentHeader = null;

        if (!file_exists($this->currentFile)) {
            $this->errors[] = "File not found: {$this->currentFile}";
            return false;
        }

        $this->isGzip = (str_ends_with($this->currentFile, '.gz') || preg_match('#\.gz\.[0-9]+$#', $this->currentFile));

        if ($this->isGzip) {
            $this->res = @gzopen($this->currentFile, 'rb');
        } else {
            $this->res = @fopen($this->currentFile, 'rb');
        }

        if (!$this->res) {
            $this->errors[] = "Cannot open file: {$this->currentFile}";
            return false;
        }

        // Read first 512 bytes to check Bitrix signature and encryption
        $str = $this->isGzip ? gzread($this->res, 512) : fread($this->res, 512);
        if ($str === false || strlen($str) < 512) {
            $this->errors[] = "Unable to read initial archive header from {$this->currentFile}";
            return false;
        }

        $data = unpack("a100empty/a90signature/a10version/a56tail/a256enc", $str);
        if (trim($data['signature'] ?? '') === self::BX_SIGNATURE) {
            $version = trim($data['version'] ?? '');
            if (version_compare($version, '1.2', '>')) {
                $this->errors[] = "Unsupported Bitrix archive version: $version";
                return false;
            }

            if ($this->md5Key === null) {
                $this->errors[] = "Archive is encrypted, but no password was provided.";
                return false;
            }

            // Test cipher methods
            $ciphers = ['aes-256-ecb', 'bf-ecb'];
            $this->cryptoAlgorithm = null;
            foreach ($ciphers as $cipher) {
                $decrypted = $this->decrypt($data['enc'], $this->md5Key, $cipher);
                if ($decrypted !== false && substr($str, 0, 256) === $decrypted) {
                    $this->cryptoAlgorithm = $cipher;
                    break;
                }
            }

            if (!$this->cryptoAlgorithm) {
                $this->errors[] = "Invalid password or unsupported encryption algorithm.";
                return false;
            }

            $this->block = 1;
            $this->blockHeader = 1;
        } else {
            // Not encrypted or old unencrypted tar
            if ($this->isGzip) {
                gzseek($this->res, 0);
            } else {
                fseek($this->res, 0);
            }
            $this->cryptoAlgorithm = null;
            $this->block = 0;
            $this->blockHeader = 0;
        }

        return true;
    }

    public function close(): void
    {
        if ($this->res) {
            if ($this->isGzip) {
                @gzclose($this->res);
            } else {
                @fclose($this->res);
            }
            $this->res = null;
        }
        $this->buffer = '';
    }

    protected function decrypt(string $data, string $key, string $method): string|false
    {
        $result = openssl_decrypt($data, $method, $key, OPENSSL_RAW_DATA | OPENSSL_NO_PADDING);
        if ($result === false && $method === 'bf-ecb') {
            $result = $this->bfEcbDecrypt($key, $data);
        }
        return $result;
    }

    protected function getNextFileName(string $file): string
    {
        $dotPos = strrpos($file, '.');
        if ($dotPos === false) {
            return $file . '.1';
        }
        $num = substr($file, $dotPos + 1);
        if (is_numeric($num)) {
            $next = ((int)$num) + 1;
            return substr($file, 0, $dotPos + 1) . $next;
        }
        return $file . '.1';
    }

    protected function openNext(): bool
    {
        $nextFile = $this->getNextFileName($this->currentFile);
        if (!file_exists($nextFile)) {
            return false;
        }

        if ($this->res) {
            if ($this->isGzip) {
                @gzclose($this->res);
            } else {
                @fclose($this->res);
            }
        }

        $this->currentFile = $nextFile;
        if ($this->isGzip) {
            $this->res = @gzopen($this->currentFile, 'rb');
        } else {
            $this->res = @fopen($this->currentFile, 'rb');
        }

        return (bool)$this->res;
    }

    public function readBlock(): string
    {
        if ($this->buffer === '') {
            $str = $this->isGzip ? gzread($this->res, self::BUFFER_SIZE) : fread($this->res, self::BUFFER_SIZE);
            if (($str === '' || $str === false) && $this->openNext()) {
                $str = $this->isGzip ? gzread($this->res, self::BUFFER_SIZE) : fread($this->res, self::BUFFER_SIZE);
            }

            if ($str !== '' && $str !== false && $this->cryptoAlgorithm !== null) {
                $str = $this->decrypt($str, $this->md5Key, $this->cryptoAlgorithm);
            }

            $this->buffer = (string)$str;
        }

        if ($this->buffer === '') {
            return '';
        }

        $block = substr($this->buffer, 0, 512);
        $this->buffer = substr($this->buffer, 512);
        $this->block++;

        return $block;
    }

    public function getDataSize(string $file): int|false
    {
        if (isset($this->dataSizeCache[$file])) {
            return $this->dataSizeCache[$file];
        }

        if (!file_exists($file)) {
            return false;
        }

        if (preg_match('#\.gz(\.[0-9]+)?$#', $file)) {
            $f = @fopen($file, 'rb');
            if ($f) {
                fseek($f, 16);
                if (fread($f, 2) === 'BX') {
                    $a = unpack('V', fread($f, 4));
                    $size = end($a);
                } else {
                    $size = false;
                }
                fclose($f);
                $this->dataSizeCache[$file] = $size;
                return $size;
            }
        } else {
            $size = filesize($file);
            $this->dataSizeCache[$file] = $size;
            return $size;
        }

        return false;
    }

    public function skipBlocks(int $blockCount): bool
    {
        if ($blockCount <= 0) {
            return true;
        }

        $this->block += $blockCount;
        $toSkip = $blockCount * 512;

        if (strlen($this->buffer) >= $toSkip) {
            $this->buffer = substr($this->buffer, $toSkip);
            return true;
        }

        $toSkip -= strlen($this->buffer);
        $this->buffer = '';

        $newPos = $this->block * 512;
        $firstName = preg_replace('#\.[0-9]+$#', '', $this->firstFile);

        if ($archiveSize = $this->getDataSize($firstName)) {
            $targetFile = $firstName;
            while ($newPos > $archiveSize) {
                $targetFile = $this->getNextFileName($targetFile);
                $newPos -= $archiveSize;
            }

            if ($targetFile !== $this->currentFile) {
                $this->close();
                $this->currentFile = $targetFile;
                if (!file_exists($targetFile)) {
                    $this->errors[] = "Next volume file does not exist: $targetFile";
                    return false;
                }
                if ($this->isGzip) {
                    $this->res = @gzopen($targetFile, 'rb');
                } else {
                    $this->res = @fopen($targetFile, 'rb');
                }
                if (!$this->res) {
                    $this->errors[] = "Could not open volume: $targetFile";
                    return false;
                }
            }

            $seekRes = $this->isGzip ? gzseek($this->res, $newPos) : fseek($this->res, $newPos);
            if ($seekRes === 0) {
                return true;
            }
            $this->errors[] = "Seek error in file {$this->currentFile} to position $newPos";
            return false;
        }

        // Fallback: read and discard
        $blocksRemaining = ceil($toSkip / 512);
        for ($i = 0; $i < $blocksRemaining; $i++) {
            if ($this->readBlock() === '') {
                return false;
            }
        }
        return true;
    }

    public function skipFile(): bool
    {
        if ($this->currentHeader === null) {
            return false;
        }
        $fileSize = (int)$this->currentHeader['size'];
        $blocks = (int)ceil($fileSize / 512);
        $res = $this->skipBlocks($blocks);
        $this->currentHeader = null;
        return $res;
    }

    public function readHeader(bool $isLong = false): ?array
    {
        $str = '';
        while (trim($str) === '') {
            $str = $this->readBlock();
            if ($str === '') {
                return null; // EOF
            }
        }

        if (!$isLong) {
            $this->blockHeader = $this->block - 1;
        }

        if (strlen($str) !== 512) {
            $this->errors[] = "Invalid block size: " . strlen($str) . " at block " . $this->block;
            return null;
        }

        $data = unpack("a100filename/a8mode/a8uid/a8gid/a12size/a12mtime/a8checksum/a1type/a100link/a6magic/a2version/a32uname/a32gname/a8devmajor/a8devminor/a155prefix", $str);
        $chk = trim($data['checksum'] ?? '');
        if (!is_numeric($chk)) {
            $this->errors[] = "Invalid TAR header checksum at block " . ($this->block - 1);
            return null;
        }

        $filename = trim(trim($data['prefix'], "\x00") . '/' . trim($data['filename'], "\x00"), '/');
        if (str_starts_with($filename, './')) {
            $filename = substr($filename, 2);
        }

        $header = [
            'filename' => $this->decodeFileName($filename),
            'mode'     => octdec(trim($data['mode'], "\x00 \t\n\r")),
            'uid'      => octdec(trim($data['uid'], "\x00 \t\n\r")),
            'gid'      => octdec(trim($data['gid'], "\x00 \t\n\r")),
            'size'     => octdec(trim($data['size'], "\x00 \t\n\r")),
            'mtime'    => octdec(trim($data['mtime'], "\x00 \t\n\r")),
            'type'     => trim($data['type'], "\x00"),
            'block'    => $this->blockHeader,
        ];

        // Handle GNU LongLink header (type 'L')
        if ($header['type'] === 'L') {
            $longFilename = '';
            $n = (int)ceil($header['size'] / 512);
            for ($i = 0; $i < $n; $i++) {
                $longFilename .= $this->readBlock();
            }
            $nextHeader = $this->readHeader(true);
            if (!$nextHeader) {
                return null;
            }
            $zeroPos = strpos($longFilename, "\x00");
            if ($zeroPos !== false) {
                $longFilename = substr($longFilename, 0, $zeroPos);
            }
            $nextHeader['filename'] = $this->decodeFileName(trim($longFilename, '/'));
            $this->currentHeader = $nextHeader;
            return $nextHeader;
        }

        if (str_ends_with($header['filename'], '/')) {
            $header['type'] = '5'; // Directory
            $header['size'] = 0;
        }

        if ($header['type'] === '5') {
            $header['size'] = 0;
        }

        $this->currentHeader = $header;
        return $header;
    }

    protected function decodeFileName(string $str): string
    {
        // Detect UTF-8 vs CP1251
        if (preg_match('/[\xC0-\xDF][\x80-\xBF]{1}|[\xE0-\xEF][\x80-\xBF]{2}|[\xF0-\xF7][\x80-\xBF]{3}/', $str)) {
            return $str; // valid UTF-8
        }
        if (preg_match('/[\xC0-\xFF]/', $str) && function_exists('mb_convert_encoding')) {
            return mb_convert_encoding($str, 'UTF-8', 'CP1251');
        }
        return $str;
    }

    public function extractCurrentFileToStream($outputHandle): bool
    {
        if ($this->currentHeader === null) {
            return false;
        }

        $fileSize = (int)$this->currentHeader['size'];
        $blocks = (int)ceil($fileSize / 512);

        for ($i = 0; $i < $blocks; $i++) {
            $chunk = $this->readBlock();
            if ($chunk === '') {
                $this->errors[] = "Unexpected EOF while reading {$this->currentHeader['filename']}";
                return false;
            }

            if ($i === $blocks - 1 && ($rem = $fileSize % 512)) {
                $chunk = substr($chunk, 0, $rem);
            }

            fwrite($outputHandle, $chunk);
        }

        $this->currentHeader = null;
        return true;
    }

    public function extractCurrentFile(string $targetPath): bool
    {
        if ($this->currentHeader === null) {
            return false;
        }

        if ($this->currentHeader['type'] === '5') {
            if (!is_dir($targetPath) && !mkdir($targetPath, 0777, true)) {
                $this->errors[] = "Cannot create directory: $targetPath";
                return false;
            }
            $this->currentHeader = null;
            return true;
        }

        $dir = dirname($targetPath);
        if (!is_dir($dir) && !mkdir($dir, 0777, true)) {
            $this->errors[] = "Cannot create directory: $dir";
            return false;
        }

        $fp = @fopen($targetPath, 'wb');
        if (!$fp) {
            $this->errors[] = "Cannot open destination file for writing: $targetPath";
            return false;
        }

        $res = $this->extractCurrentFileToStream($fp);
        fclose($fp);
        return $res;
    }

    public function getCurrentFileContent(): string|false
    {
        $mem = fopen('php://memory', 'r+');
        if (!$this->extractCurrentFileToStream($mem)) {
            fclose($mem);
            return false;
        }
        rewind($mem);
        $content = stream_get_contents($mem);
        fclose($mem);
        return $content;
    }

    protected function bfEcbDecrypt(string $key, string $ciphertext): string
    {
        // Fallback Blowfish ECB implementation
        return openssl_decrypt($ciphertext, 'bf-ecb', $key, OPENSSL_RAW_DATA | OPENSSL_NO_PADDING) ?: '';
    }
}

// -----------------------------------------------------------------------------
// CLI Application Logic
// -----------------------------------------------------------------------------

class CliApp
{
    protected array $args = [];
    protected array $options = [];
    protected string $command = 'help';

    public function __construct(array $argv)
    {
        array_shift($argv); // Remove script name

        while (!empty($argv)) {
            $arg = array_shift($argv);
            if (str_starts_with($arg, '--')) {
                $eq = strpos($arg, '=');
                if ($eq !== false) {
                    $k = substr($arg, 2, $eq - 2);
                    $v = substr($arg, $eq + 1);
                    $this->options[$k] = $v;
                } else {
                    $k = substr($arg, 2);
                    $this->options[$k] = true;
                }
            } elseif (str_starts_with($arg, '-') && strlen($arg) > 1) {
                $k = substr($arg, 1);
                if (in_array($k, ['a', 'p', 'o', 'l'])) {
                    $this->options[$k] = array_shift($argv);
                } else {
                    $this->options[$k] = true;
                }
            } else {
                $this->args[] = $arg;
            }
        }

        if (!empty($this->args)) {
            $this->command = array_shift($this->args);
        } elseif (isset($this->options['h']) || isset($this->options['help'])) {
            $this->command = 'help';
        }
    }

    protected function printHelp(): void
    {
        echo <<<HELP
========================================================================
 Bitrix Encrypted Multi-Volume Backup CLI Extractor
========================================================================

Usage:
  ./bx-backup.php <command> [pattern/path] [options]

Commands:
  list, ls [pattern]      List files in archive (supports wildcards * and ?, or substring)
  extract, x <pattern>    Extract matching file(s) to target directory
  cat, view <filepath>    Output file content directly to STDOUT
  info                    Show archive info (volumes, algorithm, size)
  help                    Show this help message

Options:
  -a, --archive=<file>    Archive first part (*.enc.gz or *.tar.gz). Auto-detected if omitted.
  -p, --password=<pass>   Archive password (prompted interactively if encrypted)
  -o, --output=<dir>      Destination directory for extracted files (default: ./extracted)
  -f, --flat              Extract files directly into output folder without subdirectories
  -y, --overwrite         Overwrite existing files
  -d, --details           Show detailed file info in list (size, mtime, type)
  -l, --limit=<N>         Maximum entries to display in list (default: 50, 0 for unlimited)
  --raw                   Print raw filenames only (ideal for piping or xargs)

Examples:
  # 1. Inspect archive details:
  ./bx-backup.php info

  # 2. Search for images:
  ./bx-backup.php ls "*.jpg" -d
  ./bx-backup.php ls "upload/*" --limit=20

  # 3. Search for PHP files:
  ./bx-backup.php ls "*.php"

  # 4. Extract an image:
  ./bx-backup.php extract "upload/iblock/123/banner.jpg" -o ./out

  # 5. Extract multiple files matching a pattern:
  ./bx-backup.php extract "local/components/*" -o ./restored_components

  # 6. View a file directly in terminal (cat):
  ./bx-backup.php cat "bitrix/.config.php"
  ./bx-backup.php cat "local/php_interface/init.php"

========================================================================

HELP;
    }

    protected function findArchiveFile(): ?string
    {
        if (!empty($this->options['archive'])) {
            return $this->options['archive'];
        }
        if (!empty($this->options['a'])) {
            return $this->options['a'];
        }

        // Look in current directory
        $candidates = glob('*.enc.gz');
        if (!empty($candidates)) {
            // Sort and pick the main volume (without .1, .2 suffix)
            foreach ($candidates as $c) {
                if (preg_match('#\.enc\.gz$#', $c)) {
                    return $c;
                }
            }
            return $candidates[0];
        }

        $candidates = glob('*.tar.gz');
        if (!empty($candidates)) {
            return $candidates[0];
        }

        return null;
    }

    protected function getPasswordForArchive(string $archiveFile): string
    {
        if (isset($this->options['password'])) {
            return (string)$this->options['password'];
        }
        if (isset($this->options['p'])) {
            return (string)$this->options['p'];
        }
        if (getenv('BITRIX_ARCHIVE_PASSWORD')) {
            return (string)getenv('BITRIX_ARCHIVE_PASSWORD');
        }

        if (BitrixArchive::checkIsEncrypted($archiveFile)) {
            return $this->promptPassword();
        }

        return '';
    }

    protected function promptPassword(): string
    {
        if (!stream_isatty(STDIN)) {
            $pass = trim((string)fgets(STDIN));
            return $pass;
        }

        fprintf(STDERR, "Archive is encrypted. Enter password: ");
        $sttyMode = shell_exec('stty -g 2>/dev/null');
        if ($sttyMode) {
            shell_exec('stty -echo 2>/dev/null');
        }

        $pass = trim((string)fgets(STDIN));

        if ($sttyMode) {
            shell_exec('stty ' . escapeshellarg(trim($sttyMode)) . ' 2>/dev/null');
        }
        fprintf(STDERR, "\n");

        return $pass;
    }

    protected function matchPattern(string $filename, string $pattern): bool
    {
        if ($pattern === '' || $pattern === '*') {
            return true;
        }

        // Exact match
        if ($filename === $pattern) {
            return true;
        }

        // Substring match if no wildcards
        if (strpos($pattern, '*') === false && strpos($pattern, '?') === false) {
            return (stripos($filename, $pattern) !== false);
        }

        // Glob wildcard pattern
        $regex = '#^' . str_replace(['\*', '\?'], ['.*', '.'], preg_quote($pattern, '#')) . '$#i';
        return (bool)preg_match($regex, $filename);
    }

    protected function formatBytes(int $bytes): string
    {
        if ($bytes >= 1073741824) {
            return round($bytes / 1073741824, 2) . ' GB';
        }
        if ($bytes >= 1048576) {
            return round($bytes / 1048576, 2) . ' MB';
        }
        if ($bytes >= 1024) {
            return round($bytes / 1024, 2) . ' KB';
        }
        return $bytes . ' B';
    }

    public function run(): int
    {
        switch ($this->command) {
            case 'help':
            case '-h':
            case '--help':
                $this->printHelp();
                return 0;

            case 'info':
                return $this->cmdInfo();

            case 'list':
            case 'ls':
            case 'find':
                return $this->cmdList();

            case 'cat':
            case 'view':
                return $this->cmdCat();

            case 'extract':
            case 'x':
                return $this->cmdExtract();

            default:
                echo "Error: Unknown command '{$this->command}'. Use --help for usage.\n";
                return 1;
        }
    }

    protected function cmdInfo(): int
    {
        $archiveFile = $this->findArchiveFile();
        if (!$archiveFile) {
            echo "Error: No archive file found in current directory. Specify with -a <file>\n";
            return 1;
        }

        $password = $this->getPasswordForArchive($archiveFile);
        $arc = new BitrixArchive($archiveFile, $password);
        if (!$arc->open()) {
            echo "Error opening archive: " . implode("\n", $arc->getErrors()) . "\n";
            return 1;
        }

        $volumes = BitrixArchive::getVolumeList($archiveFile);
        $totalDiskSize = 0;
        foreach ($volumes as $v) {
            $totalDiskSize += filesize($v);
        }

        echo "\nArchive Information:\n";
        echo "  First file:         $archiveFile\n";
        echo "  Volumes detected:   " . count($volumes) . " part(s)\n";
        echo "  Total size on disk: " . $this->formatBytes($totalDiskSize) . " (" . number_format($totalDiskSize) . " bytes)\n";
        echo "  Encrypted:          " . ($arc->getCryptoAlgorithm() ? "Yes ({$arc->getCryptoAlgorithm()})" : "No") . "\n";
        
        $uncompressedPartSize = $arc->getDataSize(preg_replace('#\.[0-9]+$#', '', $archiveFile));
        if ($uncompressedPartSize) {
            echo "  Volume chunk size:  " . $this->formatBytes($uncompressedPartSize) . "\n";
        }

        echo "\nFirst entries preview:\n";
        $count = 0;
        while ($h = $arc->readHeader()) {
            $typeStr = ($h['type'] === '5') ? '<DIR>' : $this->formatBytes($h['size']);
            echo sprintf("  %-10s  %s  %s\n", $typeStr, date('Y-m-d H:i', $h['mtime']), $h['filename']);
            $count++;
            if ($count >= 5) break;
            $arc->skipFile();
        }

        $arc->close();
        echo "\n";
        return 0;
    }

    protected function cmdList(): int
    {
        $archiveFile = $this->findArchiveFile();
        if (!$archiveFile) {
            echo "Error: No archive file found in current directory. Specify with -a <file>\n";
            return 1;
        }

        $password = $this->getPasswordForArchive($archiveFile);
        $arc = new BitrixArchive($archiveFile, $password);
        if (!$arc->open()) {
            echo "Error opening archive: " . implode("\n", $arc->getErrors()) . "\n";
            return 1;
        }

        $pattern = $this->args[0] ?? '*';
        $limit = isset($this->options['limit']) ? (int)$this->options['limit'] : (isset($this->options['l']) ? (int)$this->options['l'] : 50);
        $showDetails = isset($this->options['details']) || isset($this->options['d']);
        $raw = isset($this->options['raw']);

        $matched = 0;
        $total = 0;
        $t0 = microtime(true);

        if (!$raw) {
            echo "Searching in archive for pattern: '$pattern' ...\n\n";
            if ($showDetails) {
                printf("%-10s  %-16s  %s\n", "SIZE", "MODIFIED", "FILENAME");
                echo str_repeat('-', 70) . "\n";
            }
        }

        while ($h = $arc->readHeader()) {
            $total++;
            $fn = $h['filename'];

            if ($this->matchPattern($fn, $pattern)) {
                $matched++;
                if ($raw) {
                    echo "$fn\n";
                } elseif ($showDetails) {
                    $sizeStr = ($h['type'] === '5') ? '<DIR>' : $this->formatBytes($h['size']);
                    $dateStr = date('Y-m-d H:i', $h['mtime']);
                    printf("%-10s  %-16s  %s\n", $sizeStr, $dateStr, $fn);
                } else {
                    echo "$fn\n";
                }

                if ($limit > 0 && $matched >= $limit) {
                    break;
                }
            }

            $arc->skipFile();
        }

        $arc->close();
        $elapsed = round(microtime(true) - $t0, 2);

        if (!$raw) {
            echo "\nFound $matched match(es) (scanned $total entries in {$elapsed}s)";
            if ($limit > 0 && $matched >= $limit) {
                echo " [Output limited to $limit. Use --limit=0 to show all]";
            }
            echo "\n";
        }

        return 0;
    }

    protected function cmdCat(): int
    {
        if (empty($this->args)) {
            echo "Error: Missing target file path. Usage: ./bx-backup.php cat <filename>\n";
            return 1;
        }

        $targetFile = ltrim($this->args[0], '/');
        $archiveFile = $this->findArchiveFile();
        if (!$archiveFile) {
            echo "Error: No archive file found. Specify with -a <file>\n";
            return 1;
        }

        $password = $this->getPasswordForArchive($archiveFile);
        $arc = new BitrixArchive($archiveFile, $password);
        if (!$arc->open()) {
            echo "Error opening archive: " . implode("\n", $arc->getErrors()) . "\n";
            return 1;
        }

        $found = false;
        while ($h = $arc->readHeader()) {
            if ($h['filename'] === $targetFile) {
                $found = true;
                $arc->extractCurrentFileToStream(STDOUT);
                break;
            }
            $arc->skipFile();
        }

        $arc->close();

        if (!$found) {
            fprintf(STDERR, "Error: File '%s' not found in archive.\n", $targetFile);
            return 1;
        }

        return 0;
    }

    protected function cmdExtract(): int
    {
        if (empty($this->args)) {
            echo "Error: Missing file pattern to extract. Usage: ./bx-backup.php extract <pattern> [-o <outDir>]\n";
            return 1;
        }

        $pattern = ltrim($this->args[0], '/');
        $archiveFile = $this->findArchiveFile();
        if (!$archiveFile) {
            echo "Error: No archive file found. Specify with -a <file>\n";
            return 1;
        }

        $outDir = $this->options['output'] ?? ($this->options['o'] ?? './extracted');
        $isFlat = isset($this->options['flat']) || isset($this->options['f']);
        $overwrite = isset($this->options['overwrite']) || isset($this->options['y']);

        $password = $this->getPasswordForArchive($archiveFile);
        $arc = new BitrixArchive($archiveFile, $password);
        if (!$arc->open()) {
            echo "Error opening archive: " . implode("\n", $arc->getErrors()) . "\n";
            return 1;
        }

        $isExactFile = (strpos($pattern, '*') === false && strpos($pattern, '?') === false);
        $extractedCount = 0;
        $totalBytes = 0;
        $t0 = microtime(true);

        echo "Extracting matching: '$pattern' -> '$outDir' ...\n";

        while ($h = $arc->readHeader()) {
            $fn = $h['filename'];

            if ($this->matchPattern($fn, $pattern)) {
                if ($isFlat) {
                    $targetPath = rtrim($outDir, '/') . '/' . basename($fn);
                } else {
                    $targetPath = rtrim($outDir, '/') . '/' . $fn;
                }

                if (file_exists($targetPath) && !$overwrite && $h['type'] !== '5') {
                    echo "  [SKIP] $fn (already exists, use -y to overwrite)\n";
                    $arc->skipFile();
                    continue;
                }

                if ($h['type'] === '5') {
                    if (!$isFlat && !is_dir($targetPath)) {
                        mkdir($targetPath, 0777, true);
                    }
                    $arc->skipFile();
                    continue;
                }

                $sizeStr = $this->formatBytes($h['size']);
                echo "  [EXTRACT] $fn ($sizeStr) -> $targetPath\n";

                if (!$arc->extractCurrentFile($targetPath)) {
                    echo "  [ERROR] Failed to extract $fn: " . implode(', ', $arc->getErrors()) . "\n";
                } else {
                    $extractedCount++;
                    $totalBytes += $h['size'];
                }

                // If exact file match and not wildcard, we can stop immediately!
                if ($isExactFile && $fn === $pattern) {
                    break;
                }
            } else {
                $arc->skipFile();
            }
        }

        $arc->close();
        $elapsed = round(microtime(true) - $t0, 2);

        if ($extractedCount === 0) {
            echo "No matching files were extracted.\n";
            return 1;
        }

        echo "\nSuccessfully extracted $extractedCount file(s) (" . $this->formatBytes($totalBytes) . ") in {$elapsed}s.\n";
        return 0;
    }
}

$app = new CliApp($argv);
exit($app->run());
