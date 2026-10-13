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
    protected array $volumes = [];
    protected ?array $volumeSizes = null;
    protected int $volumeIndex = 0;

    public function __construct(string $filePath, string $password = '')
    {
        // Accept any volume (*.enc.gz.7) and start from the first one
        $base = preg_replace('#\.[0-9]+$#', '', $filePath);
        if ($base !== $filePath && file_exists($base)) {
            $filePath = $base;
        }

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

    public function getVolumes(): array
    {
        return $this->volumes;
    }

    public function getVolumeIndex(): int
    {
        return $this->volumeIndex;
    }

    /**
     * Total size of the decoded (uncompressed) data of all volumes, null if unknown.
     */
    public function getTotalDataSize(): ?int
    {
        return $this->volumeSizes === null ? null : array_sum($this->volumeSizes);
    }

    protected static function isGzipName(string $filePath): bool
    {
        return (str_ends_with($filePath, '.gz') || preg_match('#\.gz\.[0-9]+$#', $filePath));
    }

    public static function checkIsEncrypted(string $filePath): bool
    {
        if (!file_exists($filePath)) {
            return false;
        }
        $isGzip = self::isGzipName($filePath);
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

    /**
     * Number of the last volume, stored by Bitrix in the gzip extra field of the first one.
     */
    protected static function readLastVolumeNumber(string $file): ?int
    {
        $f = @fopen($file, 'rb');
        if (!$f) {
            return null;
        }
        fseek($f, 12);
        $last = null;
        if (fread($f, 2) === 'LN') {
            $a = unpack('v', (string)fread($f, 2));
            $last = $a ? (int)end($a) : null;
        }
        fclose($f);
        return $last;
    }

    protected function detectVolumes(): bool
    {
        $base = $this->firstFile;
        $this->volumes = [$base];

        $last = $this->isGzip ? self::readLastVolumeNumber($base) : null;
        if ($last !== null) {
            for ($i = 1; $i <= $last; $i++) {
                if (!file_exists($base . '.' . $i)) {
                    $this->errors[] = "Missing volume: $base.$i (archive consists of " . ($last + 1) . " volumes)";
                    return false;
                }
                $this->volumes[] = $base . '.' . $i;
            }
        } else {
            $i = 1;
            while (file_exists($base . '.' . $i)) {
                $this->volumes[] = $base . '.' . $i;
                $i++;
            }

            // A higher-numbered volume after the first gap means a part is missing
            $prefix = basename($base) . '.';
            foreach (@scandir(dirname($base)) ?: [] as $name) {
                $suffix = substr($name, strlen($prefix));
                if (str_starts_with($name, $prefix) && ctype_digit($suffix) && (int)$suffix > $i) {
                    $this->errors[] = "Missing volume: $base.$i";
                    return false;
                }
            }
        }

        $sizes = [];
        foreach ($this->volumes as $volume) {
            $size = $this->getDataSize($volume);
            if (!$size) {
                $sizes = null;
                break;
            }
            $sizes[] = $size;
        }
        $this->volumeSizes = $sizes;

        return true;
    }

    public function open(): bool
    {
        $this->close();
        $this->currentFile = $this->firstFile;
        $this->block = 0;
        $this->buffer = '';
        $this->currentHeader = null;
        $this->errors = [];

        if (!file_exists($this->currentFile)) {
            $this->errors[] = "File not found: {$this->currentFile}";
            return false;
        }

        $this->isGzip = self::isGzipName($this->currentFile);

        if (!$this->detectVolumes() || !$this->openVolume(0)) {
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
                $error = "Invalid password or unsupported encryption algorithm.";
                if (!in_array('bf-ecb', array_map('strtolower', openssl_get_cipher_methods()), true)) {
                    $error .= " (Archives of old Bitrix versions use Blowfish, which needs the OpenSSL legacy provider.)";
                }
                $this->errors[] = $error;
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

    protected function closeHandle(): void
    {
        if ($this->res) {
            if ($this->isGzip) {
                @gzclose($this->res);
            } else {
                @fclose($this->res);
            }
            $this->res = null;
        }
    }

    public function close(): void
    {
        $this->closeHandle();
        $this->buffer = '';
    }

    protected function decrypt(string $data, string $key, string $method): string|false
    {
        return @openssl_decrypt($data, $method, $key, OPENSSL_RAW_DATA | OPENSSL_NO_PADDING);
    }

    protected function openVolume(int $index): bool
    {
        if (!isset($this->volumes[$index])) {
            return false;
        }

        $this->closeHandle();

        $file = $this->volumes[$index];
        $res = $this->isGzip ? @gzopen($file, 'rb') : @fopen($file, 'rb');
        if (!$res) {
            $this->errors[] = "Cannot open file: $file";
            return false;
        }

        $this->res = $res;
        $this->currentFile = $file;
        $this->volumeIndex = $index;

        return true;
    }

    /**
     * Makes sure the buffer holds decoded data, moving on to the next volume when needed.
     * Returns false at the end of the archive (or on error, see getErrors()).
     */
    protected function fillBuffer(): bool
    {
        if ($this->buffer !== '') {
            return true;
        }
        if (!$this->res) {
            return false;
        }

        $str = $this->isGzip ? gzread($this->res, self::BUFFER_SIZE) : fread($this->res, self::BUFFER_SIZE);
        while ($str === '' || $str === false) {
            if ($str === false) {
                $this->errors[] = "Read error in {$this->currentFile} (corrupted volume?)";
                return false;
            }
            if (!$this->openVolume($this->volumeIndex + 1)) {
                return false;
            }
            $str = $this->isGzip ? gzread($this->res, self::BUFFER_SIZE) : fread($this->res, self::BUFFER_SIZE);
        }

        if ($this->cryptoAlgorithm !== null) {
            $str = $this->decrypt($str, $this->md5Key, $this->cryptoAlgorithm);
            if ($str === false) {
                $this->errors[] = "Decryption error in {$this->currentFile} at block {$this->block}";
                return false;
            }
        }

        $this->buffer = $str;
        return true;
    }

    public function readBlock(): string
    {
        if (!$this->fillBuffer()) {
            return '';
        }

        $block = substr($this->buffer, 0, 512);
        $this->buffer = (string)substr($this->buffer, 512);
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

    /**
     * Positions the archive at an absolute 512-byte block of the decoded stream.
     * Volumes in between are not read at all: ECB blocks decrypt independently,
     * so decoding may start at any block boundary.
     */
    public function seekToBlock(int $block): bool
    {
        $delta = $block - $this->block;

        // Target is already in the buffer
        if ($this->res && $delta >= 0 && $delta * 512 <= strlen($this->buffer)) {
            $this->buffer = (string)substr($this->buffer, $delta * 512);
            $this->block = $block;
            return true;
        }

        if ($this->volumeSizes === null && count($this->volumes) > 1) {
            // Volume sizes are unknown: read and discard
            if ($delta < 0) {
                $errors = $this->errors;
                if (!$this->open()) {
                    return false;
                }
                $this->errors = $errors;
                $delta = $block - $this->block;
            }
            for ($i = 0; $i < $delta; $i++) {
                if ($this->readBlock() === '') {
                    return false;
                }
            }
            return true;
        }

        $pos = $block * 512;
        $index = 0;
        if ($this->volumeSizes !== null) {
            $count = count($this->volumeSizes);
            while ($index < $count && $pos >= $this->volumeSizes[$index]) {
                $pos -= $this->volumeSizes[$index];
                $index++;
            }

            if ($index >= $count) {
                if ($pos > 0) {
                    $this->errors[] = "Block $block is beyond the end of the archive (truncated archive or missing volume)";
                    return false;
                }
                // Exactly the end of the archive
                $this->close();
                $this->block = $block;
                return true;
            }
        }

        $this->buffer = '';
        if ((!$this->res || $index !== $this->volumeIndex) && !$this->openVolume($index)) {
            return false;
        }

        $seekRes = $this->isGzip ? gzseek($this->res, $pos) : fseek($this->res, $pos);
        if ($seekRes !== 0) {
            $this->errors[] = "Seek error in file {$this->currentFile} to position $pos";
            return false;
        }

        $this->block = $block;
        return true;
    }

    public function skipBlocks(int $blockCount): bool
    {
        if ($blockCount <= 0) {
            return true;
        }

        return $this->seekToBlock($this->block + $blockCount);
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

    /**
     * Positions the archive at the data of an entry previously returned by readHeader()
     * (see the 'data_block' key), without scanning the entries before it.
     */
    public function selectEntry(array $header): bool
    {
        $this->currentHeader = null;
        if (!$this->seekToBlock((int)$header['data_block'])) {
            return false;
        }
        $this->currentHeader = $header;
        return true;
    }

    protected function checksum(string $str): int
    {
        // Sum of all header bytes, the checksum field itself counted as spaces
        $sum = 8 * 32;
        foreach (count_chars(substr($str, 0, 148) . substr($str, 156), 1) as $byte => $count) {
            $sum += $byte * $count;
        }
        return $sum;
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
        if (!is_numeric($chk) || octdec($chk) !== $this->checksum($str)) {
            $this->errors[] = "Invalid TAR header checksum at block " . ($this->block - 1)
                . " in {$this->currentFile} (corrupted or truncated archive)";
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

        // First block of the file data, see selectEntry()
        $header['data_block'] = $this->block;

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

        $name = $this->currentHeader['filename'];
        $left = (int)$this->currentHeader['size'];
        $toConsume = (int)ceil($left / 512) * 512;
        $this->currentHeader = null;

        while ($toConsume > 0) {
            if (!$this->fillBuffer()) {
                $this->errors[] = "Unexpected EOF while reading $name";
                return false;
            }

            // Take as much as the buffer holds, the tail padding of the last block is dropped
            $n = min($toConsume, strlen($this->buffer));
            $chunk = substr($this->buffer, 0, $n);
            $this->buffer = (string)substr($this->buffer, $n);
            $this->block += intdiv($n, 512);
            $toConsume -= $n;

            if ($left > 0) {
                if ($n > $left) {
                    $chunk = substr($chunk, 0, $left);
                }
                if (@fwrite($outputHandle, $chunk) !== strlen($chunk)) {
                    $this->errors[] = "Write error while extracting $name";
                    return false;
                }
                $left -= strlen($chunk);
            }
        }

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

    /**
     * Writes the whole decoded archive (a plain TAR stream) to the given handle.
     * Must be called right after open().
     */
    public function streamTo($outputHandle): bool
    {
        while ($this->fillBuffer()) {
            if (@fwrite($outputHandle, $this->buffer) !== strlen($this->buffer)) {
                $this->errors[] = "Write error at block {$this->block}";
                return false;
            }
            $this->block += intdiv(strlen($this->buffer), 512);
            $this->buffer = '';
        }

        return empty($this->errors);
    }
}

/**
 * Sidecar index of archive entries (<archive>.idx).
 *
 * Listing an archive otherwise means decoding all of its volumes; with the index
 * a listing is a plain file read and any entry is reachable with a single seek.
 */
class ArchiveIndex
{
    const MAGIC = '#bx-backup-index v1';

    public static function pathFor(string $archive): string
    {
        $path = $archive . '.idx';
        if (file_exists($path) || is_writable(dirname($path))) {
            return $path;
        }
        return sys_get_temp_dir() . '/bx-backup-' . md5((string)realpath($archive)) . '.idx';
    }

    /**
     * Changes whenever any volume is replaced, so a stale index is never used.
     */
    public static function fingerprint(array $volumes): string
    {
        $parts = [];
        foreach ($volumes as $volume) {
            $parts[] = basename($volume) . ':' . filesize($volume) . ':' . filemtime($volume);
        }
        return md5(implode('|', $parts));
    }

    public static function isFresh(string $path, string $fingerprint): bool
    {
        $f = @fopen($path, 'rb');
        if (!$f) {
            return false;
        }
        $line = rtrim((string)fgets($f), "\n");
        fclose($f);
        return $line === self::MAGIC . "\t" . $fingerprint;
    }

    /**
     * Scans the whole archive and writes the index. Returns the number of entries.
     */
    public static function build(BitrixArchive $arc, string $path, string $fingerprint, ?callable $progress = null): int|false
    {
        if (!$arc->open()) {
            return false;
        }

        $tmp = $path . '.tmp' . getmypid();
        $f = @fopen($tmp, 'wb');
        if (!$f) {
            return false;
        }
        fwrite($f, self::MAGIC . "\t" . $fingerprint . "\n");

        $count = 0;
        while ($h = $arc->readHeader()) {
            fwrite($f, implode("\t", [
                $h['data_block'],
                $h['size'],
                $h['mtime'],
                $h['type'],
                addcslashes($h['filename'], "\\\n\r\t"),
            ]) . "\n");
            $count++;

            if ($progress && $count % 2000 === 0) {
                $progress($count);
            }
            if (!$arc->skipFile()) {
                break;
            }
        }
        fclose($f);

        if ($arc->getErrors() || !rename($tmp, $path)) {
            @unlink($tmp);
            return false;
        }

        return $count;
    }

    /**
     * Yields entries in archive order, in the format of BitrixArchive::readHeader().
     */
    public static function read(string $path): \Generator
    {
        $f = fopen($path, 'rb');
        fgets($f);
        while (($line = fgets($f)) !== false) {
            $parts = explode("\t", rtrim($line, "\n"), 5);
            if (count($parts) !== 5) {
                continue;
            }
            yield [
                'data_block' => (int)$parts[0],
                'size'       => (int)$parts[1],
                'mtime'      => (int)$parts[2],
                'type'       => $parts[3],
                'filename'   => stripcslashes($parts[4]),
            ];
        }
        fclose($f);
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
  index                   (Re)build the file index (<archive>.idx)
  stream                  Write the whole decrypted archive to STDOUT as a plain TAR stream
  help                    Show this help message

Options:
  -a, --archive=<file>    Archive first part (*.enc.gz or *.tar.gz). Auto-detected if omitted.
  -p, --password=<pass>   Archive password. Visible in shell history and process list:
                          prefer the interactive prompt or BITRIX_ARCHIVE_PASSWORD
  -o, --output=<dir>      Destination directory for extracted files (default: ./extracted)
  -f, --flat              Extract files directly into output folder without subdirectories
  -y, --overwrite         Overwrite existing files
  -d, --details           Show detailed file info in list (size, mtime, type)
  -l, --limit=<N>         Maximum entries to display in list (default: 50, 0 for unlimited)
  --raw                   Print raw filenames only (ideal for piping or xargs)

The first list/cat/extract scans the whole archive once and saves the file index
next to it (<archive>.idx, contains file names in plain text). After that listing
is instant and files are read with a direct seek to the right volume.

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

  # 7. Unpack everything with the system tar:
  ./bx-backup.php stream | tar -xf - -C ./site

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

    /**
     * Finds and opens the archive, reports problems to STDERR.
     */
    protected function openArchive(): ?BitrixArchive
    {
        $archiveFile = $this->findArchiveFile();
        if (!$archiveFile) {
            fprintf(STDERR, "Error: No archive file found in current directory. Specify with -a <file>\n");
            return null;
        }

        $password = $this->getPasswordForArchive($archiveFile);
        $arc = new BitrixArchive($archiveFile, $password);
        if (!$arc->open()) {
            fprintf(STDERR, "Error opening archive: %s\n", implode("\n", $arc->getErrors()));
            return null;
        }

        return $arc;
    }

    /**
     * Returns the path of an up-to-date index, building it when missing or stale.
     */
    protected function ensureIndex(BitrixArchive $arc, bool $force = false): ?string
    {
        $path = ArchiveIndex::pathFor($arc->getFirstFile());
        $fingerprint = ArchiveIndex::fingerprint($arc->getVolumes());
        if (!$force && ArchiveIndex::isFresh($path, $fingerprint)) {
            return $path;
        }

        $volumeCount = count($arc->getVolumes());
        $isTty = stream_isatty(STDERR);
        fprintf(STDERR, "Building file index for %d volume(s), this is done once...\n", $volumeCount);

        $t0 = microtime(true);
        $count = ArchiveIndex::build($arc, $path, $fingerprint, function (int $count) use ($arc, $volumeCount, $isTty) {
            if ($isTty) {
                fprintf(STDERR, "\r  %d entries (volume %d of %d)", $count, $arc->getVolumeIndex() + 1, $volumeCount);
            }
        });
        if ($isTty) {
            fprintf(STDERR, "\r%s\r", str_repeat(' ', 60));
        }

        if ($count === false) {
            $errors = $arc->getErrors() ?: ["Cannot write index file: $path"];
            fprintf(STDERR, "Error building index: %s\n", implode("\n", $errors));
            return null;
        }

        fprintf(STDERR, "Indexed %d entries in %ss -> %s\n\n", $count, round(microtime(true) - $t0, 2), $path);
        return $path;
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

    /**
     * Archive file names are untrusted: never let one escape the output directory.
     */
    protected function isUnsafePath(string $filename): bool
    {
        if ($filename === '' || str_contains($filename, "\0")) {
            return true;
        }
        $segments = explode('/', str_replace('\\', '/', $filename));
        return $segments[0] === '' || in_array('..', $segments, true);
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

            case 'index':
                return $this->cmdIndex();

            case 'stream':
                return $this->cmdStream();

            default:
                echo "Error: Unknown command '{$this->command}'. Use --help for usage.\n";
                return 1;
        }
    }

    protected function cmdInfo(): int
    {
        $arc = $this->openArchive();
        if (!$arc) {
            return 1;
        }

        $archiveFile = $arc->getFirstFile();
        $volumes = $arc->getVolumes();
        $totalDiskSize = 0;
        foreach ($volumes as $v) {
            $totalDiskSize += filesize($v);
        }

        echo "\nArchive Information:\n";
        echo "  First file:         $archiveFile\n";
        echo "  Volumes detected:   " . count($volumes) . " part(s)\n";
        echo "  Total size on disk: " . $this->formatBytes($totalDiskSize) . " (" . number_format($totalDiskSize) . " bytes)\n";
        if ($totalDataSize = $arc->getTotalDataSize()) {
            echo "  Unpacked size:      " . $this->formatBytes($totalDataSize) . " (" . number_format($totalDataSize) . " bytes)\n";
        }
        echo "  Encrypted:          " . ($arc->getCryptoAlgorithm() ? "Yes ({$arc->getCryptoAlgorithm()})" : "No") . "\n";

        $uncompressedPartSize = $arc->getDataSize($archiveFile);
        if ($uncompressedPartSize) {
            echo "  Volume chunk size:  " . $this->formatBytes($uncompressedPartSize) . "\n";
        }

        $indexPath = ArchiveIndex::pathFor($archiveFile);
        if (ArchiveIndex::isFresh($indexPath, ArchiveIndex::fingerprint($volumes))) {
            $entries = 0;
            foreach (ArchiveIndex::read($indexPath) as $e) {
                $entries++;
            }
            echo "  File index:         $indexPath (" . number_format($entries) . " entries)\n";
        } else {
            echo "  File index:         not built yet (created on first ls/cat/extract, or run: index)\n";
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

    protected function cmdIndex(): int
    {
        $arc = $this->openArchive();
        if (!$arc) {
            return 1;
        }

        $indexPath = $this->ensureIndex($arc, true);
        $arc->close();

        return $indexPath ? 0 : 1;
    }

    protected function cmdStream(): int
    {
        if (stream_isatty(STDOUT)) {
            fprintf(STDERR, "Error: stream writes binary TAR data, redirect it: ./bx-backup.php stream | tar -xf - -C <dir>\n");
            return 1;
        }

        $arc = $this->openArchive();
        if (!$arc) {
            return 1;
        }

        $ok = $arc->streamTo(STDOUT);
        $arc->close();

        if (!$ok) {
            fprintf(STDERR, "Error: %s\n", implode("\n", $arc->getErrors()));
            return 1;
        }

        return 0;
    }

    protected function cmdList(): int
    {
        $arc = $this->openArchive();
        if (!$arc) {
            return 1;
        }

        $indexPath = $this->ensureIndex($arc);
        $arc->close();
        if (!$indexPath) {
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

        foreach (ArchiveIndex::read($indexPath) as $h) {
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
        }

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
        $arc = $this->openArchive();
        if (!$arc) {
            return 1;
        }

        $indexPath = $this->ensureIndex($arc);
        if (!$indexPath) {
            return 1;
        }

        $found = false;
        $ok = true;
        foreach (ArchiveIndex::read($indexPath) as $h) {
            if ($h['filename'] === $targetFile) {
                $found = true;
                $ok = $arc->selectEntry($h) && $arc->extractCurrentFileToStream(STDOUT);
                break;
            }
        }

        $arc->close();

        if (!$found) {
            fprintf(STDERR, "Error: File '%s' not found in archive.\n", $targetFile);
            return 1;
        }

        if (!$ok) {
            fprintf(STDERR, "Error: %s\n", implode("\n", $arc->getErrors()));
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
        $arc = $this->openArchive();
        if (!$arc) {
            return 1;
        }

        $indexPath = $this->ensureIndex($arc);
        if (!$indexPath) {
            return 1;
        }

        $outDir = $this->options['output'] ?? ($this->options['o'] ?? './extracted');
        $isFlat = isset($this->options['flat']) || isset($this->options['f']);
        $overwrite = isset($this->options['overwrite']) || isset($this->options['y']);

        $isExactFile = (strpos($pattern, '*') === false && strpos($pattern, '?') === false);
        $extractedCount = 0;
        $failedCount = 0;
        $totalBytes = 0;
        $t0 = microtime(true);

        echo "Extracting matching: '$pattern' -> '$outDir' ...\n";

        foreach (ArchiveIndex::read($indexPath) as $h) {
            $fn = $h['filename'];

            if (!$this->matchPattern($fn, $pattern)) {
                continue;
            }

            if ($this->isUnsafePath($fn)) {
                echo "  [SKIP] $fn (unsafe path, would be written outside of the output directory)\n";
                $failedCount++;
                continue;
            }

            if ($isFlat) {
                $targetPath = rtrim($outDir, '/') . '/' . basename($fn);
            } else {
                $targetPath = rtrim($outDir, '/') . '/' . $fn;
            }

            if ($h['type'] === '5') {
                if (!$isFlat && !is_dir($targetPath)) {
                    mkdir($targetPath, 0777, true);
                }
                continue;
            }

            if (file_exists($targetPath) && !$overwrite) {
                echo "  [SKIP] $fn (already exists, use -y to overwrite)\n";
                continue;
            }

            $sizeStr = $this->formatBytes($h['size']);
            echo "  [EXTRACT] $fn ($sizeStr) -> $targetPath\n";

            $errorsBefore = count($arc->getErrors());
            if (!$arc->selectEntry($h) || !$arc->extractCurrentFile($targetPath)) {
                echo "  [ERROR] Failed to extract $fn: " . implode(', ', array_slice($arc->getErrors(), $errorsBefore)) . "\n";
                $failedCount++;
            } else {
                $extractedCount++;
                $totalBytes += $h['size'];
            }

            // If exact file match and not wildcard, we can stop immediately!
            if ($isExactFile && $fn === $pattern) {
                break;
            }
        }

        $arc->close();
        $elapsed = round(microtime(true) - $t0, 2);

        if ($extractedCount === 0) {
            echo "No matching files were extracted.\n";
            return 1;
        }

        echo "\nSuccessfully extracted $extractedCount file(s) (" . $this->formatBytes($totalBytes) . ") in {$elapsed}s.\n";
        if ($failedCount > 0) {
            echo "$failedCount file(s) were NOT extracted, see [ERROR]/[SKIP] lines above.\n";
            return 1;
        }

        return 0;
    }
}

$app = new CliApp($argv);
exit($app->run());
