#!/usr/bin/env bash
# Install the pinned Verus toolchain into ~/tools.
#
# Verus makes rolling releases roughly weekly and requires an exact Rust
# toolchain and an exact Z3; all three are pinned in rust/toolchain-versions.txt
# and bumped deliberately, never tracked.
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS="${VERUS_TOOLS_DIR:-$HOME/tools}"

VERUS_TAG=$(awk '/^verus/{print $2}'  "$REPO/rust/toolchain-versions.txt")
RUST_TC=$(awk  '/^rust/{print $2}'    "$REPO/rust/toolchain-versions.txt")
Z3_VER=$(awk   '/^z3/{print $2}'      "$REPO/rust/toolchain-versions.txt")
VERUS_VER="${VERUS_TAG#release/}"

echo "verus $VERUS_VER | rust $RUST_TC | z3 $Z3_VER  ->  $TOOLS"
mkdir -p "$TOOLS/bin"

# --- rustup and the exact toolchain Verus needs ------------------------------
if ! command -v rustup >/dev/null 2>&1; then
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
    | sh -s -- -y --no-modify-path --default-toolchain stable --profile minimal
fi
export PATH="$HOME/.cargo/bin:$PATH"
rustup toolchain install "$RUST_TC" --profile minimal

# --- Verus -------------------------------------------------------------------
if [ ! -x "$TOOLS/verus/verus" ]; then
  URL="https://github.com/verus-lang/verus/releases/download/$VERUS_TAG/verus-$VERUS_VER-x86-linux.zip"
  echo "downloading $URL"
  curl -sSL "$URL" -o /tmp/verus.zip
  rm -rf "$TOOLS/verus-tmp"
  python3 -c "import zipfile;zipfile.ZipFile('/tmp/verus.zip').extractall('$TOOLS/verus-tmp')"
  mv "$TOOLS/verus-tmp/verus-x86-linux" "$TOOLS/verus"
  rmdir "$TOOLS/verus-tmp"
  chmod +x "$TOOLS/verus/verus" "$TOOLS/verus/rust_verify" "$TOOLS/verus/cargo-verus"
fi

# --- Z3 (not bundled with the release) ---------------------------------------
if [ ! -x "$TOOLS/bin/z3" ] || ! "$TOOLS/bin/z3" --version | grep -q "$Z3_VER"; then
  URL="https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VER/z3-$Z3_VER-x64-glibc-2.39.zip"
  echo "downloading $URL"
  curl -sSL "$URL" -o /tmp/z3.zip
  rm -rf /tmp/z3x
  python3 -c "import zipfile;zipfile.ZipFile('/tmp/z3.zip').extractall('/tmp/z3x')"
  cp "$(find /tmp/z3x -name z3 -type f | head -1)" "$TOOLS/bin/z3"
  chmod +x "$TOOLS/bin/z3"
fi

echo "--- installed ---"
PATH="$HOME/.cargo/bin:$TOOLS/bin:$PATH" "$TOOLS/verus/verus" --version | head -4
"$TOOLS/bin/z3" --version
