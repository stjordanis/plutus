#!/usr/bin/env bash

# Regenerate the `pkgs/default.nix` file based on the current
# contents of cabal and stack files, with a hackage snapshot.

set -euo pipefail
cd "$(dirname -- "$(readlink -f -- "${BASH_SOURCE[0]}")")"
exec "$(nix-build ../default.nix -A localLib.regeneratePackages)" "default.nix" "$@"
