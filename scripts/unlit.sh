#!/usr/bin/env bash
set -euo pipefail

dir=$(dirname "$1")
agdafile=$(basename "$1" .lagda).agda
awk -f scripts/unlit.awk < "$1" > "$dir/$agdafile"
rm "$1"
