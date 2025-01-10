#!/usr/bin/env bash

set -euo pipefail

find . -type f -name '*.lagda' -exec "./scripts/unlit.sh" {} \;


