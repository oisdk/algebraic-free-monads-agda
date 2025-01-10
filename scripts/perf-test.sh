#!/usr/bin/env bash

version_string="$(agda --version)"
version=${version_string#"Agda version "}
file="${1%.*}"
artefact="_build/$version/agda/${file}.agdai"
[ -f "$artefact" ] && rm "$artefact"
time agda "${1}"
