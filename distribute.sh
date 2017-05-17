#!/usr/bin/env sh

tar c src/* examples/* README.md LICENSE | gzip -9 > holes.tar.gz
