#!/bin/sh
set -e

PATH=/lc/bin:/go/bin:$PATH

./scripts/build_x86.sh
./scripts/build_llvm.sh
./scripts/post_build.sh
./scripts/prove.sh
