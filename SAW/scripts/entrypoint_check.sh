#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -e

PATH=/lc/bin:/go/bin:$PATH

# TODO: Remove these patches
PATCH=$(realpath ./patch)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/rsa-encrypt.patch || true)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-aes_gcm_from_cipher_ctx.patch || true)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-bn_sub_words.patch || true)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-rsa_blinding.patch || true)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-ec_random_nonzero_scalar.patch || true)

./scripts/build_x86.sh
./scripts/build_llvm.sh
./scripts/post_build.sh
./scripts/run_checks.sh
