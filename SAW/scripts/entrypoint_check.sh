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
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-bn_reduce_once_in_place.patch || true)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-ec_scalar_from_montgomery.patch || true)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-ec_scalar_mul_montgomery.patch || true)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-ec_scalar_to_montgomery.patch || true)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-ec_point_mul_scalar_base.patch || true)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-ec_scalar_add.patch || true)
(cd ../src; patch -p1 -r - --forward < "$PATCH"/noinline-ec_scalar_is_zero.patch || true)

./scripts/build_x86.sh
./scripts/build_llvm.sh
./scripts/post_build.sh
./scripts/run_checks.sh
