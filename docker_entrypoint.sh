#!/bin/bash -ex

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# The container runs as root, but the git checkout was performed by another user.
# Disable git security checks that ensure files are owned by the current user.
git config --global --add safe.directory '*'
NUM_CPU_THREADS=$(grep -c ^processor /proc/cpuinfo)
(pushd SAW; ./scripts/install.sh; popd)
export CI=true
export PATH=/lc/bin:$PATH
export OPAMROOT=/root/.opam
eval $(opam env)
#(pushd Coq; make -j $NUM_CPU_THREADS; popd)
(pushd Coq; make; popd)
(pushd SAW; ./scripts/entrypoint_check.sh; popd)
