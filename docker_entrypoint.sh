#!/bin/bash -ex

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


(pushd SAW; ./scripts/install.sh; popd)
export PATH=$PATH:$HOME/bin
export CI=true
export OPAMROOT=/root/.opam
eval $(opam env)
(pushd Coq; make; popd)
#(pushd SAW; ./scripts/entrypoint_check.sh; popd)
