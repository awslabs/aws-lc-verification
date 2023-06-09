# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


FROM ocaml/opam:ubuntu-20.04-opam
ENV GOROOT=/usr/local/go
ENV PATH="$GOROOT/bin:$PATH"
ARG GO_VERSION=1.20.1
ARG GO_ARCHIVE="go${GO_VERSION}.linux-amd64.tar.gz"
RUN echo 'sudo debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN sudo apt-get update \
   && sudo apt-get install -y wget unzip git cmake clang llvm python3-pip libncurses5  libgmp-dev cabal-install
RUN wget "https://dl.google.com/go/${GO_ARCHIVE}" && tar -xvf $GO_ARCHIVE && \
   sudo mkdir $GOROOT && sudo mv go/* $GOROOT && rm $GO_ARCHIVE

RUN sudo pip3 install wllvm

RUN opam switch install coq 4.14.1
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam install -vv -y -j "$(nproc)" coq.8.15.1 \
   && opam install -y coq-bits \
   && opam pin -y entree-specs https://github.com/GaloisInc/entree-specs.git#52c4868f1f65c7ce74e90000214de27e23ba98fb

ADD ./SAW/scripts /lc/scripts
RUN sudo /lc/scripts/docker_install.sh
ENV CRYPTOLPATH="../../../cryptol-specs:../../spec"


# This container expects all files in the directory to be mounted or copied. 
# The GitHub action will mount the workspace and set the working directory of the container.
# Another way to mount the files is: docker run -v `pwd`:`pwd` -w `pwd` <name>

# execute entrypoint using opam to make the required executables available
ENTRYPOINT ["./docker_entrypoint.sh"]
