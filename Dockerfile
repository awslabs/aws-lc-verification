FROM ubuntu:20.04
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update
RUN apt-get install -y wget unzip git cmake clang llvm golang python3-pip libncurses5
RUN pip3 install wllvm

WORKDIR /lc
ADD ./scripts /lc/scripts

RUN ./scripts/install.sh

ENTRYPOINT ["./scripts/docker_entrypoint.sh"]