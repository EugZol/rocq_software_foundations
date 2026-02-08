FROM ubuntu:24.04

ARG USERNAME=ubuntu
ARG USER_UID=1000
ARG USER_GID=$USER_UID

RUN apt-get update -y && apt-get install -y --no-install-recommends \
    curl ca-certificates git build-essential pkg-config unzip rsync \
    m4 bubblewrap \
    libgmp-dev \
    linux-libc-dev m4 time zip sudo opam \
 && rm -rf /var/lib/apt/lists/*

USER $USERNAME

# CompCert is broken with newer melnir versions, so older one is pinned.

RUN opam init -y --disable-sandboxing
RUN opam switch create -y rocq-vst ocaml-base-compiler.4.14.2
RUN eval "$(opam env --switch=rocq-vst)" \
 && opam repo add -y rocq-released https://rocq-prover.org/opam/released \
 && opam update -y \
 && opam pin add -y coq 9.0.1 \
 && opam pin add -y menhir 20250912 \
 && opam install -y --verbose coq-vst.2.16 \
 && opam install -y vsrocq-language-server \
 && opam clean -a -y

SHELL ["/bin/bash", "-lc"]

RUN echo 'eval "$(opam env --switch=rocq-vst --set-switch)"' >> /home/ubuntu/.bashrc
