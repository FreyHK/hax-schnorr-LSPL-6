FROM ubuntu:22.04

RUN apt-get update && apt-get install -y \
    build-essential \
    curl \
    cmake \
    git \
    opam \
    jq \
    git

# Install Node
RUN curl -sL https://deb.nodesource.com/setup_18.x | bash - && apt-get install -y nodejs  

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

# Install the nightly version of Rust
# RUN rustup install nightly
# RUN rustup default nightly

# Install Opam
RUN opam init --disable-sandboxing --auto-setup --yes
RUN opam switch create 5.1.1
RUN eval $(opam env)

# Install Coq
RUN apt-get update && apt-get install -y libgmp-dev pkg-config
RUN opam pin add coq 8.18.0 --yes
RUN opam install vscoq-language-server --yes

# Install Coq packages
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam install -y \
    coq-record-update

# Pull Hax
# RUN git clone https://github.com/cryspen/hax.git

# Run setup
# RUN cd /hax && \
#   eval $(opam env) && \
#   ./setup.sh

# Persist opam environment
ENV OPAMSWITCH=5.1.1
ENV PATH="/root/.opam/${OPAMSWITCH}/bin:${PATH}"