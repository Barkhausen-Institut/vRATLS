# vRATLS
A formal specification for RATLS (remote attestation embedded into TLS).

We are using [SSProve](https://github.com/SSProve), a framework for security proofs in Coq.

## Setup

Do not forget to clone this project with recursive submodules:
```git clone --recurse-submodules```

Please use [`nix`](https://nixos.org/download.html) to get all the setup you need for this project.
Please [enable `flake` support in `nix`](https://nixos.wiki/wiki/Flakes). 
If the `~/.config/nix/` folder and/or the `~/.config/nix/nix.conf` file do not exist then just create them.

After that all you need to issue at the command line is:
```
nix develop
```
Be prepared to wait a while because it will essentially build everything from scratch, even Coq itself.
Once it finished, the SSProve was successfully compiled and you are all set.

## Development

We use `dune` for building the project.
So please run:
```dune build```
