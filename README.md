# vRATLS
A formal specification for RATLS (remote attestation embedded into TLS).

We are using [SSProve](https://github.com/SSProve), a framework for security proofs in Coq.

## Setup

Please use [`nix`](https://nixos.org/download.html) to get all the setup you need for this project.
Please [enable `flake` support in `nix`](https://nixos.wiki/wiki/Flakes). 
If the `~/.config/nix/` folder and/or the `~/.config/nix/nix.conf` file do not exist then just create them.

After that all you need to issue at the command line is:
```
nix develop
```
Be prepared to wait a while because it will essentially build everything from scratch, even Coq itself.
Once it finished, the SSProve was successfully compiled and you are all set.

Currently there is no package for Spacemacs on Nix. Hence, we suggest to install it from inside the `nix shell`.

- First, you need to install `emacs`.
- [Here](https://www.spacemacs.org/#) you can find the command to install Spacemacs.
- But instead install `spacemacs` right at the root project directory via 
  ```git clone https://github.com/syl20bnr/spacemacs .emacs.d```
- Start emacs now like so: `HOME=. emacs`. This will have the effect that emacs is started with the new local spacemacs configuration which is clean and can be configured now.
- Once installation is complete you need to [edit the config](https://develop.spacemacs.org/doc/QUICK_START.html) and [activate the Coq layer](https://develop.spacemacs.org/layers/+lang/coq/README.html).

## Development

To compile the theories, simply run ```make```.

( old version:
We use `dune` for building the project.
So please run:
```dune build```
)
