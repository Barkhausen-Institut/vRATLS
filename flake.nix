{
  inputs = {
    nixpkgs.url        = github:nixos/nixpkgs;
    flake-utils.url    = github:numtide/flake-utils;
   # mathcomp-extra.url = github:sertel/mathcomp-extra;
    ssprove.url = github:sertel/ssprove/nix;
    ssprove.inputs.nixpkgs.follows = "nixpkgs";
    ssprove.inputs.flake-utils.follows = "flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils
  # , mathcomp-extra
  , ssprove
  }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        ocamlPackages = pkgs.ocamlPackages;
        coq = pkgs.coq_8_18;
        coqPackages = pkgs.coqPackages_8_18.overrideScope
          (self: super: {
            mathcomp = super.mathcomp.override { version = "2.1.0"; };
            mathcomp-analysis = super.mathcomp-analysis.override { version = "1.0.0"; };
          });
        # mathcompExtra = mathcomp-extra...
        ssp_args = {
          inherit (pkgs) stdenv which;
          inherit coqPackages coq;
        };
        ssprove' = ssprove.mkDrv ssp_args;
      in {
        devShell = pkgs.mkShell {
          packages =
            (with ocamlPackages; [ dune_3 ])
            ++
            (with pkgs; [coq gnumake])
            ++
            [ssprove'];

          shellHook = ''
                    alias ll="ls -lasi"
                    alias spacemacs="HOME=. emacs"
                    '';
        };
      }
    );
}
