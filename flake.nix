{
  inputs = {
    nixpkgs.url        = github:nixos/nixpkgs;
    flake-utils.url    = github:numtide/flake-utils;
   # mathcomp-extra.url = github:sertel/mathcomp-extra;
   ssprove.url = github:sertel/ssprove/mathcomp.2.1.0;
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
          inherit coq coqPackages;
        };
        ssprove' = ssprove.mkDrv ssp_args;
      in {
        devShell = pkgs.mkShell {
          packages =
            (with pkgs; [ coq gnumake ])
            ++
            (with ocamlPackages; [ dune_3 ])
            ++
            (with coqPackages; [
              equations
              mathcomp-analysis
              mathcomp-ssreflect
              # mathcompExtra
              extructures
              deriving
            ]);

          shellHook = ''
                    alias ll="ls -lasi"
                    alias spacemacs="HOME=. emacs"
                    '';
        };
      }
    );
}
