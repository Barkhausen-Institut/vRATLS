{
  inputs = {
    nixpkgs.url = github:nixos/nixpkgs;
    flake-utils.url = github:numtide/flake-utils;
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
#        spacemacs = pkgs.stdenv.mkDerivation {
#          name = "spacemacs";
#          src = pkgs.fetchFromGitHub {
#            owner = "syl20bnr";
#            repo = "spacemacs";
#            rev = "58a52ae6ef6c573bb9731cfcf1b9fe95627b2cc9";
#            hash = "sha256-5wP+EH/gs0zfzt/ahKEM294o5udTmG+hHDFjpV2oM3w=";
#          };
#          installPhase = "mkdir $out ; mv * .??* $out/";
#        };

	      #ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_09;

        coq = pkgs.coq_8_14.override {
          #customOCamlPackages = ocamlPackages;
        };
        # See here: https://github.com/vellvm/vellvm/blob/dev/flake.nix
        coqPackages = pkgs.coqPackages_8_14.overrideScope'
          (self: super: {
            equations          = super.equations.override { version = "1.3+8.14"; };
            mathcomp           = super.mathcomp.override { version = "1.13.0"; };
            mathcomp-ssreflect = super.mathcomp-ssreflect.override { version = "1.13.0"; };
            mathcomp-analysis  = super.mathcomp-analysis.override { version = "0.3.13"; };
            extructures        = super.extructures.override { version = "0.3.1"; };
            deriving           = super.deriving.override { version = "0.1"; };
         });
      in {
        devShell = pkgs.mkShell {
          packages =
            # basic tools
            (with pkgs; [ coq emacs gnumake ])
            ++
#            (with ocamlPackages; [
#              ocaml dune_2 findlib base core stdio parsexp hashcons zarith
#            ])
#            ++
            (with coqPackages; [
              equations
              mathcomp-analysis
              mathcomp-ssreflect
              extructures
              deriving
              # This did not work.
                      #equations.override { version = "1.3"; }
                      #mathcomp-analysis.override { version = "0.3.13"; }
                      #mathcomp-ssreflect.override { version = "1.13.0"; }
                      #extructures.override { version = "0.3.1"; }
                      #deriving.override { version = "0.1"; }
                      ]
            );

          shellHook = ''
                    alias ll="ls -lasi"
                    cd ssprove && make clean && make
                    '';
#          shellHook = ''
#            export XDG_CONFIG_HOME=$PWD/.config
#            export SPACEMACSDIR=$XDG_CONFIG_HOME/spacemacs
#
#            if ! test -d "$XDG_CONFIG_HOME/emacs" ; then
#              echo 'Installing spacemacs.'
#              mkdir -p "$XDG_CONFIG_HOME"
#              cp -Rp ${spacemacs} "$XDG_CONFIG_HOME/emacs"
#              chmod -R u+w "$XDG_CONFIG_HOME/emacs"
#            fi
#
#            test -r ~/.shellrc && . ~/.shellrc
#          '';
        };
      }
    );
}
