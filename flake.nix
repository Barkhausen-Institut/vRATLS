{
  inputs = {
    nixpkgs.url        = github:nixos/nixpkgs;
    flake-utils.url    = github:numtide/flake-utils;
   # mathcomp-extra.url = github:sertel/mathcomp-extra;
    ssprove.url = github:sertel/ssprove/nix;
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
          inherit coqPackages;
        };
        ssprove' = builtins.trace ssprove (ssprove.mkDrv ssp_args);
        coqPackages' = coqPackages // {
          ssprove = ssprove';
        };
#        coq-version = coq.version;
        ssprove'' = ssprove'.overrideAttrs (oldAttrs: {
          setupHook = coq.setupHook;
          installPhase = ''
            runHook setupHook
            '';
        });

      in {
        devShell = pkgs.mkShell {
          packages =
            (with ocamlPackages; [ dune_3 ])
            ++
            (with pkgs; [coq gnumake])
#            ++
#            (with coqPackages; [equations
#                                mathcomp
#                                mathcomp-analysis
#                                mathcomp-ssreflect])
            #++
            #[extructures']
            ++
            [ssprove''];

          shellHook = ''
                    alias ll="ls -lasi"
                    alias spacemacs="HOME=. emacs"
                    '';
        };
      }
    );
}
