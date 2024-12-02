{
  description = ''
    Deriving provides generic instances of MathComp classes for
    inductive data types.  It includes native support for eqType,
    choiceType, countType and finType instances, and it allows users to
    define their own instances for other classes.
  '';

  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system}; in rec {
            packages = rec {
              coq = pkgs.coq_8_19;
              coqPackages = pkgs.coqPackages_8_19.overrideScope (self: super:
                { mathcomp = super.mathcomp.override {
                    version = "2.2.0";
                  };
                  deriving = super.deriving.overrideAttrs {
                    version = "0.2.0";
                    src = ./.;
                  };
                });
              ocaml = pkgs.ocaml;
            };

            devShell = pkgs.mkShell {
              packages = with packages; [ coq coqPackages.mathcomp.ssreflect ocaml ];
            };
      }
    );
}
