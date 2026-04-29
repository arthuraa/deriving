{
  description = ''
    Deriving provides generic instances of MathComp classes for
    inductive data types.  It includes native support for eqType,
    choiceType, countType and finType instances, and it allows users to
    define their own instances for other classes.
  '';

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    nix-github-actions.url = "github:nix-community/nix-github-actions";
    nix-github-actions.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = inputs@{ self, flake-parts, nixpkgs, nix-github-actions, ... }:
    let
      # Coq/Rocq package sets we test against.  The first entry is exposed as
      # packages.default / checks.default.  Used by the overlay (to decide what
      # to override) and by perSystem (to populate packages and checks).
      coqVersions = [
        "9_1"
        "9_0"
        "8_20"
        "8_19"
        "8_18"
        "8_17"
      ];
      defaultVersion = builtins.head coqVersions;
    in
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        # To import a flake module
        # 1. Add foo to inputs
        # 2. Add foo as a parameter to the outputs function
        # 3. Add here: foo.flakeModule

      ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        _module.args.pkgs = import self.inputs.nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
          config = { };
        };

        devShells.default = pkgs.mkShell {
          propagatedBuildInputs = [
            pkgs.coqPackages.coq-lsp
          ];
          inputsFrom = [
            self'.checks.default
          ];
        };

        packages =
          let packagesByVersion =
                nixpkgs.lib.listToAttrs
                  (map (coqVersion: {
                    name = coqVersion;
                    value = pkgs."coqPackages_${coqVersion}".deriving;
                  }) coqVersions);
          in
            packagesByVersion // {
              default = packagesByVersion.${defaultVersion};
            };

        checks = builtins.mapAttrs (set: package:
          package.overrideAttrs { doCheck = true; })
          self'.packages;
      };

      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

        githubActions = nix-github-actions.lib.mkGithubMatrix {
          checks =
            # Drop the "default" check — it is an alias for one of
            # the versioned checks, and including it would build
            # the same derivation twice in CI.
            builtins.mapAttrs
              (_: checks: builtins.removeAttrs checks [ "default" ])
              (nixpkgs.lib.getAttrs
                [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ]
                self.checks);
        };

        overlays.default = final: prev:
          let
            overrideDeriving = coqPackages:
              coqPackages.overrideScope (final': prev': {
                deriving = prev'.lib.overrideCoqDerivation {
                  version = ./.;
                  checkFlags = [ "VERBOSE=" ];
                  # The nixpkgs coq setup hook sets COQPATH for dependency
                  # lookup, but rocq 9.0+ warns that COQPATH is deprecated in
                  # favour of ROCQPATH.  Translate once, before any phase runs,
                  # to silence the warning.  Older versions still need COQPATH,
                  # so this is a no-op there.
                  preConfigure = prev.lib.optionalString
                    (prev.lib.versionAtLeast prev'.coq.coq-version "9.0") ''
                      if [ -n "''${COQPATH-}" ]; then
                        export ROCQPATH="$COQPATH"
                        unset COQPATH
                      fi
                    '';
                  nativeCheckInputs = [
                    final.gnuplot
                    final'.coq.ocamlPackages.findlib
                    final'.coq.ocamlPackages.csv
                  ];
                  # When the check phase ran, copy the bench artifacts into $out
                  # so CI can upload them.  Guarded so the non-check build
                  # (packages.default) is unaffected.
                  postInstall = ''
                    if [ -d bench/results/latest ]; then
                      mkdir -p $out/share/deriving/bench
                      cp -r bench/results/latest/. $out/share/deriving/bench/
                    fi
                  '';
                } prev'.deriving;
              });
          in
            nixpkgs.lib.listToAttrs
              (map (coqVersion:
                { name = "coqPackages_${coqVersion}";
                  value = overrideDeriving prev."coqPackages_${coqVersion}";})
                coqVersions);

      };
    };
}
