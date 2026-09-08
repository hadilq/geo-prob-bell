{
  description = "Formal companion to \"Geometrical Probability of Bell's Theorem\" (Lean 4 + Mathlib)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        devShells.default = pkgs.mkShell {
          # `elan` is the Lean toolchain manager.  We deliberately do *not*
          # pin a Lean compiler in Nix: Mathlib dictates the exact version,
          # and `lean-toolchain` in this repo is the single source of truth.
          # elan reads that file and fetches the matching compiler.
          packages = with pkgs; [
            elan
            git
            curl
            cacert
            gnumake
            unzip # `lake exe cache get` unpacks the Mathlib olean cache
          ];

          shellHook = ''
            # Keep elan's state inside the repo so the shell is reproducible
            # and `nix develop` never touches ~/.elan.
            export ELAN_HOME="''${ELAN_HOME:-$PWD/.elan}"
            export PATH="$ELAN_HOME/bin:$PATH"

            # Lake and elan both download over TLS.
            export SSL_CERT_FILE="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
            export CURL_CA_BUNDLE="$SSL_CERT_FILE"

            if [ ! -x "$ELAN_HOME/bin/lake" ]; then
              echo "==> installing the Lean toolchain named in ./lean-toolchain"
              elan toolchain install "$(cat lean-toolchain)" >/dev/null
              elan default "$(cat lean-toolchain)" >/dev/null
            fi

            echo "Lean toolchain: $(cat lean-toolchain)"
            echo "Next: make setup   (fetch Mathlib + its prebuilt oleans)"
            echo "Then: make build   (check every proof in this repo)"
          '';
        };

        # `nix flake check` only sanity-checks the shell; the real check is
        # `make build`, which is what CI runs.  A pure-Nix Mathlib build is
        # deliberately not attempted here: it would rebuild Mathlib from
        # source and discard the upstream olean cache.
        checks.devShell = self.devShells.${system}.default;
      });
}
