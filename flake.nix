{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        indurative = pkgs.haskellPackages.callCabal2nix "indurative" ./. { };
      in {
        packages.default = indurative;

        devShell = with pkgs;
          haskellPackages.shellFor {
            packages = _: [ indurative ];
            shellHook = "hpack";
            buildInputs = with haskellPackages;
              [ hlint cabal-install haskell-language-server ];
          };
      }
    );
}
