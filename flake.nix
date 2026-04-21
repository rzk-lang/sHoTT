{
  description = "Rzk development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils"i;
    rzk-modal = "git+file://Users/lishy2/Workspace/rzk?ref=modal"
  };

  outputs = { self, nixpkgs, flake-utils, rzk-modal }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells.default = pkgs.mkShell {
          packages = [ rzk-modal ];
        };

        packages.default = rzk-modal;
      });
}
