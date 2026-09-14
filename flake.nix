{
  description = "Nix flake for building sHoTT documentation";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    pygments-rzk = {
      url = "github:rzk-lang/pygments-rzk";
      flake = false;
    };
    mkdocs-plugin-rzk = {
      url = "github:rzk-lang/mkdocs-plugin-rzk";
      flake = false;
    };
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    pygments-rzk,
    mkdocs-plugin-rzk,
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {inherit system;};

        pkg-pygments-rzk = pkgs.python3.pkgs.buildPythonPackage {
          pname = "pygments-rzk";
          version = "0.1.6";
          src = pygments-rzk;
          format = "pyproject";
          nativeBuildInputs = [pkgs.python3.pkgs.setuptools];
          propagatedBuildInputs = [pkgs.python3.pkgs.pygments];
        };

        pkg-mkdocs-plugin-rzk = pkgs.python3.pkgs.buildPythonPackage {
          pname = "mkdocs-plugin-rzk";
          version = "0.1.4";
          src = mkdocs-plugin-rzk;
          format = "pyproject";
          nativeBuildInputs = [pkgs.python3.pkgs.setuptools];
          propagatedBuildInputs = [
            pkgs.python3.pkgs.mkdocs
          ];
        };

        pythonEnv = pkgs.python3.withPackages (ps:
          with ps; [
            mkdocs
            mkdocs-material
            python-markdown-math
            pkg-pygments-rzk
            pkg-mkdocs-plugin-rzk
          ]);
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pythonEnv
          ];
        };
      }
    );
}
