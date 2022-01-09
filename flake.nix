{
  description = "Conceptual mathematics: learning category theory once and for all";

  inputs = {
    nixpkgs.url = github:nixos/nixpkgs/nixpkgs-unstable;
    flake-utils.url = github:numtide/flake-utils;
  };

  outputs = inputs:
    with inputs.flake-utils.lib;
    eachDefaultSystem (system:

    let
      pkgs = import inputs.nixpkgs {
        inherit system;
      };
      utils = inputs.flake-utils.lib;
    in
      {
        # nix develop
        devShell =
          pkgs.mkShell {
            buildInputs = with pkgs; [
              (agda.withPackages (ps: [
                ps.standard-library
                ])
              )
            ];
          };
      });
}
