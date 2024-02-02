{
  description = "lean4-protobuf";

  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils }: utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };
      inherit (pkgs) lean4 mkShell;
    in
    {
      devShells.default = mkShell {
        packages = [ lean4 ];
      };
    });
}
