{
  description = "lean4-protobuf";

  inputs = {
    nixpkgs.follows = "lean/nixpkgs";
    utils.follows = "lean/flake-utils";
    lean.url = "github:leanprover/lean4/v4.4.0";
  };

  outputs = { self, nixpkgs, utils, lean }@inputs: {
    overlays.default = final: prev: {
      # Use of `stdenv.hostPlatform` is fine cause buildLeanPackage doesn't
      # appear to support cross compiling anyway since it also references
      # `stdenv.hostPlatform`.
      lean4-protobuf =
        lean.packages.${final.stdenv.hostPlatform.system}.buildLeanPackage {
          name = "Protobuf";
          src = builtins.path { path = ./..; name = "lean4-protobuf-src"; };
          # TODO: Add `executableName` field once protoc plugin is implemented.
        };
    };
  } // utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs {
        overlays = [ self.overlays.default ];
        inherit system;
      };
      inherit (pkgs) lean4-protobuf mkShell;
      leanPkgs = inputs.lean.packages.${system};
      inherit (leanPkgs) lean-all;
    in
    {
      packages.default = lean4-protobuf.modRoot;

      devShells.default = mkShell {
        packages = [ lean-all ];
      };
    });
}
