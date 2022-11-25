{
  description = "A very basic flake";

  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let pkgs = nixpkgs.legacyPackages.${system};
      in
        {
          packages.default = pkgs.agdaPackages.mkDerivation rec {
            pname = "UniAgda";
            version = "0.0.1";
            src = ./.;
            everythingFile = "./UniAgda/Everything.agda";
            libraryName = "UniAgda";
            libraryFile = "UniAgda.agda-lib";
            meta = {
              homepage = https://github.com/jeslie0/UniAgda;
              description = "A HoTT library, written in Agda.";
            };
          };




          defaultPackage = self.packages.${system}.default;
          devShell = pkgs.mkShell {
            inputsFrom = [ ]; # Include build inputs from packages in
            # this list
            buildInputs = [ ]; # Extra packages to go in the shell
          };
      }
    );

}
