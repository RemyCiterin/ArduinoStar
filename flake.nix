{
  description = "ArduinoStar";

  inputs = {
    fstar.url = "github:fstarlang/fstar";
    flake-utils.follows = "fstar/flake-utils";
    nixpkgs.follows = "fstar/nixpkgs";
    karamel = {
      url = "github:fstarlang/karamel";
      inputs.fstar.follows = "fstar";
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  # outputs = { self, fstar, flake-utils, nixpkgs, karamel }: {
  #   packages.x86_64-linux.hello = nixpkgs.legacyPackages.x86_64-linux.hello;
  #   packages.x86_64-linux.default = self.packages.x86_64-linux.hello;
  # };

  outputs = { self, fstar, flake-utils, nixpkgs, karamel }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };
        fstarPackages = fstar.packages.${system};
        karamel-home = karamel.packages.${system}.karamel.home;
        ArduinoStar = pkgs.callPackage ./nix/ArduinoStar.nix {
          inherit (fstarPackages) ocamlPackages z3 fstar;
          karamel = karamel-home;
          fstar-scripts = "${fstar}/.scripts";
          inherit pkgs;
        };
      in
      {
        packages = {
          inherit ArduinoStar;
          default = ArduinoStar;
        };
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [ ccls ];
        };
      });
}
