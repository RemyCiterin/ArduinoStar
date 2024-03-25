{
  fetchFromGitHub, fstar, fstar-scripts, git, karamel, lib,
  ocamlPackages, z3, python3, stdenv, pkgs ? import <nixpkgs> { }
}:
let
  ArduinoStar = stdenv.mkDerivation {
    name = "ArduinoStar";

    src = lib.cleanSourceWith {
      src = ./..;
      filter = path: type:
        let relPath = lib.removePrefix (toString ./.. + "/") (toString path);
        in type == "directory" || lib.elem relPath [
          ".gitignore"
          "Makefile"
          "Makefile.common"
          "Makefile.include"
          ] || lib.any (lib.flip lib.hasPrefix relPath) [
          "code"
          "hints"
          "lib"
          "providers"
          "secure_api"
          "specs"
          "tests"
          "tools"
          "vale"
        ];
    };

    nativeBuildInputs = [ z3 fstar karamel python3 git ]
      ++ (with ocamlPackages; [
        ocaml
        findlib
        batteries
        pprint
        stdint
        yojson
        zarith
        ppxlib
        ppx_deriving
        ppx_deriving_yojson
        ctypes
        cppo
        alcotest
        qcheck-core
        secp256k1-internal
        menhirLib
        process
        sedlex
      ]);

      buildInputs = [
        z3
        pkgs.gnumake
        fstar
        karamel
        pkgs.emacsPackages.fstar-mode
      ];

    FSTAR_HOME = fstar;
    KRML_HOME = karamel;

    configurePhase = "export HACL_HOME=$(pwd)";

    enableParallelBuilding = true;

    installPhase = ''
      cp -r ./. $out
    '';

    dontFixup = true;
  };
in ArduinoStar


