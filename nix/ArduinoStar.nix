{
  fetchFromGitHub, fstar, fstar-scripts, git, karamel, lib,
  ocamlPackages, z3, python3, stdenv
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
        zarith
      ]);

    buildInputs = [ z3 fstar karamel ];

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


