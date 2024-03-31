let
 pkgs = import <nixpkgs> {};
 # choose the ocaml version you want to use
 ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
in
pkgs.mkShell {

  # build tools
  nativeBuildInputs = with ocamlPackages; [ ocaml findlib dune_3 ocaml-lsp ];

  # dependencies
  buildInputs = with ocamlPackages; [ ocamlgraph menhir ocaml-vdom ];

  packages = with pkgs; [ (vscode-with-extensions.override {
    vscodeExtensions = with vscode-extensions; [
      ocamllabs.ocaml-platform
      vscodevim.vim
    ]; })
    opam
    ocamlformat
    ocamlPackages.utop
  ];
}
