{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  name = "tarantool-small";

  buildInputs = with pkgs; [
    alloy6
    gnumake
    python3
  ];
}
