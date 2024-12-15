let
	pkgs = import (builtins.fetchTarball {
		url = "https://github.com/NixOS/nixpkgs/archive/7a339d87931bba829f68e94621536cad9132971a.tar.gz"; # gets lean4 v4.4.0, as v4.3.0 was not uploaded
	}) {};
	myPkg = pkgs.lean4;
in
{
  pkgs ? import <nixpkgs> { },
}:
pkgs.mkShellNoCC {
  nativeBuildInputs = [ myPkg ];
  shellHook = ''
    elan override set 4.4.0 && elan run 4.4.0 lake exe cache get && elan run 4.4.0 lake build Library && elan run 4.4.0 lake build AutograderLib
  ''; # not sure, but it might be the thing that's spawning all those lean instancesy
}
