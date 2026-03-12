let
  pkgs = import <nixpkgs> {
  };
  antigravity = pkgs.callPackage ./antigravity.nix {};

in pkgs.mkShell{
  packages = [
    #pkgs.antigravity
    pkgs.google-chrome
    antigravity
  ] ++ (with pkgs; [
    python313 ( with python313.pkgs; [requests pandas networkx linearmodels numpy scipy statsmodels] )
    jq
  ]) ;
  shellHook = ''
    LANG=C
  '';
}
