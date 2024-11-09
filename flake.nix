{
  description = "A flake with builds and shells for computacao-algebrica";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        defaultShellHook = { shellName, ... }: ''
            export PS1="\n\[\033[1;32m\][${shellName}: \w]\n\$\[\033[0m\] "
            export PURE="$([[ $IN_NIX_SHELL = 'pure' ]] && echo 1 || echo 0)"
            echo "PURE=$PURE"
            echo -n '>> Welcome to ${shellName}! <<'
          '';
        myShell = input@{
            name,
            buildInputs ? [],
            toShellName ? n: "${n}-shell",
            shellHook ? defaultShellHook,
          }: pkgs.mkShell {
            name = toShellName name;

            buildInputs = buildInputs;

            shellHook = shellHook
              (input // {
                inherit defaultShellHook;
                shellName = toShellName name;
              });
          };
      in {
        devShells = {
          default = self.devShells.${system}.singular;

          singular = myShell {
            name = "singular";
            buildInputs = with pkgs; [
              singular
            ];
          };
        };
      });
}
