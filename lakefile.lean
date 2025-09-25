import Lake
open Lake DSL

package «RBHOTT» where

@[default_target]
lean_lib «RBHOTT» where
  srcDir := "src"
  globs := #[.submodules `RBHOTT]

lean_exe rbhott where
  root := `Main
