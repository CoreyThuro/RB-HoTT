import Lake
open Lake DSL

package «RBHOTT» where
  -- add any dependencies here if needed

@[default_target]
lean_lib «RBHOTT» where
  srcDir := "src"

lean_exe rbhott where
  root := `Main
  srcDir := "src"

lean_exe «check-budgets» where
  root := `RBHOTT.Scripts.CheckBudgets
  srcDir := "scripts"
  supportInterpreter := true
