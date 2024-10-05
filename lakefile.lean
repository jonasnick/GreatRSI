import Lake
open Lake DSL

package "greatrsi" where
  version := v!"0.1.0"

lean_lib «GreatRSI» where
  -- add library configuration options here

@[default_target]
lean_exe "wots" where
  root := `Main
