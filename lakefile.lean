import Lake
open Lake DSL

package «lean4-no_mathlib» where
  -- add package configuration options here

lean_lib «Lean4NoMathlib» where
  -- add library configuration options here

@[default_target]
lean_exe «lean4-no_mathlib» where
  root := `Main

require std from git "https://github.com/leanprover/std4" @ "main"
