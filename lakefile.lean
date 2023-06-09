import Lake
open Lake DSL

package «category» {
  -- add package configuration options here
}

lean_lib «Category» {
  -- add library configuration options here
}

--@[default_target]
--lean_exe «category» {
--  root := `Main
--}
require std from git "https://github.com/leanprover/std4.git" @ "5770b609aeae209cb80ac74655ee8c750c12aabd"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"724a444a35a78ce1922f5c3626ff618f50976f62"
require Qq from git "https://github.com/gebner/quote4" @ "master"
