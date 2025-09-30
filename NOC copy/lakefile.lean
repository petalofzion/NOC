import Lake
open Lake DSL

/-- Project package name (arbitrary). -/
package «NOC» where
  -- You can pin mathlib if you want reproducibility:
  -- more info: https://github.com/leanprover-community/mathlib4
  -- add any extra config here if needed

/-- mathlib dependency. You can add a commit hash with `@ "<commit>"` if you want to pin it. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

/-- Your local library root: modules live under `NOC/` and are imported as `NOC.*`. -/
@[default_target]
lean_lib «NOC» where
  -- You can add `globs := #["NOC/**"]` if you want explicit globs; default works fine.
  -- globs := #["NOC/**"]
