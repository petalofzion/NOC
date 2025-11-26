import Lake
open Lake DSL

package «NOC» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
    -- ⟨`weak.linter.mathlibStandardSet, true⟩ -- (Optional: enable if supported by your Lean version)
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.23.0"

@[default_target]
lean_lib «NOC» where
  -- You can add `globs := #["NOC/**"]` if you want explicit globs; default works fine.
  -- globs := #["NOC/**"]
