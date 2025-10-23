import Lake
open Lake DSL

require mathlib from git "https://github.com/jlh18/mathlib4" @ "clans"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.23.0-rc2"

package hottlean where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`grind.warning, false⟩
  ]

/-- We must ensure the theory prelude gets built
so that theory environments can be created from its `.olean`.
But we should not import the theory prelude into any external Lean environment.
So it is built manually. -/
lean_lib Prelude where
  roots := #[`HoTTLean.Prelude]

@[default_target]
lean_lib HoTTLean where
  needs := #[Prelude]

@[test_driver]
lean_lib test where
