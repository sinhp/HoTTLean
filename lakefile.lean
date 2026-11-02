import Lake
open Lake DSL

-- Lean v4.34.1 port, proposed in sinhp/Poly#41.
require Poly from git "https://github.com/sosudo/Poly" @ "ba73d5149ac19b1186b6e58648217b52db6b8cdb"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.34.1"

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

/-- A target for the natural model.
We cannot include this in `HoTTLean.lean`
because it exports the same names as `Unstructured`. -/
lean_lib NaturalModel where
  roots := #[]
  globs := #[.submodules `HoTTLean.Model.Natural]

@[default_target]
lean_lib HoTTLean where
  needs := #[Prelude]

@[test_driver]
lean_lib HoTTLeanTest where
