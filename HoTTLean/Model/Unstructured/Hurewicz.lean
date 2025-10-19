import HoTTLean.Model.Unstructured.UnstructuredUniverse
import Mathlib.CategoryTheory.NatIso

universe u v

noncomputable section

open CategoryTheory Opposite

namespace Model

namespace UnstructuredUniverse

open MonoidalCategory

open Functor in
structure Cylinder (Ctx : Type u) [Category Ctx] where
  (I : Ctx ⥤ Ctx)
  (δ0 δ1 : 𝟭 Ctx ⟶ I)
  (π : I ⟶ 𝟭 Ctx)
  (δ0_π : δ0 ≫ π = 𝟙 _)
  (δ1_π : δ1 ≫ π = 𝟙 _)
  (symm : I ⋙ I ≅ I ⋙ I)
  -- (δ_0_symm : whiskerLeft I δ0 ≫ symm.hom = whiskerRight δ0 I )
  -- (δ_1_symm : whiskerLeft I δ1 ≫ symm.hom = whiskerRight δ1 I )
  -- (symm_π_π : symm.hom ≫ whiskerRight π I ≫ π = whiskerRight π I ≫ π)

variable {Ctx : Type u} [Category Ctx] (cyl : Cylinder Ctx)

namespace Cylinder

@[reassoc (attr := simp)]
lemma δ0_π' : cyl.δ0 ≫ cyl.π = 𝟙 _ := δ0_π _

@[reassoc (attr := simp)]
lemma δ1_π' : cyl.δ1 ≫ cyl.π = 𝟙 _ := δ1_π _

@[reassoc (attr := simp)]
lemma δ0_π'_app (X) : cyl.δ0.app X ≫ cyl.π.app _ = 𝟙 _ := by
  simp [← NatTrans.comp_app]

@[reassoc (attr := simp)]
lemma δ1_π'_app (X) : cyl.δ1.app X ≫ cyl.π.app _ = 𝟙 _ := by
  simp [← NatTrans.comp_app]

@[reassoc]
lemma δ0_naturality {Γ Δ} (σ : Δ ⟶ Γ) : cyl.δ0.app Δ ≫ cyl.I.map σ = σ ≫ cyl.δ0.app Γ := by
  simp [← NatTrans.naturality]

@[reassoc]
lemma δ1_naturality {Γ Δ} (σ : Δ ⟶ Γ) : cyl.δ1.app Δ ≫ cyl.I.map σ = σ ≫ cyl.δ1.app Γ := by
  simp [← NatTrans.naturality]

structure Hurewicz {X Y : Ctx} (f : Y ⟶ X) where
  (lift : ∀ {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X), y ≫ f = cyl.δ0.app Γ ≫ p →
    (cyl.I.obj Γ ⟶ Y))
  (lift_comp_self : ∀ {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p), lift y p comm_sq ≫ f = p)
  (δ0_comp_lift : ∀ {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p), cyl.δ0.app Γ ≫ lift y p comm_sq = y)

variable {cyl} {X Y : Ctx} {f : Y ⟶ X} (hrwcz : cyl.Hurewicz f)

@[reassoc (attr := simp)]
lemma Hurewicz.lift_comp_self' {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p) : hrwcz.lift y p comm_sq ≫ f = p :=
  lift_comp_self ..

@[reassoc (attr := simp)]
lemma Hurewicz.δ0_comp_lift' {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p) : cyl.δ0.app Γ ≫ hrwcz.lift y p comm_sq = y :=
  δ0_comp_lift ..

class Hurewicz.IsUniform : Prop where
  (lift_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p), hrwcz.lift (σ ≫ y) (cyl.I.map σ ≫ p)
    (by simp [comm_sq, δ0_naturality_assoc]) = cyl.I.map σ ≫ hrwcz.lift y p comm_sq)

@[reassoc]
lemma Hurewicz.lift_comp [IsUniform hrwcz] {Γ Δ} (σ : Δ ⟶ Γ) (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p) : hrwcz.lift (σ ≫ y) (cyl.I.map σ ≫ p)
    (by simp [comm_sq, δ0_naturality_assoc]) = cyl.I.map σ ≫ hrwcz.lift y p comm_sq :=
  IsUniform.lift_comp ..

class Hurewicz.IsNormal : Prop where
  (isNormal : ∀ {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X) (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p)
    (x : Γ ⟶ X), p = cyl.π.app Γ ≫ x → hrwcz.lift y p comm_sq = cyl.π.app Γ ≫ y)

@[reassoc]
lemma Hurewicz.isNormal [IsNormal hrwcz] {Γ} (y : Γ ⟶ Y) (p : cyl.I.obj Γ ⟶ X)
    (comm_sq : y ≫ f = cyl.δ0.app Γ ≫ p) (x : Γ ⟶ X) (hp : p = cyl.π.app Γ ≫ x) :
    hrwcz.lift y p comm_sq = cyl.π.app Γ ≫ y := by
  sorry

end Cylinder

open Cylinder

structure Path (U : UnstructuredUniverse Ctx) where
  (Id : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm), (a0 ≫ U.tp = A) → a1 ≫ U.tp = A →
    (Γ ⟶ U.Ty))
  (Id_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm)
    (a0_tp : a0 ≫ U.tp = A) (a1_tp : a1 ≫ U.tp = A),
    Id (A := σ ≫ A) (σ ≫ a0) (σ ≫ a1) (by simp [a0_tp]) (by simp [a1_tp]) =
    σ ≫ Id a0 a1 a0_tp a1_tp)
  (unPath : ∀ {Γ} {A : Γ ⟶ U.Ty} (p : cyl.I.obj Γ ⟶ U.Tm),
    p ≫ U.tp = cyl.π.app Γ ≫ A → (Γ ⟶ U.Tm))
  (unPath_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.Ty}
    (p : cyl.I.obj Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = cyl.π.app Γ ≫ A),
    unPath (A := σ ≫ A) ((cyl.I.map σ) ≫ p) (by simp [p_tp]) =
    σ ≫ unPath p p_tp)
  (unPath_tp : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (p : cyl.I.obj Γ ⟶ U.Tm)
    (p_tp : p ≫ U.tp = cyl.π.app Γ ≫ A) (δ0_p : cyl.δ0.app Γ ≫ p = a0)
    (δ1_p : cyl.δ1.app Γ ≫ p = a1), unPath p p_tp ≫ U.tp =
    Id (A := A) a0 a1 (by simp [← δ0_p, p_tp]) (by simp [← δ1_p, p_tp]))
  (path : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm), p ≫ U.tp =
    Id a0 a1 a0_tp a1_tp → (cyl.I.obj Γ ⟶ U.Tm))
  (path_tp : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = Id a0 a1 a0_tp a1_tp),
    path a0 a1 a0_tp a1_tp p p_tp ≫ U.tp = cyl.π.app _ ≫ A)
  (δ0_path : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = Id a0 a1 a0_tp a1_tp),
    cyl.δ0.app _ ≫ path a0 a1 a0_tp a1_tp p p_tp = a0)
  (δ1_path : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = Id a0 a1 a0_tp a1_tp),
    cyl.δ1.app _ ≫ path a0 a1 a0_tp a1_tp p p_tp = a1)
  (path_unPath : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (p : cyl.I.obj Γ ⟶ U.Tm)
    (p_tp : p ≫ U.tp = cyl.π.app Γ ≫ A) (δ0_p : cyl.δ0.app Γ ≫ p = a0)
    (δ1_p : cyl.δ1.app Γ ≫ p = a1),
    path (A := A) a0 (a1) (by simp [← δ0_p, p_tp]) (by simp [← δ1_p, p_tp])
    (unPath p p_tp) (unPath_tp a0 a1 p p_tp δ0_p δ1_p) = p)
  (unPath_path : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = Id a0 a1 a0_tp a1_tp),
    unPath (A := A) (path a0 a1 a0_tp a1_tp p p_tp)
    (path_tp ..) = p)

namespace Path

variable {cyl} {U0 : UnstructuredUniverse Ctx} (P0 : Path cyl U0)

-- TODO: make stability under precomposition/naturality lemma for `path` using `unPath_comp`
-- and the bijection `path_unPath` and `unPath_path`
-- lemma path_comp

@[reassoc (attr := simp)]
lemma unPath_tp' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (p : cyl.I.obj Γ ⟶ U0.Tm)
    (p_tp : p ≫ U0.tp = cyl.π.app Γ ≫ A) (δ0_p : cyl.δ0.app Γ ≫ p = a0)
    (δ1_p : cyl.δ1.app Γ ≫ p = a1) : P0.unPath p p_tp ≫ U0.tp =
    P0.Id (A := A) a0 a1 (by simp [← δ0_p, p_tp]) (by simp [← δ1_p, p_tp]) :=
  P0.unPath_tp a0 a1 p p_tp δ0_p δ1_p

@[reassoc (attr := simp)]
lemma path_tp' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Γ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = P0.Id a0 a1 a0_tp a1_tp) :
    P0.path a0 a1 a0_tp a1_tp p p_tp ≫ U0.tp = cyl.π.app _ ≫ A :=
  path_tp ..

@[reassoc (attr := simp)]
lemma path_unPath' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (p : cyl.I.obj Γ ⟶ U0.Tm)
    (p_tp : p ≫ U0.tp = cyl.π.app Γ ≫ A) (δ0_p : cyl.δ0.app Γ ≫ p = a0)
    (δ1_p : cyl.δ1.app Γ ≫ p = a1) :
    P0.path (A := A) a0 (a1) (by simp [← δ0_p, p_tp]) (by simp [← δ1_p, p_tp])
    (P0.unPath p p_tp) (P0.unPath_tp a0 a1 p p_tp δ0_p δ1_p) = p :=
  P0.path_unPath a0 a1 p p_tp δ0_p δ1_p

@[reassoc (attr := simp)]
lemma unPath_path' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Γ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = P0.Id a0 a1 a0_tp a1_tp) :
    P0.unPath (A := A) (P0.path a0 a1 a0_tp a1_tp p p_tp) (P0.path_tp ..) = p :=
  unPath_path ..

/-- An alternative version of `unPath` that allows the domain context to be any context `Δ`,
not just the context `Γ` for `A`. -/
@[simp]
abbrev unPath' {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (p : cyl.I.obj Δ ⟶ U0.Tm)
    (p_tp : p ≫ U0.tp = cyl.π.app Δ ≫ σ ≫ A) : Δ ⟶ U0.Tm :=
  P0.unPath (A := σ ≫ A) p p_tp

abbrev path' {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Δ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = σ ≫ P0.Id a0 a1 a0_tp a1_tp) :
    (cyl.I.obj Δ ⟶ U0.Tm) :=
  P0.path (A := σ ≫ A) (σ ≫ a0) (σ ≫ a1) (by simp [a0_tp]) (by simp [a1_tp]) p
  (by simp [p_tp, ← Id_comp])

-- @[reassoc (attr := simp)]
-- lemma unPath'_tp {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm)
--     (a0_tp : a0 ≫ U0.tp = A) (a1_tp : a1 ≫ U0.tp = A)
--     (p : cyl.I.obj Δ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = cyl.π.app Δ ≫ σ ≫ A)
--     (δ0_p : cyl.δ0.app Δ ≫ p = σ ≫ a0) (δ1_p : cyl.δ1.app Δ ≫ p = σ ≫ a1) :
--     P0.unPath' σ a0 a1 p p_tp δ0_p δ1_p ≫ U0.tp =
--     σ ≫ P0.Id (A := A) a0 a1 a0_tp a1_tp := by
--   simp [unPath', ← Id_comp]

-- lemma unPath'_comp {Γ Δ0 Δ1} (τ : Δ1 ⟶ Δ0) (σ : Δ0 ⟶ Γ)
--     {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (p : cyl.I.obj Δ0 ⟶ U0.Tm)
--     (p_tp : p ≫ U0.tp = cyl.π.app Δ0 ≫ σ ≫ A) (δ0_p : cyl.δ0.app Δ0 ≫ p = σ ≫ a0)
--     (δ1_p : cyl.δ1.app Δ0 ≫ p = σ ≫ a1) :
--     P0.unPath' (τ ≫ σ) a0 a1 sorry sorry sorry sorry =
--     τ ≫ P0.unPath' σ a0 a1 p p_tp δ0_p δ1_p := sorry

variable (hrwcz0 : Hurewicz cyl U0.tp)

def substLift {Γ Δ} {A : Γ ⟶ U0.Ty} (a : Δ ⟶ U0.ext A) (p : cyl.I.obj Δ ⟶ Γ)
    (comm_sq : a ≫ disp .. = cyl.δ0.app Δ ≫ p) : cyl.I.obj Δ ⟶ U0.ext A :=
  substCons U0 p A (hrwcz0.lift (a ≫ var ..) (p ≫ A)
  (by (slice_rhs 1 2 => rw [← comm_sq]); simp)) (by simp)

@[reassoc (attr := simp)]
lemma substLift_comp_disp {Γ Δ} {A : Γ ⟶ U0.Ty} (a : Δ ⟶ U0.ext A) (p : cyl.I.obj Δ ⟶ Γ)
    (comm_sq : a ≫ disp .. = cyl.δ0.app Δ ≫ p) : substLift hrwcz0 a p comm_sq ≫ disp .. = p := by
  simp [substLift]

@[reassoc (attr := simp)]
lemma δ0_comp_substLift {Γ Δ} {A : Γ ⟶ U0.Ty} (a : Δ ⟶ U0.ext A) (p : cyl.I.obj Δ ⟶ Γ)
    (comm_sq : a ≫ disp .. = cyl.δ0.app Δ ≫ p) :
    cyl.δ0.app Δ ≫ substLift hrwcz0 a p comm_sq = a := by
  apply (disp_pullback ..).hom_ext <;> simp [comm_sq, substLift]

@[simps]
def polymorphicIdIntro : PolymorphicIdIntro U0 U0 where
  Id := P0.Id
  Id_comp := P0.Id_comp
  refl {_ A} a a_tp := P0.unPath (A := A) (cyl.π.app _ ≫ a) (by simp [a_tp])
  refl_comp σ A a a_tp := by simp [← unPath_comp, a_tp]
  refl_tp a a_tp := by simp

open PolymorphicIdIntro

variable [Hurewicz.IsUniform hrwcz0] [Hurewicz.IsNormal hrwcz0]

section connection

variable {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)

/-- The substitution `connectionAux` is defined using universal path lifting `hrwcz0.lift` -/
def connectionAux : cyl.I.obj (U0.ext (P0.polymorphicIdIntro.weakenId a a_tp)) ⟶ U0.ext A :=
  sorry

/-- The path lift needed in `connection`.
Fix `Γ ⊢ a : A`, we think of `connection` as a
path `(j : I);(x : A)(p : Id(a,x)) ⊢ χ j : Id(a,x)` such that `χ 0 = refl a`.
It is defined as the lift of the path `p i` (provided by the variable `p`)
in `Γ.A` up the fibration `Γ.A.Id → Γ.A`,
starting at the point `refl a` in the fiber over `a`.
-/
def connectionLift : cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp) ⟶ U0.Tm :=
  hrwcz0.lift (disp .. ≫ disp .. ≫ P0.polymorphicIdIntro.refl a a_tp)
  (P0.connectionAux a a_tp ≫ P0.polymorphicIdIntro.weakenId a a_tp) sorry

/-- Fix `Γ ⊢ a : A`, we think of `connection` as a cubical (as opposed to globular)
homotopy `(i j : I);(x : A)(p : Id(a,x)) ⊢ χ i j : A`
such that `χ 0 j = refl a j` is the reflexive path at `a : A` and `χ 1 j = p j`.
It will also satisfy `χ i 0 = refl a i`.

```
i→   j↓

a ====== p 0
‖         |
‖    χ    | p j
‖         V
a ====== p 1
```

We define `connection` by path lifting,
but we need to switch the indices using `cyl.symm` since
1. we need to do path lifting in the `j` direction (i.e. starting at `χ i 0 = refl a i`)
2. we eventually want a homotopy in the `i` direction (i.e. from `χ 0 j` to `χ 1 j`)
-/
def connection : cyl.I.obj (cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp)) ⟶ U0.Tm :=
  cyl.symm.hom.app _ ≫
  P0.path' (A := disp .. ≫ A) (cyl.π.app (P0.polymorphicIdIntro.motiveCtx a a_tp) ≫ disp ..)
    (disp .. ≫ a) (var ..)
    (by simp [a_tp])
    (by simp)
    (P0.connectionLift hrwcz0 a a_tp)
    sorry



  -- hrwcz0.lift (Γ := cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp))
  -- (cyl.π.app _ ≫ disp .. ≫ disp .. ≫ a)
  -- (cyl.π.app _ ≫ cyl.π.app _ ≫ disp .. ≫ disp .. ≫ A)
  -- (by simp [a_tp])

lemma connection_tp : P0.connection hrwcz0 a a_tp ≫ U0.tp =
    cyl.π.app (cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp)) ≫
    cyl.π.app (P0.polymorphicIdIntro.motiveCtx a a_tp) ≫
    U0.disp (P0.polymorphicIdIntro.weakenId a a_tp) ≫ U0.disp A ≫ A := by

  sorry

/-- Fixing `Γ ⊢ a : A`, `substConsConnection` is thought of as a substitution
`(i : I); (x : A) (p : Id(a,x)) ⊢ (α i : A, β i : Id (a, α i))`
such that at the start and end-points we have
`(α 0, β 0) = (a, refl a)` and `(α 1, β 1) = (x, p)`.
These equations are `δ0_substConsConnection` and `δ1_substConsConnection`, proven below.

It is defined by
-/
def substConsConnection : cyl.I.obj (U0.ext ((polymorphicIdIntro P0).weakenId a a_tp)) ⟶
    P0.polymorphicIdIntro.motiveCtx a a_tp :=
  U0.substCons (P0.connectionAux a a_tp) (P0.polymorphicIdIntro.weakenId a a_tp)
  (P0.unPath' (Δ := cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp)) (Γ := U0.ext A)
    (cyl.π.app _ ≫ disp ..) (A := disp .. ≫ A) (P0.connection hrwcz0 a a_tp)
    (by simp only [Functor.id_obj, Category.assoc, connection_tp]))
  (by
    simp [← Id_comp]
    congr 1
    · sorry
    · sorry
    · sorry)

@[reassoc (attr := simp)]
lemma δ0_substConsConnection : cyl.δ0.app _ ≫ P0.substConsConnection hrwcz0 a a_tp =
    disp .. ≫ disp .. ≫ reflSubst _ a a_tp := by
  apply (disp_pullback ..).hom_ext
  · simp [substConsConnection]
    rw [← unPath_comp]
    sorry
  · simp [substConsConnection]
    sorry

@[reassoc (attr := simp)]
lemma δ1_substConsConnection : cyl.δ1.app _ ≫ P0.substConsConnection hrwcz0 a a_tp = 𝟙 _ := by
  apply (disp_pullback ..).hom_ext
  · simp [substConsConnection]
    sorry
  · simp [substConsConnection]
    sorry

@[reassoc]
lemma substConsConnection_comp_motiveSubst :
    P0.substConsConnection hrwcz0 (σ ≫ a) (by simp [a_tp]) ≫ motiveSubst _ σ a a_tp =
    cyl.I.map (motiveSubst _ σ a a_tp) ≫ P0.substConsConnection hrwcz0 a a_tp :=
  sorry

/-- `substConsConnection` is *normal*. -/
@[reassoc]
lemma reflSubst_comp_substConsConnection : cyl.I.map (reflSubst _ a a_tp) ≫
    P0.substConsConnection hrwcz0 a a_tp = cyl.π.app _ ≫ reflSubst _ a a_tp := sorry

end connection

variable (U1 : UnstructuredUniverse Ctx) (hrwcz1 : Hurewicz cyl U1.tp) [Hurewicz.IsUniform hrwcz1]
  [Hurewicz.IsNormal hrwcz1]

def polymorphicIdElim : PolymorphicIdElim (polymorphicIdIntro P0) U1 where
  j a a_tp C c c_tp := cyl.δ1.app _ ≫ hrwcz1.lift (disp .. ≫ disp .. ≫ c)
    (substConsConnection P0 hrwcz0 a a_tp ≫ C) (by rw [δ0_substConsConnection_assoc]; simp [c_tp]) -- FIXME simp failed
  comp_j σ A a a_tp C c c_tp := by
    slice_rhs 1 2 => rw [← δ1_naturality]
    slice_rhs 2 3 => rw [← hrwcz1.lift_comp]
    congr 2
    · simp [motiveSubst, substWk_disp_assoc]
    · rw [substConsConnection_comp_motiveSubst_assoc]
  j_tp a a_tp C c c_tp := by
    simp only [motiveCtx, polymorphicIdIntro_Id, Category.assoc, Hurewicz.lift_comp_self']
    erw [δ1_substConsConnection_assoc] -- FIXME simp, rw failed
  reflSubst_j {Γ A} a a_tp C c c_tp := calc _
    _ = cyl.δ1.app Γ ≫ cyl.I.map (reflSubst _ a a_tp) ≫
        hrwcz1.lift (U0.disp (weakenId _ a a_tp) ≫ U0.disp A ≫ c) (P0.substConsConnection hrwcz0 a a_tp ≫ C) _ := by
      rw [← δ1_naturality_assoc]
    _ = cyl.δ1.app Γ ≫
    hrwcz1.lift
      (reflSubst _ a a_tp ≫ disp .. ≫ disp .. ≫ c)
      (cyl.I.map (reflSubst _ a a_tp) ≫ P0.substConsConnection hrwcz0 a a_tp ≫ C) _ := by
      rw [← Hurewicz.lift_comp]
    _ = cyl.δ1.app Γ ≫ cyl.π.app Γ ≫ P0.polymorphicIdIntro.reflSubst a a_tp ≫
        U0.disp (P0.polymorphicIdIntro.weakenId a a_tp) ≫ U0.disp A ≫ c := by
      rw [Hurewicz.isNormal hrwcz1 _ _ _ (P0.polymorphicIdIntro.reflSubst a a_tp ≫ C)]
      rw [reflSubst_comp_substConsConnection_assoc]
    _ = c := by simp [reflSubst]

end Path
