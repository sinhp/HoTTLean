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
  (δ0_symm : whiskerLeft I δ0 ≫ symm.hom = whiskerRight δ0 I)
  (δ1_symm : whiskerLeft I δ1 ≫ symm.hom = whiskerRight δ1 I)
  (symm_π_π : symm.hom ≫ whiskerLeft I π ≫ π = whiskerLeft I π ≫ π)

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

-- open Functor in
-- @[reassoc]
-- lemma symm_π_π' : cyl.symm.hom ≫ whiskerLeft cyl.I cyl.π ≫ cyl.π =
--     whiskerLeft cyl.I cyl.π ≫ cyl.π :=
--   symm_π_π ..

@[reassoc (attr := simp)]
lemma δ0_symm_app (X) : cyl.δ0.app (cyl.I.obj X) ≫ cyl.symm.hom.app X = cyl.I.map (cyl.δ0.app X) :=
  NatTrans.congr_app (cyl.δ0_symm) X

@[reassoc (attr := simp)]
lemma δ1_symm_app (X) : cyl.δ1.app (cyl.I.obj X) ≫ cyl.symm.hom.app X = cyl.I.map (cyl.δ1.app X) :=
  NatTrans.congr_app (cyl.δ1_symm) X

@[reassoc]
lemma symm_π_π'_app (X) : cyl.symm.hom.app X ≫ cyl.π.app (cyl.I.obj X) ≫ cyl.π.app X =
    cyl.π.app (cyl.I.obj X) ≫ cyl.π.app X :=
  NatTrans.congr_app (cyl.symm_π_π) X

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
    hrwcz.lift y p comm_sq = cyl.π.app Γ ≫ y :=
  IsNormal.isNormal y p comm_sq x hp

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
    path (A := A) a0 a1 (by simp [← δ0_p, p_tp]) (by simp [← δ1_p, p_tp])
    (unPath p p_tp) (unPath_tp a0 a1 p p_tp δ0_p δ1_p) = p)
  (unPath_path : ∀ {Γ} {A : Γ ⟶ U.Ty} (a0 a1 : Γ ⟶ U.Tm) (a0_tp : a0 ≫ U.tp = A)
    (a1_tp : a1 ≫ U.tp = A) (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = Id a0 a1 a0_tp a1_tp),
    unPath (A := A) (path a0 a1 a0_tp a1_tp p p_tp)
    (path_tp ..) = p)

namespace Path

variable {cyl} {U0 : UnstructuredUniverse Ctx} (P0 : Path cyl U0)

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

@[reassoc (attr := simp)]
lemma δ0_path' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Γ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = P0.Id a0 a1 a0_tp a1_tp) :
    cyl.δ0.app _ ≫ P0.path a0 a1 a0_tp a1_tp p p_tp = a0 :=
  δ0_path ..

@[reassoc (attr := simp)]
lemma δ1_path' {Γ} {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Γ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = P0.Id a0 a1 a0_tp a1_tp) :
    cyl.δ1.app _ ≫ P0.path a0 a1 a0_tp a1_tp p p_tp = a1 :=
  δ1_path ..

lemma path_ext {Γ} (A : Γ ⟶ U0.Ty) (a0 a1 : Γ ⟶ U0.Tm) (p1 p2 : cyl.I.obj Γ ⟶ U0.Tm)
    (p1_tp : p1 ≫ U0.tp = cyl.π.app Γ ≫ A) (p2_tp : p2 ≫ U0.tp = cyl.π.app Γ ≫ A)
    (h : P0.unPath p1 p1_tp = P0.unPath p2 p2_tp)
    (δ0_p1 : cyl.δ0.app Γ ≫ p1 = a0) (δ1_p1 : cyl.δ1.app Γ ≫ p1 = a1)
    (δ0_p2 : cyl.δ0.app Γ ≫ p2 = a0) (δ1_p2 : cyl.δ1.app Γ ≫ p2 = a1) : p1 = p2 := by
  rw [← P0.path_unPath (A := A) a0 a1 p1 p1_tp δ0_p1 δ1_p1]
  rw [← P0.path_unPath a0 a1 p2 p2_tp δ0_p2 δ1_p2]
  rw! [h]

lemma path_comp {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Γ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = P0.Id a0 a1 a0_tp a1_tp) :
    P0.path (A := σ ≫ A) (σ ≫ a0) (σ ≫ a1) (by simp [a0_tp]) (by simp [a1_tp]) (σ ≫ p)
    (by simp [p_tp, ← Id_comp]) = cyl.I.map σ ≫ P0.path a0 a1 a0_tp a1_tp p p_tp := by
  apply P0.path_ext (σ ≫ A) (σ ≫ a0) (σ ≫ a1) <;> simp [unPath_comp, δ0_naturality_assoc,
    δ1_naturality_assoc]

/-- An alternative version of `unPath` that allows the domain context to be any context `Δ`,
not just the context `Γ` for `A`. -/
@[simp]
abbrev unPath' {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (p : cyl.I.obj Δ ⟶ U0.Tm)
    (p_tp : p ≫ U0.tp = cyl.π.app Δ ≫ σ ≫ A) : Δ ⟶ U0.Tm :=
  P0.unPath (A := σ ≫ A) p p_tp

@[simp]
abbrev path' {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a0 a1 : Γ ⟶ U0.Tm) (a0_tp : a0 ≫ U0.tp = A)
    (a1_tp : a1 ≫ U0.tp = A) (p : Δ ⟶ U0.Tm) (p_tp : p ≫ U0.tp = σ ≫ P0.Id a0 a1 a0_tp a1_tp) :
    cyl.I.obj Δ ⟶ U0.Tm :=
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

section connection

variable {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)

/-- Fixing `Γ ⊢ a : A`, `ev` / `substConsEv` can be viewed as the cubical substitution
`(i : I);(x : A).(p : Id(a,x)) ⊢ p' i : A`,
satisfying equations `p' 0 = a` and `p' 1 = x`,
proven in `δ0_ev` and `δ1_ev`.
It can be thought of as the "evaluation" of the path `p` at a point in the interval.
It is defined by taking `path` of the map `var : Γ.(x:A).Id(a,x) ⟶ Tm` -/
abbrev ev : cyl.I.obj (U0.ext (P0.polymorphicIdIntro.weakenId a a_tp)) ⟶ U0.Tm :=
  P0.path' (A := disp .. ≫ A) (disp ..) (disp .. ≫ a) (var ..)
  (by cat_disch) (by simp) (var ..) (by simp)

@[inherit_doc ev]
def substConsEv : cyl.I.obj (U0.ext (P0.polymorphicIdIntro.weakenId a a_tp)) ⟶ U0.ext A :=
  U0.substCons (cyl.π.app _ ≫ disp .. ≫ disp ..) A
  (P0.ev a a_tp) (by simp)

@[reassoc (attr := simp)]
lemma substConsEv_disp : P0.substConsEv a a_tp ≫ disp .. = cyl.π.app _ ≫ U0.disp _ ≫ U0.disp A := by
  simp [substConsEv]

@[reassoc (attr := simp)]
lemma substConsEv_var : P0.substConsEv a a_tp ≫ var .. = P0.path (A := disp .. ≫ disp .. ≫ A)
    (U0.disp .. ≫ U0.disp A ≫ a) (U0.disp .. ≫ U0.var A)
    (by cat_disch) (by simp) (U0.var ..) (by simp [← Id_comp]) := by
  simp [substConsEv, ev]

@[reassoc (attr := simp)]
lemma δ0_substConsEv : cyl.δ0.app _ ≫ P0.substConsEv a a_tp = disp .. ≫ disp .. ≫ U0.sec A a a_tp := by
  apply (disp_pullback ..).hom_ext
  · simp [substConsEv]
  · simp [substConsEv]

@[reassoc (attr := simp)]
lemma δ1_substConsEv : cyl.δ1.app _ ≫ P0.substConsEv a a_tp = U0.disp .. := by
  apply (disp_pullback ..).hom_ext
  · simp [substConsEv]
  · simp [substConsEv]

lemma substConsEv_comp_Id : P0.substConsEv a a_tp ≫
    P0.Id (A := disp .. ≫ A) (U0.disp A ≫ a) (U0.var A) (by cat_disch) (by simp) =
    P0.Id (A := cyl.π.app _ ≫ disp .. ≫ disp .. ≫ A)
    (cyl.π.app _ ≫ disp .. ≫ U0.disp A ≫ a) (P0.ev a a_tp)
    sorry sorry := by
  simp [← Id_comp]
  congr 1

-- lemma substConsEv_comp_Id' : P0.substConsEv a a_tp ≫
--     P0.Id (A := disp .. ≫ A) (U0.disp A ≫ a) (U0.var A) (by cat_disch) (by simp) =
--     cyl.π.app _ ≫  P0.Id (A := disp .. ≫ disp .. ≫ A)
--     (disp .. ≫ U0.disp A ≫ a) (by simp; sorry)
--     sorry sorry := by
--   rw [substConsEv_comp_Id]
--   simp [← Id_comp]
--   congr 1
--   -- have h := P0.path_comp (U0.disp (P0.Id (U0.disp A ≫ a) (U0.var A) sorry sorry)) (U0.disp A ≫ a)
--   --   (U0.var A) sorry sorry
--   sorry

/-- The path lift needed in `connection`.
Fix `Γ ⊢ a : A`, we think of `connection` as a
path `(j : I);(x : A)(p : Id(a,x)) ⊢ χ j : Id(a,x)` such that `χ 0 = refl a`.
It is defined as the lift of the path `p i` (provided by the variable `p`)
in `Γ.A` up the fibration `Γ.A.Id → Γ.A`,
starting at the point `refl a` in the fiber over `a`.
-/
def connectionLift : cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp) ⟶ U0.Tm :=
  hrwcz0.lift (disp .. ≫ disp .. ≫ P0.polymorphicIdIntro.refl a a_tp)
  (P0.substConsEv a a_tp ≫ P0.polymorphicIdIntro.weakenId a a_tp) (by
    simp only [motiveCtx, polymorphicIdIntro_Id, polymorphicIdIntro_refl, Functor.id_obj,
      Category.assoc, δ0_π'_app_assoc, δ1_π'_app_assoc, unPath_tp', ← Id_comp, weakenId]
    rw! (transparency := .default) [P0.δ0_substConsEv_assoc a a_tp,
      P0.δ0_substConsEv_assoc a a_tp, P0.δ0_substConsEv_assoc a a_tp]
    simp)

/-- Fix `Γ ⊢ a : A`, we think of `connection` as a cubical (as opposed to globular)
homotopy `(i j : I);(x : A)(p : Id(a,x)) ⊢ χ i j : A`
such that `χ 0 j = refl a j` is the reflexive path at `a : A` and `χ 1 j = p j`.
These are proven below as `δ0_connection` and `δ1_connection` respectively.
It will also satisfy `χ i 0 = refl a i`.

```
i→   j↓

a ====== p 0
‖         |
‖    χ    | p j
‖         V
a -----> p 1
```
Note that we know the top path is `χ i 0 = refl a i`
but we do not know how the bottom path `χ i 1` computes.

We define `connection` by path lifting,
but we need to switch the indices using `cyl.symm` since
1. we need to do path lifting in the `j` direction (i.e. starting at `χ i 0 = refl a i`)
2. we substConsEventually want a homotopy in the `i` direction (i.e. from `χ 0 j` to `χ 1 j`)


`symmConnection` is the symmetric homotopy `j i ⊢ χ i j`, visualised as
```
j→   i↓

a ======  a
‖         |
‖    χ    |
‖         V
p 0 ----> p 1
    p j
```
Note that we know the left path is `χ i 0 = refl a i`
but we do not know how the right path `χ i 1` computes.
-/
abbrev symmConnection : cyl.I.obj (cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp)) ⟶ U0.Tm :=
  P0.path' (A := disp .. ≫ A) (substConsEv ..)
    (disp .. ≫ a) (var ..)
    (by simp [a_tp])
    (by simp)
    (P0.connectionLift hrwcz0 a a_tp)
    (by simp [connectionLift])

@[reassoc]
lemma δ0_symmConnection : cyl.δ0.app _ ≫ P0.symmConnection hrwcz0 a a_tp =
    cyl.π.app _ ≫ disp .. ≫ U0.disp A ≫ a := by
  simp

@[reassoc]
lemma δ1_symmConnection : cyl.δ1.app _ ≫ P0.symmConnection hrwcz0 a a_tp =
    P0.ev a a_tp := by
  simp only [symmConnection]
  simp only [path']
  simp only [δ1_path']
  simp [ev]

@[reassoc]
lemma I_δ0_symmConnection : cyl.I.map (cyl.δ0.app _) ≫ P0.symmConnection hrwcz0 a a_tp =
    cyl.π.app _ ≫ disp .. ≫ U0.disp A ≫ a := by
  fapply P0.path_ext (disp .. ≫ U0.disp A ≫ A) (disp .. ≫ U0.disp A ≫ a) (disp .. ≫ U0.disp A ≫ a)
    <;> simp [symmConnection, path', ← path_comp, connectionLift, ← unPath_comp, a_tp]

@[inherit_doc symmConnection]
def connection : cyl.I.obj (cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp)) ⟶ U0.Tm :=
  cyl.symm.hom.app _ ≫
  P0.path' (A := disp .. ≫ A) (substConsEv ..)
    (disp .. ≫ a) (var ..)
    (by simp [a_tp])
    (by simp)
    (P0.connectionLift hrwcz0 a a_tp)
    (by simp [connectionLift])

lemma connection_tp : P0.connection hrwcz0 a a_tp ≫ U0.tp =
    cyl.π.app (cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp)) ≫
    cyl.π.app (P0.polymorphicIdIntro.motiveCtx a a_tp) ≫
    U0.disp (P0.polymorphicIdIntro.weakenId a a_tp) ≫ U0.disp A ≫ A := by
  simp [connection, cyl.symm_π_π'_app_assoc]

-- @[reassoc]
-- lemma δ0_connection : cyl.δ0.app _ ≫ P0.connection hrwcz0 a a_tp =
--     P0.path (A := disp .. ≫ disp .. ≫ A) (disp .. ≫ U0.disp A ≫ a)
--     (disp .. ≫ U0.disp A ≫ a) (by aesop_cat) (by aesop_cat)
--     (cyl.δ0.app _ ≫ P0.connectionLift hrwcz0 a a_tp) (by simp [connectionLift, ← Id_comp]) := by
--   simp [connection, δ0_symm_app_assoc, ← path_comp]

@[reassoc]
lemma δ0_connection : cyl.δ0.app _ ≫ P0.connection hrwcz0 a a_tp =
    cyl.π.app _ ≫ disp .. ≫ U0.disp A ≫ a := by
  simp only [motiveCtx, polymorphicIdIntro_Id, Functor.id_obj, connection, Functor.comp_obj, path',
    substConsEv_disp_assoc, substConsEv_var, connectionLift, polymorphicIdIntro_refl, weakenId,
    δ0_symm_app_assoc, ← path_comp, δ0_π'_app_assoc, δ0_path', Hurewicz.δ0_comp_lift']
  apply P0.path_ext (disp .. ≫ disp .. ≫ A) (disp .. ≫ disp .. ≫ a) (disp .. ≫ disp .. ≫ a) <;>
  simp [a_tp, ← unPath_comp]

@[reassoc]
lemma δ1_connection : cyl.δ1.app _ ≫ P0.connection hrwcz0 a a_tp = P0.ev a a_tp := by
  simp only [connection]
  simp only [δ1_symm_app_assoc]
  simp only [path']
  simp only [← path_comp]

  fapply P0.path_ext (A := disp .. ≫ disp .. ≫ A) (disp .. ≫ disp .. ≫ a) (disp .. ≫ var ..) <;> simp
  -- simp only [motiveCtx, polymorphicIdIntro_Id, Functor.id_obj, Functor.comp_obj, path',
  --   substConsEv_disp_assoc, substConsEv_var, connectionLift, polymorphicIdIntro_refl, weakenId,
  --   δ1_symm_app_assoc, ← path_comp, δ1_π'_app_assoc, δ1_path', ev]
  -- congr 1
  · simp [← path_comp, connectionLift]
    -- rw [← hrwcz0.lift_comp]
    sorry
  -- P0.path (A := disp .. ≫ disp .. ≫ A) (disp .. ≫ U0.disp A ≫ a) (disp .. ≫ U0.var A)
  -- sorry sorry (var ..) sorry := sorry

/-- Fixing `Γ ⊢ a : A`, `substConsConnection` is thought of as a substitution
`(i : I); (x : A) (p : Id(a,x)) ⊢ (α i : A, β i : Id (a, α i))`
such that at the start and end-points we have
`(α 0, β 0) = (a, refl a)` and `(α 1, β 1) = (x, p)`.
These equations are `δ0_substConsConnection` and `δ1_substConsConnection`, proven below.
-/
def substConsConnection : cyl.I.obj (U0.ext ((polymorphicIdIntro P0).weakenId a a_tp)) ⟶
    P0.polymorphicIdIntro.motiveCtx a a_tp :=
  U0.substCons (P0.substConsEv a a_tp) (P0.polymorphicIdIntro.weakenId a a_tp)
  (P0.unPath' (Δ := cyl.I.obj (P0.polymorphicIdIntro.motiveCtx a a_tp)) (Γ := U0.ext A)
    ((cyl.π.app (U0.4 (P0.Id (U0.disp A ≫ a) (U0.var A) sorry sorry))) ≫ disp ..) (A := disp .. ≫ A) (P0.connection hrwcz0 a a_tp)
    (by simp [Functor.id_obj, motiveCtx, polymorphicIdIntro_Id, connection_tp]))
  (by
    simp
    simp [← Id_comp]
    congr 1
    · erw [δ0_connection]
      simp
    · simp [connection, ev, ← path_comp, connectionLift]
      congr 1
      sorry
    )

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
