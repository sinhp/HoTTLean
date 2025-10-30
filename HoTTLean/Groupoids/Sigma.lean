import HoTTLean.Groupoids.UnstructuredModel
import HoTTLean.ForMathlib.CategoryTheory.RepPullbackCone

-- TODO: come up with a more readable naming scheme for univs
universe v u v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

noncomputable section

namespace GroupoidModel

open CategoryTheory Model UnstructuredUniverse Opposite Functor.Groupoidal PGrpd

attribute [local simp] eqToHom_map Grpd.id_eq_id Grpd.comp_eq_comp Functor.id_comp

namespace FunctorOperation

section
-- TODO: univ levels are A < Γ < B nooooo
variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
    (B : ∫ A ⥤ Grpd.{v₃,u₃}) (x : Γ)
/--
For a point `x : Γ`, `(sigma A B).obj x` is the groupoidal Grothendieck
  construction on the composition
  `ι _ x ⋙ B : A.obj x ⥤ Groupoidal A ⥤ Grpd`
-/
def sigmaObj : Grpd := Grpd.of (∫ι A x ⋙ B)

variable {x} {y : Γ} (f : x ⟶ y)
/--
For a morphism `f : x ⟶ y` in `Γ`, `(sigma A B).map y` is a
composition of functors.
The first functor `map (whiskerRight (ιNatTrans f) B)`
is an equivalence which replaces `ι A x` with the naturally
isomorphic `A.map f ⋙ ι A y`.
The second functor is the action of precomposing
`A.map f` with `ι A y ⋙ B` on the Grothendieck constructions.

            map ⋯                  pre ⋯
  ∫ ι A x ⋙ B ⥤ ∫ A.map f ⋙ ι A y ⋙ B ⥤ ∫ ι A y ⋙ B
-/
def sigmaMap : sigmaObj B x ⥤ sigmaObj B y :=
  map (Functor.whiskerRight (ιNatTrans f) B) ⋙ pre (ι A y ⋙ B) (A.map f)

@[simp] theorem sigmaMap_obj_base (a) :
    ((sigmaMap B f).obj a).base = (A.map f).obj a.base :=
  rfl

@[simp] theorem sigmaMap_obj_fiber (a) :
    ((sigmaMap B f).obj a).fiber = (B.map ((ιNatTrans f).app a.base)).obj (a.fiber) := rfl

theorem ιNatTrans_app_base (a : sigmaObj B x) : ((ιNatTrans f).app a.base) = homMk f (𝟙 (A.map f).obj a.base) :=
  rfl

@[simp] theorem sigmaMap_map_base {a b : sigmaObj B x} {p : a ⟶ b} :
    ((sigmaMap B f).map p).base = (A.map f).map p.base := rfl

theorem sigmaMap_map_fiber_aux {a b : sigmaObj B x} {p : a ⟶ b} :
    (((ι A y ⋙ B)).map ((sigmaMap B f).map p).base).obj ((sigmaMap B f).obj a).fiber =
    (B.map ((ιNatTrans f).app (base b))).obj (((ι A x ⋙ B).map p.base).obj a.fiber) := by
  simp only [sigmaObj, sigmaMap, Functor.comp_obj, Functor.comp_map, pre_map_base, map_map_base,
    pre_obj_fiber, map_obj_fiber, Functor.whiskerRight_app]
  simp only [← Functor.comp_obj, ← Grpd.comp_eq_comp, ← Functor.map_comp]
  congr 2
  exact ((ιNatTrans f).naturality p.base).symm

@[simp] theorem sigmaMap_map_fiber {a b : sigmaObj B x} {p : a ⟶ b} :
    ((sigmaMap B f).map p).fiber =
    eqToHom (sigmaMap_map_fiber_aux B f) ≫ (B.map ((ιNatTrans f).app (base b))).map p.fiber := by
  simp only [sigmaObj, sigmaMap, Functor.comp_obj, Functor.comp_map,
    pre_map_fiber, map_map_fiber, Functor.whiskerRight_app]

variable {B}

@[simp] theorem sigmaMap_id_obj {p} : (sigmaMap B (𝟙 x)).obj p = p := by
  apply hext
  · simp [sigmaMap]
  · simp [sigmaMap, Grpd.eqToHom_obj]

@[simp] theorem sigmaMap_id_map {p1 p2} {hp2 : p2 = (sigmaMap B (𝟙 x)).obj p2}
    (f : p1 ⟶ p2) :
    (sigmaMap B (𝟙 x)).map f =
    eqToHom (by simp) ≫ f ≫ eqToHom (by simp) := by
  have h (a : A.obj x) : B.map ((ιNatTrans (𝟙 x)).app a) =
      eqToHom (by simp) :=
    calc
      B.map ((ιNatTrans (𝟙 x)).app a)
      _ = B.map (eqToHom (by simp)) := by
        rw [ιNatTrans_id_app]
      _ = eqToHom (by simp) := by
        simp
  have h1 : B.map ((ι A x).map (eqToHom hp2).base) = eqToHom (by simp) := by
    simp [sigmaObj, base_eqToHom]
  fapply Hom.ext
  · simp [sigmaObj, sigmaMap]
  · simp [sigmaObj, sigmaMap_map_fiber, Functor.congr_hom (h p2.base) f.fiber,
      Functor.congr_hom h1]

@[simp] theorem sigmaMap_id : sigmaMap B (𝟙 x) = 𝟭 _ := by
    apply CategoryTheory.Functor.ext
    · intro p1 p2 f
      simp
    · intro p
      simp

variable {z : Γ} {f} {g : y ⟶ z}

@[simp] theorem sigmaMap_comp_obj {p} : (sigmaMap B (f ≫ g)).obj p =
    (sigmaMap B g).obj ((sigmaMap B f).obj p) := by
  dsimp only [sigmaMap]
  apply hext
  · simp
  · simp only [sigmaObj, Functor.comp_obj, pre_obj_fiber, map_obj_fiber, Functor.whiskerRight_app,
      ιNatTrans_comp_app, Functor.map_comp, eqToHom_map, Grpd.comp_eq_comp, Grpd.eqToHom_obj, cast_heq_iff_heq, heq_eq_eq]
    aesop_cat

@[simp] theorem sigmaMap_comp_map {A : Γ ⥤ Grpd.{v₁,u₁}}
    {B : ∫(A) ⥤ Grpd.{v₃,u₃}} {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z}
    {p q : sigmaObj B x} (hpq : p ⟶ q)
    {h1 : (sigmaMap B (f ≫ g)).obj p = (sigmaMap B g).obj ((sigmaMap B f).obj p)}
    {h2 : (sigmaMap B g).obj ((sigmaMap B f).obj q) = (sigmaMap B (f ≫ g)).obj q}
    : (sigmaMap B (f ≫ g)).map hpq =
    eqToHom h1 ≫ (sigmaMap B g).map ((sigmaMap B f).map hpq) ≫ eqToHom h2 := by
  have h : B.map ((ιNatTrans (f ≫ g)).app q.base) =
    B.map ((ιNatTrans f).app q.base)
    ≫ B.map ((ιNatTrans g).app ((A.map f).obj q.base))
    ≫ eqToHom (by simp) := by simp
  fapply Hom.hext
  · simp only [sigmaObj, Grpd.coe_of, sigmaMap_obj_base, sigmaMap_map_base, Grpd.map_comp_map,
    comp_base, base_eqToHom]
  · have h3 : (ι A z ⋙ B).map (eqToHom h2).base
        = eqToHom (by simp only [sigmaMap, Functor.comp_obj]; congr 3) := by
      rw [base_eqToHom, eqToHom_map]
    simp only [sigmaObj, Grpd.coe_of, sigmaMap_obj_base, Functor.comp_obj, sigmaMap_map_base,
      Functor.comp_map, sigmaMap_obj_fiber, sigmaMap_map_fiber, Functor.congr_hom h,
      Grpd.comp_eq_comp, eqToHom_trans_assoc, comp_base, Functor.Groupoidal.comp_fiber,
      fiber_eqToHom, eqToHom_map, Functor.map_comp, Category.assoc, heq_eqToHom_comp_iff,
      heq_comp_eqToHom_iff, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rw! (transparency := .default) [Functor.congr_hom h3]
    simp only [sigmaObj, Functor.comp_obj, Functor.comp_map, heq_eqToHom_comp_iff,
      heq_comp_eqToHom_iff, heq_eq_eq]

theorem sigmaMap_comp : sigmaMap B (f ≫ g) = sigmaMap B f ⋙ sigmaMap B g := by
  apply CategoryTheory.Functor.ext
  · intro p q hpq
    simp
  · intro p
    simp

lemma sigmaMap_forget : sigmaMap B f ⋙ forget = forget ⋙ A.map f := rfl

/-- The formation rule for Σ-types for the ambient natural model `base`
  unfolded into operations between functors.
  See `sigmaObj` and `sigmaMap` for the actions of this functor.
 -/
@[simps] def sigma (A : Γ ⥤ Grpd.{v₁,u₁})
    (B : ∫(A) ⥤ Grpd.{v₃,u₃}) : Γ ⥤ Grpd.{max v₁ v₃, max u₁ u₃} where
  -- NOTE using Grpd.of here instead of earlier speeds things up
  obj x := sigmaObj B x
  map := sigmaMap B
  map_id _ := sigmaMap_id
  map_comp _ _ := sigmaMap_comp

variable (B) {Δ : Type u₄} [Category.{v₄} Δ] (σ : Δ ⥤ Γ)
theorem sigma_naturality_aux (x) :
    ι (σ ⋙ A) x ⋙ pre A σ ⋙ B = ι A (σ.obj x) ⋙ B := by
  rw [← ι_comp_pre]
  rfl

lemma whiskerRight_ιNatTrans_naturality {x y : Δ} (f : x ⟶ y) :
  Functor.whiskerRight (ιNatTrans f) (pre A σ ⋙ B) =
    eqToHom (sigma_naturality_aux B σ x) ≫ Functor.whiskerRight (ιNatTrans (σ.map f)) B ≫
    eqToHom (by simp [Functor.assoc, sigma_naturality_aux B σ y]) := by
  aesop

lemma sigma_naturality_obj (x) :
    Grpd.of (∫ι A (σ.obj x) ⋙ B)
    = Grpd.of (∫ι (σ ⋙ A) x ⋙ pre A σ ⋙ B) := by
  rw [sigma_naturality_aux]

lemma sigmaObj_naturality (x) :
    sigmaObj B (σ.obj x) = sigmaObj (pre A σ ⋙ B) x :=
  sigma_naturality_obj _ _ _

lemma sigmaMap_naturality {x y : Δ} (f : x ⟶ y) : sigmaMap B (σ.map f)
    = Grpd.homOf (map (eqToHom (sigma_naturality_aux B σ x).symm)) ≫
    sigmaMap (pre A σ ⋙ B) f ≫
    Grpd.homOf (map (eqToHom (sigma_naturality_aux B σ y))) := by
  have : pre (ι A (σ.obj y) ⋙ B) (A.map (σ.map f))
      = map (eqToHom (by rw[← (sigma_naturality_aux B σ y)]))
      ⋙ pre (ι (σ ⋙ A) y ⋙ pre A σ ⋙ B) (A.map (σ.map f))
      ⋙ map (eqToHom (sigma_naturality_aux B σ y)) := by
    rw [pre_congr_functor]
  dsimp [Grpd.homOf, sigmaMap, ← Functor.assoc]
  rw [← map_comp_eq, whiskerRight_ιNatTrans_naturality]
  simp [map_comp_eq, this, Functor.assoc]

lemma sigmaMap_naturality_heq {x y : Δ} (f : x ⟶ y) : sigmaMap B (σ.map f)
    ≍ sigmaMap (pre A σ ⋙ B) f := by
  rw [sigmaMap_naturality]
  simp only [sigmaObj, Functor.comp_obj, Grpd.homOf,
    ← eqToHom_eq_homOf_map (sigma_naturality_aux B σ x).symm,
    ← eqToHom_eq_homOf_map (sigma_naturality_aux B σ y)]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  rfl

-- NOTE formerly called `sigmaBeckChevalley`
theorem sigma_naturality : σ ⋙ sigma A B = sigma (σ ⋙ A) (pre A σ ⋙ B) := by
  fapply CategoryTheory.Functor.hext
  . apply sigmaObj_naturality
  . apply sigmaMap_naturality_heq

end

namespace sigma

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₃,u₃})

@[simp] def assocFib (x : Γ) : sigmaObj B x ⥤ ∫(B) :=
  pre _ _

def assocIso {x y : Γ} (f : x ⟶ y) :
    assocFib B x ≅ sigmaMap B f ⋙ assocFib B y :=
  preNatIso B (ιNatIso A f)

@[simp] theorem assocIso_id {x} :
    assocIso B (𝟙 x) = eqToIso (by simp [sigmaMap_id, Functor.id_comp]) := by
  simp [assocIso, preNatIso_congr B (ιNatIso_id A x), preNatIso_eqToIso]

theorem assocIso_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) : assocIso B (f ≫ g) =
    assocIso B f ≪≫ Functor.isoWhiskerLeft (sigmaMap B f) (assocIso B g)
    ≪≫ eqToIso (by simp [sigmaMap_comp, Functor.assoc]) := by
  simp only [assocFib, sigmaMap, assocIso, preNatIso_congr B (ιNatIso_comp A f g), Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, eqToIso.hom, pre_comp, preNatIso_comp, preNatIso_eqToIso,
    isoWhiskerLeft_eqToIso, eqToIso_trans, Functor.isoWhiskerLeft_trans, Iso.trans_assoc]
  rfl

def assocHom {x y : Γ} (f : x ⟶ y) :
    assocFib B x ⟶ sigmaMap B f ⋙ assocFib B y :=
  (assocIso B f).hom

@[simp] theorem assocHom_id {x : Γ} :
    assocHom B (𝟙 x) = eqToHom (by simp [sigmaMap_id, Functor.id_comp]) := by
  simp [assocHom, assocIso_id]

theorem assocHom_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    assocHom B (f ≫ g) = assocHom B f ≫ Functor.whiskerLeft (sigmaMap B f) (assocHom B g) ≫
      eqToHom (by simp [sigmaMap_comp, Functor.assoc]) := by
  simp [assocHom, assocIso_comp]

-- deprecated in favor of `assoc`
def assoc' : ∫(sigma A B) ⥤ ∫(B) :=
  functorFrom (assocFib B) (assocHom B) (by simp) (by simp [assocHom_comp])

-- lemma assoc_pre {Δ : Type u₄} [Groupoid.{v₄} Δ] (σ : Δ ⥤ Γ) :
--     assoc (pre A σ ⋙ B) ⋙ pre B (pre A σ) =
--     (map (eqToHom (sigma_naturality ..).symm) ⋙ pre (sigma A B) σ) ⋙ assoc B := by
--   dsimp [assoc]
--   rw [functorFrom_comp]
--   sorry

section

variable {B}

@[simp]
def assocFibObj (x : ∫ B) : sigmaObj B x.base.base :=
  objMk x.base.fiber x.fiber

@[simp] theorem assocFibObj_base (x : ∫ B) : (assocFibObj x).base = x.base.fiber :=
  rfl

theorem assocFibMapAux {x y : ∫ B} (f : x ⟶ y) :
    ((ι A y.base.base ⋙ B).map (Hom.fiber (Hom.base f))).obj
    (fiber ((sigmaMap B (Hom.base (Hom.base f))).obj (assocFibObj x))) =
    (B.map (Hom.base f)).obj x.fiber := by
  simp only [assocFibObj, objMk_base, ← Functor.comp_obj, Functor.comp_map,
    sigmaMap_obj_fiber, objMk_fiber]
  simp only [Functor.comp_obj, ← Grpd.comp_eq_comp, ← Functor.map_comp]
  congr 2
  apply Hom.ext <;> simp

def assocFibMap {x y : ∫ B} (f : x ⟶ y) :
    (sigmaMap B (Hom.base (Hom.base f))).obj (assocFibObj x) ⟶ assocFibObj y :=
  homMk f.base.fiber (eqToHom (assocFibMapAux ..) ≫ f.fiber)

@[simp↓] theorem assocFibMap_base {x y : ∫ B} (f : x ⟶ y) :
    (assocFibMap f).base = f.base.fiber :=
  rfl

@[simp↓] theorem assocFibMap_fiber {x y : ∫ B} (f : x ⟶ y) :
    (assocFibMap f).fiber = eqToHom (assocFibMapAux ..) ≫ f.fiber := by
  rfl

lemma assocFibMap_id (x : ∫ B) : assocFibMap (𝟙 x) = eqToHom (by simp) := by
  apply Hom.ext <;> simp [sigmaObj]

lemma assocFibMap_comp {x y z : ∫ B} (f : x ⟶ y) (g : y ⟶ z) :
    assocFibMap (f ≫ g) = eqToHom (by simp) ≫
    (sigmaMap B (Hom.base (Hom.base g))).map (assocFibMap f) ≫ assocFibMap g := by
  fapply Hom.ext
  · simp only [sigmaObj, Grpd.coe_of, comp_base, assocFibObj, sigmaMap_obj_base, objMk_base,
    ↓assocFibMap_base, Functor.Groupoidal.comp_fiber, assocFibMap, Functor.comp_obj,
    Functor.comp_map, sigmaMap_obj_fiber, objMk_fiber, base_eqToHom, sigmaMap_map_base, homMk_base]
  · simp only [assocFibObj, objMk_base, Functor.comp_obj, comp_base, sigmaMap, ↓assocFibMap_base,
      Functor.comp_map, objMk_fiber, ↓assocFibMap_fiber, Functor.Groupoidal.comp_fiber,
      eqToHom_trans_assoc, assocFibMap, ← heq_eq_eq, heq_eqToHom_comp_iff, eqToHom_comp_heq_iff]
    rw [Functor.Groupoidal.comp_fiber]
    simp only [objMk_base, Functor.comp_obj, comp_base, Functor.comp_map, objMk_fiber,
      heq_eqToHom_comp_iff]
    rw! [fiber_eqToHom, eqToHom_map]
    simp only [heq_eqToHom_comp_iff]
    rw [Functor.Groupoidal.comp_fiber]
    simp only [objMk_base, Functor.comp_obj, comp_base, homMk_base, Functor.comp_map, objMk_fiber,
      pre_map_fiber, map_map_fiber, Functor.whiskerRight_app, Grpd.comp_eq_comp, homMk_fiber,
      Functor.map_comp, eqToHom_map, eqToHom_trans_assoc, Category.assoc, heq_eqToHom_comp_iff]
    have : Hom.base g = (ιNatTrans (Hom.base (Hom.base g))).app y.base.fiber ≫
        (ι A z.base.base).map (Hom.fiber (Hom.base g)) := by
      fapply Hom.ext
      · simp
      · simp
    conv => left; rw! (castMode := .all) [this]
    simp only [Functor.comp_obj, Grpd.map_comp_map, Category.assoc, eqRec_heq_iff_heq,
      eqToHom_comp_heq_iff, heq_eq_eq]
    congr 1
    simp [← heq_eq_eq]
    rfl

lemma assocFib_comp_forget (c : Γ) : assocFib B c ⋙ forget ⋙
    forget = ι (sigma A B) c ⋙ forget := by
  dsimp [assocFib]
  rw [ι_comp_forget, ← Functor.assoc, pre_comp_forget, Functor.assoc, ι_comp_forget]
  aesop_cat

lemma assocFibObj_assocFib_obj (c : Γ) (x : sigmaObj B c) :
    assocFibObj ((assocFib B c).obj x) ≍ x := by
  simp only [assocFib, assocFibObj, pre_obj_fiber, heq_eq_eq]
  apply Functor.Groupoidal.ext
  · simp
  · rw! (castMode := .all) [pre_obj_base]
    simp

lemma assocFibMap_assocFib_map (c : Γ) {x y : sigmaObj B c} (f : x ⟶ y) :
    assocFibMap ((assocFib B c).map f) ≍ f := by
  dsimp [assocFib, assocFibMap]
  rw! (castMode := .all) [pre_obj_base]
  rw! (castMode := .all) [pre_obj_base]
  rw! (castMode := .all) [pre_map_base]
  apply Hom.hext' <;> simp

lemma assocFib_forget_comp_forget_obj (x : ∫ B) :
    (assocFib B ((forget ⋙ forget).obj x)).obj
    (assocFibObj x) = x := by
  dsimp [assocFib, assocFibObj]
  fapply Functor.Groupoidal.ext
  · fapply Functor.Groupoidal.ext
    · simp
    · rw! (castMode := .all) [pre_obj_base]
      simp
  · simp

lemma assocHom_app_comp_pre_map_assocFibMap {x y : ∫ B} (f : x ⟶ y) :
    (assocHom B (Hom.base (Hom.base f))).app (assocFibObj x) ≫
      (pre B (ι A y.base.base)).map (assocFibMap f) ≍ f := by
  dsimp [assocFibObj, assocHom, assocFibMap, assocIso]
  fapply Hom.hext' rfl
  · simp only [heq_eq_eq]
    exact assocFib_forget_comp_forget_obj x
  · simp only [heq_eq_eq]
    exact assocFib_forget_comp_forget_obj y
  · fapply Hom.hext' rfl
    · conv => right; rw [← assocFib_forget_comp_forget_obj x]
      simp
    · conv => right; rw [← assocFib_forget_comp_forget_obj y]
      simp
    · simp [ιNatIso_hom]
      apply Category.comp_id -- FIXME
    · simp only [Functor.Groupoidal.comp_base, Functor.Groupoidal.comp_fiber, eqToHom_comp_heq_iff]
      rw [preNatIso_hom_app_base, ιNatIso_hom]
      rw! (transparency := .default) (castMode := .all) [CategoryTheory.Functor.map_id]
      erw [Category.id_comp]
      rw! (castMode := .all) [pre_map_base]
      simp [- heq_eq_eq]
      rfl
  · simp

lemma assocFib_comp_forget_comp_forget_obj (c : Γ) (x : sigmaObj B c) :
    (assocFib B c ⋙ forget ⋙ forget).obj x = c := by
  rfl

lemma forget_comp_forget_map_assocHom_app {c c' : Γ} (f : c ⟶ c') (x : sigmaObj B c) :
    (Functor.Groupoidal.forget ⋙ Functor.Groupoidal.forget).map ((assocHom B f).app x) ≍ f := by
  rfl

lemma assocFibMap_assocHom_app {c c' : Γ} (f : c ⟶ c') (x : sigmaObj B c) :
    assocFibMap ((assocHom B f).app x) ≍ 𝟙 ((sigmaMap B f).obj x) := by
  dsimp [assocFibMap, assocHom, assocIso]
  fapply Hom.hext' rfl HEq.rfl HEq.rfl
  · rfl
  · simp only [objMk_base, Functor.comp_obj, sigmaMap_obj_base, homMk_base, Functor.comp_map,
    sigmaMap_obj_fiber, objMk_fiber, homMk_fiber, preNatIso_hom_app_fiber, pre_comp,
    Category.comp_id, heq_eq_eq]
    symm
    apply Functor.Groupoidal.id_fiber

end

@[simps!]
def assoc : ∫ B ≅≅ ∫ sigma A B := .symm <| functorIsoFrom
  (assocFib B) (assocHom B) (by simp) (by simp [assocHom_comp])
  (forget ⋙ forget) assocFibObj assocFibMap assocFibMap_id assocFibMap_comp
  assocFib_comp_forget assocFibObj_assocFib_obj assocFibMap_assocFib_map
  assocFib_forget_comp_forget_obj assocHom_app_comp_pre_map_assocFibMap
  assocFib_comp_forget_comp_forget_obj forget_comp_forget_map_assocHom_app
  assocFibMap_assocHom_app

lemma assoc_hom : (assoc B).hom = Functor.Groupoidal.functorTo (forget ⋙ forget) assocFibObj
    assocFibMap assocFibMap_id assocFibMap_comp :=
  rfl

lemma assoc_hom_comp_forget : (assoc B).hom ⋙ forget = forget ⋙ forget := by
  simp [assoc_hom]
  erw [Functor.Groupoidal.functorTo_forget]

lemma assoc_inv_comp_forget_comp_forget : (assoc B).inv ⋙ forget ⋙ forget
    = Functor.Groupoidal.forget :=
  calc _
  _ = (assoc B).inv ⋙ (assoc B).hom ⋙ Functor.Groupoidal.forget := by
    rw [assoc_hom_comp_forget]
  _ = _ := by simp

lemma assocFibMap_pre_pre_map {Δ : Type u₄} [Groupoid.{v₄} Δ] {σ : Δ ⥤ Γ} {x y} (f : x ⟶ y) :
    assocFibMap ((pre B (pre A σ)).map f) ≍ assocFibMap f := by
  have pre_pre_obj_base_base (x) : ((pre B (pre A σ)).obj x).base.base = σ.obj x.base.base := by
    rw [pre_obj_base, pre_obj_base]
  have pre_pre_obj_base_fiber (x) : ((pre B (pre A σ)).obj x).base.fiber = x.base.fiber := by
    rw! (castMode := .all) [pre_obj_base, pre_obj_fiber]
  simp [assocFibMap]
  apply Hom.hext'
  · rw [sigma_naturality_aux]
    rfl
  · simp only [pre_map_base, pre_obj_fiber]
    rw! [sigmaMap_naturality]
    simp only [Functor.comp_obj, ← eqToHom_eq_homOf_map, Grpd.comp_eq_comp, Grpd.coe_of,
      Grpd.eqToHom_obj, cast_heq_iff_heq, heq_eq_eq]
    rw! (castMode := .all) [pre_pre_obj_base_fiber]
    congr 1
    simp only [← heq_eq_eq, cast_heq_iff_heq]
    apply Functor.Groupoidal.hext'
    · rw! (castMode := .all) [sigma_naturality_aux, pre_pre_obj_base_base]
    · simp
    · simp
  · apply Functor.Groupoidal.hext'
    · rw! (castMode := .all) [sigma_naturality_aux, pre_pre_obj_base_base]
    · simp [pre_pre_obj_base_fiber]
    · simp
  · simp only [sigmaMap_obj_base, objMk_base, homMk_base, Functor.comp_obj, Functor.comp_map]
    rfl
  · simp

lemma assoc_comp_fiber {Δ : Type u₄} [Groupoid.{v₄} Δ] {σ : Δ ⥤ Γ} {x y} (f : x ⟶ y) :
    Hom.fiber (((assoc (pre A σ ⋙ B)).hom ⋙ map (eqToHom (sigma_naturality ..).symm) ⋙
    pre (sigma A B) σ).map f) ≍ Hom.fiber ((pre B (pre A σ) ⋙ (assoc B).hom).map f) := by
  simp only [assoc_hom, Functor.comp_obj, sigma_obj, Functor.comp_map, sigma_map, pre_map_fiber,
    map_map_fiber, Functor.Groupoidal.functorTo_obj_base, Functor.Groupoidal.forget_obj,
    Functor.Groupoidal.functorTo_map_base, forget_map, Grpd.comp_eq_comp,
    Functor.Groupoidal.functorTo_obj_fiber, assocFibObj, Functor.Groupoidal.functorTo_map_fiber,
    eqToHom_comp_heq_iff]
  rw [Grpd.eqToHom_app, Grpd.eqToHom_hom]
  rw! [assocFibMap_pre_pre_map]
  simp

lemma assoc_comp {Δ : Type u₄} [Groupoid.{v₄} Δ] (σ : Δ ⥤ Γ) :
    (sigma.assoc ((pre A σ) ⋙ B)).hom ⋙
    map (eqToHom (by simp [sigma_naturality])) ⋙ pre (sigma A B) σ =
    pre B (pre A σ) ⋙ (sigma.assoc B).hom := by
  simp only [assoc_hom]
  apply FunctorTo.hext
  · simp only [Functor.assoc, pre_comp_forget]
    conv => left; right; rw [← Functor.assoc, map_forget]
    rw [← Functor.assoc _ forget σ]
    conv => left; left; apply Functor.Groupoidal.functorTo_forget
    conv => right; right; apply Functor.Groupoidal.functorTo_forget
    conv => right; rw [← Functor.assoc, pre_comp_forget]
    simp only [Functor.assoc, pre_comp_forget]
  · intro x
    simp only [Functor.comp_obj, sigma_obj, pre_obj_fiber, map_obj_fiber,
      Functor.Groupoidal.functorTo_obj_base, Functor.Groupoidal.forget_obj, eqToHom_app,
      Functor.Groupoidal.functorTo_obj_fiber, assocFibObj, heq_eq_eq]
    rw! (castMode := .all) [pre_obj_base B]
    simp only [Grpd.eqToHom_obj, ← heq_eq_eq, cast_heq_iff_heq]
    congr 1
    rw! (castMode := .all) [pre_obj_base A]
    rw [← Functor.assoc, ι_comp_pre]
  · intro x y f
    apply assoc_comp_fiber

lemma assoc_comp' {Δ : Type u₄} [Groupoid.{v₄} Δ] {σ : Δ ⥤ Γ} (Aσ) (eq : Aσ = σ ⋙ A) :
    (sigma.assoc ((map (eqToHom eq) ⋙ pre A σ) ⋙ B)).hom ⋙
    map (eqToHom (by subst eq; simp [sigma_naturality, map_id_eq])) ⋙ pre (sigma A B) σ =
    (pre (pre A σ ⋙ B) (map (eqToHom eq)) ⋙ pre B (pre A σ)) ⋙ (sigma.assoc B).hom := by
  subst eq
  rw! [eqToHom_refl, map_id_eq]
  simp [assoc_comp]

section

def fstAux' : ∫(sigma A B) ⥤ ∫(A) :=
  (assoc B).inv ⋙ forget

/-- `fst` projects out the pointed groupoid `(A,a)` appearing in `(A,B,a : A,b : B a)` -/
def fst : ∫(sigma A B) ⥤ PGrpd :=
  fstAux' B ⋙ toPGrpd A

theorem fst_forgetToGrpd : fst B ⋙ PGrpd.forgetToGrpd = forget ⋙ A := by
  dsimp only [fst, fstAux']
  rw [Functor.assoc, (Functor.Groupoidal.isPullback A).comm_sq,
    ← Functor.assoc]
  conv => left; left; rw [Functor.assoc, assoc_inv_comp_forget_comp_forget]

end
end

end sigma

end FunctorOperation

open FunctorOperation

section

namespace USig

/-! We now define Sigma on small types.

Type `A` is `v₁`-sized. Type `B` depending on `A` is `v₂`-sized.
The context category has to fit `ΣA. B` which is `max v₁ v₂`-sized,
but it can also be larger.
Thus the context category is `max u (max v₁ v₂ + 1)`-sized. -/

variable {X : Type (v₂ + 1)} [LargeCategory.{v₂} X]
  {Y : Type (max v₁ v₂ + 1)} [LargeCategory.{max v₁ v₂} Y]

variable
  (S : ∀ {Γ : Ctx.{max u (max v₁ v₂ + 1)}} (A : Γ ⥤ Grpd.{v₁,v₁}), (∫(A) ⥤ X) → (Γ ⥤ Y))
  {Γ Δ : Ctx.{max u (max v₁ v₂ + 1)}}
  (σ : Δ ⟶ Γ)
  {A : Γ ⟶ U.{v₁, max u (max v₁ v₂ + 1)}.Ty}
  {σA : Δ ⟶ U.{v₁, max u (max v₁ v₂ + 1)}.Ty}
  (eq : σ ≫ A = σA)
  (B : U.ext A ⟶ U.{v₂, max u (max v₁ v₂ + 1)}.Ty)

-- TODO: make `u` the last univ param to match other Ctx-based defs.
@[simp]
abbrev SigAux
    (B : U.ext A ⟶ Ctx.coreAsSmall.{v₂, max u (max v₁ v₂ + 1)} X) :
    Γ ⟶ Ctx.coreAsSmall.{max v₁ v₂, max u (max v₁ v₂ + 1)} Y :=
  toCoreAsSmallEquiv.symm (S (toCoreAsSmallEquiv A) (toCoreAsSmallEquiv B))

theorem SigAux_comp
    (S_naturality : ∀ {Γ Δ : Ctx.{max u (max v₁ v₂ + 1)}} (σ : Δ ⟶ Γ) {A : Γ ⥤ Grpd.{v₁,v₁}}
      {B : ∫(A) ⥤ X}, σ ⋙ S A B = S (σ ⋙ A) (pre A σ ⋙ B))
    (B : U.ext A ⟶ Ctx.coreAsSmall.{v₂, max u (max v₁ v₂ + 1)} X) :
    SigAux.{u,v₁,v₂} S (U.substWk σ A σA eq ≫ B) = σ ≫ SigAux.{u,v₁,v₂} S B := by
  simp only [SigAux, Grpd.comp_eq_comp]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left]
  congr 1
  rw [S_naturality]
  subst eq
  simp only [Grpd.comp_eq_comp]
  conv => left; right; rw! [toCoreAsSmallEquiv_apply_comp_left]
  rw! (castMode := .all) [toCoreAsSmallEquiv_apply_comp_left]
  simp [U.substWk_eq, map_id_eq]
  rfl

def Sig : Γ ⟶ U.{max v₁ v₂, max u (max v₁ v₂ + 1)}.Ty :=
  SigAux.{u,v₁,v₂} sigma B

/--
Naturality for the formation rule for Σ-types.
Also known as Beck-Chevalley.
-/
theorem Sig_comp : Sig.{u,v₁,v₂} (U.substWk σ A σA eq ≫ B) = σ ≫ Sig.{u,v₁,v₂} B :=
  SigAux_comp.{u,v₁,v₂} sigma σ eq (by intros; rw [sigma_naturality]) B

def assoc : U.ext B ≅ U.ext (Sig.{u,v₁,v₂} B) :=
  Grpd.mkIso' (sigma.assoc (toCoreAsSmallEquiv B)) ≪≫
    eqToIso (by dsimp [U.ext, Sig]; rw [toCoreAsSmallEquiv.apply_symm_apply])

set_option maxHeartbeats 400000 in
lemma assoc_comp : (assoc (U.substWk σ A σA eq ≫ B)).hom ≫ U.substWk σ (Sig.{u,v₁,v₂} B)
    (Sig.{u,v₁,v₂} (U.substWk σ A σA eq ≫ B)) (Sig_comp.{u,v₁,v₂} ..).symm =
    U.substWk (U.substWk σ A σA eq) B (U.substWk σ A σA eq ≫ B) rfl ≫ (assoc B).hom := by
  dsimp [assoc]
  simp only [Sig, SigAux, U.substWk_eq, eqToHom_refl, map_id_eq, Cat.of_α]
  rw! (castMode := .all) [toCoreAsSmallEquiv_apply_comp_left]
  rw! (castMode := .all) [toCoreAsSmallEquiv.apply_symm_apply]
  rw! (castMode := .all) [toCoreAsSmallEquiv.apply_symm_apply]
  rw! [U.substWk_eq]
  simp only [pre_comp, Functor.id_comp]
  apply sigma.assoc_comp' (toCoreAsSmallEquiv B) (σ := σ) (toCoreAsSmallEquiv σA)

lemma assoc_disp : (assoc B).hom ≫ U.disp (Sig.{u,v₁,v₂} B) = U.disp B ≫ U.disp A := by
  simpa [assoc] using sigma.assoc_hom_comp_forget _

end USig

open USig in
def USig : PolymorphicSigma
    U.{v₁, max u (max v₁ v₂ + 1)}
    U.{v₂, max u (max v₁ v₂ + 1)}
    U.{max v₁ v₂, max u (max v₁ v₂ + 1)} :=
  .mk' Sig.{u,v₁,v₂} Sig_comp assoc assoc_comp assoc_disp

end

end GroupoidModel
end
