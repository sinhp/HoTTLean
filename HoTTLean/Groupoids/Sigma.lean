import HoTTLean.Groupoids.UnstructuredModel
import HoTTLean.ForMathlib.CategoryTheory.RepPullbackCone

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

namespace GroupoidModel

open CategoryTheory UnstructuredModel Universe Opposite Functor.Groupoidal PGrpd

attribute [local simp] eqToHom_map Grpd.id_eq_id Grpd.comp_eq_comp Functor.id_comp

namespace FunctorOperation

section
variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
    (B : ∫ A ⥤ Grpd.{v₁,u₁}) (x : Γ)
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
    {B : ∫(A) ⥤ Grpd.{v₁,u₁}} {x y z : Γ} {f : x ⟶ y} {g : y ⟶ z}
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
    (B : ∫(A) ⥤ Grpd.{v₁,u₁}) : Γ ⥤ Grpd.{v₁,u₁} where
  -- NOTE using Grpd.of here instead of earlier speeds things up
  obj x := sigmaObj B x
  map := sigmaMap B
  map_id _ := sigmaMap_id
  map_comp _ _ := sigmaMap_comp

variable (B) {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)
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

section

variable {Γ : Type u₂} [Category.{v₂} Γ] {α β : Γ ⥤ PGrpd.{v₁,u₁}}
  {B : ∫(α ⋙ forgetToGrpd) ⥤ Grpd.{v₁,u₁}}
  (h : β ⋙ forgetToGrpd = sec _ α rfl ⋙ B)

def pairObjFiber (x : Γ) : sigmaObj B x :=
  objMk (objFiber α x) (objFiber' h x)

@[simp] theorem pairObjFiber_base (x : Γ) : (pairObjFiber h x).base = objFiber α x :=
  rfl

@[simp] theorem pairObjFiber_fiber (x : Γ) :
    (pairObjFiber h x).fiber = (objFiber' h x) :=
  rfl

theorem pairSectionMap_aux_aux {x y} (f : x ⟶ y) :
    (ιNatTrans f).app (pairObjFiber h x).base
    ≫ (ι _ y).map (mapFiber α f)
    = (sec _ α rfl).map f := by
  apply Hom.ext
  · simp only [Functor.Groupoidal.comp_fiber, ιNatTrans_app_fiber, ι_obj_fiber, ι_map_fiber,
      sec_map_fiber, mapFiber', mapFiber]
    rw! (transparency := .default) [CategoryTheory.Functor.map_id, Category.id_comp]
    simp [mapFiber'EqToHom]
  · simp

/--
  The left hand side
  `mapPairSectionObjFiber h f` is an object in the fiber `sigma A B y` over `y`
  The fiber itself consists of bundles, so `(mapPairSectionObjFiber h f).fiber`
  is an object in the fiber `B a` for an `a` in the fiber `A y`.
  But this `a` is isomorphic to `(pairSectionObjFiber y).base`
  and the functor `(ι _ y ⋙ B).map (mapPoint α f)`
  converts the data along this isomorphism.

  The right hand side is `(*)` in the diagram.
     sec α             B
  Γ -------> ∫(A) ------------> Grpd

  x                              (B ⋙ sec α).obj x     objPt' h x
  | f                     (B ⋙ sec α).map f  |              -
  V                                          V              |
  y                              (B ⋙ sec α).obj y          V
                                                           (*)
-/
theorem pairMapFiber_aux {x y} (f : x ⟶ y) :
    ((ι _ y ⋙ B).map (mapFiber α f)).obj ((sigmaMap B f).obj (pairObjFiber h x)).fiber =
    ((sec _ α rfl ⋙ B).map f).obj (objFiber' h x) := by
  simp only [Grpd.forgetToCat.eq_1, Functor.comp_obj, Functor.comp_map,
    sigmaObj, sigmaMap, pre_obj_fiber, map_obj_fiber, Functor.whiskerRight_app]
  rw [← Grpd.map_comp_obj, pairSectionMap_aux_aux]
  rfl

/--
This can be thought of as the action of parallel transport on f
or perhaps the path over f, but defined within the fiber over y

  sigma A B x     ∋ pairObjFiber h x
  |                        -
  |                        |
  |  sigma A B f           |
  |                        |
  V                        V
  sigma A B y     ∋         PairMapFiber
                           _ ⟶ pairObjFiber h y
-/
def pairMapFiber {x y : Γ} (f : x ⟶ y) : (sigmaMap B f).obj (pairObjFiber h x)
    ⟶ (pairObjFiber h y : ∫(ι _ y ⋙ B)) :=
  homMk (mapFiber α f) (eqToHom (pairMapFiber_aux h f) ≫ mapFiber' h f)

@[simp↓] theorem pairMapFiber_base {x y} (f : x ⟶ y) :
    (pairMapFiber h f).base = mapFiber α f :=
  rfl

/-
1. The first implicit argument to `Groupoidal.Hom.fiber` is `(α ⋙ forgetToGrpd).obj y`.
   The global `simp` rule `Functor.comp_obj` (which normally fires before this)
   rewrites that to `forgetToGrpd.obj (α.obj x)`,
   and then this lemma no longer applies.
   As a workaround, we instruct `simp` to apply this before visiting subterms.

2. `@[simps! fiber]` on `pairMapFiber` generates a lemma
  that refers to `Grothendieck.Hom.fiber` rather than `Groupoidal.Hom.fiber`,
  so we write this by hand. -/
@[simp↓] theorem pairMapFiber_fiber {x y} (f : x ⟶ y) :
    (pairMapFiber h f).fiber = eqToHom (pairMapFiber_aux h f) ≫ mapFiber' h f :=
  rfl

theorem pairMapFiber_id (x : Γ) : pairMapFiber h (𝟙 x) = eqToHom (by simp) := by
  apply Hom.ext <;> simp [sigmaObj]

theorem pairMapFiber_comp_aux_aux {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    ((ι _ z ⋙ B).map (mapFiber α g)).obj
    (((ι _ z ⋙ B ⋙ Grpd.forgetToCat).map
    (((sigmaMap B g).map (pairMapFiber h f))).base).obj
    ((sigmaMap B g).obj (((sigmaMap B f).obj (pairObjFiber h x)))).fiber)
    = ((sec _ α rfl ⋙ B).map f ≫ (sec _ α rfl ⋙ B).map g).obj (objFiber' h x) := by
  have h1 : (sec _ α rfl ⋙ B).map f ≫ (sec _ α rfl ⋙ B).map g = (sec _ α rfl ⋙ B).map (f ≫ g) := by
    rw [← Functor.map_comp]
  rw [Functor.congr_obj h1, ← pairMapFiber_aux,mapFiber_comp,
    Functor.map_comp, eqToHom_map, Grpd.comp_eq_comp]
  simp only [Functor.comp_obj, Functor.map_comp, Grpd.eqToHom_obj]
  congr 2
  have : (sigmaMap B g).obj ((sigmaMap B f).obj (pairObjFiber h x))
    = (sigmaMap B (f ≫ g)).obj (pairObjFiber h x) := by
    rw [sigmaMap_comp]
    rfl
  rw [eq_cast_iff_heq]
  congr

theorem pairMapFiber_comp_aux {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    ((ι _ z ⋙ B).map (mapFiber α g)).map ((sigmaMap B g).map (pairMapFiber h f)).fiber
    = eqToHom (pairMapFiber_comp_aux_aux h f g)
    ≫ ((sec _ α rfl ⋙ B).map g).map (mapFiber' h f)
    ≫ eqToHom (by rw [← pairMapFiber_aux]) := by
  simp only [Functor.comp_map, sigmaObj, sigmaMap_map_fiber,
    Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    Grpd.map_comp_map', eqToHom_trans_assoc, eqToHom_comp_iff, comp_eqToHom_iff,
    eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
  rw! [pairSectionMap_aux_aux]
  simp only [pairMapFiber_fiber, Functor.map_comp, eqToHom_refl, Category.comp_id, eqToHom_map]

-- TODO remove bleedings of `Grothendieck`, e.g. `Grothendieck.forget_obj`
theorem pairMapFiber_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    (pairMapFiber h (f ≫ g)) = eqToHom (by simp)
    ≫ (((sigma (α ⋙ forgetToGrpd) B).map g).map (pairMapFiber h f) ≫ pairMapFiber h g) := by
  fapply Hom.ext
  · simp [sigmaObj, - Functor.comp_obj, mapFiber] -- FIXME
  · rw! (transparency := .default) [pairMapFiber_fiber, Functor.Groupoidal.comp_fiber, Functor.Groupoidal.comp_fiber,
      fiber_eqToHom, eqToHom_map, pairMapFiber_comp_aux,
      Functor.congr_hom (Functor.congr_hom h.symm g) (mapFiber' h f), mapFiber'_comp]
    simp only [sigmaObj, pairMapFiber_fiber, mapFiber', eqToHom_trans_assoc, Category.assoc,
      eqToHom_comp_iff, mapFiber'EqToHom]
    simp only [← Category.assoc]
    congr 1
    simp only [Grpd.coe_of, Grpd.eqToHom_hom, pairObjFiber_base,
      Functor.comp_map, Grpd.comp_eq_comp, Category.assoc]
    conv => right; right; simp only [← congrArg_cast_hom_left, cast_cast]
    rw [conj_eqToHom_iff_heq]
    · simp only [heq_cast_iff_heq, cast_heq_iff_heq]
      congr 1
      · erw [Functor.congr_obj (Functor.congr_hom h.symm f) (objFiber' h x)]
        simp [Grpd.forgetToCat, id_eq, Functor.comp_obj, Functor.comp_map,
          Grpd.comp_eq_comp, objFiber', objFiber,
          Grpd.eqToHom_obj, cast_cast, cast_eq]
      · simp only [objFiber', Functor.comp_obj, objFiber,
          Grpd.eqToHom_obj, cast_cast, cast_eq]
      · simp only [heq_cast_iff_heq, heq_eq_eq]
    · simp [Grpd.eqToHom_obj, Grpd.coe_of, objFiber', Functor.comp_obj,
      objFiber, cast_cast, cast_eq]

variable (α) (β) (B) in
def pair : Γ ⥤ PGrpd.{v₁,u₁} :=
  PGrpd.functorTo (sigma _ B) (pairObjFiber h) (pairMapFiber h)
  (pairMapFiber_id h) (pairMapFiber_comp h)

@[simp] theorem pair_obj_base (x : Γ) :
    ((pair α β B h).obj x).base = ∫(ι (α ⋙ forgetToGrpd) x ⋙ B) :=
  rfl

@[simp] theorem pair_obj_fiber (x : Γ) :
    ((pair α β B h).obj x).fiber = pairObjFiber h x :=
  rfl

@[simp] theorem pair_map_base {x y : Γ} (f : x ⟶ y) :
    ((pair α β B h).map f).base = sigmaMap B f :=
  rfl

@[simp] theorem pair_map_fiber {x y : Γ} (f : x ⟶ y) :
    ((pair α β B h).map f).fiber = pairMapFiber h f :=
  rfl

@[simp] theorem pair_comp_forgetToGrpd :
    pair α β B h ⋙ forgetToGrpd = sigma (α ⋙ forgetToGrpd) B := rfl

section

variable {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ)

include h in
theorem pair_naturality_aux : (σ ⋙ β) ⋙ forgetToGrpd =
  sec ((σ ⋙ α) ⋙ forgetToGrpd) (σ ⋙ α) rfl ⋙ pre (α ⋙ forgetToGrpd) σ ⋙ B := by
  rw [Functor.assoc, h, ← Functor.assoc, sec_naturality]
  rfl

theorem pair_naturality_ι_pre (x) :
    (ι ((σ ⋙ α) ⋙ forgetToGrpd) x ⋙ pre (α ⋙ forgetToGrpd) σ)
    = ι (α ⋙ forgetToGrpd) (σ.obj x) := by
  apply ι_comp_pre (α ⋙ forgetToGrpd) σ x

theorem pair_naturality_obj (x : Δ) : HEq (pairObjFiber h (σ.obj x))
    (pairObjFiber (pair_naturality_aux h σ) x) := by
  apply hext'
  · rw [← Functor.assoc, pair_naturality_ι_pre]
  · simp only [heq_eq_eq]
    erw [pairObjFiber_base]
  · simp only [heq_eq_eq]
    erw [pairObjFiber_fiber]

theorem pair_naturality_aux_1 {x y} (f : x ⟶ y) :
    HEq ((sigmaMap B (σ.map f)).obj (pairObjFiber h (σ.obj x)))
    ((sigmaMap (pre (α ⋙ forgetToGrpd) σ ⋙ B) f).obj (pairObjFiber (pair_naturality_aux h σ) x)) := by
  apply hext'
  . apply Eq.symm
    calc ι (σ ⋙ α ⋙ forgetToGrpd) y ⋙ pre (α ⋙ forgetToGrpd) σ ⋙ B =
        (ι ((σ ⋙ α) ⋙ forgetToGrpd) y ⋙ pre (α ⋙ forgetToGrpd) σ) ⋙ B := by exact
          rfl
        _ = ι (α ⋙ forgetToGrpd) (σ.obj y) ⋙ B := by rw! [pair_naturality_ι_pre]
  . simp only [heq_eq_eq]
    erw [sigmaMap_obj_base]
  . simp only [heq_eq_eq]
    erw [sigmaMap_obj_fiber]

theorem pair_naturality : σ ⋙ pair α β B h = pair (σ ⋙ α) (σ ⋙ β) (pre (α ⋙ forgetToGrpd) σ ⋙ B)
    (by erw [Functor.assoc, h, ← Functor.assoc, sec_naturality, Functor.assoc]) := by
  apply PGrpd.Functor.hext
  · apply sigma_naturality
  · intro x
    apply pair_naturality_obj
  · intro x y f
    apply Hom.hext'
    · rw [← Functor.assoc, pair_naturality_ι_pre]
    · apply pair_naturality_aux_1
    · apply pair_naturality_obj
    · simp [- Functor.comp_obj, - Functor.comp_map, Functor.comp_map, mapFiber_naturality]
    · simp [- Functor.comp_obj, - Functor.comp_map, Functor.comp_map, ← mapFiber'_naturality]

end

end

namespace sigma
section
variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}} (B : ∫(A) ⥤ Grpd.{v₁,u₁})

@[simps] def fstAux : sigma A B ⟶ A where
  app x := Grpd.homOf forget

lemma fstAux_comp {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ) : fstAux (pre A σ ⋙ B) =
    eqToHom (sigma_naturality ..).symm ≫ Functor.whiskerLeft σ (fstAux B) := by
  ext
  simp only [sigma_obj, Functor.comp_obj, fstAux_app, NatTrans.comp_app, eqToHom_app,
    Functor.whiskerLeft_app, ← heq_eq_eq, heq_eqToHom_comp_iff]
  congr
  all_goals rw [← Functor.assoc, ι_comp_pre]

def fstAux' : ∫(sigma A B) ⥤ ∫(A) :=
  map (fstAux B)

/-- `fst` projects out the pointed groupoid `(A,a)` appearing in `(A,B,a : A,b : B a)` -/
def fst : ∫(sigma A B) ⥤ PGrpd :=
  fstAux' B ⋙ toPGrpd A

theorem fst_forgetToGrpd : fst B ⋙ forgetToGrpd = forget ⋙ A := by
  dsimp only [fst, fstAux']
  rw [Functor.assoc, (Functor.Groupoidal.isPullback A).comm_sq,
    ← Functor.assoc, map_forget]

lemma fst_comp {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ) :
    fst (pre A σ ⋙ B) = map (eqToHom (sigma_naturality B σ).symm) ⋙ pre (sigma A B) σ ⋙ fst B := by
  simp [fst, fstAux']
  rw [fstAux_comp, map_comp_eq, ← pre_toPGrpd]
  rfl -- FIXME: heavy rfl

end

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
    (B : ∫(A) ⥤ Grpd.{v₁,u₁})

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

def assoc : ∫(sigma A B) ⥤ ∫(B) :=
  functorFrom (assocFib B) (assocHom B) (by simp) (by simp [assocHom_comp])

lemma assoc_pre {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ) :
    assoc (pre A σ ⋙ B) ⋙ pre B (pre A σ) =
    (map (eqToHom (sigma_naturality ..).symm) ⋙ pre (sigma A B) σ) ⋙ assoc B := by
  dsimp [assoc]
  rw [functorFrom_comp]
  sorry

def snd : ∫(sigma A B) ⥤ PGrpd :=
  assoc B ⋙ toPGrpd B

lemma snd_comp {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ) : snd (A := σ ⋙ A) (pre A σ ⋙ B) =
    map (eqToHom (sigma_naturality ..).symm) ⋙ pre (sigma A B) σ ⋙ snd B := by
  dsimp [snd]
  have : toPGrpd (pre A σ ⋙ B) = pre B (pre A σ) ⋙ toPGrpd B := rfl
  simp only [this, ← Functor.assoc, assoc_pre]

theorem ι_sigma_comp_map_fstAux (x) : ι (sigma A B) x ⋙ map (fstAux B)
    = forget ⋙ ι A x := by
  apply FunctorTo.hext
  · rw [Functor.assoc, map_forget]
    rfl
  · intro x
    simp
  · intro x y f
    simp only [sigma_obj, sigmaObj, Functor.comp_obj, ι_obj_base,
      Functor.comp_map, ι_map_base, fstAux_app, ι_obj_fiber,
      Functor.Groupoidal.forget_obj, map_map_fiber, sigma_map, eqToHom_refl, ι_map_fiber,
      Functor.Groupoidal.forget_map, Category.id_comp, heq_eq_eq]
    convert comp_base (eqToHom _) f
    · rfl
    · simp

theorem functorFrom_comp_fib_assocFib_forget :
  functorFrom_comp_fib (assocFib B) forget = asFunctorFrom_fib (map (fstAux B)) := by
  ext x
  exact (ι_sigma_comp_map_fstAux B x).symm

lemma ιNatTrans_app_base_eq {c₁ c₂ : Γ} (f: c₁ ⟶ c₂) (x : ((sigma A B).obj c₁)) :
    (ιNatTrans f).app (base x) = (map (fstAux B)).map ((ιNatTrans f).app x) := by
  apply Hom.hext
  · rfl
  · simp only [map_map_fiber, eqToHom_refl, Category.id_comp]
    rfl

theorem assoc_forget : assoc B ⋙ forget = fstAux' B := by
  simp only [assoc, fstAux', functorFrom_comp]
  rw [← asFunctorFrom (map (fstAux B))]
  fapply Functor.Grothendieck.functorFrom_eq_of -- FIXME: bleeding Grothendieck
  · exact functorFrom_comp_fib_assocFib_forget B
  · intro c₁ c₂ f
    rw [comp_eqToHom_iff]
    ext x
    simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl, Category.comp_id, Category.id_comp]
    apply ιNatTrans_app_base_eq

theorem snd_forgetToGrpd : snd B ⋙ forgetToGrpd = fstAux' B ⋙ B :=
  calc
    _ = assoc B ⋙ forget ⋙ B := rfl
    _ = fstAux' B ⋙ B := by rw [← assoc_forget]; rfl

@[simp] theorem fst_obj_fiber {x} : ((fst B).obj x).fiber = x.fiber.base := rfl

@[simp] theorem fst_map_fiber {x y} (f : x ⟶ y) : ((fst B).map f).fiber = f.fiber.base := by
  simp [fst, fstAux']

@[simp] theorem snd_obj_fiber {x} : ((snd B).obj x).fiber = x.fiber.fiber := by
  simp [snd, assoc]; rfl

@[simp] theorem assoc_hom_app_fiber {x y : ∫(sigma A B)} (f : x ⟶ y) :
    (assocHom B (Hom.base f)).app x.fiber
    = homMk (homMk f.base (𝟙 _)) (𝟙 _) := by
  apply Hom.hext
  · apply Hom.hext
    · simp [sigmaObj, assocFib, Functor.comp_obj, assocHom,
        assocIso, preNatIso_hom_app_base, ιNatIso_hom]
    · rw [assocHom, assocIso, preNatIso_hom_app_base, ιNatIso_hom]
      simp
      rfl
  · simp [assocHom, assocIso]
    rfl

-- FIXME: should probably make `snd_map_base` and use that to prove the `eqToHom`
@[simp] theorem snd_map_fiber {x y} (f : x ⟶ y) : ((snd B).map f).fiber =
    eqToHom (by simp [snd, assoc]; rfl) ≫ Hom.fiber (Hom.fiber f) := by
  simp only [snd, assoc, Functor.comp_map]
  rw! [Functor.Groupoidal.functorFrom_map, assoc_hom_app_fiber]
  simp only [toPGrpd_map_fiber, Functor.Groupoidal.comp_fiber]
  rw! (transparency := .default) [CategoryTheory.Functor.map_id]
  simp

end

section

variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}} (B : ∫(A) ⥤ Grpd.{v₁,u₁})
  (αβ : Γ ⥤ PGrpd.{v₁,u₁}) (hαβ : αβ ⋙ forgetToGrpd = sigma A B)

/--  Let `Γ` be a category.
For any pair of functors `A : Γ ⥤ Grpd` and `B : ∫(A) ⥤ Grpd`,
and any "term of sigma", meaning a functor `αβ : Γ ⥤ PGrpd`
satisfying `αβ ⋙ forgetToGrpd = sigma A B : Γ ⥤ Grpd`,
there is a "term of `A`" `fst' : Γ ⥤ PGrpd` such that `fst ⋙ forgetToGrpd = A`,
thought of as `fst' : A`.
There is a "type" `dependent' : ∫(fst ⋙ forgetToGrpd) ⥤ Grpd`,
which is hequal to `B` modulo `fst ⋙ forgetToGrpd` being equal to `A`.
And there is a "term" `snd' : Γ ⥤ PGrpd` satisfying
`snd' ⋙ forgetToGrpd = sec _ fst rfl ⋙ dependent'`.
-/
def fst' : Γ ⥤ PGrpd := sec (sigma A B) αβ hαβ ⋙ fst B

@[inherit_doc fst'] theorem fst'_forgetToGrpd : fst' B αβ hαβ ⋙ forgetToGrpd = A :=
  rfl

lemma fst'_comp {Δ : Type u₃} [Category.{v₃} Δ] (σ : Δ ⥤ Γ) :
    fst' (A := σ ⋙ A) (pre A σ ⋙ B) (σ ⋙ αβ) (by simp [Functor.assoc, hαβ, sigma_naturality]) =
    σ ⋙ fst' B αβ hαβ := by
  dsimp [fst']
  conv => right; rw [← Functor.assoc, Functor.Groupoidal.sec_naturality, Functor.assoc]
  rw! [fst_comp, ← sigma_naturality]
  simp [map_id_eq]

@[inherit_doc fst'] def dependent' : ∫(fst' B αβ hαβ ⋙ forgetToGrpd) ⥤ Grpd :=
  map (eqToHom rfl) ⋙ B

end

section
variable {Γ : Type u₂} [Groupoid.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}} (B : ∫(A) ⥤ Grpd.{v₁,u₁})
  (αβ : Γ ⥤ PGrpd.{v₁,u₁}) (hαβ : αβ ⋙ forgetToGrpd = sigma A B)

@[inherit_doc fst'] def snd' : Γ ⥤ PGrpd := sec (sigma A B) αβ hαβ ⋙ snd B

lemma snd'_comp {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ) :
    snd' (A := σ ⋙ A) (pre A σ ⋙ B) (σ ⋙ αβ) (by rw [Functor.assoc, hαβ, sigma_naturality]) =
    σ ⋙ snd' B αβ hαβ := by
  dsimp [snd']
  conv => right; rw [← Functor.assoc, sec_naturality]
  rw! [snd_comp, ← sigma_naturality]
  simp [map_id_eq]
  rfl

@[simp] theorem fst'_obj_base {x} : ((fst' B αβ hαβ).obj x).base =
    A.obj x := rfl

theorem fst'_obj_fiber {x} : ((fst' B αβ hαβ).obj x).fiber = (objFiber' hαβ x).base := by
  simp [fst']

@[simp] theorem fst'_map_base {x y} (f : x ⟶ y) : ((fst' B αβ hαβ).map f).base =
    A.map f := rfl

theorem fst'_map_fiber {x y} (f : x ⟶ y) : ((fst' B αβ hαβ).map f).fiber =
    (mapFiber' hαβ f).base := by
  simp [fst']

theorem sec_fstAux' : sec (sigma A B) αβ hαβ ⋙ fstAux' B =
  sec (fst' B αβ hαβ ⋙ forgetToGrpd) (fst' B αβ hαβ) rfl := by
  apply FunctorTo.hext
  · rfl
  · intro x
    erw [sec_obj_fiber]
    rfl
  · intro x y f
    erw [sec_map_fiber]
    simp [fstAux', mapFiber'_rfl, mapFiber, fst'_map_fiber]

@[inherit_doc fst] theorem snd'_forgetToGrpd : snd' B αβ hαβ ⋙ forgetToGrpd
    = sec _ (fst' B αβ hαβ) rfl ⋙ dependent' B αβ hαβ := by
  rw [snd', Functor.assoc, snd_forgetToGrpd, dependent', ← Functor.assoc, sec_fstAux']
  simp [map_id_eq, Functor.id_comp]

theorem snd'_obj_fiber {x} : ((snd' B αβ hαβ).obj x).fiber = (objFiber' hαβ x).fiber := by
  simp [snd']

-- FIXME: here the `simp` proof should also be factored through a `snd_map_base`
theorem snd'_map_fiber {x y} (f : x ⟶ y) : ((snd' B αβ hαβ).map f).fiber =
    eqToHom (by simp [snd', snd, assoc]; rfl) ≫ Hom.fiber (mapFiber' hαβ f) := by
  simp [snd']

theorem ι_fst'_forgetToGrpd_comp_dependent' (x) :
    ι (fst' B αβ hαβ ⋙ forgetToGrpd) x ⋙ dependent' B αβ hαβ = ι A x ⋙ B := by
  simp [dependent', map_id_eq, Functor.id_comp, fst'_forgetToGrpd]

theorem pairObjFiber_snd'_eq (x : Γ) : pairObjFiber (snd'_forgetToGrpd B αβ hαβ) x =
    objMk (objFiber' hαβ x).base (objFiber' (snd'_forgetToGrpd B αβ hαβ) x) := by
  apply hext
  · rw [pairObjFiber_base]
    simp [objFiber, fst'_obj_fiber]
  · rw [pairObjFiber_fiber]
    simp

theorem pairObjFiber_snd'_heq (x : Γ) : HEq (pairObjFiber (snd'_forgetToGrpd B αβ hαβ) x)
    (αβ.obj x).fiber := by
  rw [pairObjFiber_snd'_eq]
  apply @HEq.trans _ _ _ _ ((objFiber'EqToHom hαβ x).obj (αβ.obj x).fiber) _ ?_ ?_
  · apply hext'
    · apply ι_fst'_forgetToGrpd_comp_dependent'
    · rfl
    · rfl
  · simp [Grpd.eqToHom_obj]

theorem pairMapFiber_snd'_eq {x y} (f : x ⟶ y) :
    pairMapFiber (snd'_forgetToGrpd B αβ hαβ) f
    = homMk (mapFiber (fst' B αβ hαβ) f)
      (eqToHom (pairMapFiber_aux (snd'_forgetToGrpd B αβ hαβ) f)
        ≫ mapFiber' (snd'_forgetToGrpd B αβ hαβ) f) := by
  apply Hom.hext
  · simp
  · simp

theorem pairMapFiber_snd'_heq_src_heq {x y} (f : x ⟶ y) :
    HEq ((sigmaMap (dependent' B αβ hαβ) f).obj (pairObjFiber (snd'_forgetToGrpd _ _ hαβ) x))
    ((objFiber'EqToHom hαβ y).obj ((αβ.map f).base.obj (αβ.obj x).fiber)) := by
  have h : (αβ.map f).base.obj (αβ.obj x).fiber = _ :=
    Functor.congr_obj (Functor.congr_hom hαβ f) (αβ.obj x).fiber
  rw [Grpd.eqToHom_obj, heq_cast_iff_heq, h]
  simp only [Grpd.forgetToCat, dependent', eqToHom_refl, sigmaObj, Functor.comp_obj,
    sigma_obj, sigma_map, Grpd.comp_eq_comp,
    Grpd.eqToHom_obj, heq_cast_iff_heq]
  rw! [map_id_eq]
  congr
  apply eq_of_heq
  rw [heq_cast_iff_heq]
  apply HEq.trans _ (pairObjFiber_snd'_heq B αβ hαβ x)
  simp only [pairObjFiber, Functor.comp_obj, sigmaObj]
  congr
  simp [map_id_eq]

theorem pairMapFiber_snd'_heq_trg_heq {y} :
    HEq (pairObjFiber (snd'_forgetToGrpd B αβ hαβ) y)
    ((objFiber'EqToHom hαβ y).obj (αβ.obj y).fiber) := by
  rw [Grpd.eqToHom_obj, heq_cast_iff_heq]
  exact pairObjFiber_snd'_heq B αβ hαβ y

theorem sigmaMap_obj_objFiber' {x y} (f : x ⟶ y) : (sigmaMap B f).obj (objFiber' hαβ x) =
    (objFiber'EqToHom hαβ y).obj ((αβ.map f).base.obj (αβ.obj x).fiber) := by
  erw [Functor.congr_obj (Functor.congr_hom hαβ.symm f) (objFiber' hαβ x)]
  simp [Grpd.eqToHom_obj, objFiber', objFiber]

theorem pairMapFiber_snd'_heq {x y} (f : x ⟶ y) : HEq (pairMapFiber (snd'_forgetToGrpd B αβ hαβ) f)
    (αβ.map f).fiber := by
  rw [pairMapFiber_snd'_eq]
  apply @HEq.trans _ _ _ _ ((objFiber'EqToHom hαβ y).map (αβ.map f).fiber) _ ?_ ?_
  · apply Hom.hext'
    · apply ι_fst'_forgetToGrpd_comp_dependent'
    · apply pairMapFiber_snd'_heq_src_heq
    · rw [Grpd.eqToHom_obj, heq_cast_iff_heq]
      exact pairObjFiber_snd'_heq B αβ hαβ y
    · rw [homMk_base, mapFiber, fst'_map_fiber]
      congr!
      · apply sigmaMap_obj_objFiber'
      · apply HEq.trans (eqToHom_comp_heq _ _)
        simp
    · simp only [homMk_fiber, eqToHom_comp_heq_iff]
      apply HEq.trans (mapFiber'_heq _ f)
      simp only [snd'_map_fiber, Functor.comp_map, eqToHom_comp_heq_iff]
      congr!
      · apply sigmaMap_obj_objFiber'
      · apply HEq.trans (eqToHom_comp_heq _ _)
        simp
  · simp [Grpd.eqToHom_hom]

theorem eta : pair (fst' B αβ hαβ) (snd' B αβ hαβ)
    (dependent' B αβ hαβ) (snd'_forgetToGrpd _ _ _) = αβ := by
  apply PGrpd.Functor.hext
  · rw [pair, PGrpd.functorTo_forget, hαβ]
    congr
    simp [dependent', map_id_eq, Functor.id_comp]
  · intro x
    exact pairObjFiber_snd'_heq _ _ _ _
  · intro x y f
    exact pairMapFiber_snd'_heq _ _ _ _

end

section
variable {Γ : Type u₂} [Groupoid.{v₂} Γ] {α β : Γ ⥤ PGrpd.{v₁,u₁}}
  {B : ∫(α ⋙ forgetToGrpd) ⥤ Grpd.{v₁,u₁}} (h : β ⋙ forgetToGrpd = sec _ α rfl ⋙ B)

@[simp] theorem fst'_pair : fst' B (pair α β B h) (pair_comp_forgetToGrpd _) = α := by
  apply PGrpd.Functor.hext
  · rw [fst'_forgetToGrpd]
  · intro x
    erw [fst'_obj_fiber]
  · intro x y f
    simp only [fst'_map_fiber, objFiber'_rfl, mapFiber'_rfl]
    erw [pairMapFiber_base, mapFiber]

@[simp] theorem snd'_pair : snd' B (pair α β B h) (pair_comp_forgetToGrpd _) = β := by
  apply PGrpd.Functor.hext
  · rw [snd'_forgetToGrpd, h, dependent']
    congr 2
    · rw [fst'_pair]
    · simp [map_id_eq, Functor.id_comp]
  · intro x
    simp only [snd'_obj_fiber, objFiber'_rfl, objFiber, pair_obj_fiber, pairObjFiber_fiber]
    simp [objFiber', Grpd.eqToHom_obj, objFiber]
  · intro x y f
    simp only [snd'_map_fiber]
    apply (eqToHom_comp_heq _ _).trans
    simp only [sigmaObj, objFiber'_rfl, sigma_obj, Grpd.coe_of, mapFiber', eqToHom_refl,
      Grpd.id_eq_id, mapFiber'EqToHom, pair_map_fiber, Functor.id_map,
      Functor.Groupoidal.comp_fiber, Functor.Groupoidal.id_fiber, eqToHom_map]
    apply (eqToHom_comp_heq _ _).trans
    rw [pairMapFiber_fiber]
    apply (eqToHom_comp_heq _ _).trans
    simp only [mapFiber', mapFiber'EqToHom, Grpd.eqToHom_hom, eqToHom_trans_assoc]
    apply (eqToHom_comp_heq _ _).trans
    simp

end

end sigma

end FunctorOperation

open FunctorOperation

section

@[simp]
abbrev USig.SigAux {X : Type (v + 1)} [Category.{v} X]
    (S : ∀ {Γ : Ctx} (A : Γ ⥤ Grpd.{v,v}) (B : ∫(A) ⥤ X), Γ ⥤ X)
    {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ Ctx.coreAsSmall X) :
    Γ ⟶ Ctx.coreAsSmall X :=
  toCoreAsSmallEquiv.symm (S (toCoreAsSmallEquiv A) (toCoreAsSmallEquiv B))

theorem USig.SigAux_comp {X : Type (v + 1)} [Category.{v} X]
    (S : ∀ {Γ : Ctx} (A : Γ ⥤ Grpd.{v,v}) (B : ∫(A) ⥤ X), Γ ⥤ X)
    (S_naturality : ∀ {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {A : Γ ⥤ Grpd}
      {B : ∫(A) ⥤ X}, σ ⋙ S A B = S (σ ⋙ A) (pre A σ ⋙ B))
    {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.{v}.Ty} {σA : Δ ⟶ U.Ty}
    (eq : σ ≫ A = σA) (B : U.ext A ⟶ Ctx.coreAsSmall X) :
    USig.SigAux S (U.substWk σ A σA eq ≫ B) = σ ≫ USig.SigAux S B := by
  simp only [USig.SigAux, Grpd.comp_eq_comp]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left]
  congr 1
  rw [S_naturality]
  subst eq
  simp only [Grpd.comp_eq_comp]
  conv => left; right; rw! [toCoreAsSmallEquiv_apply_comp_left]
  rw! (castMode := .all) [toCoreAsSmallEquiv_apply_comp_left]
  simp [U.substWk_eq, map_id_eq]
  rfl

def USig.Sig {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.{v}.Ty) : Γ ⟶ U.{v}.Ty :=
  USig.SigAux sigma B

/--
Naturality for the formation rule for Σ-types.
Also known as Beck-Chevalley.
-/
theorem USig.Sig_comp {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.{v}.Ty} {σA : Δ ⟶ U.Ty}
    (eq : σ ≫ A = σA) (B : U.ext A ⟶ U.{v}.Ty) :
    USig.Sig (U.substWk σ A σA eq ≫ B) = σ ≫ USig.Sig B :=
  USig.SigAux_comp sigma (by intros; rw [sigma_naturality]) σ eq B

lemma USig.pair_aux {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.{v}.Ty) (a : Γ ⟶ U.Tm)
    (a_tp : a ≫ U.tp = A) (b : Γ ⟶ U.Tm) (b_tp : b ≫ U.tp = U.sec A a a_tp ≫ B) :
    toCoreAsSmallEquiv b ⋙ forgetToGrpd =
    sec (toCoreAsSmallEquiv a ⋙ forgetToGrpd) (toCoreAsSmallEquiv a) rfl ⋙
    map (eqToHom (by rw [← a_tp, ← toCoreAsSmallEquiv_apply_comp_right]; rfl)) ⋙
    toCoreAsSmallEquiv B := by
  rw [← toCoreAsSmallEquiv_apply_comp_right, ← toCoreAsSmallEquiv_apply_comp_left,
    ← toCoreAsSmallEquiv_apply_comp_left]
  congr 1
  simp only [Grpd.comp_eq_comp, U.tp] at b_tp
  rw [b_tp]
  subst a_tp
  simp [map_id_eq]
  rfl

def USig.pair {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.{v}.Ty) (a : Γ ⟶ U.Tm)
    (a_tp : a ≫ U.tp = A) (b : Γ ⟶ U.Tm) (b_tp : b ≫ U.tp = U.sec A a a_tp ≫ B) :
    Γ ⟶ U.{v}.Tm :=
  toCoreAsSmallEquiv.symm <|
    FunctorOperation.pair (toCoreAsSmallEquiv a) (toCoreAsSmallEquiv b)
    (map (eqToHom (by
      rw [← a_tp, ← toCoreAsSmallEquiv_apply_comp_right, Grpd.comp_eq_comp, U.tp])) ⋙
    toCoreAsSmallEquiv B) <| pair_aux B a a_tp b b_tp

theorem USig.pair_comp {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.{v}.Ty} {σA : Δ ⟶ U.Ty}
    (eq : σ ≫ A = σA) (B : U.ext A ⟶ U.{v}.Ty) (a : Γ ⟶ U.Tm)
    (a_tp : a ≫ U.tp = A) (b : Γ ⟶ U.Tm) (b_tp : b ≫ U.tp = U.sec A a a_tp ≫ B) :
  USig.pair (U.substWk σ A σA eq ≫ B) (σ ≫ a) (by cat_disch) (σ ≫ b)
    (by rw! [Category.assoc, b_tp, comp_sec_assoc]) = σ ≫ USig.pair B a a_tp b b_tp := by
  dsimp [pair]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, FunctorOperation.pair_naturality]
  congr 2
  slice_rhs 2 3 => rw [← toCoreAsSmallEquiv_apply_comp_left]
  subst a_tp eq
  simp [← toCoreAsSmallEquiv_apply_comp_left, map_id_eq, U.substWk_eq]
  rfl

lemma USig.pair_tp {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.{v}.Ty) (a : Γ ⟶ U.Tm)
    (a_tp : a ≫ U.tp = A) (b : Γ ⟶ U.Tm) (b_tp : b ≫ U.tp = U.sec A a a_tp ≫ B) :
    USig.pair B a a_tp b b_tp ≫ U.tp = USig.Sig B := by
  dsimp [pair, Sig, U.tp]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_right, FunctorOperation.pair_comp_forgetToGrpd,
    ← toCoreAsSmallEquiv_apply_comp_left]
  subst a_tp
  congr 3
  convert_to Grpd.homOf (map (eqToHom _)) ≫ B = 𝟙 (U.ext (a ≫ U.tp)) ≫ B
  rw [← eqToHom_eq_homOf_map]
  simp

lemma USig.fst_aux {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.{v}.Ty)
    (s : Γ ⟶ U.Tm) (s_tp : s ≫ U.tp = USig.Sig B) :
    toCoreAsSmallEquiv s ⋙ forgetToGrpd = sigma (toCoreAsSmallEquiv A) (toCoreAsSmallEquiv B) := by
  dsimp only [U.tp, Grpd.comp_eq_comp, Sig] at s_tp
  rw [← toCoreAsSmallEquiv_apply_comp_right, s_tp]
  simp

def USig.fst {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.Ty)
    (s : Γ ⟶ U.Tm) (s_tp : s ≫ U.tp = USig.Sig B) : Γ ⟶ U.Tm.{v} :=
  toCoreAsSmallEquiv.symm <| FunctorOperation.sigma.fst' (toCoreAsSmallEquiv B)
    (toCoreAsSmallEquiv s) <| fst_aux B s s_tp

lemma USig.fst_comp {Γ Δ : Grpd} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.Ty} {σA : Δ ⟶ U.Ty} (eq : σ ≫ A = σA)
    (B : U.ext A ⟶ U.Ty) (s : Γ ⟶ U.Tm) (s_tp : s ≫ U.tp = USig.Sig B) :
    USig.fst (U.substWk σ A σA eq ≫ B) (σ ≫ s) (by rw [Category.assoc, s_tp, Sig_comp]) =
    σ ≫ USig.fst B s s_tp := by
  dsimp [fst]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, ← sigma.fst'_comp]
  subst eq
  rw! [toCoreAsSmallEquiv_apply_comp_left, U.substWk_eq]
  simp [map_id_eq]
  rfl

lemma USig.fst_tp {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.Ty)
    (s : Γ ⟶ U.Tm) (s_tp : s ≫ U.tp = USig.Sig B) :
    USig.fst B s s_tp ≫ U.tp = A := by
  dsimp [fst, U.tp]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_right, sigma.fst'_forgetToGrpd]
  simp

def USig.snd {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.Ty)
    (s : Γ ⟶ U.Tm) (s_tp : s ≫ U.tp = USig.Sig B) : Γ ⟶ U.Tm.{v} :=
  toCoreAsSmallEquiv.symm <| FunctorOperation.sigma.snd' (toCoreAsSmallEquiv B)
    (toCoreAsSmallEquiv s) <| fst_aux B s s_tp

lemma USig.snd_comp {Γ Δ : Grpd} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.Ty} {σA : Δ ⟶ U.Ty} (eq : σ ≫ A = σA)
    (B : U.ext A ⟶ U.Ty) (s : Γ ⟶ U.Tm) (s_tp : s ≫ U.tp = USig.Sig B) :
    USig.snd (U.substWk σ A σA eq ≫ B) (σ ≫ s) (by rw [Category.assoc, s_tp, Sig_comp]) =
    σ ≫ USig.snd B s s_tp := by
  dsimp [snd]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left]
  congr 1
  rw [← sigma.snd'_comp]
  subst eq
  congr 1
  rw [toCoreAsSmallEquiv_apply_comp_left, U.substWk_eq]
  simp [map_id_eq]
  rfl

def USig.snd_tp {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.Ty)
    (s : Γ ⟶ U.Tm) (s_tp : s ≫ U.tp = USig.Sig B) :
    USig.snd B s s_tp ≫ U.tp = U.sec A (USig.fst B s s_tp) (fst_tp ..) ≫ B := by
  dsimp [snd, U.tp]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_right, sigma.snd'_forgetToGrpd,
    toCoreAsSmallEquiv.symm_apply_eq, toCoreAsSmallEquiv_apply_comp_left]
  simp [sigma.dependent', map_id_eq]
  rfl

lemma USig.fst_pair {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.{v}.Ty) (a : Γ ⟶ U.Tm)
    (a_tp : a ≫ U.tp = A) (b : Γ ⟶ U.Tm) (b_tp : b ≫ U.tp = U.sec A a a_tp ≫ B) :
    fst B (USig.pair B a a_tp b b_tp) (pair_tp ..) = a := by
  dsimp [fst, pair]
  rw [toCoreAsSmallEquiv.symm_apply_eq]
  subst a_tp
  simp only [Grpd.comp_eq_comp, eqToHom_refl, map_id_eq, Cat.of_α, Functor.id_comp,
    Equiv.apply_symm_apply]
  exact sigma.fst'_pair (α := toCoreAsSmallEquiv a) (β := toCoreAsSmallEquiv b)
      (B := toCoreAsSmallEquiv B) (by rw [pair_aux B a rfl b b_tp]; simp [map_id_eq]; rfl)

lemma USig.snd_pair {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.{v}.Ty) (a : Γ ⟶ U.Tm)
    (a_tp : a ≫ U.tp = A) (b : Γ ⟶ U.Tm) (b_tp : b ≫ U.tp = U.sec A a a_tp ≫ B) :
    USig.snd B (USig.pair B a a_tp b b_tp) (pair_tp ..) = b := by
  dsimp [snd, pair]
  rw [toCoreAsSmallEquiv.symm_apply_eq]
  subst a_tp
  simp only [Grpd.comp_eq_comp, eqToHom_refl, map_id_eq, Cat.of_α, Functor.id_comp,
    Equiv.apply_symm_apply]
  exact sigma.snd'_pair (α := toCoreAsSmallEquiv a) (β := toCoreAsSmallEquiv b)
      (B := toCoreAsSmallEquiv B) (by rw [pair_aux B a rfl b b_tp]; simp [map_id_eq]; rfl)

lemma USig.eta {Γ : Grpd} {A : Γ ⟶ U.Ty} (B : U.ext A ⟶ U.Ty) (s : Γ ⟶ U.Tm)
    (s_tp : s ≫ U.tp = USig.Sig B) :
    USig.pair B (USig.fst B s s_tp) (fst_tp ..) (USig.snd B s s_tp) (snd_tp ..) = s := by
  dsimp [pair]
  rw [toCoreAsSmallEquiv.symm_apply_eq]
  have h := FunctorOperation.sigma.eta (toCoreAsSmallEquiv B) (toCoreAsSmallEquiv s)
    (by rwa [fst_aux])
  simp only [map_id_eq, Cat.of_α, Functor.id_comp]
  rw [← h]
  congr 1
  simp [sigma.dependent', map_id_eq]

def USig : Universe.PolymorphicSigma U.{v} U.{v} U.{v} where
  Sig := USig.Sig
  Sig_comp := USig.Sig_comp
  pair := USig.pair
  pair_comp := USig.pair_comp
  pair_tp := USig.pair_tp
  fst := USig.fst
  fst_comp := USig.fst_comp
  fst_tp := USig.fst_tp
  snd := USig.snd
  snd_comp := USig.snd_comp
  snd_tp := USig.snd_tp
  fst_pair := USig.fst_pair
  snd_pair := USig.snd_pair
  eta := USig.eta

end

end GroupoidModel
end
