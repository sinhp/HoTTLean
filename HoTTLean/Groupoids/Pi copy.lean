import HoTTLean.Groupoids.Sigma
import HoTTLean.ForMathlib.CategoryTheory.Whiskering
import HoTTLean.ForMathlib.CategoryTheory.NatTrans

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
-- NOTE temporary section for stuff to be moved elsewhere
section ForOther

lemma hcongr_fun {α α' : Type u} (hα : α ≍ α') (β : α → Type v) (β' : α' → Type v) (hβ : β ≍ β')
    (f : (x : α) → β x) (f' : (x : α') → β' x) (hf : f ≍ f')
    {x : α} {x' : α'} (hx : x ≍ x') : f x ≍ f' x' := by
  subst hα hβ hf hx
  rfl

namespace CategoryTheory

lemma Functor.Iso.whiskerLeft_inv_hom_heq {C : Type u} [Category.{v} C] {D : Type u₁}
    [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E] (F : C ≅≅ D) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.inv ⋙ F.hom).whiskerLeft η ≍ η := by
  rw [F.inv_hom_id]
  aesop_cat

lemma Functor.Iso.whiskerLeft_inv_hom {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E] (F : C ≅≅ D) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.inv ⋙ F.hom).whiskerLeft η = eqToHom (by aesop) ≫ η ≫ eqToHom (by aesop) := by
  simpa [← heq_eq_eq] using
    Functor.Iso.whiskerLeft_inv_hom_heq F G H η

lemma Functor.Iso.whiskerLeft_hom_inv_heq {C : Type u} [Category.{v} C] {D : Type u₁}
    [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E] (F : D ≅≅ C) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.hom ⋙ F.inv).whiskerLeft η ≍ η := by
  rw [F.hom_inv_id]
  aesop_cat

lemma Functor.Iso.whiskerLeft_hom_inv {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E] (F : D ≅≅ C) (G H : D ⥤ E) (η : G ⟶ H) :
    (F.hom ⋙ F.inv).whiskerLeft η = eqToHom (by aesop) ≫ η ≫ eqToHom (by aesop) := by
  simpa [← heq_eq_eq] using
    Functor.Iso.whiskerLeft_hom_inv_heq F G H η

lemma Functor.associator_eq {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : associator F G H = CategoryTheory.Iso.refl _ :=
  rfl

section
variable {A B : Type*} [Category A] [Category B] (F : B ⥤ A)

-- NOTE to follow mathlib convention can use camelCase for definitions, and capitalised first letter when that definition is a Prop or Type
def IsSection (s : A ⥤ B) := s ⋙ F = Functor.id A

abbrev Section := ObjectProperty.FullSubcategory (IsSection F)

instance Section.category : Category (Section F) :=
  ObjectProperty.FullSubcategory.category (IsSection F)

abbrev Section.ι : Section F ⥤ (A ⥤ B) :=
  ObjectProperty.ι (IsSection F)

end

namespace ObjectProperty

lemma ι_mono {T C : Type u} [Category.{v} C] [Category.{v} T]
    {Z : C → Prop} (f g : T ⥤ FullSubcategory Z)
    (e : f ⋙ ι Z = g ⋙ ι Z) : f = g := by
  apply CategoryTheory.Functor.ext_of_iso _ _ _
  · exact Functor.fullyFaithfulCancelRight (ι Z) (eqToIso e)
  · intro X
    ext
    exact Functor.congr_obj e X
  · intro X
    simp only [Functor.fullyFaithfulCancelRight_hom_app, Functor.preimage, ι_obj, ι_map,
      eqToIso.hom, eqToHom_app, Functor.comp_obj, Classical.choose_eq]
    rfl

end ObjectProperty

instance {C : Type*} [Groupoid C] (P : ObjectProperty C) :
    Groupoid (P.FullSubcategory) :=
  InducedCategory.groupoid C (ObjectProperty.ι _).obj

instance Grpd.ι_mono (G : Grpd) (P : ObjectProperty G) : Mono (Grpd.homOf (ObjectProperty.ι P)) :=
  ⟨ fun _ _ e => ObjectProperty.ι_mono _ _ e ⟩

lemma Grpd.ObjectProperty.FullSubcategory.congr {A A' : Grpd.{v,u}} (hA : A ≍ A')
    (P : ObjectProperty A) (P' : ObjectProperty A') (hP : P ≍ P')
    (a : A) (a' : A') (ha : a ≍ a') (ha : P a) (ha' : P' a') :
    (⟨ a, ha ⟩ : P.FullSubcategory) ≍ (⟨ a', ha' ⟩ : P'.FullSubcategory) := by
  subst hA ha hP
  rfl

lemma Grpd.ObjectProperty.FullSubcategory.hext {A A' : Grpd.{v,u}} (hA : A ≍ A')
    (P : ObjectProperty A) (P' : ObjectProperty A') (hP : P ≍ P')
    (p : P.FullSubcategory) (p' : P'.FullSubcategory)
    (hp : p.obj ≍ p'.obj) : p ≍ p' := by
  cases p; cases p'
  subst hA hP hp
  rfl

end CategoryTheory

namespace GroupoidModel

open CategoryTheory Opposite Functor.Groupoidal

end GroupoidModel

end ForOther

-- NOTE content for this doc starts here
namespace GroupoidModel

open CategoryTheory Opposite Functor.Groupoidal

attribute [local simp] eqToHom_map Grpd.id_eq_id Grpd.comp_eq_comp Functor.id_comp Functor.comp_id

namespace FunctorOperation
section

open CategoryTheory.Functor

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A B : Γ ⥤ Grpd.{v₁,u₁})

/--
The functor that, on objects `G : A.obj x ⥤ B.obj x` acts by
creating the map on the right,
by taking the inverse of `f : x ⟶ y` in the groupoid
         A f
  A x --------> A y
   |             .
   |             |
   |             .
G  |             | conjugating A B f G
   |             .
   V             V
  B x --------> B y
         B f
-/

@[simp]
def conjugating' {x y : Γ} (f : x ⟶ y) : (A.obj x ⥤ B.obj x) ⥤
    (A.obj y ⥤ B.obj y) :=
  whiskeringLeftObjWhiskeringRightObj (A.map (inv f)) (B.map f)

def conjugating {x y : Γ} (f : x ⟶ y) : Grpd.of (A.obj x ⥤ B.obj x) ⟶
    Grpd.of (A.obj y ⥤ B.obj y) :=
  conjugating' A B f

lemma conjugating_obj {x y : Γ} (f : x ⟶ y) (s : A.obj x ⥤ B.obj x) :
    (conjugating A B f).obj s = A.map (inv f) ⋙ s ⋙ B.map f := by
  rfl

lemma conjugating_map {x y : Γ} (f : x ⟶ y) {s1 s2 : A.obj x ⥤ B.obj x} (h : s1 ⟶ s2) :
    (conjugating A B f).map h
    = whiskerRight (whiskerLeft (A.map (inv f)) h) (B.map f) := by
  rfl

@[simp] lemma conjugating_id (x : Γ) : conjugating A B (𝟙 x) = 𝟭 _ := by
  simp [conjugating]

@[simp] lemma conjugating_comp (x y z : Γ) (f : x ⟶ y) (g : y ⟶ z) :
    conjugating A B (f ≫ g) = conjugating A B f ⋙ conjugating A B g := by
  simp [conjugating]

@[simp] lemma conjugating_naturality_map {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)
    {x y} (f : x ⟶ y) : conjugating (σ ⋙ A) (σ ⋙ B) f = conjugating A B (σ.map f) := by
  simp [conjugating]

def conjugatingObjNatTransEquiv' {x y : Γ} (f : x ⟶ y) (S) (T) :
    ((Grpd.Functor.iso A f).inv ⋙ S ⋙ (Grpd.Functor.iso B f).hom ⟶ T) ≃
    (S ⋙ (Grpd.Functor.iso B f).hom ⟶ (Grpd.Functor.iso A f).hom ⋙ T) where
  toFun η := eqToHom (by simp) ≫ whiskerLeft (Grpd.Functor.iso A f).hom η
  invFun η := whiskerLeft (Grpd.Functor.iso A f).inv η ≫ eqToHom (by simp)
  left_inv η := by
    simp only [whiskerLeft_comp, whiskerLeft_eqToHom, whiskerLeft_twice, associator_eq,
      CategoryTheory.Iso.refl_inv, CategoryTheory.Iso.refl_hom, Category.comp_id, Category.assoc,
      ← heq_eq_eq, eqToHom_comp_heq_iff]
    rw! (transparency := .default) [Category.id_comp, comp_eqToHom_heq_iff]
    apply Functor.Iso.whiskerLeft_inv_hom_heq
  right_inv η := by
    simp only [whiskerLeft_comp, whiskerLeft_twice, associator_eq, CategoryTheory.Iso.refl_inv,
      CategoryTheory.Iso.refl_hom, Category.comp_id, whiskerLeft_eqToHom, Category.assoc, ←
      heq_eq_eq, eqToHom_comp_heq_iff]
    rw! (transparency := .default) [Category.id_comp, comp_eqToHom_heq_iff]
    apply Functor.Iso.whiskerLeft_hom_inv_heq

-- @[simp]
-- lemma conjugatingObjNatTransEquiv'_apply {x y : Γ} (f : x ⟶ y) (S) (T) (g) :
--     conjugatingObjNatTransEquiv' A B f S T g =
--     eqToHom (by simp) ≫ g ≫ eqToHom (by simp) := by
--   ext
--   simp [conjugatingObjNatTransEquiv', Grpd.Functor.iso]

@[simp]
lemma conjugatingObjNatTransEquiv'_id (x : Γ) (S) (T) (g) :
    conjugatingObjNatTransEquiv' A B (𝟙 x) S T g =
    eqToHom (by simp) ≫ g ≫ eqToHom (by simp) := by
  ext
  simp [conjugatingObjNatTransEquiv', Grpd.Functor.iso]

lemma conjugatingObjNatTransEquiv'_comp {x y z : Γ} (f1 : x ⟶ y) (f2 : y ⟶ z) (S) (T) (g) :
    conjugatingObjNatTransEquiv' A B (f1 ≫ f2) S T g =
    eqToHom (by simp [Grpd.Functor.iso, ← Grpd.comp_eq_comp]) ≫
    (A.map f1 ⋙ A.map f2).whiskerLeft g ≫
    eqToHom (by simp [Grpd.Functor.iso, ← Grpd.comp_eq_comp]) := by
  simp [conjugatingObjNatTransEquiv', Grpd.Functor.iso]
  rw! [Functor.map_comp A f1 f2]
  simp

lemma whiskerLeft_map_comp {x y z : Γ} (f1 : x ⟶ y) (f2 : y ⟶ z)
    (T1 T2 : (A.obj z) ⥤ (B.obj z))
    (g12 : T1 ⟶ T2) :
    whiskerLeft (A.map (f1 ≫ f2)) g12 =
    eqToHom (by simp) ≫ (A.map f1 ⋙ A.map f2).whiskerLeft g12 ≫ eqToHom (by simp) := by
  aesop_cat

lemma Functor.id_whiskerLeft {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {H0 H1 : C ⥤ D} (α : H0 ⟶ H1) :
    whiskerLeft (𝟭 C) α = α :=
  rfl

lemma Functor.comp_whiskerLeft {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : B ⥤ C) {H0 H1 : C ⥤ D} (α : H0 ⟶ H1) :
    whiskerLeft (F ⋙ G) α = whiskerLeft F (whiskerLeft G α) :=
  rfl

lemma Functor.whiskerRight_whiskerLeft {A B C D : Type*} [Category A] [Category B] [Category C]
    [Category D] (F : A ⥤ B) (G0 G1 : B ⥤ C) (H : C ⥤ D) (α : G0 ⟶ G1) :
    whiskerRight (whiskerLeft F α) H = whiskerLeft F (whiskerRight α H) := by
  rfl

theorem whiskerLeft_twice' {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : B ⥤ C) {H K : C ⥤ D} (α : H ⟶ K) :
    whiskerLeft F (whiskerLeft G α) =
    whiskerLeft (F ⋙ G) α :=
  rfl

lemma conjugatingObjNatTransEquiv'_comp' {x y z : Γ} (f1 : x ⟶ y) (f2 : y ⟶ z)
    (S0 : (A.obj x) ⥤ (B.obj x))
    (S1 : (A.obj y) ⥤ (B.obj y))
    (S2 : (A.obj z) ⥤ (B.obj z))
    (g01 : A.map (CategoryTheory.inv f1) ⋙ S0 ⋙ B.map f1 ⟶ S1)
    (g12 : A.map (CategoryTheory.inv f2) ⋙ S1 ⋙ B.map f2 ⟶ S2)
    (g02 : A.map (CategoryTheory.inv (f1 ≫ f2)) ⋙ S0 ⋙ B.map (f1 ≫ f2) ⟶ S2)
    (h : g02 = eqToHom (by simp [← Grpd.comp_eq_comp]) ≫
      Functor.whiskerRight (Functor.whiskerLeft (A.map (CategoryTheory.inv f2)) g01) (B.map f2) ≫
      eqToHom (by simp [← Grpd.comp_eq_comp]) ≫ g12) :
    conjugatingObjNatTransEquiv' A B (f1 ≫ f2) S0 S2 g02 =
    eqToHom (by simp [← Grpd.comp_eq_comp, Grpd.Functor.iso]) ≫
    (whiskerRight (conjugatingObjNatTransEquiv' A B f1 S0 S1 g01) (B.map f2)) ≫
    (whiskerLeft (A.map f1) (conjugatingObjNatTransEquiv' A B f2 S1 S2 g12)) ≫
    eqToHom (by simp [← Grpd.comp_eq_comp, Grpd.Functor.iso]) := by
  subst h
  simp [conjugatingObjNatTransEquiv', Grpd.Functor.iso, Functor.associator_eq] at *
  erw [Category.id_comp]
  rw [whiskerLeft_map_comp]
  rw [whiskerLeft_map_comp]
  simp [← Category.assoc]
  congr 2
  rw [Functor.comp_whiskerLeft, Functor.whiskerRight_whiskerLeft, Functor.whiskerRight_whiskerLeft]
  rw [whiskerLeft_twice' (A.map f2)]
  simp only [← Grpd.comp_eq_comp]
  rw! (castMode := .all) [← Functor.map_comp A f2, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Grpd.id_eq_id]
  simp only [Functor.id_whiskerLeft]
  simp [← heq_eq_eq]
  congr 1
  · simp [← Grpd.comp_eq_comp]
  · simp [← Grpd.comp_eq_comp]
  · simp

def conjugatingObjNatTransEquiv₁ {x y : Γ} (f : x ⟶ y) (S) (T) :
    (A.map (inv f) ⋙ S ⋙ B.map f ⟶ T) ≃
    (S ⋙ B.map f ≅ A.map f ⋙ T) := (conjugatingObjNatTransEquiv' A B f S T).trans
    (Groupoid.isoEquivHom (S ⋙ B.map f) (A.map f ⋙ T)).symm

@[simp]
lemma conjugatingObjNatTransEquiv₁_id_inv {x : Γ} (S) (T)
    (g : A.map (inv (𝟙 x)) ⋙ S ⋙ B.map (𝟙 x) ⟶ T) :
    (conjugatingObjNatTransEquiv₁ A B (𝟙 x) S T g).inv =
    eqToHom (by simp) ≫ CategoryTheory.inv g ≫ eqToHom (by simp) := by
  dsimp only [conjugatingObjNatTransEquiv₁, Equiv.trans_apply]
  erw [conjugatingObjNatTransEquiv'_id]
  simp [Groupoid.isoEquivHom]

lemma conjugatingObjNatTransEquiv₁_comp_inv {x y z : Γ} (f1 : x ⟶ y) (f2 : y ⟶ z)
      (S0 : (A.obj x) ⥤ (B.obj x))
      (S1 : (A.obj y) ⥤ (B.obj y))
      (S2 : (A.obj z) ⥤ (B.obj z))
      (g01 : A.map (inv f1) ⋙ S0 ⋙ B.map f1 ⟶ S1)
      (g12 : A.map (inv f2) ⋙ S1 ⋙ B.map f2 ⟶ S2)
      (g02 : A.map (inv (f1 ≫ f2)) ⋙ S0 ⋙ B.map (f1 ≫ f2) ⟶ S2)
      (h : g02 = eqToHom (by simp [← Grpd.comp_eq_comp]) ≫
      Functor.whiskerRight (Functor.whiskerLeft (A.map (CategoryTheory.inv f2)) g01) (B.map f2) ≫
      eqToHom (by simp [← Grpd.comp_eq_comp]) ≫ g12) :
      (conjugatingObjNatTransEquiv₁ A B (f1 ≫ f2) S0 S2 g02).inv =
      eqToHom (by simp [← Grpd.comp_eq_comp]) ≫
      whiskerLeft (A.map f1) (conjugatingObjNatTransEquiv₁ A B f2 S1 S2 g12).inv ≫
      whiskerRight ((conjugatingObjNatTransEquiv₁ A B f1 S0 S1 g01).inv) (B.map f2) ≫
      eqToHom (by simp [← Grpd.comp_eq_comp]) := by
  dsimp [conjugatingObjNatTransEquiv₁]
  erw [conjugatingObjNatTransEquiv'_comp' A B f1 f2 S0 S1 S2 g01 g12 g02 h]
  simp [Groupoid.isoEquivHom]
  rfl

-- lemma conjugatingObjNatTransEquiv₁_comp_inv {x y z : Γ} (f1 : x ⟶ y) (f2 : y ⟶ z) (S) (T)
--     (g : A.map (inv (f1 ≫ f2)) ⋙ S ⋙ B.map (f1 ≫ f2) ⟶ T) :
--     (conjugatingObjNatTransEquiv₁ A B (f1 ≫ f2) S T g).inv =
--     eqToHom (by simp [Functor.assoc]) ≫
--     (A.map f1 ⋙ A.map f2).whiskerLeft (CategoryTheory.inv g) ≫
--     eqToHom (by simp [← Grpd.comp_eq_comp])
--      := by
--   simp only [conjugatingObjNatTransEquiv₁, Groupoid.isoEquivHom, Groupoid.inv_eq_inv,
--     Equiv.trans_apply, Equiv.coe_fn_symm_mk]
--   erw [conjugatingObjNatTransEquiv'_comp]
--   simp [IsIso.inv_comp, inv_eqToHom, inv_whiskerLeft, Category.assoc]

-- lemma conjugatingObjNatTransEquiv₁_comp_inv {x y z : Γ} (f1 : x ⟶ y) (f2 : y ⟶ z) (S) (T)
--     (g : A.map (inv (f1 ≫ f2)) ⋙ S ⋙ B.map (f1 ≫ f2) ⟶ T) :
--     (conjugatingObjNatTransEquiv₁ A B (f1 ≫ f2) S T g).inv =
--     eqToHom (by simp [Functor.assoc]) ≫
--     whiskerLeft (A.map f1) (whiskerLeft (A.map f2) (CategoryTheory.inv g)) ≫
--     eqToHom (by simp [← Grpd.comp_eq_comp])
--      := by
--   dsimp only [conjugatingObjNatTransEquiv₁, Equiv.trans_apply]
--   simp only [Groupoid.isoEquivHom, Groupoid.inv_eq_inv, Equiv.coe_fn_symm_mk]
--   erw [conjugatingObjNatTransEquiv'_comp]
--   simp only [IsIso.inv_comp, inv_eqToHom, inv_whiskerLeft, Category.assoc]
end

section

variable {Γ : Type u₂} [Category.{v₂} Γ] {A : Γ ⥤ Grpd.{v₁,u₁}}
  (B : ∫(A) ⥤ Grpd.{v₁,u₁}) (x : Γ)

-- NOTE: domain changed from sigmaObj, since we don't want to view domain as an object in `Grpd`
abbrev sigma.fstAuxObj : ∫ ι A x ⋙ B ⥤ A.obj x := forget

open sigma

def piObj : Grpd := Grpd.of (Section (fstAuxObj B x))

lemma piObj.hext {A A' : Γ ⥤ Grpd.{v,u}} (hA : A ≍ A') {B : ∫ A ⥤ Grpd.{v,u}}
    {B' : ∫ A' ⥤ Grpd.{v,u}} (hB : B ≍ B') (x : Γ)
    (f : piObj B x) (f' : piObj B' x) (hf : f.obj ≍ f'.obj) : f ≍ f' := by
  subst hA hB
  simp only [heq_eq_eq] at *
  unfold piObj Section Grpd.of Bundled.of
  ext
  rw [hf]

end

section
variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (B : ∫(A) ⥤ Grpd.{u₁,u₁})
variable {x y : Γ} (f: x ⟶ y)

open sigma

/--
If `s : piObj B x` then the underlying functor is of the form `s : A x ⥤ sigma A B x`
and it is a section of the forgetful functor `sigma A B x ⥤ A x`.
This theorem states that conjugating `A f⁻¹ ⋙ s ⋙ sigma A B f⁻¹ : A y ⥤ sigma A B y`
using some `f : x ⟶ y` produces a section of the forgetful functor `sigma A B y ⥤ A y`.
-/
theorem isSection_conjugating_isSection (s : piObj B x) : IsSection (fstAuxObj B y)
    ((Section.ι (fstAuxObj B x) ⋙ conjugating A (sigma A B) f).obj s) := by
  simp only [IsSection, Functor.comp_obj, ObjectProperty.ι_obj,
    conjugating_obj, Functor.assoc, sigma_map, fstAuxObj]
  rw [sigmaMap_forget]
  convert_to (Grpd.Functor.iso A f).inv ⋙ (s.obj ⋙ fstAuxObj B x) ⋙ (Grpd.Functor.iso A f).hom = _
  rw [s.property]
  simp

/-- The functorial action of `pi` on a morphism `f : x ⟶ y` in `Γ`
is given by "conjugation".
Since `piObj B x` is a full subcategory of `sigma A B x ⥤ A x`,
we obtain the action `piMap : piObj B x ⥤ piObj B y`
as the induced map in the following diagram
          the inclusion
           Section.ι
   piObj B x   ⥤   (A x ⥤ sigma A B x)
     ⋮                     ||
     ⋮                     || conjugating A (sigma A B) f
     VV                     VV
   piObj B y   ⥤   (A y ⥤ sigma A B y)
-/
def piMap : piObj B x ⥤ piObj B y :=
  ObjectProperty.lift (IsSection (fstAuxObj B y))
  ((Section.ι (fstAuxObj B x) ⋙ conjugating A (sigma A B) f))
  (isSection_conjugating_isSection A B f)

lemma piMap_obj_obj (s: piObj B x) : ((piMap A B f).obj s).obj =
    (conjugating A (sigma A B) f).obj s.obj := rfl

lemma piMap_map (s1 s2: piObj B x) (η: s1 ⟶ s2) :
    (piMap A B f).map η = (conjugating A (sigma A B) f).map η :=
  rfl

/--
The square commutes

   piObj B x   ⥤   (A x ⥤ sigma A B x)
     ⋮                     ||
piMap⋮                     || conjugating A (sigma A B) f
     VV                     VV
   piObj B y   ⥤   (A y ⥤ sigma A B y)
-/
lemma piMap_ι : piMap A B f ⋙ Section.ι (fstAuxObj B y)
    = Section.ι (fstAuxObj B x) ⋙ conjugating A (sigma A B) f :=
  rfl

@[simp] lemma piMap_id (x : Γ) : piMap A B (𝟙 x) = 𝟭 (piObj B x) := by
  simp only [piMap, conjugating_id]
  rfl

lemma piMap_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    piMap A B (f ≫ g) = (piMap A B f) ⋙ (piMap A B g) := by
  simp only [piMap, conjugating_comp]
  rfl

/-- The formation rule for Π-types for the natural model `smallU`
  as operations between functors -/
@[simps] def pi : Γ ⥤ Grpd.{u₁,u₁} where
  obj x := piObj B x
  map := piMap A B
  map_id := piMap_id A B
  map_comp := piMap_comp A B

end

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (B : ∫(A) ⥤ Grpd.{u₁,u₁})
  {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)

theorem IsSection_eq (x) : sigma.fstAuxObj B (σ.obj x) ≍ sigma.fstAuxObj (pre A σ ⋙ B) x := by
  dsimp [sigma.fstAuxObj]
  rw [sigma_naturality_aux]

lemma piObj_naturality (x):
  piObj B (σ.obj x) = piObj (pre A σ ⋙ B) x := by
  dsimp [pi, piObj, sigma.fstAuxObj]
  rw [sigma_naturality_aux]

section

variable (x y : Δ)

lemma eqToHom_ι_aux :
    Grpd.of ((A.obj (σ.obj x)) ⥤ ∫(ι A (σ.obj x) ⋙ B))
    = Grpd.of (A.obj (σ.obj x) ⥤ ∫(ι (σ ⋙ A) x ⋙ pre A σ ⋙ B)) :=
  by rw [sigma_naturality_aux]

lemma ObjectProperty.eqToHom_comp_ι {C D : Grpd} (h : C = D) (P : ObjectProperty C)
    (Q : ObjectProperty D) (hP : P ≍ Q) :
    let h' : Grpd.of P.FullSubcategory = Grpd.of Q.FullSubcategory := by
      subst h hP; rfl
    eqToHom h' ⋙ (ObjectProperty.ι Q) = (ObjectProperty.ι P) ⋙ eqToHom h := by
  subst h hP; rfl

lemma eqToHom_ι' (x) :
    ObjectProperty.ι (IsSection (sigma.fstAuxObj (pre A σ ⋙ B) x)) ≍
    ObjectProperty.ι (IsSection (sigma.fstAuxObj B (σ.obj x))) := by
  dsimp [sigma.fstAuxObj]
  rw [sigma_naturality_aux]

lemma eqToHom_ι (x) :
    eqToHom (piObj_naturality A B σ x) ≫
    Grpd.homOf (ObjectProperty.ι (IsSection (sigma.fstAuxObj (pre A σ ⋙ B) x))) =
    Grpd.homOf (ObjectProperty.ι (IsSection (sigma.fstAuxObj B (σ.obj x)))) ≫
    eqToHom (eqToHom_ι_aux A B σ x) := by
  rw [← heq_eq_eq, eqToHom_comp_heq_iff, heq_comp_eqToHom_iff]
  apply eqToHom_ι'

end

section
variable  {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (P Q : ObjectProperty D)
  (F : C ⥤ D) (hF : ∀ X, P (F.obj X))

theorem FullSubcategory.lift_comp_inclusion_eq :
    P.lift F hF ⋙ P.ι = F :=
  rfl

end

lemma conjugating_naturality_sigma {x y} (f : x ⟶ y):
    conjugating (σ ⋙ A) (sigma (σ ⋙ A) (pre A σ ⋙ B)) f ≍
    conjugating A (sigma A B) (σ.map f) := by
  rw! [← sigma_naturality]
  rw [conjugating_naturality_map]

lemma eqToHom_conjugating {x y} (f : x ⟶ y):
    eqToHom (eqToHom_ι_aux A B σ x) ≫ conjugating (σ ⋙ A) (sigma (σ ⋙ A) (pre A σ ⋙ B)) f =
    conjugating A (sigma A B) (σ.map f) ≫ eqToHom (eqToHom_ι_aux A B σ y) := by
  rw [← heq_eq_eq, eqToHom_comp_heq_iff, heq_comp_eqToHom_iff]
  exact conjugating_naturality_sigma A B σ f

lemma comm_sq_of_comp_mono {C : Type*} [Category C]
    {X Y Z W X' Y' Z' W' : C}
    (f : X ⟶ Y) (h : X ⟶ W) (g : Y ⟶ Z) (i : W ⟶ Z)
    (f' : X' ⟶ Y') (h' : X' ⟶ W') (g' : Y' ⟶ Z') (i' : W' ⟶ Z')
    (mX : X ⟶ X') (mY : Y ⟶ Y') (mW : W ⟶ W') (mZ : Z ⟶ Z')
    (hbot : f' ≫ g' = h' ≫ i')
    (hf : f ≫ mY = mX ≫ f')
    (hh : h ≫ mW = mX ≫ h')
    (hg : g ≫ mZ = mY ≫ g')
    (hi : i ≫ mZ = mW ≫ i')
    [e : Mono mZ]
    : f ≫ g = h ≫ i := by
  apply e.right_cancellation
  calc (f ≫ g) ≫ mZ
    _ = f ≫ mY ≫ g' := by aesop
    _ = (f ≫ mY) ≫ g' := by simp
    _  = (h ≫ mW) ≫ i' := by aesop
    _  = h ≫ mW ≫ i' := by simp
    _  = (h ≫ i) ≫ mZ := by aesop

theorem pi_naturality_map {x y} (f : x ⟶ y) :
    Grpd.homOf (piMap A B (σ.map f)) ≫ eqToHom (piObj_naturality A B σ y)
    = eqToHom (piObj_naturality A B σ x) ≫ (Grpd.homOf (piMap (σ ⋙ A) (pre A σ ⋙ B) f)) := by
  apply comm_sq_of_comp_mono (e := Grpd.ι_mono (Grpd.of (_ ⥤ _))
      (IsSection (sigma.fstAuxObj (pre A σ ⋙ B) y)))
    (Grpd.homOf (piMap A B (σ.map f)))
    (eqToHom (piObj_naturality A B σ x))
    (eqToHom (piObj_naturality A B σ y)) (Grpd.homOf (piMap (σ ⋙ A) (pre A σ ⋙ B) f))
    (Grpd.homOf (conjugating A (sigma A B) (σ.map f)))
    (eqToHom (eqToHom_ι_aux A B σ x)) (eqToHom (eqToHom_ι_aux A B σ y))
    (Grpd.homOf (conjugating (σ ⋙ A) (sigma (σ ⋙ A) (pre A σ ⋙ B)) f))
    (Grpd.homOf (ObjectProperty.ι _))
    (Grpd.homOf (ObjectProperty.ι _))
    (Grpd.homOf (ObjectProperty.ι _))
    (Grpd.homOf (ObjectProperty.ι _))
  · rw [eqToHom_conjugating]
  · apply FunctorOperation.FullSubcategory.lift_comp_inclusion_eq
  · apply eqToHom_ι
  · apply eqToHom_ι
  · apply FunctorOperation.FullSubcategory.lift_comp_inclusion_eq

theorem pi_naturality : σ ⋙ pi A B = pi (σ ⋙ A) (pre A σ ⋙ B) := by
  fapply CategoryTheory.Functor.ext
  · apply piObj_naturality
  · intro x y f
    erw [← Category.assoc, ← pi_naturality_map]
    simp [- Grpd.comp_eq_comp, - Grpd.id_eq_id]

end

namespace pi

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] {A : Γ ⥤ Grpd.{u₁,u₁}} (B : ∫(A) ⥤ Grpd.{u₁,u₁})
  (s : Γ ⥤ PGrpd.{u₁,u₁}) (hs : s ⋙ PGrpd.forgetToGrpd = pi A B)
  {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)

def strongTrans.naturality {x y : Γ} (g : x ⟶ y) :
    A.map g ⋙ (PGrpd.objFiber' hs y).obj ≅ (PGrpd.objFiber' hs x).obj ⋙ sigmaMap B g :=
  let fib : A.map (CategoryTheory.inv g) ⋙ (PGrpd.objFiber' hs x).obj ⋙ (sigma A B).map g ⟶
      (PGrpd.objFiber' hs y).obj := PGrpd.mapFiber' hs g
  ((conjugatingObjNatTransEquiv₁ _ _ _ _ _).toFun fib).symm

lemma eqToHom_heq_eqToHom {C : Type*} [Category C] (x y x' y' : C) (hx : x = x')
    (h : x = y) (h' : x' = y') : eqToHom h ≍ eqToHom h' := by aesop

lemma eqToHom_heq_id {C : Type*} [Category C] (x y z : C) (h : x = y)
    (hz : z = x) : eqToHom h ≍ 𝟙 z := by cat_disch

@[reassoc]
lemma _root_.CategoryTheory.Functor.leftUnitor_hom_comp_rightUnitor_inv
    {C : Type u₁} [Category.{v₁, u₁} C] {D : Type u₂}
    [Category.{v₂, u₂} D] (F : C ⥤ D) : F.leftUnitor.hom ≫ F.rightUnitor.inv = 𝟙 _ := by
  aesop_cat

theorem _root_.CategoryTheory.PGrpd.mapFiber'_comp'
    {A : Γ ⥤ Grpd.{v₁,u₁}} {α : Γ ⥤ PGrpd.{v₁,u₁}} (h : α ⋙ PGrpd.forgetToGrpd = A)
    {x y z} (f : x ⟶ y)
    (g : y ⟶ z) : PGrpd.mapFiber' h (f ≫ g)
    = eqToHom (by simp) ≫ (A.map g).map (PGrpd.mapFiber' h f) ≫ PGrpd.mapFiber' h g := by
  subst h
  simp [PGrpd.mapFiber]

@[simp]
lemma strongTrans.naturality_id_hom {x : Γ} :
    (strongTrans.naturality B s hs (𝟙 x)).hom = eqToHom (by simp) := by
  dsimp [strongTrans.naturality]
  erw [conjugatingObjNatTransEquiv₁_id_inv]
  simp only [sigma_obj, sigma_map, PGrpd.mapFiber'_id, pi_obj, pi_map, eqToHom_comp_iff,
    eqToHom_trans, IsIso.inv_comp_eq]
  simp only [← heq_eq_eq, heq_comp_eqToHom_iff]
  apply eqToHom_heq_eqToHom
  · simp
  · simp

-- lemma Grpd.inv_heq_inv {C C' : Grpd} (hC : C ≍ C') {X Y : C} {X' Y' : C'}
--     (hX : X ≍ X') (hY : Y ≍ Y') {f : X ⟶ Y} {f' : X' ⟶ Y'} (hf : f ≍ f') [IsIso f] :
--     have : IsIso f' := by aesop
--     inv f ≍ inv f' := by
--   subst hC hX hY hf
--   rfl

lemma inv_heq_inv {C : Type*} [Category C] {X Y : C} {X' Y' : C}
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'} (hf : f ≍ f') [IsIso f] :
    have : IsIso f' := by aesop
    inv f ≍ inv f' := by
  subst hX hY hf
  rfl

@[reassoc]
lemma strongTrans.naturality_comp_hom_aux {x y} (g : x ⟶ y) :
    A.map g ≫ ((piMap A B g).obj (PGrpd.objFiber' hs x)).obj =
    (PGrpd.objFiber' hs x).obj ⋙ sigmaMap B g := by
  simp [piMap, conjugating, ← Grpd.comp_eq_comp]

-- lemma strongTrans.naturality_comp_hom' {x y z : Γ} (g1 : x ⟶ y) (g2 : y ⟶ z) :
--     (strongTrans.naturality B s hs (g1 ≫ g2)).hom =
--     eqToHom (by simp) ≫
--     CategoryTheory.inv
--         ((A.map g1 ⋙ A.map g2).whiskerLeft ((piMap A B g2).map (PGrpd.mapFiber' hs g1) ≫
--         PGrpd.mapFiber' hs g2)) ≫
--       eqToHom (by
--         simp only [← Grpd.comp_eq_comp, ← Functor.map_comp, pi_obj, pi_map, ObjectProperty.ι_obj]
--         simp only [← Functor.comp_obj, ← piMap_comp]
--         apply strongTrans.naturality_comp_hom_aux) := by
--   simp only [naturality, sigma_obj, sigma_map, Equiv.toFun_as_coe, Iso.symm_hom,
--     ObjectProperty.ι_obj, pi_obj, pi_map, PGrpd.mapFiber'_comp']
--   erw [conjugatingObjNatTransEquiv₁_comp_inv]
--   simp only [← heq_eq_eq, heq_eqToHom_comp_iff, eqToHom_comp_heq_iff,
--     comp_eqToHom_heq_iff]
--   simp only [← Category.assoc, heq_comp_eqToHom_iff]
--   simp only [← Functor.inv_whiskerLeft]
--   congr! 2
--   · rw [← Functor.comp_obj, ← piMap_comp]
--     simp only [piMap_obj_obj]
--     rfl
--   · rw [← Functor.comp_obj, ← piMap_comp]
--     simp only [piMap_obj_obj]
--     rfl
--   · simp only [Category.assoc]
--     apply HEq.trans (eqToHom_comp_heq ..)
--     rfl

set_option maxHeartbeats 400000
lemma strongTrans.naturality_comp_hom {x y z : Γ} (g1 : x ⟶ y) (g2 : y ⟶ z) :
    (strongTrans.naturality B s hs (g1 ≫ g2)).hom =
    eqToHom (by simp [Functor.assoc]) ≫
    Functor.whiskerLeft (A.map g1) (strongTrans.naturality B s hs g2).hom ≫
    Functor.whiskerRight (strongTrans.naturality B s hs g1).hom (sigmaMap B g2)
    ≫ eqToHom (by simp [Functor.assoc, sigmaMap_comp]) := by
  simp only [naturality, sigma_obj, sigma_map, Equiv.toFun_as_coe, Iso.symm_hom]
  refine conjugatingObjNatTransEquiv₁_comp_inv A (sigma A B) g1 g2
    (PGrpd.objFiber' hs x).obj (PGrpd.objFiber' hs y).obj (PGrpd.objFiber' hs z).obj
    (PGrpd.mapFiber' hs g1) (PGrpd.mapFiber' hs g2)
    (PGrpd.mapFiber' hs (g1 ≫ g2)) ?_
  simp [PGrpd.mapFiber'_comp', piMap, conjugating]
  rfl

  -- rw [strongTrans.naturality_comp_hom']
  -- simp only [sigma_obj, sigma_map, conjugatingObjNatTransEquiv₁, Groupoid.isoEquivHom,
  --   Groupoid.inv_eq_inv, Equiv.trans_apply, Equiv.coe_fn_symm_mk]
  -- simp only [← Functor.inv_whiskerLeft, ← CategoryTheory.Functor.inv_whiskerRight,
  --   ← IsIso.inv_comp_assoc]
  -- simp only [← heq_eq_eq, heq_eqToHom_comp_iff, eqToHom_comp_heq_iff,
  --   comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  -- congr! 2
  -- · simp [← Grpd.comp_eq_comp, sigmaMap_comp, Functor.assoc]
  --   simp
  -- · have h := conjugatingObjNatTransEquiv'_comp A (sigma A B) g1 g2
  --     (PGrpd.objFiber' hs x).obj (PGrpd.objFiber' hs z).obj (PGrpd.mapFiber' hs (g1 ≫ g2))
  --   simp [conjugatingObjNatTransEquiv', Grpd.Functor.iso, ← heq_eq_eq] at h

set_option maxHeartbeats 400000
@[simps]
def strongTrans : (A ⋙ Grpd.forgetToCat).toPseudoFunctor'.StrongTrans
  (sigma A B ⋙ Grpd.forgetToCat).toPseudoFunctor' where
    app x := (PGrpd.objFiber' hs x.as).obj
    naturality {x y} g := strongTrans.naturality B s hs g.as
    naturality_naturality := by
      intro x y f g η
      have : f = g := LocallyDiscrete.eq_of_hom η
      subst this
      simp [Functor.toPseudoFunctor', pseudofunctorOfIsLocallyDiscrete]
    naturality_id := by
      intro x
      simp only [Functor.toPseudoFunctor'_obj, Functor.comp_obj, sigma_obj,
        Functor.toPseudoFunctor'_map, LocallyDiscrete.id_as, Functor.comp_map, sigma_map,
        strongTrans.naturality_id_hom, Functor.toPseudoFunctor'_mapId, eqToIso.hom,
        Bicategory.whiskerLeft_eqToHom, eqToHom_trans, Bicategory.eqToHom_whiskerRight,
        Bicategory.leftUnitor, Bicategory.rightUnitor,
        Functor.leftUnitor_hom_comp_rightUnitor_inv (PGrpd.objFiber' hs x.as).obj,
        Functor.simpIdComp, ← heq_eq_eq, heq_eqToHom_comp_iff]
      apply eqToHom_heq_id
      simp [Grpd.forgetToCat, Cat.comp_eq_comp]
    naturality_comp := by
      intro x y z g1 g2
      simp only [Functor.toPseudoFunctor'_obj, Functor.comp_obj, sigma_obj,
        Functor.toPseudoFunctor'_map, LocallyDiscrete.comp_as, Functor.comp_map, sigma_map,
        Bicategory.whiskerLeft, Functor.toPseudoFunctor'_mapComp, eqToIso.hom,
        Bicategory.whiskerRight, Bicategory.associator, Functor.associator_eq, Iso.refl_hom,
        Iso.refl_inv]
      rw [Functor.whiskerLeft_eqToHom, Functor.eqToHom_whiskerRight,
        strongTrans.naturality_comp_hom]
      simp only [← Grpd.comp_eq_comp, Category.assoc]
      erw [Category.id_comp, Category.id_comp, Category.comp_id]
      simp only [Grpd.forgetToCat, id_eq, Cat.of_α, eqToHom_trans, eqToHom_refl, Category.comp_id]

def mapStrongTrans : ∫ A ⥤ ∫ sigma A B :=
  Functor.Grothendieck.toPseudoFunctor'Iso.hom _ ⋙
  Pseudofunctor.Grothendieck.map (strongTrans B s hs) ⋙
  Functor.Grothendieck.toPseudoFunctor'Iso.inv _

@[simp]
lemma mapStrongTrans_obj_base (x) : ((mapStrongTrans B s hs).obj x).base = x.base :=
  rfl

@[simp]
lemma mapStrongTrans_obj_fiber (x) : ((mapStrongTrans B s hs).obj x).fiber =
    (PGrpd.objFiber' hs x.base).obj.obj x.fiber :=
  rfl

@[simp]
lemma mapStrongTrans_map_base {x y} (f : x ⟶ y) : ((mapStrongTrans B s hs).map f).base =
    f.base :=
  rfl

@[simp]
lemma mapStrongTrans_map_fiber {x y} (f : x ⟶ y) : ((mapStrongTrans B s hs).map f).fiber =
    eqToHom (by
      simp only [mapStrongTrans_obj_base, sigma_obj, mapStrongTrans_map_base, sigma_map,
        mapStrongTrans_obj_fiber, pi_obj, pi_map, piMap, ObjectProperty.ι_obj,
        ObjectProperty.lift_obj_obj, Functor.comp_obj, conjugating_obj, Functor.map_inv]
      simp [← Functor.comp_obj, ← Grpd.comp_eq_comp]) ≫
    (PGrpd.mapFiber' hs f.base).app ((A.map f.base).obj x.fiber) ≫
    (PGrpd.objFiber' hs y.base).obj.map f.fiber := by
  simp only [mapStrongTrans, Functor.Grothendieck.toPseudoFunctor'Iso.inv, Functor.comp_obj,
    Pseudofunctor.Grothendieck.map_obj_base, Functor.Grothendieck.toPseudoFunctor'Iso.hom_obj_base,
    Pseudofunctor.Grothendieck.map_obj_fiber, Functor.toPseudoFunctor'_obj, sigma_obj,
    strongTrans_app, Functor.Grothendieck.toPseudoFunctor'Iso.hom_obj_fiber, Functor.comp_map,
    Pseudofunctor.Grothendieck.map_map_base, Functor.Grothendieck.toPseudoFunctor'Iso.hom_map_base,
    Pseudofunctor.Grothendieck.map_map_fiber, Functor.toPseudoFunctor'_map, Quiver.Hom.toLoc_as,
    sigma_map, strongTrans_naturality, strongTrans.naturality, conjugatingObjNatTransEquiv₁,
    Grpd.Functor.iso, Grpd.functorIsoOfIso_inv, Functor.mapIso_inv, asIso_inv,
    Grpd.functorIsoOfIso_hom, Functor.mapIso_hom, asIso_hom, conjugatingObjNatTransEquiv',
    Groupoid.isoEquivHom, Equiv.toFun_as_coe, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk, Iso.symm_mk, NatTrans.comp_app, Cat.comp_obj, Functor.whiskerLeft_app,
    Functor.Grothendieck.toPseudoFunctor'Iso.hom_map_fiber, Hom.fiber,
    Functor.Grothendieck.Hom.mk_fiber, eqToHom_app, Category.assoc]
  rfl

/--  Let `Γ` be a category.
For any pair of functors `A : Γ ⥤ Grpd` and `B : ∫(A) ⥤ Grpd`,
and any "term of pi", meaning a functor `f : Γ ⥤ PGrpd`
satisfying `f ⋙ forgetToGrpd = pi A B : Γ ⥤ Grpd`,
there is a "term of `B`" `inversion : Γ ⥤ PGrpd` such that `inversion ⋙ forgetToGrpd = B`.
-/
@[simps!]
def inversion : ∫(A) ⥤ PGrpd := mapStrongTrans B s hs ⋙ (sigma.assoc B).inv ⋙ toPGrpd B

@[simp]
lemma assocHom_app_base_base
    {Γ : Type u₂} [Groupoid Γ] {A : Γ ⥤ Grpd} (B : ∫ A ⥤ Grpd)
    {x y : Γ} (f : x ⟶ y) (a) :
    ((sigma.assocHom B f).app a).base.base = f := by
  simp [sigma.assocHom, sigma.assocIso, ιNatIso_hom]

lemma assocHom_app_base_fiber
    {Γ : Type u₂} [Groupoid Γ] {A : Γ ⥤ Grpd} (B : ∫ A ⥤ Grpd)
    {x y : Γ} (f : x ⟶ y) (a) :
    ((sigma.assocHom B f).app a).base.fiber = eqToHom (by
      simp only [sigma.assocFib.eq_1, Functor.comp_obj, assocHom_app_base_base]
      rw! (castMode := .all) [pre_obj_base B (ι A y) ((sigmaMap B f).obj a)]
      rw! (castMode := .all) [pre_obj_base B (ι A x) a]
      simp) := by
  simp only [sigma.assocFib.eq_1, Functor.comp_obj, sigma.assocHom,
    sigma.assocIso, eqToHom_refl]
  rw! (castMode := .all) [preNatIso_hom_app_base, ιNatIso_hom]
  simp
  rfl

lemma _root_.GroupoidModel.FunctorOperation.sigma.assoc_inv_obj_base_base'
    {Γ : Type u₂} [Groupoid Γ] {A : Γ ⥤ Grpd} (B : ∫ A ⥤ Grpd)
    (x : ∫ sigma A B) :
    ((sigma.assoc B).inv.obj x).base.base = x.base := by
  simp only [sigma.assoc, Functor.Iso.symm_inv, functorIsoFrom_hom_obj, sigma_obj,
    sigma.assocFib.eq_1]
  rw! (castMode := .all) [pre_obj_base]
  simp
  rfl

lemma _root_.GroupoidModel.FunctorOperation.sigma.assoc_inv_obj_base_fiber'
    {Γ : Type u₂} [Groupoid Γ] {A : Γ ⥤ Grpd} (B : ∫ A ⥤ Grpd)
    (x : ∫ sigma A B) :
    ((sigma.assoc B).inv.obj x).base.fiber = x.fiber.base := by
  simp only [sigma.assoc, Functor.Iso.symm_inv, functorIsoFrom_hom_obj, sigma_obj,
    sigma.assocFib.eq_1]
  rw! (castMode := .all) [pre_obj_base]
  simp
  rfl

lemma _root_.GroupoidModel.FunctorOperation.sigma.assoc_inv_map_base_base'
    {Γ : Type u₂} [Groupoid Γ] {A : Γ ⥤ Grpd} (B : ∫ A ⥤ Grpd)
    {X Y : ∫ sigma A B} (f : X ⟶ Y) :
    ((sigma.assoc B).inv.map f).base.base = f.base := by
  simp only [sigma.assoc, Functor.Iso.symm_inv, functorIsoFrom_hom_obj, sigma_obj,
    sigma.assocFib.eq_1, functorIsoFrom_hom_map, sigma_map, comp_base, pre_map_base,
    assocHom_app_base_base, ι_map_base, ι_obj_base]
  erw [Category.comp_id]
  simp [Hom.base]

-- TODO replace simps! with this
lemma _root_.GroupoidModel.FunctorOperation.sigma.assoc_inv_map_base_fiber'
    {Γ : Type u₂} [Groupoid Γ] {A : Γ ⥤ Grpd} (B : ∫ A ⥤ Grpd)
    {X Y : ∫ sigma A B} (f : X ⟶ Y) :
    ((sigma.assoc B).inv.map f).base.fiber = eqToHom (by
      simp
      rw! [sigma.assoc_inv_map_base_base', sigma.assoc_inv_obj_base_fiber']) ≫
      f.fiber.base := by
  simp only [sigma.assoc, Functor.Iso.symm_inv, functorIsoFrom_hom_obj, sigma_obj,
    sigma.assocFib.eq_1, functorIsoFrom_hom_map, sigma_map, comp_base, comp_fiber,
    sigmaMap_obj_base]
  rw! [pre_map_base, ι_map_fiber]
  simp only [ι_map_base, ι_obj_base, ι_obj_fiber]
  erw [Grpd.map_id_map, assocHom_app_base_fiber]
  simp only [sigma.assocFib.eq_1, Functor.comp_obj, eqToHom_refl, Category.id_comp, eqToHom_trans]
  erw [Category.id_comp]
  simp
  rfl

lemma mapStrongTrans_comp_fstAux' : mapStrongTrans B s hs ⋙ sigma.fstAux' B = 𝟭 _ := by
  apply Functor.Groupoidal.FunctorTo.hext
  · rw [Functor.assoc, sigma.fstAux', Functor.assoc, sigma.assoc_inv_comp_forget_comp_forget,
      mapStrongTrans, Functor.assoc,
      Functor.assoc, Functor.Groupoidal.forget,
      Functor.Grothendieck.toPseudoFunctor'Iso.inv_comp_forget,
      Pseudofunctor.Grothendieck.map_comp_forget, Functor.id_comp,
      Functor.Grothendieck.toPseudoFunctor'Iso.hom_comp_forget,
      Functor.Groupoidal.forget]
  · intro x
    simp only [sigma.fstAux', Functor.comp_obj, Functor.Groupoidal.forget_obj,
      Functor.id_obj, heq_eq_eq]
    apply (sigma.assoc_inv_obj_base_fiber' B ((mapStrongTrans B s hs).obj x)).trans
    simp only [mapStrongTrans_obj_fiber]
    exact Functor.congr_obj (PGrpd.objFiber' hs x.base).property x.fiber
  · intro x y f
    simp [sigma.fstAux']
    rw [sigma.assoc_inv_map_base_fiber']
    have h := Functor.congr_hom (PGrpd.objFiber' hs y.base).property f.fiber
    dsimp [IsSection, sigma.fstAuxObj] at h
    simp [h]
    simp [← Category.assoc]
    -- rw! [PGrpd.mapFiber'_heq]
    -- rw [← comp_base]
    -- erw [mapStrongTrans_map_fiber_base]
    -- apply heq_of_eq_of_heq (sigma.assoc_inv_map_base_fiber ..)
    -- simp [Grpd.forgetToCat]
    -- have h := pre_map_base B (ι A y.base) ((mapStrongTrans B s hs).map f).fiber
    -- erw [h]
    -- erw [sigma.assoc_inv_map_base_fiber]
    -- #check pre_map_base
    -- #check mapStrongTrans_map_fiber_base
    sorry

lemma inversion_comp_forgetToGrpd : inversion B s hs ⋙ PGrpd.forgetToGrpd = B := by
  simp only [inversion, Functor.assoc, toPGrpd_forgetToGrpd]
  conv => left; right; rw [← Functor.assoc, ← sigma.fstAux']
  simp [← Functor.assoc, mapStrongTrans_comp_fstAux']

-- JH: make some API for this? Mixture of Pseudofunctor.Grothendieck
-- and Functor.Grothendieck and Functor.Groupoidal is messy.
lemma ι_comp_inversion {x} : ι A x ⋙ inversion B s hs =
    (PGrpd.objFiber' hs x).obj ⋙ toPGrpd (ι A x ⋙ B) := by
  apply PGrpd.Functor.hext
  · simp only [Functor.assoc, inversion_comp_forgetToGrpd, toPGrpd_forgetToGrpd]
    rw [← Functor.assoc, (PGrpd.objFiber' hs x).property, Functor.id_comp]
  · intro a
    rfl -- This is probably bad practice
  · intro a b h
    simp
    have h := sigma.assoc_inv_map_fiber B ((mapStrongTrans B s hs).map ((ι A x).map h))
    rw [← heq_eq_eq, heq_eqToHom_comp_iff] at h
    apply h.trans
    simp
    sorry

end

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (β : ∫(A) ⥤ PGrpd.{u₁,u₁})

section
variable (x : Γ)

def lamObjFiberObj : Grpd.of (A.obj x ⥤ sigmaObj (β ⋙ PGrpd.forgetToGrpd) x) :=
  sec (ι A x ⋙ β ⋙ PGrpd.forgetToGrpd) (ι A x ⋙ β) rfl

@[simp] lemma lamObjFiberObj_obj_base (a) : ((lamObjFiberObj A β x).obj a).base = a := by
  simp [lamObjFiberObj]

@[simp] lemma lamObjFiberObj_obj_fiber (a) : ((lamObjFiberObj A β x).obj a).fiber
    = PGrpd.objFiber (ι A x ⋙ β) a := by
  simp [lamObjFiberObj]

@[simp] lemma lamObjFiberObj_map_base {a a'} (h: a ⟶ a'):
    ((lamObjFiberObj A β x).map h).base = h := by
  simp [lamObjFiberObj]

@[simp] lemma lamObjFiberObj_map_fiber {a a'} (h: a ⟶ a'):
    ((lamObjFiberObj A β x).map h).fiber = PGrpd.mapFiber (ι A x ⋙ β) h := by
  simp [lamObjFiberObj]

def lamObjFiber : piObj (β ⋙ PGrpd.forgetToGrpd) x :=
  ⟨lamObjFiberObj A β x , rfl⟩

@[simp] lemma lamObjFiber_obj : (lamObjFiber A β x).obj = lamObjFiberObj A β x :=
  rfl

@[simp] lemma lamObjFiber_obj_obj : (lamObjFiber A β x).obj = lamObjFiberObj A β x :=
  rfl

end

section
variable {x y : Γ} (f : x ⟶ y)

open CategoryTheory.Functor

def lamObjFiberObjCompSigMap.app (a : A.obj x) :
    (lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f).obj a ⟶
    (A.map f ⋙ lamObjFiberObj A β y).obj a :=
  homMk (𝟙 _) (eqToHom (by simp; rfl) ≫ (β.map ((ιNatTrans f).app a)).fiber)

@[simp] lemma lamObjFiberObjCompSigMap.app_base (a : A.obj x) : (app A β f a).base = 𝟙 _ := by
  simp [app]

lemma lamObjFiberObjCompSigMap.app_fiber_eq (a : A.obj x) : (app A β f a).fiber =
    eqToHom (by simp; rfl) ≫ (β.map ((ιNatTrans f).app a)).fiber := by
  simp [app]

lemma lamObjFiberObjCompSigMap.app_fiber_heq (a : A.obj x) : (app A β f a).fiber ≍
    (β.map ((ιNatTrans f).app a)).fiber := by
  simp [app]

lemma lamObjFiberObjCompSigMap.naturality {x y : Γ} (f : x ⟶ y) {a1 a2 : A.obj x} (h : a1 ⟶ a2) :
    (lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f).map h
    ≫ lamObjFiberObjCompSigMap.app A β f a2 =
    lamObjFiberObjCompSigMap.app A β f a1
    ≫ (A.map f ⋙ lamObjFiberObj A β y).map h := by
  apply Hom.hext
  · simp [sigmaObj]
  · have β_ιNatTrans_naturality : β.map ((ι A x).map h) ≫ β.map ((ιNatTrans f).app a2)
        = β.map ((ιNatTrans f).app a1) ≫ β.map ((A.map f ⋙ ι A y).map h) := by
      simp [← Functor.map_comp, (ιNatTrans f).naturality h]
    have h_naturality : (β.map ((ιNatTrans f).app a2)).base.map (β.map ((ι A x).map h)).fiber
        ≫ (β.map ((ιNatTrans f).app a2)).fiber ≍
        (β.map ((ι A y).map ((A.map f).map h))).base.map (β.map ((ιNatTrans f).app a1)).fiber
        ≫ (β.map ((ι A y).map ((A.map f).map h))).fiber := by
      simpa [← heq_eq_eq] using Grothendieck.Hom.congr β_ιNatTrans_naturality
    simp only [Grpd.forgetToCat.eq_1, sigmaObj, Grpd.coe_of, comp_obj, sigmaMap_obj_base,
      Functor.comp_map, comp_base, sigmaMap_map_base, sigmaMap_obj_fiber, comp_fiber,
      sigmaMap_map_fiber, lamObjFiberObj_map_fiber, map_comp, eqToHom_map, app_fiber_eq, Cat.of_α,
      id_eq, Category.assoc, eqToHom_trans_assoc, heq_eqToHom_comp_iff, eqToHom_comp_heq_iff]
    rw [← Category.assoc]
    apply HEq.trans _ h_naturality
    apply heq_comp _ rfl rfl _ HEq.rfl
    · aesop_cat
    · simp only [← Functor.comp_map, ← Grpd.comp_eq_comp, comp_eqToHom_heq_iff]
      congr 3
      aesop_cat

@[simp] lemma lamObjFiberObjCompSigMap.app_id (a) : lamObjFiberObjCompSigMap.app A β (𝟙 x) a
    = eqToHom (by simp) := by
  apply Hom.hext
  · rw [base_eqToHom]
    simp
  · simp [app]
    rw! (castMode := .all) [ιNatTrans_id_app, fiber_eqToHom]
    simp [Grothendieck.Hom.congr (eqToHom_map β _), Functor.Grothendieck.fiber_eqToHom,
      eqToHom_trans]
    apply (eqToHom_heq_id_cod _ _ _).trans (eqToHom_heq_id_cod _ _ _).symm

lemma lamObjFiberObjCompSigMap.app_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) (a) :
    app A β (f ≫ g) a
    = eqToHom (by simp)
    ≫ (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g).map (app A β f a)
    ≫ app A β g ((A.map f).obj a) ≫ eqToHom (by simp) := by
  fapply Hom.hext
  · simp only [Grpd.forgetToCat.eq_1, sigmaObj, Grpd.coe_of, comp_obj, sigmaMap_obj_base, app_base,
    comp_base, base_eqToHom, sigmaMap_map_base, map_id, lamObjFiberObj_obj_base, map_comp,
    Grpd.comp_eq_comp, eqToHom_naturality, Category.comp_id, eqToHom_trans, eqToHom_refl]
  · have : (β.map ((ιNatTrans (f ≫ g)).app a)) = β.map ((ιNatTrans f).app a)
      ≫ β.map ((ιNatTrans g).app ((A.map f).obj a))
      ≫ eqToHom (by simp) := by
      simp [ιNatTrans_comp_app]
    simp only [Grpd.forgetToCat.eq_1, sigmaObj, Grpd.coe_of, comp_obj, sigmaMap_obj_base, app,
      Functor.comp_map, PGrpd.forgetToGrpd_map, sigmaMap_obj_fiber, Cat.of_α, id_eq, homMk_base,
      homMk_fiber, Grothendieck.Hom.congr this, Grothendieck.Hom.comp_base, Grpd.comp_eq_comp,
      Grothendieck.Hom.comp_fiber, eqToHom_refl, Functor.Grothendieck.fiber_eqToHom,
      Category.id_comp, eqToHom_trans_assoc, comp_base, sigmaMap_map_base, comp_fiber,
      fiber_eqToHom, eqToHom_map, sigmaMap_map_fiber, map_comp, Category.assoc,
      heq_eqToHom_comp_iff, eqToHom_comp_heq_iff]
    have : ((ιNatTrans g).app ((A.map f).obj a)) = homMk g (𝟙 _) := by
      apply Hom.ext _ _ (by simp) (by aesop_cat)
    rw! (castMode := .all) [Category.id_comp, base_eqToHom, eqToHom_map, eqToHom_map,
      Functor.Grothendieck.base_eqToHom, ιNatTrans_app_base, this]
    aesop_cat

def lamObjFiberObjCompSigMap :
    lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f ⟶
    A.map f ⋙ lamObjFiberObj A β y where
  app := lamObjFiberObjCompSigMap.app A β f
  naturality _ _ h := lamObjFiberObjCompSigMap.naturality A β f h

@[simp] lemma lamObjFiberObjCompSigMap_id (x : Γ) : lamObjFiberObjCompSigMap A β (𝟙 x) =
    eqToHom (by simp [sigmaMap_id]) := by
  ext a
  simp [lamObjFiberObjCompSigMap]

/-
lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) (f ≫ g)

_ ⟶ lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) g
:= eqToHom ⋯

_ ⟶ A.map f ⋙ lamObjFiberObj A β y ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) g
:= whiskerRight (lamObjFiberObjCompSigMap A β f) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)

_ ⟶ A.map f ⋙ A.map g ⋙ lamObjFiberObj A β z
:= whiskerLeft (A.map f) (lamObjFiberObjCompSigMap A β g)

_ ⟶ A.map (f ≫ g) ⋙ lamObjFiberObj A β z
:= eqToHom ⋯

-/
lemma lamObjFiberObjCompSigMap_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) :
    lamObjFiberObjCompSigMap A β (f ≫ g) =
    eqToHom (by rw [sigmaMap_comp]; rfl)
    ≫ whiskerRight (lamObjFiberObjCompSigMap A β f) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)
    ≫ whiskerLeft (A.map f) (lamObjFiberObjCompSigMap A β g)
    ≫ eqToHom (by rw [Functor.map_comp, Grpd.comp_eq_comp, Functor.assoc]) := by
  ext a
  simp [lamObjFiberObjCompSigMap, lamObjFiberObjCompSigMap.app_comp]

def whiskerLeftInvLamObjObjSigMap :
    A.map (CategoryTheory.inv f) ⋙ lamObjFiberObj A β x ⋙ sigmaMap (β ⋙ PGrpd.forgetToGrpd) f ⟶
    lamObjFiberObj A β y :=
  whiskerLeft (A.map (CategoryTheory.inv f)) (lamObjFiberObjCompSigMap A β f)
  ≫ eqToHom (by simp [← Grpd.comp_eq_comp])

@[simp] lemma whiskerLeftInvLamObjObjSigMap_id (x : Γ) :
    whiskerLeftInvLamObjObjSigMap A β (𝟙 x) = eqToHom (by simp [sigmaMap_id]) := by
  simp [whiskerLeftInvLamObjObjSigMap]

attribute [local simp] Functor.assoc in
lemma whiskerLeftInvLamObjObjSimgaMap_comp_aux {A A' B B' C C' : Type*}
    [Category A] [Category A'] [Category B] [Category B'] [Category C] [Category C']
    (F : Functor.Iso A B) (G : Functor.Iso B C) (lamA : A ⥤ A') (lamB : B ⥤ B') (lamC : C ⥤ C')
    (F' : A' ⥤ B') (G' : B' ⥤ C')
    (lamF : lamA ⋙ F' ⟶ F.hom ⋙ lamB) (lamG : lamB ⋙ G' ⟶ G.hom ⋙ lamC)
    (H1 : A ⥤ C') (e1 : H1 = _) (H2 : A ⥤ C') (e2 : F.hom ⋙ G.hom ⋙ lamC = H2) :
    whiskerLeft (G.inv ⋙ F.inv)
      (eqToHom e1 ≫ whiskerRight lamF G' ≫ whiskerLeft F.hom lamG ≫ eqToHom e2) =
    eqToHom (by aesop) ≫
      whiskerRight (whiskerLeft G.inv (whiskerLeft F.inv lamF ≫ eqToHom (by simp))) G' ≫
      whiskerLeft G.inv lamG ≫
      eqToHom (by aesop) :=
  calc _
    _ = eqToHom (by aesop) ≫
      (G.inv ⋙ F.inv).whiskerLeft (whiskerRight lamF G') ≫
      (G.inv ⋙ F.inv ⋙ F.hom).whiskerLeft lamG ≫
      eqToHom (by aesop) := by aesop
    _ = (eqToHom (by aesop)) ≫
      whiskerLeft (G.inv ⋙ F.inv) (whiskerRight lamF G') ≫
      eqToHom (by simp) ≫
      whiskerLeft G.inv lamG ≫
      eqToHom (by aesop) := by
        congr 2
        simp only [Functor.assoc, ← heq_eq_eq, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff,
          comp_eqToHom_heq_iff]
        rw! (castMode := .all) [F.inv_hom_id, Functor.comp_id]
        simp
    _ = eqToHom (by aesop) ≫
      whiskerRight (whiskerLeft G.inv (whiskerLeft F.inv lamF ≫ eqToHom (by simp))) G' ≫
      whiskerLeft G.inv lamG ≫
      eqToHom (by aesop) := by aesop_cat

lemma whiskerLeftInvLamObjObjSigMap_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    whiskerLeftInvLamObjObjSigMap A β (f ≫ g)
    = eqToHom (by simp [Functor.assoc, sigmaMap_comp])
    ≫ whiskerRight (whiskerLeft (A.map (CategoryTheory.inv g))
      (whiskerLeftInvLamObjObjSigMap A β f)) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)
    ≫ whiskerLeftInvLamObjObjSigMap A β g := by
  simp only [whiskerLeftInvLamObjObjSigMap, lamObjFiberObjCompSigMap_comp]
  have hAfg : A.map (CategoryTheory.inv (f ≫ g)) = (Grpd.Functor.iso A g).inv ≫
    (Grpd.Functor.iso A f).inv := by simp [Grpd.Functor.iso]
  rw! (castMode := .all) [hAfg]
  erw [whiskerLeftInvLamObjObjSimgaMap_comp_aux (Grpd.Functor.iso A f) (Grpd.Functor.iso A g)
    _ _ _ (sigmaMap (β ⋙ PGrpd.forgetToGrpd) f) (sigmaMap (β ⋙ PGrpd.forgetToGrpd) g)]
  simp only [Category.assoc, eqToHom_trans, Grpd.Functor.iso_hom, Grpd.Functor.iso_inv]

def lamMapFiber :
    ((pi A (β ⋙ PGrpd.forgetToGrpd)).map f).obj (lamObjFiber A β x) ⟶ lamObjFiber A β y :=
  whiskerLeftInvLamObjObjSigMap A β f

@[simp] lemma lamMapFiber_id (x : Γ) : lamMapFiber A β (𝟙 x) = eqToHom (by simp) := by
  simp [lamMapFiber]
  rfl

lemma lamMapFiber_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    lamMapFiber A β (f ≫ g)
    = eqToHom (by rw [← Functor.comp_obj]; apply Functor.congr_obj; simp [piMap_comp])
    ≫ ((piMap A (β ⋙ PGrpd.forgetToGrpd)) g).map ((lamMapFiber A β) f)
    ≫ lamMapFiber A β g := by
  simp [lamMapFiber, piMap, whiskerLeftInvLamObjObjSigMap_comp]
  rfl

def lam : Γ ⥤ PGrpd.{u₁,u₁} :=
  PGrpd.functorTo
  (pi A (β ⋙ PGrpd.forgetToGrpd))
  (lamObjFiber A β)
  (lamMapFiber A β)
  (lamMapFiber_id A β)
  (lamMapFiber_comp A β)

@[simp]
lemma lam_obj_base (x) : ((lam A β).obj x).base = piObj (β ⋙ PGrpd.forgetToGrpd) x := rfl

@[simp]
lemma lam_obj_fib (x) : ((lam A β).obj x).fiber = lamObjFiber A β x :=
  rfl

@[simp]
lemma lam_map_base {x y} (f : x ⟶ y) : ((lam A β).map f).base =
    piMap A (β ⋙ PGrpd.forgetToGrpd) f :=
  rfl

@[simp]
lemma lam_map_fib {x y} (f : x ⟶ y) : ((lam A β).map f).fiber = lamMapFiber A β f :=
  rfl

lemma lam_comp_forgetToGrpd : lam A β ⋙ PGrpd.forgetToGrpd = pi A (β ⋙ PGrpd.forgetToGrpd) :=
  rfl

variable {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)

lemma lam_naturality_aux (x) :
    ι A (σ.obj x) ⋙ β ⋙ PGrpd.forgetToGrpd = ι (σ ⋙ A) x ⋙ pre A σ ⋙ β ⋙ PGrpd.forgetToGrpd := by
  simp [← Functor.assoc, ← ι_comp_pre]

lemma lamObjFiberObj_naturality (x) :
    lamObjFiberObj A β (σ.obj x) ≍ lamObjFiberObj (σ ⋙ A) (pre A σ ⋙ β) x := by
  simp only [lamObjFiberObj, ← ι_comp_pre, comp_obj, Functor.assoc]
  congr!

lemma lam_naturality_obj_aux (x) :
    Grpd.of (A.obj (σ.obj x) ⥤ sigmaObj (β ⋙ PGrpd.forgetToGrpd) (σ.obj x)) ≍
    Grpd.of (A.obj (σ.obj x) ⥤ sigmaObj ((pre A σ ⋙ β) ⋙ PGrpd.forgetToGrpd) x) := by
  rw [sigmaObj_naturality, Functor.assoc]

theorem lam_naturality_obj (x : Δ) : HEq (lamObjFiber A β (σ.obj x))
    (lamObjFiber (σ ⋙ A) (pre A σ ⋙ β) x) := by
  simp only [lamObjFiber]
  apply Grpd.ObjectProperty.FullSubcategory.hext (lam_naturality_obj_aux A β σ x)
  · simp only [sigma.fstAuxObj, Functor.assoc]
    congr!
    any_goals simp [lam_naturality_aux]
  · apply lamObjFiberObj_naturality

lemma lamObjFiberObjCompSigMap.app_naturality {x y} (f : x ⟶ y) (a) :
    lamObjFiberObjCompSigMap.app A β (σ.map f) a ≍
    lamObjFiberObjCompSigMap.app (σ ⋙ A) (pre A σ ⋙ β) f a := by
  apply Hom.hext'
  any_goals apply Grpd.Functor.hcongr_obj
  any_goals apply Grpd.comp_hcongr
  any_goals simp only [comp_obj, Functor.comp_map, heq_eq_eq]
  any_goals apply sigmaObj_naturality
  any_goals apply lam_naturality_aux
  any_goals apply sigmaMap_naturality_heq
  any_goals apply lamObjFiberObj_naturality
  any_goals simp [app]; rfl

lemma lamObjFiberObjCompSigMap_naturality {x y} (f : x ⟶ y) :
    lamObjFiberObjCompSigMap A β (σ.map f) ≍
    lamObjFiberObjCompSigMap (σ ⋙ A) (pre A σ ⋙ β) f := by
  apply Grpd.NatTrans.hext
  any_goals apply Grpd.comp_hcongr
  any_goals simp only [comp_obj, Functor.comp_map, heq_eq_eq, eqToHom_refl]
  any_goals apply sigmaObj_naturality
  any_goals apply lamObjFiberObj_naturality
  · apply sigmaMap_naturality_heq
  · apply lamObjFiberObjCompSigMap.app_naturality

lemma whiskerLeftInvLamObjObjSigMap_naturality_heq {x y} (f : x ⟶ y) :
    whiskerLeftInvLamObjObjSigMap A β (σ.map f) ≍
    whiskerLeftInvLamObjObjSigMap (σ ⋙ A) (pre A σ ⋙ β) f := by
  simp only [whiskerLeftInvLamObjObjSigMap, Functor.comp_map]
  apply HEq.trans (comp_eqToHom_heq _ _)
  apply HEq.trans _ (comp_eqToHom_heq _ _).symm
  rw [Functor.map_inv, Functor.map_inv, Functor.map_inv]
  apply Grpd.whiskerLeft_hcongr_right
  any_goals apply Grpd.comp_hcongr
  any_goals simp only [comp_obj, heq_eq_eq]
  any_goals apply sigmaObj_naturality
  any_goals apply lamObjFiberObj_naturality
  · apply sigmaMap_naturality_heq
  · apply lamObjFiberObjCompSigMap_naturality

lemma lam_naturality_map {x y} (f : x ⟶ y) :
    lamMapFiber A β (σ.map f) ≍ lamMapFiber (σ ⋙ A) (pre A σ ⋙ β) f := by
  apply whiskerLeftInvLamObjObjSigMap_naturality_heq

theorem lam_naturality : σ ⋙ lam A β = lam (σ ⋙ A) (pre A σ ⋙ β) := by
  apply PGrpd.Functor.hext
  · apply pi_naturality
  · apply lam_naturality_obj
  · apply lam_naturality_map

lemma inversion_lam : inversion (β ⋙ PGrpd.forgetToGrpd) (lam A β)
    (lam_comp_forgetToGrpd ..) = β := by
  apply PGrpd.Functor.hext
  · simp [inversion_comp_forgetToGrpd]
  · intro x
    simp [inversion]
    sorry
  · intro x y f
    simp [inversion]
    sorry

end

section

variable (B : ∫ A ⥤ Grpd) (s : Γ ⥤ PGrpd) (hs : s ⋙ PGrpd.forgetToGrpd = pi A B)

lemma lamObjFiberObj_inversion_heq (x) :
    lamObjFiberObj A (pi.inversion B s hs) x ≍ (PGrpd.objFiber' hs x).obj := by
  dsimp only [lamObjFiberObj]
  rw! [pi.inversion_comp_forgetToGrpd B s hs]
  simp only [sec_eq_lift, Grpd.forgetToCat.eq_1, heq_eq_eq]
  symm
  apply Functor.IsPullback.lift_uniq
  · symm
    apply pi.ι_comp_inversion
  · exact (PGrpd.objFiber' hs x).property

lemma lamObjFiber_inversion_heq' (x) :
    lamObjFiber A (pi.inversion B s hs) x ≍ PGrpd.objFiber' hs x := by
  dsimp [pi_obj]
  apply piObj.hext
  · rfl
  · simp [pi.inversion_comp_forgetToGrpd]
  · apply lamObjFiberObj_inversion_heq

lemma lamObjFiber_inversion_heq (x) :
    lamObjFiber A (pi.inversion B s hs) x ≍ PGrpd.objFiber s x :=
  HEq.trans (lamObjFiber_inversion_heq' A B s hs x) (PGrpd.objFiber'_heq hs)

lemma lamMapFiber_inversion_heq {x y} (f : x ⟶ y) :
    lamMapFiber A (pi.inversion B s hs) f ≍ PGrpd.mapFiber s f :=
  sorry

lemma lam_inversion : lam A (inversion B s hs) = s := by
  apply PGrpd.Functor.hext -- TODO: rename to PGrpd.ToFunctor.hext
  · rw [lam_comp_forgetToGrpd, inversion_comp_forgetToGrpd, hs]
  · apply lamObjFiber_inversion_heq
  · apply lamMapFiber_inversion_heq

end

end

end pi

end FunctorOperation

section
variable {Γ : Ctx}

open FunctorOperation

namespace UPi

def Pi {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.{v}.Ty) : Γ ⟶ U.{v}.Ty :=
  USig.SigAux pi B

/-- Naturality for the formation rule for Π-types.
Also known as Beck-Chevalley. -/
lemma Pi_comp {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.{v}.Ty} {σA : Δ ⟶ U.Ty}
    (eq : σ ≫ A = σA) (B : U.ext A ⟶ U.{v}.Ty) :
    Pi (U.substWk σ A σA eq ≫ B) = σ ≫ Pi B :=
  USig.SigAux_comp pi (by intros; rw [pi_naturality]) σ eq B

def lam {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (b : U.ext A ⟶ U.{v}.Tm) : Γ ⟶ U.{v}.Tm :=
  USig.SigAux pi.lam b

lemma lam_comp {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.{v}.Ty} {σA : Δ ⟶ U.Ty}
    (eq : σ ≫ A = σA) (b : U.ext A ⟶ U.{v}.Tm) :
    lam (U.substWk σ A σA eq ≫ b) = σ ≫ lam b :=
  USig.SigAux_comp pi.lam (by intros; rw [pi.lam_naturality]) σ eq b

lemma lam_tp {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.Ty) (b : U.ext A ⟶ U.{v}.Tm)
    (b_tp : b ≫ U.tp = B) : UPi.lam b ≫ U.tp = Pi B := by
  subst b_tp
  dsimp [lam, Pi, U.tp]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_right]
  rfl

def unLam {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.Ty) (f : Γ ⟶ U.Tm)
    (f_tp : f ≫ U.tp = UPi.Pi B) : U.ext A ⟶ U.{v}.Tm :=
  toCoreAsSmallEquiv.symm <| pi.inversion (toCoreAsSmallEquiv B) (toCoreAsSmallEquiv f) (by
    simp [U.tp] at f_tp
    rw [← toCoreAsSmallEquiv_apply_comp_right, f_tp]
    simp [Pi])

lemma unLam_tp {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.Ty) (f : Γ ⟶ U.Tm)
    (f_tp : f ≫ U.tp = UPi.Pi B) : UPi.unLam B f f_tp ≫ U.tp = B := by
  dsimp [unLam, U.tp]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_right, toCoreAsSmallEquiv.symm_apply_eq,
    pi.inversion_comp_forgetToGrpd]
  rfl

lemma unLam_lam {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.Ty) (b : U.ext A ⟶ U.Tm)
    (b_tp : b ≫ U.tp = B) : UPi.unLam B (UPi.lam b) (lam_tp _ _ b_tp) = b := by
  subst b_tp
  simp only [unLam, lam, toCoreAsSmallEquiv.symm_apply_eq, U.tp, Grpd.comp_eq_comp,
    Equiv.apply_symm_apply]
  rw! [toCoreAsSmallEquiv_apply_comp_right]
  rw [pi.inversion_lam (toCoreAsSmallEquiv A) (toCoreAsSmallEquiv b)]
  rfl

lemma lam_unLam {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (B : U.ext A ⟶ U.Ty) (f : Γ ⟶ U.Tm)
    (f_tp : f ≫ U.tp = UPi.Pi B) : UPi.lam (UPi.unLam B f f_tp) = f := by
  simp [lam, unLam, toCoreAsSmallEquiv.symm_apply_eq]
  erw [toCoreAsSmallEquiv.apply_symm_apply]
  rw [pi.lam_inversion]

end UPi

def UPi : Model.UnstructuredUniverse.PolymorphicPi U.{v} U.{v} U.{v} where
  Pi := UPi.Pi
  Pi_comp := UPi.Pi_comp
  lam _ b _ := UPi.lam b
  lam_comp _ _ _ _ _ _ _ := UPi.lam_comp ..
  lam_tp := UPi.lam_tp
  unLam := UPi.unLam
  unLam_tp := UPi.unLam_tp
  unLam_lam := UPi.unLam_lam
  lam_unLam := UPi.lam_unLam

end

end GroupoidModel
