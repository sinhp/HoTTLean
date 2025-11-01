import HoTTLean.Groupoids.Sigma
import HoTTLean.ForMathlib.CategoryTheory.Whiskering
import HoTTLean.ForMathlib.CategoryTheory.NatTrans
import HoTTLean.ForMathlib.CategoryTheory.MorphismProperty.WideSubcategory

universe v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

namespace CategoryTheory

lemma Pseudofunctor.StrongTrans.ext {C D : Type*} [Bicategory C] [Bicategory D]
    {F G : Pseudofunctor C D} (α α' : F ⟶ G) (happ : ∀ x, α.app x = α'.app x)
    (hnaturality : ∀ {x y} (f : x ⟶ y), (α.naturality f).hom ≫ eqToHom (by rw [happ]) =
      eqToHom (by rw [happ]) ≫ (α'.naturality f).hom) :
      α = α' := by
  rcases α with ⟨app, naturality⟩
  rcases α' with ⟨app', naturality'⟩
  congr!
  · ext
    apply happ
  · apply fun_hext
    · rfl
    · apply fun_hext
      · rfl
      · rfl
      · aesop
    · aesop

section
variable {A B : Type*} [Category A] [Category B] (F : B ⥤ A)

def IsSection : ObjectProperty (A ⥤ B) := fun s => s ⋙ F = Functor.id A

def IsOverId : MorphismProperty ((IsSection F).FullSubcategory) :=
  fun s t α => Functor.whiskerRight α F = eqToHom s.property ≫ 𝟙 (𝟭 A) ≫ eqToHom t.property.symm

instance : (IsOverId F).IsMultiplicative where
  id_mem := by
    intro s
    simp only [IsOverId, Category.id_comp, eqToHom_trans, eqToHom_refl]
    erw [Functor.whiskerRight_id]
    rfl
  comp_mem := by
    intro s0 s1 s2 α β hα hβ
    simp only [IsOverId]
    erw [Functor.whiskerRight_comp, hα, hβ]
    simp

abbrev Section := (IsOverId F).WideSubcategory

abbrev Section.ι : Section F ⥤ (A ⥤ B) :=
  MorphismProperty.wideSubcategoryInclusion _ ⋙ ObjectProperty.ι (IsSection F)

end

instance {A B : Type*} [Category A] [Groupoid B] (F : B ⥤ A) :
    IsGroupoid ((IsSection F).FullSubcategory) :=
  InducedCategory.isGroupoid (A ⥤ B) (ObjectProperty.ι _).obj

instance {A B : Type*} [Category A] [Groupoid B] (F : B ⥤ A) :
    IsGroupoid (Section F) where
  all_isIso {x y} f := {
    out := ⟨⟨ CategoryTheory.inv f.1,
      by
        simp only [IsOverId, Category.id_comp, eqToHom_trans, Set.mem_setOf_eq]
        erw [← Functor.inv_whiskerRight]
        rw! [f.2]
        simp⟩,
      by apply MorphismProperty.WideSubcategory.hom_ext; simp,
      by apply MorphismProperty.WideSubcategory.hom_ext; simp⟩
  }

instance Section.groupoid {A B : Type*} [Category A] [Groupoid B] (F : B ⥤ A) :
    Groupoid (Section F) :=
  Groupoid.ofIsGroupoid

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

local instance {G : Type*} [Groupoid G] (P : ObjectProperty G) :
    Groupoid (P.FullSubcategory) :=
  InducedCategory.groupoid G (ObjectProperty.ι _).obj

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

lemma Grpd.MorphismProperty.WideSubcategory.hext {A A' : Grpd.{v,u}} (hA : A ≍ A')
    (P : MorphismProperty A) (P' : MorphismProperty A') (hP : P ≍ P')
    [P.IsMultiplicative] [P'.IsMultiplicative]
    (p : P.WideSubcategory) (p' : P'.WideSubcategory)
    (hp : p.obj ≍ p'.obj) : p ≍ p' := by
  cases p; cases p'
  subst hA hP hp
  rfl

end CategoryTheory

namespace GroupoidModel

open CategoryTheory Opposite Functor.Groupoidal

end GroupoidModel

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

def conjugating {x y : Γ} (f : x ⟶ y) : (A.obj x ⥤ B.obj x) ⥤
    (A.obj y ⥤ B.obj y) :=
  conjugating' A B f

lemma conjugating_obj {x y : Γ} (f : x ⟶ y) (s : A.obj x ⥤ B.obj x) :
    (conjugating A B f).obj s = A.map (inv f) ⋙ s ⋙ B.map f := by
  rfl

lemma conjugating_map {x y : Γ} (f : x ⟶ y) {s1 s2 : A.obj x ⥤ B.obj x} (h : s1 ⟶ s2) :
    (conjugating A B f).map h =
    whiskerRight (whiskerLeft (A.map (inv f)) h) (B.map f) := by
  rfl

@[simp] lemma conjugating_id (x : Γ) : conjugating A B (𝟙 x) = 𝟭 _ := by
  simp [conjugating]

@[simp] lemma conjugating_comp (x y z : Γ) (f : x ⟶ y) (g : y ⟶ z) :
    conjugating A B (f ≫ g) = conjugating A B f ⋙ conjugating A B g := by
  simp [conjugating]

@[simp] lemma conjugating_comp_map {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)
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
  simp only [Grpd.Functor.iso, Grpd.functorIsoOfIso_hom, mapIso_hom, asIso_hom,
    Grpd.functorIsoOfIso_inv, mapIso_inv, asIso_inv, conjugatingObjNatTransEquiv', eqToHom_refl,
    Category.id_comp, Equiv.coe_fn_mk, whiskerLeft_comp, whiskerLeft_eqToHom, eqToHom_trans_assoc,
    whiskerRight_comp, eqToHom_whiskerRight, whiskerLeft_twice, associator_eq,
    CategoryTheory.Iso.refl_inv, CategoryTheory.Iso.refl_hom, Category.comp_id, Category.assoc] at *
  erw [Category.id_comp]
  rw [whiskerLeft_map_comp, whiskerLeft_map_comp]
  simp only [← Category.assoc, eqToHom_trans]
  congr 2
  rw [Functor.comp_whiskerLeft, Functor.whiskerRight_whiskerLeft, Functor.whiskerRight_whiskerLeft,
    whiskerLeft_twice' (A.map f2)]
  simp only [← Grpd.comp_eq_comp]
  rw! (castMode := .all) [← Functor.map_comp A f2, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Grpd.id_eq_id]
  simp only [Functor.id_whiskerLeft, Grpd.comp_eq_comp, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id, ← heq_eq_eq, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff,
    eqToHom_comp_heq_iff]
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

end

namespace Section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] {A : Γ ⥤ Grpd.{u₁,u₁}}
  {B : Γ ⥤ Grpd.{u₁,u₁}} (φ : B ⟶ A)

def functorObj (x : Γ) : Grpd.{u₁,u₁} := Grpd.of (Section (φ.app x))

def obj_hext {A A' : Grpd.{u₁,u₁}} (hA : A ≍ A') {B B' : Grpd.{u₁,u₁}} (hB : B ≍ B')
    {F : A ⟶ B} {F' : A' ⟶ B'} (hF : F ≍ F') (x : Section F) (x' : Section F')
    (hx : x.obj.obj ≍ x'.obj.obj) : x ≍ x' := by
  aesop

def hom_hext {A A' : Grpd.{u₁,u₁}} (hA : A ≍ A') {B B' : Grpd.{u₁,u₁}} (hB : B ≍ B')
    {F : A ⟶ B} {F' : A' ⟶ B'} (hF : F ≍ F') {x y : Section F} {x' y' : Section F'}
    {f : x ⟶ y} {f' : x' ⟶ y'} (hx : x ≍ x')
    (hy : y ≍ y') (hf : f.1 ≍ f'.1) :
    f ≍ f' := by
  subst hA hB hF hx hy
  simp at *
  apply MorphismProperty.WideSubcategory.hom_ext
  apply hf

def hom_hext' {A A' : Grpd.{u₁,u₁}} (hA : A ≍ A') {B B' : Grpd.{u₁,u₁}} (hB : B ≍ B')
    {F : A ⟶ B} {F' : A' ⟶ B'} (hF : F ≍ F') {x y : Section F} {x' y' : Section F'}
    {f : x ⟶ y} {f' : x' ⟶ y'} (hx : x ≍ x')
    (hy : y ≍ y') (hf : ∀ k k', k ≍ k' → f.1.app k ≍ f'.1.app k') :
    f ≍ f' := by
  subst hA hB hF hx hy
  simp at *
  apply MorphismProperty.WideSubcategory.hom_ext
  apply NatTrans.ext
  ext
  apply hf

section

variable {x y : Γ} (f : x ⟶ y)

/-- The functorial action of `pi` on a morphism `f : x ⟶ y` in `Γ`
is given by "conjugation".
Since `piObj B x` is a subcategory of `sigma A B x ⥤ A x`,
we obtain the action `piMap : piObj B x ⥤ piObj B y`
as the induced map in the following diagram

```
           Section.ι
   piObj B x   ⥤   (A x ⥤ B x)
     ⋮                     ||
     ⋮                     || conjugating A B f
     VV                     VV
   piObj B y   ⥤   (A y ⥤ B y)
```
-/
def functorMap : functorObj φ x ⥤ functorObj φ y :=
  MorphismProperty.lift _
  (ObjectProperty.lift (IsSection (φ.app y))
  ((Section.ι _ ⋙ conjugating A B f))
  (by
    intro s
    have := s.obj.property
    simp only [IsSection, ← Grpd.comp_eq_comp, ← Grpd.id_eq_id, Functor.comp_obj,
      MorphismProperty.wideSubcategoryInclusion.obj, ObjectProperty.ι_obj, conjugating_obj,
      Functor.map_inv, Category.assoc, NatTrans.naturality] at *
    slice_lhs 2 3 => rw [this]
    simp [- Grpd.comp_eq_comp, - Grpd.id_eq_id]))
  (by
    intro s t α
    have := α.property
    simp only [IsOverId, ← Grpd.comp_eq_comp, Category.id_comp, eqToHom_trans, Set.mem_setOf_eq,
      ObjectProperty.lift_obj_obj, Functor.comp_obj, MorphismProperty.wideSubcategoryInclusion.obj,
      ObjectProperty.ι_obj, ObjectProperty.lift_map, Functor.comp_map,
      MorphismProperty.wideSubcategoryInclusion.map, ObjectProperty.ι_map, conjugating_map,
      Functor.whiskerRight_twice, Functor.associator_eq, Iso.refl_hom, Iso.refl_inv] at *
    rw [Functor.whiskerRight_whiskerLeft]
    conv => left; left; rw! (castMode := .all) [φ.naturality, Grpd.comp_eq_comp]
    erw [Functor.comp_whiskerRight, this, Category.comp_id]
    simp only [Grpd.comp_eq_comp, Functor.eqToHom_whiskerRight, Functor.whiskerLeft_eqToHom,
      ← heq_eq_eq, eqRec_heq_iff_heq]
    congr! 1
    · simp only [← Grpd.comp_eq_comp, ← φ.naturality]
      rfl
    · simp only [← Grpd.comp_eq_comp, ← φ.naturality]
      rfl)

def functor : Γ ⥤ Grpd.{u₁,u₁} where
  obj := functorObj φ
  map := functorMap φ
  map_id _ := by simp only [functorMap, conjugating_id]; rfl
  map_comp _ _ := by simp only [functorMap, conjugating_comp]; rfl

lemma functor_comp {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ) :
    functor (A := σ ⋙ A) (B := σ ⋙ B) (Functor.whiskerLeft σ φ) =
    σ ⋙ functor φ := by
  fapply CategoryTheory.Functor.ext
  · intro x
    simp [functor, functorObj]
  · intro x y f
    simp [functor, functorMap]

@[simp]
lemma functor_map_map {s t} (α : s ⟶ t) : (((functor φ).map f).map α).1 =
    Functor.whiskerRight (Functor.whiskerLeft (A.map (inv f)) α.1) (B.map f) := by
  simp [functor, functorMap, conjugating, MorphismProperty.lift]

end

section

variable (app : (x : Γ) → A.obj x ⥤ B.obj x)
  (naturality : {x y : Γ} → (f : x ⟶ y) → A.map f ⋙ app y ≅ app x ⋙ B.map f)
  (naturality_id : (x : Γ) → (naturality (𝟙 x)).hom = eqToHom (by simp))
  (naturality_comp : {x y z : Γ} → (f : x ⟶ y) → (g : y ⟶ z) →
    (naturality (f ≫ g)).hom = eqToHom (by simp [Functor.assoc]) ≫
    Functor.whiskerLeft (A.map f) (naturality g).hom ≫
    eqToHom (Functor.assoc ..) ≫
    Functor.whiskerRight (naturality f).hom (B.map g)
    ≫ eqToHom (by simp [Functor.assoc]))

def strongTrans : (A ⋙ Grpd.forgetToCat).toPseudoFunctor'.StrongTrans
    (B ⋙ Grpd.forgetToCat).toPseudoFunctor' where
  app x := app x.as
  naturality f := naturality f.as
  naturality_naturality := by
    intro x y f g η
    have := LocallyDiscrete.eq_of_hom η
    subst this
    simp only [Functor.toPseudoFunctor', Functor.comp_obj, Functor.comp_map, LocallyDiscrete.id_as,
      LocallyDiscrete.comp_as, pseudofunctorOfIsLocallyDiscrete, Bicategory.whiskerRight,
      eqToHom_refl, Bicategory.whiskerLeft]
    aesop
  naturality_id := by
    intro x
    simp only [Functor.toPseudoFunctor', Functor.comp_obj, Functor.comp_map, LocallyDiscrete.id_as,
      LocallyDiscrete.comp_as, pseudofunctorOfIsLocallyDiscrete, Bicategory.whiskerLeft,
      eqToIso.hom, Bicategory.whiskerRight, Bicategory.leftUnitor, Bicategory.rightUnitor]
    rw [Functor.eqToHom_whiskerRight, Functor.leftUnitor_hom_comp_rightUnitor_inv,
      Functor.whiskerLeft_eqToHom, naturality_id]
    simp
    conv => right; apply Category.comp_id
  naturality_comp := by
    intro x y z f g
    simp only [Grpd.forgetToCat, Functor.toPseudoFunctor', Functor.comp_obj, Functor.comp_map,
      id_eq, LocallyDiscrete.id_as, LocallyDiscrete.comp_as, pseudofunctorOfIsLocallyDiscrete,
      naturality_comp, eqToHom_refl, Category.id_comp, Bicategory.whiskerLeft, Cat.of_α,
      eqToIso.hom, Category.assoc, Bicategory.whiskerRight, Bicategory.associator,
      Functor.associator_eq, Iso.refl_hom, Iso.refl_inv]
    rw [Functor.eqToHom_whiskerRight, Functor.whiskerLeft_eqToHom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    simp

lemma strongTrans_comp_toStrongTrans'_self_aux (happ : ∀ x, app x ⋙ φ.app x = 𝟭 _)
    {x y} (f : x ⟶ y) (a : A.obj x) :
    (φ.app y).obj ((A.map f ⋙ app y).obj a) = (φ.app y).obj ((app x ⋙ B.map f).obj a) := by
  erw [Functor.congr_obj (φ.naturality f) ((app x).obj a),
    Functor.congr_obj (happ y)]
  simp only [Functor.id_obj, Grpd.comp_eq_comp, Functor.comp_obj]
  erw [Functor.congr_obj (happ x)]
  simp

open CategoryTheory.Pseudofunctor.StrongTrans in
lemma strongTrans_comp_toStrongTrans'_self (happ : ∀ x, app x ⋙ φ.app x = 𝟭 _)
    (hnaturality : ∀ {x y} (f : x ⟶ y) (a : A.obj x),
      (φ.app y).map ((naturality f).hom.app a) =
      eqToHom (strongTrans_comp_toStrongTrans'_self_aux φ app happ f a)) :
    (strongTrans app naturality naturality_id naturality_comp) ≫
    (Functor.whiskerRight φ Grpd.forgetToCat).toStrongTrans' = 𝟙 _ := by
  fapply Pseudofunctor.StrongTrans.ext
  · intro x
    simp only [Grpd.forgetToCat, Functor.toPseudoFunctor'_obj, Functor.comp_obj, strongTrans,
      comp_app, NatTrans.toStrongTrans'_app, Functor.whiskerRight_app, id_eq, categoryStruct_id_app]
    apply happ
  · intro x y f
    ext a
    simp only [Grpd.forgetToCat, Functor.toPseudoFunctor'_obj, Functor.comp_obj, Cat.of_α,
      Functor.toPseudoFunctor'_map, Functor.comp_map, id_eq, strongTrans, comp_app,
      NatTrans.toStrongTrans'_app, Functor.whiskerRight_app, Cat.comp_obj, categoryStruct_id_app,
      Cat.id_obj, categoryStruct_comp_naturality_hom, Bicategory.associator,
      NatTrans.toStrongTrans'_naturality, eqToIso.hom, Bicategory.whiskerLeft_eqToHom,
      Category.assoc, Cat.comp_app, Functor.associator_inv_app, Cat.whiskerRight_app,
      Functor.associator_hom_app, Cat.eqToHom_app, Category.id_comp, eqToHom_trans,
      categoryStruct_id_naturality_hom, Bicategory.rightUnitor, Bicategory.leftUnitor,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.comp_id, ← heq_eq_eq,
      comp_eqToHom_heq_iff]
    rw! [hnaturality]
    apply eqToHom_heq_eqToHom
    rfl

def mapStrongTrans : ∫ A ⥤ ∫ B :=
  (Functor.Grothendieck.toPseudoFunctor'Iso _).hom ⋙
  Pseudofunctor.Grothendieck.map (strongTrans app naturality naturality_id naturality_comp) ⋙
  (Functor.Grothendieck.toPseudoFunctor'Iso _).inv

@[simp]
lemma mapStrongTrans_obj_base (x) :
    ((mapStrongTrans app naturality naturality_id naturality_comp).obj x).base = x.base :=
  rfl

@[simp]
lemma mapStrongTrans_obj_fiber (x) :
    ((mapStrongTrans app naturality naturality_id naturality_comp).obj x).fiber =
    (app x.base).obj x.fiber :=
  rfl

@[simp]
lemma mapStrongTrans_map_base {x y} (f : x ⟶ y) :
    ((mapStrongTrans app naturality naturality_id naturality_comp).map f).base = f.base :=
  rfl

@[simp]
lemma mapStrongTrans_map_fiber {x y} (f : x ⟶ y) :
    ((mapStrongTrans app naturality naturality_id naturality_comp).map f).fiber =
    (naturality f.base).inv.app x.fiber ≫ (app y.base).map f.fiber :=
  rfl

lemma mapStrongTrans_comp_map_self (happ : ∀ x, app x ⋙ φ.app x = 𝟭 _)
    (hnaturality : ∀ {x y} (f : x ⟶ y) (a : A.obj x),
      (φ.app y).map ((naturality f).hom.app a) =
      eqToHom (strongTrans_comp_toStrongTrans'_self_aux φ app happ f a)) :
    mapStrongTrans app naturality naturality_id naturality_comp ⋙ map φ = 𝟭 _ := by
  dsimp only [mapStrongTrans, map]
  simp only [Functor.Grothendieck.map_eq_pseudofunctor_map, Functor.assoc]
  slice_lhs 3 4 => simp only [← Functor.assoc, Functor.Iso.inv_hom_id, Functor.id_comp]
  slice_lhs 2 3 => simp only [← Functor.assoc, ← Pseudofunctor.Grothendieck.map_comp_eq]
  rw [strongTrans_comp_toStrongTrans'_self φ app naturality naturality_id
    naturality_comp happ hnaturality, Pseudofunctor.Grothendieck.map_id_eq]
  simp

end

end Section

section
variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (B : ∫(A) ⥤ Grpd.{u₁,u₁})
/-- The formation rule for Π-types for the natural model `smallU`
as operations between functors.

The functorial action of `pi` on a morphism `f : x ⟶ y` in `Γ`
is given by "conjugation".
Since `piObj B x` is a subcategory of `sigma A B x ⥤ A x`,
we obtain the action `piMap : piObj B x ⥤ piObj B y`
as the induced map in the following diagram

```
           Section.ι
   piObj B x   ⥤   (A x ⥤ sigma A B x)
     ⋮                     ||
     ⋮                     || conjugating A (sigma A B) f
     VV                     VV
   piObj B y   ⥤   (A y ⥤ sigma A B y)
```
-/
@[simps!] def pi : Γ ⥤ Grpd.{u₁,u₁} := Section.functor (A := A)
  (B := sigma A B) (sigma.fstNatTrans B)

lemma pi.obj_hext {A A' : Γ ⥤ Grpd.{u₁,u₁}} (hA : A ≍ A') {B : ∫ A ⥤ Grpd.{u₁,u₁}}
    {B' : ∫ A' ⥤ Grpd.{u₁,u₁}} (hB : B ≍ B') (x : Γ)
    (f : (pi A B).obj x) (f' : (pi A' B').obj x) (hf : f.obj.obj ≍ f'.obj.obj) : f ≍ f' := by
  aesop

end

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (B : ∫(A) ⥤ Grpd.{u₁,u₁})
  {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)

lemma conjugating_comp_sigma {x y} (f : x ⟶ y):
    conjugating (σ ⋙ A) (sigma (σ ⋙ A) (pre A σ ⋙ B)) f ≍
    conjugating A (sigma A B) (σ.map f) := by
  rw! [← sigma_naturality]
  rw [conjugating_comp_map]

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

theorem pi_comp : pi (σ ⋙ A) (pre A σ ⋙ B) = σ ⋙ pi A B := by
  dsimp [pi]
  rw [← Section.functor_comp]
  congr 1
  · symm
    apply sigma_naturality
  · apply NatTrans.hext
    · symm
      apply sigma_naturality
    · rfl
    · intro x
      simp only [sigma_obj, Functor.comp_obj, sigma.fstNatTrans, Functor.whiskerLeft_app]
      congr 1
      rw [← Functor.assoc, ι_comp_pre]

end

namespace pi

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] {A : Γ ⥤ Grpd.{u₁,u₁}} (B : ∫(A) ⥤ Grpd.{u₁,u₁})
  (s : Γ ⥤ PGrpd.{u₁,u₁}) (hs : s ⋙ PGrpd.forgetToGrpd = pi A B)
  {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)

def strongTrans.app (x) : A.obj x ⟶ (sigma A B).obj x :=
  (PGrpd.objFiber' hs x).obj.obj

@[simp]
lemma strongTrans.app_obj_base (y) (a) :
    ((strongTrans.app B s hs y).obj a).base = a :=
  Functor.congr_obj (PGrpd.objFiber' hs y).obj.property a

-- NOTE: no simp lemma for ((strongTrans.app B s hs y).obj a).fiber

@[simp]
lemma strongTrans.app_map_base (y) {a a'} (f : a ⟶ a') :
    ((strongTrans.app B s hs y).map f).base = eqToHom (by simp) ≫
    f ≫ eqToHom (by simp) := by
  have := Functor.congr_hom (PGrpd.objFiber' hs y).obj.property f
  simp at this
  simp [strongTrans.app, this]

def strongTrans.twoCell {x y : Γ} (g : x ⟶ y) :
    A.map (CategoryTheory.inv g) ⋙ strongTrans.app B s hs x ⋙ sigmaMap B g ⟶
  strongTrans.app B s hs y := (PGrpd.mapFiber' hs g).1

lemma strongTrans.twoCell_app_base_aux {x y : Γ} (g : x ⟶ y) (a) :
    base ((A.map (CategoryTheory.inv g) ⋙ app B s hs x ⋙ sigmaMap B g).obj a) =
    base ((app B s hs y).obj a) := by
  simp only [Functor.map_inv, sigma_obj, Functor.comp_obj, sigmaMap_obj_base, app_obj_base]
  simp [← Functor.comp_obj, ← Grpd.comp_eq_comp]

@[simp]
lemma strongTrans.twoCell_app_base {x y : Γ} (g : x ⟶ y) (a) :
    ((strongTrans.twoCell B s hs g).app a).base = eqToHom (twoCell_app_base_aux ..) := by
  have := NatTrans.congr_app (PGrpd.mapFiber' hs g).2 a
  simp only [sigma_obj, sigma.fstNatTrans_app, pi_obj_α, Functor.comp_obj,
    Functor.Groupoidal.forget_obj, IsOverId, Set.mem_setOf_eq, Functor.whiskerRight_app, forget_map,
    Category.id_comp, eqToHom_trans, eqToHom_app] at this
  rw [twoCell, this]

@[simp]
lemma strongTrans.twoCell_id (x) :
    twoCell B s hs (𝟙 x) = eqToHom (by simp) := by
  simp [twoCell]
  rfl

set_option maxHeartbeats 400000 in
lemma strongTrans.pi_map_map {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    (((pi A B).map g).map (PGrpd.mapFiber' hs f)).1 =
    Functor.whiskerLeft (A.map (CategoryTheory.inv g))
    (Functor.whiskerRight (twoCell B s hs f) (sigmaMap B g)) :=
  Section.functor_map_map (A := A)
    (B := sigma A B) (sigma.fstNatTrans B) g (PGrpd.mapFiber' hs f)

set_option maxHeartbeats 300000 in
/--
```
A x <----- A y <----- A z
 |          |          |
 |   =>     |    =>    |
 |  conj f  |  conj g  |
 V          V          V
sigma x -> sigma x -> sigma z
```
-/
@[simp]
lemma strongTrans.twoCell_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    twoCell B s hs (f ≫ g) = eqToHom (by simp [← Grpd.comp_eq_comp, sigmaMap_comp]) ≫
    Functor.whiskerLeft (A.map (CategoryTheory.inv g))
      (Functor.whiskerRight (twoCell B s hs f) (sigmaMap B g)) ≫
    twoCell B s hs g := by
  conv => left; simp only [twoCell, sigma_obj, pi_obj_α, Set.mem_setOf_eq,
    PGrpd.mapFiber'_comp' hs f g, MorphismProperty.WideSubcategory.comp_def,
    MorphismProperty.WideSubcategory.coe_eqToHom, pi_map_map]
  rfl

def strongTrans.naturality {x y : Γ} (g : x ⟶ y) :
    A.map g ⋙ strongTrans.app B s hs y ≅ strongTrans.app B s hs x ⋙ sigmaMap B g :=
  ((conjugatingObjNatTransEquiv₁ _ _ _ _ _).toFun (twoCell B s hs g)).symm

lemma strongTrans.naturality_inv_app {x y} (f : x ⟶ y) (a) :
    (strongTrans.naturality B s hs f).inv.app a =
    eqToHom (by simp [← Functor.comp_obj]; simp [← Grpd.comp_eq_comp]) ≫
    (twoCell B s hs f).app ((A.map f).obj a) := by
  simp only [sigma_obj, Functor.comp_obj, naturality, sigma_map,
    conjugatingObjNatTransEquiv₁, Grpd.Functor.iso, Grpd.functorIsoOfIso_inv, Functor.mapIso_inv,
    asIso_inv, Grpd.functorIsoOfIso_hom, Functor.mapIso_hom, asIso_hom,
    conjugatingObjNatTransEquiv', Groupoid.isoEquivHom, Groupoid.inv_eq_inv, Equiv.toFun_as_coe,
    Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, IsIso.inv_comp,
    Functor.inv_whiskerLeft, inv_eqToHom, Iso.symm_mk, NatTrans.comp_app, eqToHom_app,
    Functor.whiskerLeft_app]

@[simp]
lemma strongTrans.naturality_inv_app_base {x y} (f : x ⟶ y) (a) :
    Hom.base ((strongTrans.naturality B s hs f).inv.app a) = eqToHom (by simp) := by
  rw [strongTrans.naturality_inv_app, comp_base, base_eqToHom]
  simp

@[simp]
lemma strongTrans.naturality_inv_app_fiber {x y} (f : x ⟶ y) (a) :
    ((strongTrans.naturality B s hs f).inv.app a).fiber =
    eqToHom (by simp only [← Functor.comp_obj, naturality_inv_app_base, twoCell_app_base,
      ← Grpd.comp_eq_comp]; rw! [← Functor.map_comp_assoc, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]) ≫
    Hom.fiber ((twoCell B s hs f).app ((A.map f).obj a)) := by
  rw! [strongTrans.naturality_inv_app, comp_fiber, fiber_eqToHom, eqToHom_map]
  simp

@[simp]
lemma strongTrans.naturality_id_hom (x : Γ) :
    (strongTrans.naturality B s hs (𝟙 x)).hom = eqToHom (by simp) := by
  dsimp [strongTrans.naturality]
  erw [conjugatingObjNatTransEquiv₁_id_inv]
  simp [sigma_obj, sigma_map, eqToHom_trans, twoCell_id]

lemma inv_heq_inv {C : Type*} [Category C] {X Y : C} {X' Y' : C}
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'} (hf : f ≍ f') [IsIso f] :
    have : IsIso f' := by aesop
    inv f ≍ inv f' := by
  subst hX hY hf
  rfl

lemma strongTrans.naturality_comp_hom {x y z : Γ} (g1 : x ⟶ y) (g2 : y ⟶ z) :
    (strongTrans.naturality B s hs (g1 ≫ g2)).hom =
    eqToHom (by simp [Functor.assoc]) ≫
    Functor.whiskerLeft (A.map g1) (strongTrans.naturality B s hs g2).hom ≫
    eqToHom (by simp [Functor.assoc]) ≫
    Functor.whiskerRight (strongTrans.naturality B s hs g1).hom (sigmaMap B g2) ≫
    eqToHom (by simp [Functor.assoc, sigmaMap_comp]) := by
  apply (conjugatingObjNatTransEquiv₁_comp_inv A (sigma A B) g1 g2
    (app B s hs x) (app B s hs y) (app B s hs z)
    (twoCell B s hs g1) (twoCell B s hs g2)
    (twoCell B s hs (g1 ≫ g2)) ?_).trans
  · simp [naturality]
  · apply (strongTrans.twoCell_comp ..).trans
    rw [Functor.whiskerRight_whiskerLeft]
    simp only [sigma, eqToHom_refl]
    erw [Category.id_comp]

lemma strongTrans.app_comp_fstNatTrans_app (x : Γ) :
    strongTrans.app B s hs x ⋙ (sigma.fstNatTrans B).app x = 𝟭 ↑(A.obj x) := by
  simpa [strongTrans.app] using (PGrpd.objFiber' hs x).obj.property

lemma strongTrans.app_map_naturality_hom_app {x y : Γ} (f : x ⟶ y) (a : (A.obj x)) :
    ((sigma.fstNatTrans B).app y).map (((strongTrans.naturality B s hs) f).hom.app a) =
    eqToHom (Section.strongTrans_comp_toStrongTrans'_self_aux (sigma.fstNatTrans B)
      (app B s hs) (app_comp_fstNatTrans_app B s hs) f a) := by
  simp only [sigma_obj, sigma.fstNatTrans, Functor.comp_obj, Functor.Groupoidal.forget_obj,
    sigmaMap_obj_base, naturality, sigma_map, conjugatingObjNatTransEquiv₁, Grpd.Functor.iso,
    Grpd.functorIsoOfIso_inv, Functor.mapIso_inv, asIso_inv, Grpd.functorIsoOfIso_hom,
    Functor.mapIso_hom, asIso_hom, conjugatingObjNatTransEquiv', Groupoid.isoEquivHom,
    Groupoid.inv_eq_inv, Equiv.toFun_as_coe, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk, IsIso.inv_comp, Functor.inv_whiskerLeft, inv_eqToHom, Iso.symm_mk,
    NatTrans.comp_app, Functor.whiskerLeft_app, NatIso.isIso_inv_app, eqToHom_app, forget_map]
  rw [Functor.Groupoidal.comp_base, Functor.Groupoidal.base_eqToHom,
    ← Functor.Groupoidal.inv_base]
  have h := NatTrans.congr_app ((PGrpd.mapFiber' hs f)).2 ((A.map f).obj a)
  simp only [Set.mem_setOf_eq, IsOverId, sigma.fstNatTrans] at h
  simp only [sigma_obj, pi_obj_α, Functor.comp_obj, Functor.Groupoidal.forget_obj,
    Functor.whiskerRight_app, forget_map, Category.id_comp, eqToHom_trans, eqToHom_app] at h
  simp [twoCell, h]

def mapStrongTrans : ∫ A ⥤ ∫ sigma A B :=
  Section.mapStrongTrans (strongTrans.app B s hs) (strongTrans.naturality B s hs)
  (strongTrans.naturality_id_hom B s hs) (strongTrans.naturality_comp_hom B s hs)

@[simp]
lemma mapStrongTrans_obj_base (x) : ((mapStrongTrans B s hs).obj x).base = x.base :=
  rfl

-- NOTE: `mapStrongTrans_obj_fiber_base` and `mapStrongTrans_obj_fiber_fiber` preferred over this
lemma mapStrongTrans_obj_fiber (x) : ((mapStrongTrans B s hs).obj x).fiber =
    (strongTrans.app B s hs x.base).obj x.fiber :=
  rfl

@[simp]
lemma mapStrongTrans_obj_fiber_base (x) : ((mapStrongTrans B s hs).obj x).fiber.base =
    x.fiber := by
  simp [mapStrongTrans]

@[simp]
lemma mapStrongTrans_obj_fiber_fiber (x) : ((mapStrongTrans B s hs).obj x).fiber.fiber =
    ((strongTrans.app B s hs x.base).obj x.fiber).fiber := by
  simp [mapStrongTrans]

@[simp]
lemma mapStrongTrans_map_base {x y} (f : x ⟶ y) : ((mapStrongTrans B s hs).map f).base =
    f.base :=
  rfl

lemma mapStrongTrans_map_fiber {x y} (f : x ⟶ y) : ((mapStrongTrans B s hs).map f).fiber =
    eqToHom (by simp [← Functor.comp_obj]; simp [← Grpd.comp_eq_comp, mapStrongTrans_obj_fiber]) ≫
    (strongTrans.twoCell B s hs f.base).app ((A.map f.base).obj x.fiber) ≫
    (strongTrans.app B s hs y.base).map f.fiber := by
  simp [mapStrongTrans, strongTrans.naturality_inv_app]

@[simp]
lemma mapStrongTrans_map_fiber_base {x y} (f : x ⟶ y) :
    ((mapStrongTrans B s hs).map f).fiber.base =
    eqToHom (by simp [mapStrongTrans_obj_fiber]) ≫
    f.fiber ≫ eqToHom (by simp [mapStrongTrans_obj_fiber]) := by
  rw [mapStrongTrans_map_fiber, comp_base, comp_base, base_eqToHom, strongTrans.twoCell_app_base]
  simp

/--  Let `Γ` be a category.
For any pair of functors `A : Γ ⥤ Grpd` and `B : ∫(A) ⥤ Grpd`,
and any "term of pi", meaning a functor `f : Γ ⥤ PGrpd`
satisfying `f ⋙ forgetToGrpd = pi A B : Γ ⥤ Grpd`,
there is a "term of `B`" `inversion : Γ ⥤ PGrpd` such that `inversion ⋙ forgetToGrpd = B`. -/
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

lemma mapStrongTrans_comp_map_fstNatTrans :
    mapStrongTrans B s hs ⋙ map (sigma.fstNatTrans B) = 𝟭 _ := by
  convert Section.mapStrongTrans_comp_map_self (sigma.fstNatTrans B)
    (strongTrans.app B s hs) (strongTrans.naturality B s hs)
    (strongTrans.naturality_id_hom B s hs) (strongTrans.naturality_comp_hom B s hs) _ _
  · apply strongTrans.app_comp_fstNatTrans_app
  · intro x y f a
    apply strongTrans.app_map_naturality_hom_app

@[simp]
lemma inversion_comp_forgetToGrpd : inversion B s hs ⋙ PGrpd.forgetToGrpd = B := by
  simp only [inversion, Functor.assoc, toPGrpd_forgetToGrpd]
  conv => left; right; rw [← Functor.assoc, ← sigma.map_fstNatTrans_eq]
  simp [← Functor.assoc, mapStrongTrans_comp_map_fstNatTrans]

-- NOTE: this is not as general as the `mapStrongTrans` simp lemmas
lemma mapStrongTrans_map_ι_map_fiber_fiber_heq {x : Γ} {a b : A.obj x} (h : a ⟶ b) :
    ((mapStrongTrans B s hs).map ((ι A x).map h)).fiber.fiber ≍
    ((strongTrans.app B s hs x).map h).fiber := by
  rw! [mapStrongTrans_map_fiber B s hs]
  apply (fiber_eqToHom_comp_heq ..).trans
  congr 1
  · simp
  · conv => left; right; rw [ι_map_fiber, Functor.map_comp, eqToHom_map]
    rw! (castMode := .all) [ι_obj_base]
    simp only [mapStrongTrans_obj_base, ι_obj_base, ι_map_base, sigma_obj, ι_obj_fiber,
      Functor.comp_obj, strongTrans.twoCell_id, eqToHom_app, eqToHom_trans_assoc]
    apply HEq.trans (eqToHom_comp_heq ..)
    rfl

lemma ι_comp_inversion {x} : ι A x ⋙ inversion B s hs =
    strongTrans.app B s hs x ⋙ toPGrpd (ι A x ⋙ B) := by
  apply PGrpd.Functor.hext
  · simp only [Functor.assoc, inversion_comp_forgetToGrpd]
    erw [toPGrpd_forgetToGrpd, ← Functor.assoc, strongTrans.app_comp_fstNatTrans_app,
      Functor.id_comp]
  · intro a
    simp only [Functor.comp_obj, inversion_obj_base, inversion_obj_fiber, ι_obj_base, sigma_obj,
      toPGrpd_obj_base, toPGrpd_obj_fiber, heq_eq_eq]
    rw! (castMode := .all) [mapStrongTrans_obj_fiber]
    simp
  · intro a b h
    simp only [Functor.comp_obj, inversion_obj_base, Functor.comp_map, inversion_map_base,
      inversion_obj_fiber, ι_obj_base, inversion_map_fiber, ι_map_base, sigma_obj, toPGrpd_obj_base,
      toPGrpd_map_base, toPGrpd_obj_fiber, toPGrpd_map_fiber, eqToHom_comp_heq_iff]
    apply mapStrongTrans_map_ι_map_fiber_fiber_heq

end

section

variable {Γ : Type u₂} [Groupoid.{v₂} Γ] (A : Γ ⥤ Grpd.{u₁,u₁}) (β : ∫(A) ⥤ PGrpd.{u₁,u₁})

section
variable (x : Γ)

def lamObjFiberObj : A.obj x ⥤ sigmaObj (β ⋙ PGrpd.forgetToGrpd) x :=
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

def lamObjFiber : Grpd.of ((pi _ (β ⋙ PGrpd.forgetToGrpd)).obj x) :=
  ⟨lamObjFiberObj A β x, rfl⟩

@[simp] lemma lamObjFiber_obj_obj : (lamObjFiber A β x).obj.obj = lamObjFiberObj A β x :=
  rfl

lemma lamObjFiber_hext {A' : Γ ⥤ Grpd.{u₁,u₁}} (hA : A ≍ A') {β' : ∫ A' ⥤ PGrpd.{u₁,u₁}}
    (hβ : β ≍ β') (x' : Γ) (hx : x ≍ x') :
    lamObjFiber A β x ≍ lamObjFiber A' β' x' := by
  aesop

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
  ⟨whiskerLeftInvLamObjObjSigMap A β f, by
    ext
    simp only [sigma_obj, sigma.fstNatTrans_app, pi_obj_α, comp_obj, Groupoidal.forget_obj,
      lamObjFiber_obj_obj, whiskerLeftInvLamObjObjSigMap, lamObjFiberObjCompSigMap,
      whiskerRight_comp, eqToHom_whiskerRight, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      forget_map, lamObjFiberObjCompSigMap.app_base, sigmaMap_obj_base, eqToHom_app, eqToHom_refl,
      Category.comp_id]
    erw [Category.id_comp]⟩

@[simp] lemma lamMapFiber_id (x : Γ) : lamMapFiber A β (𝟙 x) = eqToHom (by simp) := by
  apply MorphismProperty.WideSubcategory.hom_ext
  simp only [sigma_obj, sigma.fstNatTrans_app, pi_obj_α, Set.mem_setOf_eq, lamMapFiber,
    whiskerLeftInvLamObjObjSigMap_id, MorphismProperty.WideSubcategory.coe_eqToHom]
  rfl

lemma lamMapFiber_comp {x y z} (f : x ⟶ y) (g : y ⟶ z) :
    (lamMapFiber A β (f ≫ g))
    = eqToHom (by
        rw [← Functor.comp_obj]
        apply Functor.congr_obj
        rw [← Grpd.comp_eq_comp, Functor.map_comp])
    ≫ (((pi A (β ⋙ PGrpd.forgetToGrpd)).map g).map ((lamMapFiber A β) f))
    ≫ (lamMapFiber A β g) := by
  apply MorphismProperty.WideSubcategory.hom_ext
  simp only [sigma_obj, pi, Set.mem_setOf_eq, lamMapFiber, whiskerLeftInvLamObjObjSigMap_comp]
  rw [MorphismProperty.WideSubcategory.comp_def,
    MorphismProperty.WideSubcategory.comp_def,
    MorphismProperty.WideSubcategory.coe_eqToHom]
  simp
  rfl

def lam : Γ ⥤ PGrpd.{u₁,u₁} :=
  PGrpd.functorTo
  (pi A (β ⋙ PGrpd.forgetToGrpd))
  (lamObjFiber A β)
  (lamMapFiber A β)
  (lamMapFiber_id A β)
  (lamMapFiber_comp A β)

@[simp]
lemma lam_obj_base (x) : ((lam A β).obj x).base = (pi _ (β ⋙ PGrpd.forgetToGrpd)).obj x := rfl

@[simp]
lemma lam_obj_fib (x) : ((lam A β).obj x).fiber = lamObjFiber A β x :=
  rfl

@[simp]
lemma lam_map_base {x y} (f : x ⟶ y) : ((lam A β).map f).base =
    (pi A (β ⋙ PGrpd.forgetToGrpd)).map f :=
  rfl

@[simp]
lemma lam_map_fib {x y} (f : x ⟶ y) : ((lam A β).map f).fiber = lamMapFiber A β f :=
  rfl

lemma lam_comp_forgetToGrpd : lam A β ⋙ PGrpd.forgetToGrpd = pi A (β ⋙ PGrpd.forgetToGrpd) :=
  rfl

variable {Δ : Type u₃} [Groupoid.{v₃} Δ] (σ : Δ ⥤ Γ)

lemma lam_comp_aux (x) :
    ι A (σ.obj x) ⋙ β ⋙ PGrpd.forgetToGrpd = ι (σ ⋙ A) x ⋙ pre A σ ⋙ β ⋙ PGrpd.forgetToGrpd := by
  simp [← Functor.assoc, ← ι_comp_pre]

lemma lamObjFiberObj_naturality (x) :
    lamObjFiberObj A β (σ.obj x) ≍ lamObjFiberObj (σ ⋙ A) (pre A σ ⋙ β) x := by
  simp only [lamObjFiberObj, ← ι_comp_pre, comp_obj, Functor.assoc]
  congr!

lemma naturality_forget_heq_forget (x) :
    @Groupoidal.forget (A.obj (σ.obj x)) _ (ι A (σ.obj x) ⋙ β ⋙ PGrpd.forgetToGrpd) ≍
    @Groupoidal.forget (A.obj (σ.obj x)) _ (ι (σ ⋙ A) x ⋙ (pre A σ ⋙ β) ⋙ PGrpd.forgetToGrpd) := by
  congr 1 -- NOTE: this could maybe be avoided by making an hext lemma for Grothendieck.forget
  rw [← Functor.assoc, ← ι_comp_pre]
  simp [Functor.assoc]

theorem lamObjFiber_naturality (x : Δ) : lamObjFiber A β (σ.obj x) ≍
    lamObjFiber (σ ⋙ A) (pre A σ ⋙ β) x := by
  apply Section.obj_hext
  · simp [sigmaObj_naturality, Functor.assoc]
  · simp
  · simp only [sigma_obj, sigma.fstNatTrans_app, comp_obj]
    apply naturality_forget_heq_forget
  · simp only [sigma_obj, sigma.fstNatTrans_app, lamObjFiber_obj_obj, comp_obj]
    apply lamObjFiberObj_naturality

lemma lamObjFiberObjCompSigMap.app_naturality {x y} (f : x ⟶ y) (a) :
    lamObjFiberObjCompSigMap.app A β (σ.map f) a ≍
    lamObjFiberObjCompSigMap.app (σ ⋙ A) (pre A σ ⋙ β) f a := by
  apply Hom.hext'
  any_goals apply Grpd.Functor.hcongr_obj
  any_goals apply Grpd.comp_hcongr
  any_goals simp only [comp_obj, Functor.comp_map, heq_eq_eq]
  any_goals apply sigmaObj_naturality
  any_goals apply lam_comp_aux
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

lemma lam_comp_map {x y} (f : x ⟶ y) :
    lamMapFiber A β (σ.map f) ≍ lamMapFiber (σ ⋙ A) (pre A σ ⋙ β) f := by
  apply Section.hom_hext
  · simp [Functor.assoc, sigmaObj_naturality]
  · simp
  · simp [Functor.assoc]
    apply naturality_forget_heq_forget
  · simp only [sigma_obj, sigma.fstNatTrans_app, pi_obj_α, comp_obj, Functor.assoc]
    rw [Functor.congr_obj (Functor.congr_hom (pi_comp A (β ⋙ PGrpd.forgetToGrpd) σ) f)]
    simp only [pi_obj_α, comp_obj, Functor.comp_map, Grpd.comp_eq_comp, Grpd.eqToHom_obj,
      heq_cast_iff_heq, heq_eq_eq]
    congr 1
    simp only [← heq_eq_eq, heq_cast_iff_heq]
    apply lamObjFiber_naturality
  · apply lamObjFiber_naturality
  · apply whiskerLeftInvLamObjObjSigMap_naturality_heq

theorem lam_comp : σ ⋙ lam A β = lam (σ ⋙ A) (pre A σ ⋙ β) := by
  apply PGrpd.Functor.hext
  · simp [Functor.assoc, lam_comp_forgetToGrpd, pi_comp]
  · apply lamObjFiber_naturality
  · apply lam_comp_map

@[simp]
lemma strongTrans.app_lam_obj_base (x : Γ) (a) :
    ((strongTrans.app (β ⋙ PGrpd.forgetToGrpd) (lam A β)
    (lam_comp_forgetToGrpd ..) x).obj a).base = a := by
  simp

@[simp]
lemma strongTrans.app_lam_obj_fiber (x) : ((strongTrans.app (β ⋙ PGrpd.forgetToGrpd) (lam A β)
    (lam_comp_forgetToGrpd ..) x.base).obj x.fiber).fiber = (β.obj x).fiber :=
  rfl

@[simp]
lemma strongTrans.app_lam_map_base {x y : ∫ A} (f : x ⟶ y) :
    ((strongTrans.app (β ⋙ PGrpd.forgetToGrpd) (lam A β)
    (lam_comp_forgetToGrpd ..) y.base).map f.fiber).base =
    f.fiber :=
  rfl

@[simp]
lemma strongTrans.app_lam_map_fiber {x y : ∫ A} (f : x ⟶ y) :
    ((strongTrans.app (β ⋙ PGrpd.forgetToGrpd) (lam A β)
    (lam_comp_forgetToGrpd ..) y.base).map f.fiber).fiber =
    PGrpd.mapFiber (ι A y.base ⋙ β) (Hom.fiber f) := by
  simp [lam, app, PGrpd.objFiber]

lemma strongTrans.twoCell_lam_app {x y : ∫ A} (f : x ⟶ y) :
    ((strongTrans.twoCell (β ⋙ PGrpd.forgetToGrpd) (lam A β) (lam_comp_forgetToGrpd ..)
      (Hom.base f)).app ((A.map (Hom.base f)).obj x.fiber)) =
      homMk (eqToHom (by
        simp only [Functor.map_inv, sigma_obj, comp_obj, sigmaMap_obj_base, app_obj_base]
        simp [← Functor.comp_obj, ← Grpd.comp_eq_comp]))
        (eqToHom (by
        simp only [comp_obj, Functor.Grothendieck.forget_obj, sigma_obj, sigmaMap_obj_base,
          Functor.comp_map, eqToHom_map, Functor.Grothendieck.forget_map,
          Functor.Grothendieck.base_eqToHom, sigmaMap_obj_fiber, Grpd.eqToHom_obj, ← heq_eq_eq,
          cast_heq_iff_heq]
        simp only [← Functor.comp_obj, ← Grpd.comp_eq_comp]
        rw! [← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
        rfl) ≫
        (β.map ((ιNatTrans (Hom.base f)).app x.fiber)).fiber) := by
  simp only [sigma_obj, lam, comp_obj, twoCell, sigma.fstNatTrans_app, pi_obj_α,
    PGrpd.objFiber'_rfl, Set.mem_setOf_eq, PGrpd.mapFiber'_rfl, sigmaMap_obj_base,
    Functor.Grothendieck.forget_obj, Functor.comp_map, Functor.Grothendieck.forget_map,
    sigmaMap_obj_fiber]
  convert_to (whiskerLeftInvLamObjObjSigMap A β f.base).app ((A.map f.base).obj x.fiber) = _
  simp only [comp_obj, whiskerLeftInvLamObjObjSigMap, lamObjFiberObjCompSigMap, NatTrans.comp_app,
    whiskerLeft_app, lamObjFiberObjCompSigMap.app, sigmaMap_obj_base,
    Functor.Grothendieck.forget_obj, Functor.comp_map, Functor.Grothendieck.forget_map,
    sigmaMap_obj_fiber, eqToHom_app]
  have h : (A.map (CategoryTheory.inv (Hom.base f))).obj ((A.map (Hom.base f)).obj x.fiber) =
      x.fiber := by simp [← Functor.comp_obj, ← Grpd.comp_eq_comp]
  rw! [h]
  simp only [eqToHom_refl, Category.comp_id, ← heq_eq_eq]
  congr 1

lemma strongTrans.twoCell_lam_app_fiber {x y : ∫ A} (f : x ⟶ y) :
    ((strongTrans.twoCell (β ⋙ PGrpd.forgetToGrpd) (lam A β) (lam_comp_forgetToGrpd ..)
      (Hom.base f)).app ((A.map (Hom.base f)).obj x.fiber)).fiber =
    eqToHom (by
      simp only [comp_obj, sigma_obj, sigmaMap_obj_base, Functor.Grothendieck.forget_obj,
        twoCell_app_base, Functor.comp_map, eqToHom_map, Functor.Grothendieck.forget_map,
        Functor.Grothendieck.base_eqToHom, sigmaMap_obj_fiber]
      simp only [← Functor.comp_obj, ← Grpd.comp_eq_comp]
      rw! [← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
      ) ≫ (β.map ((ιNatTrans (Hom.base f)).app x.fiber)).fiber := by
  rw! [twoCell_lam_app]
  simp

lemma mapStrongTrans_map_lam_map_fiber_fiber_heq {x y} (f : x ⟶ y) :
    ((mapStrongTrans (β ⋙ PGrpd.forgetToGrpd) (lam A β)
      (lam_comp_forgetToGrpd ..)).map f).fiber.fiber ≍
    (β.map f).fiber := by
  rw [mapStrongTrans_map_fiber]
  apply (fiber_eqToHom_comp_heq ..).trans
  rw [comp_fiber]
  rw [strongTrans.twoCell_lam_app_fiber]
  slice_lhs 2 3 => rw [Functor.map_comp, eqToHom_map]
  rw [strongTrans.app_lam_map_fiber]
  simp only [mapStrongTrans_obj_base, comp_obj, Functor.Grothendieck.forget_obj, sigma_obj,
    sigmaMap_obj_base, Functor.comp_map, Functor.Grothendieck.forget_map, sigmaMap_obj_fiber,
    comp_base, strongTrans.app_lam_map_base, Category.assoc, eqToHom_trans_assoc,
    eqToHom_comp_heq_iff]
  simp [← Functor.comp_map, PGrpd.mapFiber]
  have : f = eqToHom (by apply Functor.Groupoidal.ext <;> simp) ≫
      (ιNatTrans (Hom.base f)).app x.fiber ≫ (ι A y.base).map f.fiber ≫
      eqToHom (by apply Functor.Groupoidal.ext <;> simp) := by
    fapply Functor.Groupoidal.Hom.ext
    · simp
    · simp
  have := Functor.congr_map β this
  simp [Functor.Grothendieck.Hom.congr this]
  rw! [Category.comp_id, CategoryTheory.Functor.map_id]
  simp only [Grothendieck.Hom.id_base, Grpd.id_eq_id, id_obj, eqToHom_refl, Functor.id_map,
    Category.id_comp, heq_eq_eq]
  erw [Category.comp_id]

lemma inversion_lam : inversion (β ⋙ PGrpd.forgetToGrpd) (lam A β)
    (lam_comp_forgetToGrpd ..) = β := by
  apply PGrpd.Functor.hext
  · simp [inversion_comp_forgetToGrpd]
  · intro x
    simp [mapStrongTrans_obj_fiber]
  · intro x y f
    simp [inversion]
    apply mapStrongTrans_map_lam_map_fiber_fiber_heq

end

section

variable (B : ∫ A ⥤ Grpd) (s : Γ ⥤ PGrpd) (hs : s ⋙ PGrpd.forgetToGrpd = pi A B)

lemma lamObjFiber_obj_obj_inversion_heq (x) :
    (lamObjFiber A (inversion B s hs) x).obj.obj ≍ strongTrans.app B s hs x := by
  dsimp only [lamObjFiber, lamObjFiberObj]
  rw! (castMode := .all) [pi.inversion_comp_forgetToGrpd B s hs]
  simp [sec_eq_lift, Grpd.forgetToCat.eq_1, heq_eq_eq]
  symm
  apply Functor.IsPullback.lift_uniq
  · symm
    apply pi.ι_comp_inversion
  · exact (PGrpd.objFiber' hs x).obj.property

lemma lamObjFiber_inversion_heq' (x) :
    lamObjFiber A (pi.inversion B s hs) x ≍ PGrpd.objFiber' hs x := by
  apply pi.obj_hext
  · rfl
  · simp [pi.inversion_comp_forgetToGrpd]
  · apply lamObjFiber_obj_obj_inversion_heq

lemma lamObjFiber_inversion_heq (x) :
    lamObjFiber A (pi.inversion B s hs) x ≍ PGrpd.objFiber s x := by
  refine HEq.trans ?_ (PGrpd.objFiber'_heq hs)
  apply lamObjFiber_inversion_heq'

lemma strongTrans.twoCell_app_inversion {x y} (f : x ⟶ y) (a) :
    (strongTrans.twoCell B s hs f).app ((A.map f).obj ((A.map (CategoryTheory.inv f)).obj a)) =
    eqToHom (by simp only [← Functor.comp_obj]; simp [← Grpd.comp_eq_comp]) ≫
    (strongTrans.twoCell B s hs f).app a ≫
    eqToHom (by simp only [← Functor.comp_obj]; simp [← Grpd.comp_eq_comp]) := by
  simp only [twoCell]
  have h : ((A.map f).obj ((A.map (CategoryTheory.inv f)).obj a)) = a := by
    simp [← Functor.comp_obj, ← Grpd.comp_eq_comp]
  apply (NatTrans.congr _ h).trans
  simp

lemma mapStrongTrans_obj_inversion_fiber {x y} (f : x ⟶ y) (a) :
    ((mapStrongTrans B s hs).obj ((A.map f ⋙ ι A y).obj ((A.map (CategoryTheory.inv f)).obj a))).fiber =
    (strongTrans.app B s hs y).obj a := by
  simp only [Functor.comp_obj, mapStrongTrans_obj_base, ι_obj_base, sigma_obj,
    mapStrongTrans_obj_fiber, ι_obj_fiber, Functor.map_inv]
  simp [← Functor.comp_obj, ← Grpd.comp_eq_comp]

lemma mapStrongTrans_map_inversion_fiber {x y} (f : x ⟶ y) (a) :
    ((mapStrongTrans B s hs).map ((ιNatTrans f).app ((A.map (CategoryTheory.inv f)).obj a))).fiber =
    (strongTrans.twoCell B s hs f).app a ≫
    eqToHom (mapStrongTrans_obj_inversion_fiber A B s hs f a).symm := by
  have h : (ιNatTrans f).app ((A.map (CategoryTheory.inv f)).obj a) =
      homMk f (𝟙 _) := by
    fapply Functor.Groupoidal.Hom.ext
    · simp
    · simp; rfl
  rw! (castMode := .all) [h]
  simp [mapStrongTrans_map_fiber B s hs, strongTrans.twoCell_app_inversion]

lemma lamObjFiberObjCompSigMap_app_inversion {x y} (f : x ⟶ y) (a) :
    lamObjFiberObjCompSigMap.app A (inversion B s hs) f ((A.map (CategoryTheory.inv f)).obj a) ≍
    (strongTrans.twoCell B s hs f).app a := by
  have h := mapStrongTrans_map_inversion_fiber A B s hs f a
  simp [← heq_eq_eq] at h
  apply HEq.trans _ h
  fapply Functor.Groupoidal.Hom.hext'
  · simp
  · simp only [Functor.map_inv, Functor.comp_obj, mapStrongTrans_obj_base, ι_obj_base, sigma_obj,
      mapStrongTrans_map_base, Functor.Groupoidal.ιNatTrans_app_base, sigma_map]
    apply Grpd.Functor.hcongr_obj
    · rw [inversion_comp_forgetToGrpd]
    · rw [inversion_comp_forgetToGrpd]
    · rw [inversion_comp_forgetToGrpd]
    · rw [Functor.map_inv]
      simp only [mapStrongTrans_obj_fiber, ι_obj_base, sigma_obj, ι_obj_fiber]
      apply Grpd.Functor.hcongr_obj rfl _ _ HEq.rfl
      · simp [inversion_comp_forgetToGrpd]
      · apply lamObjFiber_obj_obj_inversion_heq
  · simp only [Functor.map_inv, Functor.comp_obj, mapStrongTrans_obj_base, ι_obj_base,
      mapStrongTrans_obj_fiber, sigma_obj, ι_obj_fiber]
    apply Grpd.Functor.hcongr_obj
    · rfl
    · simp
    · apply lamObjFiber_obj_obj_inversion_heq
    · simp
  · rw [mapStrongTrans_map_fiber_base]
    simp
    rfl
  · apply (lamObjFiberObjCompSigMap.app_fiber_heq ..).trans
    simp [inversion]

lemma whiskerLeftInvLamObjObjSigMap_inversion_app {x y} (f : x ⟶ y) (a) :
    (whiskerLeftInvLamObjObjSigMap A (inversion B s hs) f).app a ≍
    (strongTrans.twoCell B s hs f).app a := by
  simp [whiskerLeftInvLamObjObjSigMap, lamObjFiberObjCompSigMap]
  have h := Functor.congr_obj (((pi A B).map f).obj (PGrpd.objFiber' hs x)).obj.property a
  simp only [sigma_obj, sigma.fstNatTrans_app, pi_obj_α, Functor.comp_obj,
    Functor.Groupoidal.forget_obj, Functor.id_obj] at h
  exact (comp_eqToHom_heq ..).trans (lamObjFiberObjCompSigMap_app_inversion ..)

lemma lamMapFiber_inversion_heq {x y} (f : x ⟶ y) :
    lamMapFiber A (pi.inversion B s hs) f ≍ PGrpd.mapFiber s f := by
  refine HEq.trans ?_ (PGrpd.mapFiber'_heq hs f)
  apply Section.hom_hext'
  · rw [inversion_comp_forgetToGrpd]
  · rfl
  · rw [inversion_comp_forgetToGrpd]
  · rw! (castMode := .all) [inversion_comp_forgetToGrpd]
    congr 1
    rw! [lamObjFiber_inversion_heq, PGrpd.objFiber'_heq]
    simp only [pi_obj_α, Functor.Grothendieck.forget_obj, Grpd.coe_of, ← heq_eq_eq,
      heq_cast_iff_heq, eqRec_heq_iff_heq, cast_heq_iff_heq]
    rfl
  · apply lamObjFiber_inversion_heq'
  · intro a a' ha
    subst ha
    simp only [sigma_obj, sigma.fstNatTrans_app, pi_obj_α, Set.mem_setOf_eq,
      lamMapFiber]
    exact whiskerLeftInvLamObjObjSigMap_inversion_app A B s hs f a

lemma lam_inversion : lam A (inversion B s hs) = s := by
  apply PGrpd.Functor.hext -- TODO: rename to PGrpd.ToFunctor.hext
  · rw [lam_comp_forgetToGrpd, inversion_comp_forgetToGrpd, hs]
  · apply lamObjFiber_inversion_heq
  · apply lamMapFiber_inversion_heq

lemma inversion_comp {Δ : Type u} [Groupoid.{v} Δ] {σ : Δ ⥤ Γ} :
    inversion (A := σ ⋙ A) (pre _ σ ⋙ B) (σ ⋙ s) (by rw [Functor.assoc, hs, ← pi_comp]) =
    pre _ σ ⋙ inversion B s hs := by
  rw [← inversion_lam (σ ⋙ A) (pre A σ ⋙ inversion B s hs)]
  congr 1
  · simp [Functor.assoc]
  · rw [← lam_comp, lam_inversion]

end

end

namespace Over

variable {Γ : Type u} {Δ : Type u} [Groupoid.{v} Γ] [Groupoid.{v} Δ] {σ : Δ ⥤ Γ}
  {A : Γ ⥤ Grpd.{u₁,u₁}} (B : ∫ A ⥤ Grpd.{u₁,u₁})

/-- lifts of `σ : Δ ⥤ Γ` along `forget : ∫ pi A B ⥤ Γ`
biject (since the Grothendieck construction is a pullback) with
lifts of `pi (σ ⋙ A) (pre A σ ⋙ B) : Δ ⥤ Grpd` along `forgetToGrpd : PGrpd ⥤ Grpd`
biject (via `lam` and `inversion`) with
lifts of `pre A σ ⋙ B : ∫ σ ⋙ A ⥤ Grpd` along `forgetToGrpd : PGrpd ⥤ Grpd`
biject (since the Grothendieck construction is a pullback) with
lifts of `pre A σ : ∫ σ ⋙ A ⥤ ∫ A` along `forget : ∫ B ⥤ ∫ A`.

The function `equivFun` is the forward direction in this bijection.
The function `equivInv` is the inverse direction in this bijection.
-/
def equivFun (F : Δ ⥤ ∫ pi A B) (hF : F ⋙ forget = σ) : ∫ σ ⋙ A ⥤ ∫ B :=
  (isPullback B).lift (inversion (pre A σ ⋙ B) (F ⋙ toPGrpd _) (by
    rw [Functor.assoc, toPGrpd_forgetToGrpd, ← Functor.assoc, hF, pi_comp]))
  (pre A σ) (inversion_comp_forgetToGrpd ..)

lemma equivFun_comp_forget (F : Δ ⥤ ∫ pi A B) (hF : F ⋙ forget = σ) :
    equivFun B F hF ⋙ forget = pre A σ := by
  simp [equivFun, Functor.IsPullback.fac_right]

@[inherit_doc equivFun]
def equivInv (G : ∫ σ ⋙ A ⥤ ∫ B) (hG : G ⋙ forget = pre A σ) : Δ ⥤ ∫ pi A B :=
  (isPullback (pi A B)).lift (lam (σ ⋙ A) (G ⋙ toPGrpd _)) σ (by
    rw [lam_comp_forgetToGrpd, ← pi_comp, Functor.assoc,
      toPGrpd_forgetToGrpd, ← Functor.assoc, hG])

lemma equivInv_comp_forget (G : ∫ σ ⋙ A ⥤ ∫ B) (hG : G ⋙ forget = pre A σ) :
    equivInv B G hG ⋙ forget = σ := by
  simp [equivInv, Functor.IsPullback.fac_right]

lemma equivInv_equivFun (F : Δ ⥤ ∫ pi A B) (hF : F ⋙ forget = σ) :
    equivInv B (equivFun B F hF) (equivFun_comp_forget B F hF) = F := by
  simp only [equivFun, equivInv]
  apply (isPullback _).hom_ext
  · rw [Functor.IsPullback.fac_left, Functor.IsPullback.fac_left, lam_inversion]
  · rw! [Functor.IsPullback.fac_right, hF]

lemma equivFun_equivInv (G : ∫ σ ⋙ A ⥤ ∫ B) (hG : G ⋙ forget = pre A σ) :
    equivFun B (equivInv B G hG) (equivInv_comp_forget B G hG) = G := by
  simp only [equivFun, equivInv]
  apply (isPullback B).hom_ext
  · have : pre A σ ⋙ B = (G ⋙ toPGrpd B) ⋙ PGrpd.forgetToGrpd := by
      rw [Functor.assoc, toPGrpd_forgetToGrpd, ← Functor.assoc, hG]
    rw! [Functor.IsPullback.fac_left, Functor.IsPullback.fac_left, this, inversion_lam]
  · rw [Functor.IsPullback.fac_right, hG]

lemma equivFun_comp {Δ' : Type u} [Groupoid.{v} Δ'] {σ' : Δ' ⥤ Γ} (τ : Δ' ⥤ Δ) (hτ : τ ⋙ σ = σ')
    (F : Δ ⥤ ∫ pi A B) (hF : F ⋙ forget = σ) :
    equivFun B (τ ⋙ F) (by rw [Functor.assoc, hF, hτ]) =
    map (eqToHom (by aesop_cat)) ⋙ pre _ τ ⋙ equivFun B F hF := by
  cases hτ
  simp only [equivFun, pre_comp, eqToHom_refl, map_id_eq, Cat.of_α, Functor.id_comp]
  symm
  apply (isPullback B).lift_uniq
  · simp only [Functor.assoc, Functor.IsPullback.fac_left]
    rw [inversion_comp]
  · simp [Functor.assoc, Functor.IsPullback.fac_right]

lemma equivInv_comp {Δ' : Type u} [Groupoid.{v} Δ'] {σ' : Δ' ⥤ Γ} (τ : Δ' ⥤ Δ) (hτ : τ ⋙ σ = σ')
    (G : ∫ σ ⋙ A ⥤ ∫ B) (hG : G ⋙ forget = pre A σ) :
    equivInv B (map (eqToHom (Functor.assoc ..)) ⋙ pre _ τ ⋙ G)
    (by simp [map_id_eq, Functor.assoc, hG]) =
    τ ⋙ equivInv B G hG := by
  cases hτ
  simp [map_id_eq, equivInv]
  symm
  apply (isPullback (pi A B)).lift_uniq
  · simp only [Functor.assoc, Functor.IsPullback.fac_left]
    rw [lam_comp]
  · simp [Functor.assoc, Functor.IsPullback.fac_right]

end Over

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
  USig.SigAux_comp pi (by intros; rw [← pi_comp]) σ eq B

def lam {Γ : Ctx} {A : Γ ⟶ U.{v}.Ty} (b : U.ext A ⟶ U.{v}.Tm) : Γ ⟶ U.{v}.Tm :=
  USig.SigAux pi.lam b

lemma lam_comp {Γ Δ : Ctx} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.{v}.Ty} {σA : Δ ⟶ U.Ty}
    (eq : σ ≫ A = σA) (b : U.ext A ⟶ U.{v}.Tm) :
    lam (U.substWk σ A σA eq ≫ b) = σ ≫ lam b :=
  USig.SigAux_comp pi.lam (by intros; rw [pi.lam_comp]) σ eq b

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
