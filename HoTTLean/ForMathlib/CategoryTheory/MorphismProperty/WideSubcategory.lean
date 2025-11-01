/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Joseph Hua
-/
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Wide subcategories

A wide subcategory of a category `C` is a subcategory containing all the objects of `C`.

## Main declarations

Given a category `D`, a function `F : C → D` from a type `C` to the objects of `D`,
and a morphism property `P` on `D` which contains identities and is stable under
composition, the type class `InducedWideCategory D F P` is a typeclass
synonym for `C` which comes equipped with a category structure whose morphisms `X ⟶ Y` are the
morphisms in `D` which have the property `P`.

The instance `WideSubcategory.category` provides a category structure on `WideSubcategory P`
whose objects are the objects of `C` and morphisms are the morphisms in `C` which have the
property `P`.
-/

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

namespace MorphismProperty

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v₁} D]
variable (F : C → D) (P : MorphismProperty D) [P.IsMultiplicative]

/-- `InducedWideCategory D F P`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y` which satisfy a property `P : MorphismProperty D` that is multiplicative.
-/
@[nolint unusedArguments]
def InducedWideCategory (_F : C → D) (_P : MorphismProperty D) [IsMultiplicative _P] :=
  C

variable {D}

instance InducedWideCategory.hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedWideCategory D F P) α :=
  ⟨fun c => F c⟩

@[simps!]
instance InducedWideCategory.category :
    Category (InducedWideCategory D F P) where
  Hom X Y := {f : F X ⟶ F Y | P f}
  id X := ⟨𝟙 (F X), P.id_mem (F X)⟩
  comp {_ _ _} f g := ⟨f.1 ≫ g.1, P.comp_mem _ _ f.2 g.2⟩

/-- The forgetful functor from an induced wide category to the original category. -/
@[simps]
def wideInducedFunctor : InducedWideCategory D F P ⥤ D where
  obj := F
  map {_ _} f := f.1

/-- The induced functor `wideInducedFunctor F P : InducedWideCategory D F P ⥤ D`
is faithful. -/
instance InducedWideCategory.faithful : (wideInducedFunctor F P).Faithful where
  map_injective {X Y} f g eq := by
    cases f
    cases g
    aesop

end Induced

section WideSubcategory

variable {C : Type u₁} [Category.{v₁} C]
variable (P : MorphismProperty C) [IsMultiplicative P]

/--
Structure for wide subcategories. Objects ignore the morphism property.
-/
@[ext, nolint unusedArguments]
structure WideSubcategory (_P : MorphismProperty C) [IsMultiplicative _P] where
  /-- The category of which this is a wide subcategory -/
  obj : C

instance WideSubcategory.category : Category.{v₁} (WideSubcategory P) :=
  InducedWideCategory.category WideSubcategory.obj P

@[simp]
lemma WideSubcategory.id_def (X : WideSubcategory P) : (CategoryStruct.id X).1 = 𝟙 X.obj := rfl

@[simp]
lemma WideSubcategory.comp_def {X Y Z : WideSubcategory P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = (f.1 ≫ g.1 : X.obj ⟶ Z.obj) := rfl

/-- The forgetful functor from a wide subcategory into the original category
("forgetting" the condition).
-/
def wideSubcategoryInclusion : WideSubcategory P ⥤ C :=
  wideInducedFunctor WideSubcategory.obj P

@[simp]
theorem wideSubcategoryInclusion.obj (X) : (wideSubcategoryInclusion P).obj X = X.obj :=
  rfl

@[simp]
theorem wideSubcategoryInclusion.map {X Y} {f : X ⟶ Y} :
    (wideSubcategoryInclusion P).map f = f.1 :=
  rfl

/-- The inclusion of a wide subcategory is faithful. -/
instance wideSubcategoryInclusion.faithful : (wideSubcategoryInclusion P).Faithful :=
  inferInstanceAs (wideInducedFunctor WideSubcategory.obj P).Faithful

lemma WideSubcategory.hom_ext {x y : WideSubcategory P} (f g : x ⟶ y)
    (hfg : f.1 = g.1) : f = g :=
  (wideSubcategoryInclusion P).map_injective (by simpa)

/-- Construct a functor into a widesubcategory by constructing a functor into
the ambient category, and showing that the images of morphisms satisfy the morphism property.-/
def lift {D : Type*} [Category D] (F : D ⥤ C) (hF : ∀ {X Y} (f : X ⟶ Y), P (F.map f)) :
    D ⥤ P.WideSubcategory where
  obj X := ⟨F.obj X⟩
  map f := ⟨F.map f, hF f⟩

@[simp]
lemma WideSubcategory.coe_eqToHom {X Y : P.WideSubcategory} (h : X = Y) :
    (eqToHom h).1 = eqToHom (by aesop_cat) := by aesop_cat

lemma WideSubcategory.hext {X X' : P.WideSubcategory} (hX : X.1 ≍ X'.1) : X ≍ X' := by
  aesop

lemma WideSubcategory.hom_hext {X X' Y Y' : P.WideSubcategory} (hX : X.1 ≍ X'.1)
    (hY : Y.1 ≍ Y'.1) (f : X ⟶ Y) (f' : X' ⟶ Y') (hf : f.1 ≍ f'.1) : f ≍ f' := by
  cases X; cases X'; cases Y; cases Y'; subst hX hY
  simp only [Set.mem_setOf_eq, heq_eq_eq] at *
  apply hom_ext
  assumption

end WideSubcategory

end MorphismProperty

-- @[deprecated (since := "2025-10-30")]
-- alias WideSubcategory := MorphismProperty.WideSubcategory

-- @[deprecated (since := "2025-10-30")]
-- alias InducedWideSubcategory := MorphismProperty.InducedWideCategory

end CategoryTheory
