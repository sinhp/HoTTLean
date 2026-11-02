/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Category.Cat.Limit

/-!
# Free groupoid on a category

Mathlib provides the free groupoid construction and its universal property.
This module keeps the names previously exported by HoTTLean as compatibility
aliases. The implementation now lives in `CategoryTheory.FreeGroupoid` and
`CategoryTheory.Grpd`.
-/

noncomputable section

namespace CategoryTheory.Category

universe v u v₁ u₁ v₂ u₂

variable (C : Type u) [Category.{v} C]

/-- Compatibility alias for the relation defining the free groupoid. -/
abbrev FreeGroupoid.homRel := _root_.CategoryTheory.FreeGroupoid.homRel C

namespace FreeGroupoid.homRel

/-- Compatibility alias for the identity relation constructor. -/
abbrev map_id (X : C) := _root_.CategoryTheory.FreeGroupoid.homRel.map_id X

/-- Compatibility alias for the composition relation constructor. -/
abbrev map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  _root_.CategoryTheory.FreeGroupoid.homRel.map_comp f g

end FreeGroupoid.homRel

/-- Compatibility alias for the free groupoid on a category. -/
abbrev FreeGroupoid := _root_.CategoryTheory.FreeGroupoid C

namespace FreeGroupoid

variable {C} {G : Type u₁} [Groupoid.{v₁} G]

/-- The localization functor from `C` to its free groupoid. -/
abbrev of (C : Type u) [Category.{v} C] :=
  _root_.CategoryTheory.FreeGroupoid.of C

/-- Compatibility alias for the free groupoid's identity relation. -/
@[simp] theorem of.map_id (X : C) :
    (Quotient.functor (FreeGroupoid.homRel C)).map
      ((Quiver.FreeGroupoid.of C).map (𝟙 X)) = 𝟙 _ := by
  exact Functor.map_id (_root_.CategoryTheory.FreeGroupoid.of C) X

/-- Compatibility alias for the free groupoid's composition relation. -/
@[simp] theorem of.map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Quotient.functor (FreeGroupoid.homRel C)).map
      ((Quiver.FreeGroupoid.of C).map (f ≫ g)) =
    (Quotient.functor (FreeGroupoid.homRel C)).map
      ((Quiver.FreeGroupoid.of C).map f) ≫
    (Quotient.functor (FreeGroupoid.homRel C)).map
      ((Quiver.FreeGroupoid.of C).map g) := by
  exact Functor.map_comp (_root_.CategoryTheory.FreeGroupoid.of C) f g

/-- Extend a functor from `C` to a groupoid. -/
abbrev lift (φ : C ⥤ G) := _root_.CategoryTheory.FreeGroupoid.lift φ

/-- The localization property of the free groupoid. -/
abbrev strictUniversalPropertyFixedTarget {G : Type u₁}
    [Groupoid.{v₁} G] :=
  _root_.CategoryTheory.FreeGroupoid.strictUniversalPropertyFixedTarget
    (C := C) (G := G)

/-- The free groupoid lift restricts to the original functor. -/
theorem lift_spec (φ : C ⥤ G) : of C ⋙ lift φ = φ :=
  _root_.CategoryTheory.FreeGroupoid.lift_spec φ

/-- The free groupoid lift is unique. -/
theorem lift_unique (φ : C ⥤ G) (Φ : FreeGroupoid C ⥤ G)
    (hΦ : of C ⋙ Φ = φ) : Φ = lift φ :=
  _root_.CategoryTheory.FreeGroupoid.lift_unique φ Φ hΦ

/-- Lifting commutes with postcomposition. -/
theorem lift_comp {H : Type u₂} [Groupoid.{v₂} H] (φ : C ⥤ G) (ψ : G ⥤ H) :
    lift (φ ⋙ ψ) = lift φ ⋙ ψ :=
  _root_.CategoryTheory.FreeGroupoid.lift_comp φ ψ

end FreeGroupoid

namespace FreeGroupoid

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
  {E : Type u₂} [Category.{v₂} E]

/-- The induced functor between free groupoids. -/
abbrev map (φ : C ⥤ D) : FreeGroupoid C ⥤ FreeGroupoid D :=
  _root_.CategoryTheory.FreeGroupoid.map φ

theorem map_id : map (𝟭 C) = 𝟭 (FreeGroupoid C) := by
  apply _root_.CategoryTheory.FreeGroupoid.map_id

theorem map_comp (φ : C ⥤ D) (φ' : D ⥤ E) :
    map (φ ⋙ φ') = map φ ⋙ map φ' :=
  _root_.CategoryTheory.FreeGroupoid.map_comp φ φ'

end FreeGroupoid

end CategoryTheory.Category

namespace CategoryTheory.Grpd

universe u

instance : Limits.HasLimits Grpd.{u,u} := hasLimits_of_reflective forgetToCat

end CategoryTheory.Grpd
end
