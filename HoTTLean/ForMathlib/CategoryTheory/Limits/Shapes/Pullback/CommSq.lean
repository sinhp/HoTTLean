import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

instance {X : C} : HasPullbacksAlong (𝟙 X) := by
  intro W h
  exact IsPullback.hasPullback (IsPullback.id_horiz h)
