import Mathlib.CategoryTheory.Localization.Predicate

import HoTTLean.ForMathlib.CategoryTheory.Groupoid
import HoTTLean.ForMathlib.CategoryTheory.MorphismProperty.Basic

noncomputable section

namespace CategoryTheory.Localization
open Category CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C) (E : Type*)
  [Category E]

variable {D₁ D₂ : Type _} [Category D₁] [Category D₂] (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂)
  (W' : MorphismProperty C) [L₁.IsLocalization W'] [L₂.IsLocalization W']

-- Mathlib now supplies these declarations. Check the original interfaces here.
example [L.IsLocalization W] (P : MorphismProperty D) [P.RespectsIso]
    [P.IsMultiplicative] (h₁ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P (L.map f))
    (h₂ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : W f), P (isoOfHom L W f hf).inv) :
    P = ⊤ :=
  morphismProperty_eq_top L W P h₁ h₂

example [L.IsLocalization ⊤] : IsGroupoid D :=
  isGroupoid L

example : IsGroupoid (⊤ : MorphismProperty C).Localization :=
  inferInstance

example : Groupoid (⊤ : MorphismProperty C).Localization :=
  groupoid

end CategoryTheory.Localization
