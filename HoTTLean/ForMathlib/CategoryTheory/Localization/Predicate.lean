import Mathlib.CategoryTheory.Localization.Predicate

import HoTTLean.ForMathlib.CategoryTheory.Groupoid
import HoTTLean.ForMathlib.CategoryTheory.MorphismProperty.Basic

noncomputable section

namespace CategoryTheory.Localization
open Category Functor

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C) (E : Type*)
  [Category E]

variable {D₁ D₂ : Type _} [Category D₁] [Category D₂] (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂)
  (W' : MorphismProperty C) [L₁.IsLocalization W'] [L₂.IsLocalization W']

lemma morphismProperty_eq_top [L.IsLocalization W] (P : MorphismProperty D) [P.RespectsIso]
    [P.IsMultiplicative] (h₁ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P (L.map f))
    (h₂ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : W f), P (isoOfHom L W f hf).inv) :
    P = ⊤ := by
  let P' : MorphismProperty W.Localization :=
    P.inverseImage (Construction.lift L Functor.IsLocalization.inverts)
  have hP' : P' = ⊤ := by
    apply Construction.morphismProperty_is_top
    · intros
      simp only [MorphismProperty.inverseImage_iff, Construction.lift_obj, ← Functor.comp_map,
        Functor.congr_hom (Construction.fac L Functor.IsLocalization.inverts), Functor.comp_obj,
        eqToHom_refl, Category.comp_id, Category.id_comp, h₁, P']
    · intro X Y w hw
      simp only [P', MorphismProperty.inverseImage_iff]
      convert h₂ w hw
      convert Functor.map_inv (Construction.lift L Functor.IsLocalization.inverts)
        (Construction.wIso w hw).hom
      · simp
      · have : (Construction.wIso w hw).hom = W.Q.map w := rfl
        simp only [this, ← Functor.comp_map,
          Functor.congr_hom (Construction.fac L Functor.IsLocalization.inverts)]
        simp [isoOfHom]
  have : P'.map _ = P := MorphismProperty.map_inverseImage_eq_of_isEquivalence ..
  simp [← this, hP']

lemma isGroupoid [L.IsLocalization ⊤] :
    IsGroupoid D := by
  rw [isGroupoid_iff_isomorphisms_eq_top]
  exact morphismProperty_eq_top L ⊤ _
    (fun _ _ f ↦ inverts L ⊤ _ (by simp))
    (fun _ _ f hf ↦ Iso.isIso_inv _)

instance : IsGroupoid (⊤ : MorphismProperty C).Localization :=
  isGroupoid <| MorphismProperty.Q ⊤

/-- Localization of a category with respect to all morphisms results in a groupoid. -/
def groupoid : Groupoid (⊤ : MorphismProperty C).Localization :=
  Groupoid.ofIsGroupoid

end CategoryTheory.Localization
