import Mathlib.CategoryTheory.MorphismProperty.Basic

universe u v

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type*} [Category D]

-- Mathlib now supplies the original public theorem. Keep this statement as a check.
lemma map_top_eq_top_of_essSurj_of_full_compat (F : C ⥤ D) [F.EssSurj] [F.Full] :
    (⊤ : MorphismProperty C).map F = ⊤ := by
  exact map_top_eq_top_of_essSurj_of_full F

end CategoryTheory.MorphismProperty
