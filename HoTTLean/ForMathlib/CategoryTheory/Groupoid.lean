import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.MorphismProperty.Basic

namespace CategoryTheory

open MorphismProperty in
lemma isGroupoid_iff_isomorphisms_eq_top (C : Type*) [Category C] :
    IsGroupoid C ↔ isomorphisms C = ⊤ := by
  constructor
  · rw [eq_top_iff]
    intro _ _
    simp only [isomorphisms.iff, top_apply]
    infer_instance
  · intro h
    exact ⟨of_eq_top h⟩

end CategoryTheory
