import Mathlib.CategoryTheory.MorphismProperty.Basic

universe u v

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type*} [Category D]

@[simp]
lemma map_top_eq_top_of_essSurj_of_full (F : C ⥤ D) [F.EssSurj] [F.Full] :
    (⊤ : MorphismProperty C).map F = ⊤ := by
  rw [eq_top_iff]
  intro X Y f _
  refine ⟨F.objPreimage X, F.objPreimage Y, F.preimage ?_, ⟨⟨⟩, ⟨?_⟩⟩⟩
  · exact (Functor.objObjPreimageIso F X).hom ≫ f ≫ (Functor.objObjPreimageIso F Y).inv
  · exact Arrow.isoMk' _ _ (Functor.objObjPreimageIso F X) (Functor.objObjPreimageIso F Y)
      (by simp)

end CategoryTheory.MorphismProperty
