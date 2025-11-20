import Mathlib.CategoryTheory.Comma.Presheaf.Basic

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : C}


def CostructuredArrowYonedaOver :
    CostructuredArrow yoneda (yoneda.obj (A)) ≅ CategoryTheory.Over A where
  hom X := Over.mk ((CategoryTheory.Yoneda.fullyFaithful).preimage X.hom)
  inv X := CostructuredArrow.mk (yoneda.map X.hom)


def PresheafCostructuredArrowYonedaOver :
    CategoryTheory.Over (yoneda.obj (A)) ≅
    (CategoryTheory.Over A)ᵒᵖ ⥤ Type v :=

  sorry


end CategoryTheory
