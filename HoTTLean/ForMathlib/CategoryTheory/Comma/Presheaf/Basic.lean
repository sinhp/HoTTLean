import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.Tactic.DepRewrite

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : C}


@[simps!]
def CostructuredArrowYonedaOver_functor : CostructuredArrow yoneda (yoneda.obj A) ⥤ Over A where
  obj X := Over.mk ((CategoryTheory.Yoneda.fullyFaithful).preimage X.hom)
  map {X Y} f := Over.homMk f.left (by
    have e : (yoneda.map f.left ≫ Y.hom).app (op X.left) (𝟙 X.left) =
        (X.hom ≫ (Functor.fromPUnit (yoneda.obj A)).map f.right).app
        (op X.left) (𝟙 X.left) := by simp [f.w]
    simp [- CommaMorphism.w] at e
    simpa [CategoryTheory.Yoneda.fullyFaithful_preimage])


@[simps!]
def CostructuredArrowYonedaOver_inverse : Over A ⥤ CostructuredArrow yoneda (yoneda.obj A) where
  obj X := CostructuredArrow.mk (yoneda.map X.hom)
  map {X Y} f := CostructuredArrow.homMk f.left

def CostructuredArrowYonedaOver_unitIso :
    𝟭 (CostructuredArrow yoneda (yoneda.obj A)) ≅
    CostructuredArrowYonedaOver_functor ⋙ CostructuredArrowYonedaOver_inverse :=
  NatIso.ofComponents (fun X => Comma.isoMk (Iso.refl _) (Iso.refl _)
  (by
    simp
    ext
    simp[CategoryTheory.Yoneda.fullyFaithful_preimage]) )



def CostructuredArrowYonedaOver_counitIso :
  CostructuredArrowYonedaOver_inverse ⋙ CostructuredArrowYonedaOver_functor (A:= A)
  ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => Over.isoMk (Iso.refl _))



def CostructuredArrowYonedaOver :
    CostructuredArrow yoneda (yoneda.obj (A)) ≌ CategoryTheory.Over A where
      functor := CostructuredArrowYonedaOver_functor
      inverse := CostructuredArrowYonedaOver_inverse
      unitIso := CostructuredArrowYonedaOver_unitIso
      counitIso := CostructuredArrowYonedaOver_counitIso
      functor_unitIso_comp X := by
       simp[CostructuredArrowYonedaOver_functor,CostructuredArrowYonedaOver_unitIso,
            CostructuredArrowYonedaOver_counitIso]
       ext
       simp[Over.mk]


def PresheafCostructuredArrowYonedaOver_aux:
 (CostructuredArrow yoneda (yoneda.obj (A)))ᵒᵖ ⥤ Type v ≌
 (CategoryTheory.Over A)ᵒᵖ ⥤ Type v := by
 apply Equivalence.congrLeft
 apply CategoryTheory.Equivalence.op
 exact CostructuredArrowYonedaOver



def PresheafCostructuredArrowYonedaOver :
    CategoryTheory.Over (yoneda.obj (A)) ≌
    ((CategoryTheory.Over A)ᵒᵖ ⥤ Type v) :=
   Equivalence.trans (overEquivPresheafCostructuredArrow (yoneda.obj (A)))
   (PresheafCostructuredArrowYonedaOver_aux)





end CategoryTheory
