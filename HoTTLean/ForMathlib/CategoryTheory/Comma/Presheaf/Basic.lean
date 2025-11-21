import Mathlib.CategoryTheory.Comma.Presheaf.Basic

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : C}


-- def CostructuredArrowYonedaOver :
--     CostructuredArrow yoneda (yoneda.obj (A)) ≅ CategoryTheory.Over A where
--   hom X := Over.mk ((CategoryTheory.Yoneda.fullyFaithful).preimage X.hom)
--   inv X := CostructuredArrow.mk (yoneda.map X.hom)

def CostructuredArrowYonedaOver_functor : CostructuredArrow yoneda (yoneda.obj A) ⥤ Over A where
  obj X := Over.mk ((CategoryTheory.Yoneda.fullyFaithful).preimage X.hom)
  map {X Y} f := by
   have w := f.w
   have e:
    (yoneda.map f.left ≫ Y.hom).app (op X.left) =
    (X.hom ≫ (Functor.fromPUnit (yoneda.obj A)).map f.right).app (op X.left) := by
    simp[w]
   simp[- CommaMorphism.w] at e
   apply Over.homMk f.left (by simp[CategoryTheory.Yoneda.fullyFaithful_preimage,← e])



def CostructuredArrowYonedaOver_inverse : Over A ⥤ CostructuredArrow yoneda (yoneda.obj A) where
  obj X := CostructuredArrow.mk (yoneda.map X.hom)
  map {X Y} f := CostructuredArrow.homMk f.left


def CostructuredArrowYonedaOver_unitIso :
  𝟭 (CostructuredArrow yoneda (yoneda.obj A)) ≅
  CostructuredArrowYonedaOver_functor ⋙ CostructuredArrowYonedaOver_inverse
  where
    hom := {
      app X := by
        dsimp
        simp[CostructuredArrowYonedaOver_inverse,CostructuredArrowYonedaOver_functor]
        exact (𝟙 _)
      naturality := sorry
    }
    inv := sorry
    hom_inv_id := sorry
    inv_hom_id := sorry


def CostructuredArrowYonedaOver :
    CostructuredArrow yoneda (yoneda.obj (A)) ≌ CategoryTheory.Over A where
      functor := CostructuredArrowYonedaOver_functor
      inverse := CostructuredArrowYonedaOver_inverse
      unitIso := {
        hom := sorry
        inv := sorry
        hom_inv_id := sorry
        inv_hom_id := sorry
      }
      counitIso := sorry
      functor_unitIso_comp := sorry

#check overEquivPresheafCostructuredArrow
#check CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow

def PresheafCostructuredArrowYonedaOver_aux:
 (CostructuredArrow yoneda (yoneda.obj (A)))ᵒᵖ ⥤ Type v ≌
 (CategoryTheory.Over A)ᵒᵖ ⥤ Type v := by
 apply Equivalence.congrLeft
 apply CategoryTheory.Equivalence.op
 exact CostructuredArrowYonedaOver


 /-
 @CostructuredArrow C inst✝ (Cᵒᵖ ⥤ Type v) Functor.category yoneda (yoneda.obj A) : Type (max u v)
 @CostructuredArrow C inst✝ (Cᵒᵖ ⥤ Type v) Functor.category yoneda (yoneda.obj A) : Type (max u v)

 @Over C inst✝ A : Type (max u v)
 @Over C inst✝ A : Type (max u v)
 -/

--CategoryTheory.NatIso.op

def PresheafCostructuredArrowYonedaOver :
    CategoryTheory.Over (yoneda.obj (A)) ≌
    ((CategoryTheory.Over A)ᵒᵖ ⥤ Type v) :=
   Equivalence.trans (overEquivPresheafCostructuredArrow (yoneda.obj (A)))
   (PresheafCostructuredArrowYonedaOver_aux)
   -- need A equiv B -> A => Type equiv B => Type
   -- need A equiv B -> Aᵒᵖ equiv Bᵒᵖ





end CategoryTheory
