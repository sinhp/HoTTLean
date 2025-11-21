import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.Tactic.DepRewrite

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : C}

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

lemma CostructuredArrowYonedaOver_inverse_functor :
  CostructuredArrowYonedaOver_inverse (A := A) ⋙ CostructuredArrowYonedaOver_functor = Functor.id _
 := by
  fapply Functor.ext
  · intro X
    simp only [CostructuredArrowYonedaOver_inverse, Functor.id_obj,
      CostructuredArrowYonedaOver_functor, Over.mk, Functor.comp_obj, CostructuredArrow.mk_left,
      CostructuredArrow.mk_hom_eq_self, Functor.FullyFaithful.preimage_map]
    rfl
  intro X Y f
  simp[CostructuredArrowYonedaOver_inverse,
      CostructuredArrowYonedaOver_functor]
  ext
  simp



lemma CostructuredArrowYonedaOver_functor_inverse :
  CostructuredArrowYonedaOver_functor ⋙ CostructuredArrowYonedaOver_inverse (A := A) = Functor.id _
 := by
  fapply Functor.ext
  · intro X
    simp[CostructuredArrowYonedaOver_inverse,
        CostructuredArrowYonedaOver_functor]
    apply CostructuredArrow.eq_mk
  intro X Y f
  simp[CostructuredArrowYonedaOver_inverse,
        CostructuredArrowYonedaOver_functor]



def CostructuredArrowYonedaOver_unitIso :
  𝟭 (CostructuredArrow yoneda (yoneda.obj A)) ≅
  CostructuredArrowYonedaOver_functor ⋙ CostructuredArrowYonedaOver_inverse :=
  eqToIso CostructuredArrowYonedaOver_functor_inverse.symm

def CostructuredArrowYonedaOver_counitIso :
  CostructuredArrowYonedaOver_inverse ⋙ CostructuredArrowYonedaOver_functor (A:= A)
  ≅ 𝟭 _ := eqToIso CostructuredArrowYonedaOver_inverse_functor



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
