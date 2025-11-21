import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.Tactic.DepRewrite

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : C}

attribute [local simp] CategoryTheory.Yoneda.fullyFaithful_preimage

namespace costructuredArrowYonedaEquivOver

@[simps!]
def functor : CostructuredArrow yoneda (yoneda.obj A) ⥤ Over A where
  obj X := Over.mk ((CategoryTheory.Yoneda.fullyFaithful).preimage X.hom)
  map {X Y} f := Over.homMk f.left (by
    have e : (yoneda.map f.left ≫ Y.hom).app (op X.left) (𝟙 X.left) =
        (X.hom ≫ (Functor.fromPUnit (yoneda.obj A)).map f.right).app
        (op X.left) (𝟙 X.left) := by simp [f.w]
    simp [- CommaMorphism.w] at e
    simpa)

@[simps!]
def inverse : Over A ⥤ CostructuredArrow yoneda (yoneda.obj A) where
  obj X := CostructuredArrow.mk (yoneda.map X.hom)
  map {X Y} f := CostructuredArrow.homMk f.left

@[simps!]
def unitIso : 𝟭 (CostructuredArrow yoneda (yoneda.obj A)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun X => Comma.isoMk (Iso.refl _) (Iso.refl _)
  (by cat_disch))

@[simps!]
def counitIso : inverse ⋙ functor (A := A) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => Over.isoMk (Iso.refl _))

end costructuredArrowYonedaEquivOver

open costructuredArrowYonedaEquivOver

@[simps]
def costructuredArrowYonedaEquivOver :
    CostructuredArrow yoneda (yoneda.obj A) ≌ CategoryTheory.Over A where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

@[simps!]
def overYonedaEquivPresheafOver : CategoryTheory.Over (yoneda.obj (A)) ≌
    ((CategoryTheory.Over A)ᵒᵖ ⥤ Type v) :=
  (overEquivPresheafCostructuredArrow (yoneda.obj A)).trans
  costructuredArrowYonedaEquivOver.op.congrLeft

end CategoryTheory
