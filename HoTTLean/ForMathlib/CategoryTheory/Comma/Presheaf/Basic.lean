import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.Tactic.DepRewrite
import HoTTLean.ForMathlib
import HoTTLean.ForMathlib.CategoryTheory.Adjunction.Basic
import HoTTLean.ForMathlib.CategoryTheory.Yoneda

namespace CategoryTheory

open Category Opposite

universe w v u u₁

section

attribute [local simp] CategoryTheory.Yoneda.fullyFaithful_preimage

namespace costructuredArrowYonedaEquivOver

variable {C : Type u} [Category.{v} C] {A : C}

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

variable {C : Type u} [Category.{v} C] {A : C}

@[simps]
def costructuredArrowYonedaEquivOver :
    CostructuredArrow yoneda (yoneda.obj A) ≌ CategoryTheory.Over A where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

def costructuredArrowYonedaEquivOver.inverseCompToOverIso :
    inverse ⋙ CostructuredArrow.toOver yoneda (yoneda.obj A) ≅ Over.post yoneda :=
  Iso.refl _

def overYonedaEquivPresheafOver :
    CategoryTheory.Over (yoneda.obj A) ≌ ((CategoryTheory.Over A)ᵒᵖ ⥤ Type v) :=
  (overEquivPresheafCostructuredArrow (yoneda.obj A)).trans
  costructuredArrowYonedaEquivOver.op.congrLeft

def overYonedaEquivPresheafOver.functorObjMkYonedaIso (B : Over A) :
    overYonedaEquivPresheafOver.functor.obj (Over.mk (yoneda.map B.hom)) ≅ yoneda.obj B :=
  calc overYonedaEquivPresheafOver.functor.obj (Over.mk (yoneda.map B.hom))
  _ ≅ _ := Functor.isoWhiskerLeft inverse.op <|
    (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow (yoneda.obj A)).app
    (.mk (yoneda.map B.hom))
  _ ≅ yoneda.obj B := NatIso.ofComponents (fun X =>
      costructuredArrowYonedaEquivOver.fullyFaithfulInverse.homEquiv.symm.toIso)
    (fun {X Y} f => by
      ext a
      simp only [Equiv.toIso_hom, types_comp_apply]
      erw [Functor.FullyFaithful.homEquiv_symm_apply, Functor.FullyFaithful.homEquiv_symm_apply]
      simp)

def overYonedaEquivPresheafOver.yonedaObjFunctorObjIso (X : Over y(A)) :
    y(overYonedaEquivPresheafOver.functor.obj X) ≅
    overYonedaEquivPresheafOver.inverse.op ⋙ yoneda.obj X :=
  (overYonedaEquivPresheafOver.symm.toAdjunction.representableBy X).toIso

def overYonedaEquivPresheafOver.postYonedaCompFunctorIso :
    Over.post yoneda ⋙ (overYonedaEquivPresheafOver (A := A)).functor ≅ yoneda :=
  calc _
  _ ≅ (inverse ⋙ CostructuredArrow.toOver yoneda (yoneda.obj A)) ⋙
      (overYonedaEquivPresheafOver (A := A)).functor :=
    Functor.isoWhiskerRight inverseCompToOverIso _
  _ ≅ ((inverse ⋙ CostructuredArrow.toOver yoneda (yoneda.obj A)) ⋙
      (overEquivPresheafCostructuredArrow y(A)).functor) ⋙
      costructuredArrowYonedaEquivOver.op.congrLeft.functor :=
    (Functor.associator ..).symm
  _ ≅ (inverse ⋙ (CostructuredArrow.toOver yoneda (yoneda.obj A)) ⋙
      (overEquivPresheafCostructuredArrow y(A)).functor) ⋙
      costructuredArrowYonedaEquivOver.op.congrLeft.functor :=
    Functor.isoWhiskerRight (Functor.associator ..) _
  _ ≅ (inverse ⋙ yoneda) ⋙ costructuredArrowYonedaEquivOver.op.congrLeft.functor :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft _
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow ..)) _
  _ ≅ inverse ⋙ yoneda ⋙ costructuredArrowYonedaEquivOver.op.congrLeft.functor :=
    Functor.associator ..
  _ ≅ inverse ⋙ functor ⋙ yoneda :=
    Functor.isoWhiskerLeft _ costructuredArrowYonedaEquivOver.yonedaCompCongrLeftFunctorIso
  _ ≅ 𝟭 _ ⋙ yoneda :=
    (Functor.associator ..).symm ≪≫ Functor.isoWhiskerRight counitIso _
  _ ≅ yoneda :=
    yoneda.leftUnitor

def overYonedaEquivPresheafOver.yonedaCompInverseIso :
    yoneda ⋙ (overYonedaEquivPresheafOver (A := A)).inverse ≅ Over.post yoneda :=
  (overYonedaEquivPresheafOver.isoCompInverse postYonedaCompFunctorIso).symm

end

section

variable {C : Type u} [SmallCategory C] {A : C} {D : Type*} [Category D]

open overYonedaEquivPresheafOver

/-
noncomputable def Over.yonedaIsoMk {X Y : Over (yoneda.obj A)}
    (α : (post yoneda).op ⋙ y(X) ≅ (post yoneda).op ⋙ y(Y)) :
    X ≅ Y :=
  let β (X) : yoneda.op ⋙ y(overYonedaEquivPresheafOver.functor.obj X) ≅
    (Over.post yoneda).op ⋙ yoneda.obj X :=
  calc yoneda.op ⋙ y(overYonedaEquivPresheafOver.functor.obj X)
    _ ≅ yoneda.op ⋙ overYonedaEquivPresheafOver.inverse.op ⋙ yoneda.obj X :=
      yoneda.op.isoWhiskerLeft (yonedaObjFunctorObjIso X)
    _ ≅ (yoneda.op ⋙ overYonedaEquivPresheafOver.inverse.op) ⋙ yoneda.obj X :=
      (Functor.associator ..).symm
    _ ≅ (yoneda ⋙ overYonedaEquivPresheafOver.inverse).op ⋙ yoneda.obj X :=
      Functor.isoWhiskerRight (Functor.opComp ..).symm _
    _ ≅ (Over.post yoneda).op ⋙ yoneda.obj X :=
      Functor.isoWhiskerRight (NatIso.op yonedaCompInverseIso.symm) _
  overYonedaEquivPresheafOver.functor.preimageIso
  (NatIso.yonedaMk (β X ≪≫ α ≪≫ (β Y).symm))
-/

/-- The natural hom-set bijection as an isomorphism of profunctors
```
  Psh(Over A) (y(-), overYonedaEquivPresheafOver.functor (⋆)) ≅
  Over (y(A)) (yoneda ⋙ inverse (-), ⋆) ≅
  Over (y(A)) (Over.post yoneda (-), ⋆)
```
-/
def overYonedaEquivPresheafOver.homIso : overYonedaEquivPresheafOver.functor ⋙ yoneda ⋙
    (Functor.whiskeringLeft (Over A)ᵒᵖ ((Over A)ᵒᵖ ⥤ Type u)ᵒᵖ (Type u)).obj yoneda.op ≅
    yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.post yoneda).op :=
  calc overYonedaEquivPresheafOver.functor ⋙ yoneda ⋙
    (Functor.whiskeringLeft _ _ _).obj yoneda.op
    -- `Psh(Over A) (y(-), functor (⋆))`
    _ ≅ (overYonedaEquivPresheafOver.functor ⋙ yoneda) ⋙
        (Functor.whiskeringLeft _ _ _).obj yoneda.op :=
      (Functor.associator ..).symm
    -- `Over (y(A)) (yoneda ⋙ inverse (-), ⋆)`
    _ ≅ (yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj overYonedaEquivPresheafOver.inverse.op) ⋙
        (Functor.whiskeringLeft _ _ _).obj yoneda.op :=
      Functor.isoWhiskerRight overYonedaEquivPresheafOver.symm.toAdjunction.homIso.symm _
    _ ≅ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj overYonedaEquivPresheafOver.inverse.op ⋙
        (Functor.whiskeringLeft _ _ _).obj yoneda.op :=
      Functor.associator ..
    _ ≅ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
        (yoneda.op ⋙ overYonedaEquivPresheafOver.inverse.op) :=
    Functor.isoWhiskerLeft _ (Functor.whiskeringLeftObjCompIso ..).symm
    _ ≅ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
        (yoneda ⋙ overYonedaEquivPresheafOver.inverse).op :=
      Functor.isoWhiskerLeft _ (Functor.mapIso _ (Functor.opComp ..).symm)
    -- `Over (y(A)) (Over.post yoneda (-), ⋆)`
    _ ≅ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.post yoneda).op :=
      Functor.isoWhiskerLeft _ (Functor.mapIso _
        (NatIso.op overYonedaEquivPresheafOver.yonedaCompInverseIso.symm))

/-- To show that `F ≅ G : D ⥤ Over (yoneda.obj A)`
it suffices to show the natural isomorphism of profunctors
`Over (y(A)) (Over.post yoneda (-), F(⋆)) ≅ Over (y(A)) (Over.post yoneda (-), G(⋆))` -/
def Over.yonedaNatIsoMk {F G : D ⥤ Over (yoneda.obj A)}
    (α : F ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.post yoneda).op ≅
      G ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.post yoneda).op) :
    F ≅ G :=
  -- `Psh(Over A) (y(-), F ⋙ functor (⋆)) ≅ Over (y(A)) (Over.post yoneda (-), F(⋆))`
  let β (F) : (F ⋙ (overYonedaEquivPresheafOver).functor) ⋙
        yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj yoneda.op ≅
      F ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.post yoneda).op :=
    (Functor.associator ..).symm ≪≫ Functor.isoWhiskerLeft F overYonedaEquivPresheafOver.homIso
  -- to show `F ≅ G : D ⥤ Over (yoneda.obj A)`
  (overYonedaEquivPresheafOver.fullyFaithfulFunctor.whiskeringRight _).preimageIso
  -- it suffices to compose with the equivalence
  -- `overYonedaEquivPresheafOver : Over (y(A)) ≌ Psh (Over A)` and show
  -- `F ⋙ overYonedaEquivPresheafOver.functor ≅ G ⋙ overYonedaEquivPresheafOver.functor`
  (functorToPresheafIsoMk (β F ≪≫ α ≪≫ (β G).symm))
  -- an isomorphism `F ⋙ functor ≅ G ⋙ functor : Psh C` amounts to
  -- an isomorphism `Psh(Over A) (y(-), F ⋙ functor (⋆)) ≅ Psh(Over A) (y(-), G ⋙ functor (⋆))`
  -- amounts to
  -- an isomorphism `Over (y(A)) (Over.post yoneda (-), F(⋆)) ≅ Over (y(A)) (Over.post yoneda (-), G(⋆))`

end

end CategoryTheory
