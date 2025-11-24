import Mathlib.CategoryTheory.Adjunction.Basic

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂}

def Adjunction.homIso [Category.{v₁} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (F.op) ≅ G ⋙ yoneda :=
  NatIso.ofComponents
  (fun X => (adj.representableBy X).toIso.symm)
  (fun {X Y} f => by ext; simp [Functor.RepresentableBy.toIso, Functor.representableByEquiv,
    adj.homEquiv_naturality_right])

namespace Equivalence

variable [Category.{v₂} D] {e : C ≌ D}

def isoCompInverse {J : Type*} [Category J] {X : J ⥤ C} {Y : J ⥤ D} (α : X ⋙ e.functor ≅ Y) :
    X ≅ Y ⋙ e.inverse :=
  calc X
  _ ≅ X ⋙ 𝟭 _ := X.rightUnitor.symm
  _ ≅ X ⋙ e.functor ⋙ e.inverse := Functor.isoWhiskerLeft X e.unitIso
  _ ≅ (X ⋙ e.functor) ⋙ e.inverse := Functor.associator ..
  _ ≅ Y ⋙ e.inverse := Functor.isoWhiskerRight α e.inverse

@[simp]
lemma isoCompInverse_hom_app {J : Type*} [Category J] {X : J ⥤ C} {Y : J ⥤ D}
    (α : X ⋙ e.functor ≅ Y) (A : J) :
    (isoCompInverse α).hom.app A = e.unitIso.hom.app (X.obj A) ≫ e.inverse.map (α.hom.app A) := by
  simp [isoCompInverse, Trans.trans]

@[simp]
lemma isoCompInverse_inv_app {J : Type*} [Category J] {X : J ⥤ C} {Y : J ⥤ D}
    (α : X ⋙ e.functor ≅ Y) (A : J) :
    (isoCompInverse α).inv.app A = e.inverse.map (α.inv.app A) ≫ e.unitIso.inv.app (X.obj A) := by
  simp [isoCompInverse, Trans.trans]

@[simps]
def compFunctorNatIsoEquiv {J : Type*} [Category J] (X : J ⥤ C) (Y : J ⥤ D) :
    (X ⋙ e.functor ≅ Y) ≃ (X ≅ Y ⋙ e.inverse) where
  toFun := isoCompInverse
  invFun α := (e.symm.isoCompInverse α.symm).symm
  left_inv := by cat_disch
  right_inv := by cat_disch
