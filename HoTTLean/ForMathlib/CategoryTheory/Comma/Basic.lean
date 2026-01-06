import Mathlib.CategoryTheory.Comma.Basic


namespace CategoryTheory

open Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable {A' : Type u₄} [Category.{v₄} A']
variable {B' : Type u₅} [Category.{v₅} B']
variable {T' : Type u₆} [Category.{v₆} T']
variable {L : A ⥤ T} {R : B ⥤ T}

private lemma Comma.ext {X Y : Comma L R}
    (hleft : X.left = Y.left) (hright : X.right = Y.right)
    (hhom : X.hom ≫ R.map (eqToHom hright) = L.map (eqToHom hleft) ≫ Y.hom) :
    X = Y := by
  cases X; cases Y
  rw [← heq_eq_eq, eqToHom_map, eqToHom_map, comp_eqToHom_heq_iff, heq_eqToHom_comp_iff] at hhom
  congr

lemma Comma.ext_of_iso {X Y : Comma L R} (e : X ≅ Y)
    (obj_left : X.left = Y.left) (obj_right : X.right = Y.right)
    (hom_left : e.hom.left = eqToHom obj_left) (hom_right : e.hom.right = eqToHom obj_right) :
    X = Y :=
  Comma.ext obj_left obj_right <| by rw [← hom_left, ← hom_right, e.hom.w]
