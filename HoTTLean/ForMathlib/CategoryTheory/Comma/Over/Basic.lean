import Mathlib.CategoryTheory.Comma.Over.Basic
import HoTTLean.ForMathlib.CategoryTheory.Comma.Basic

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

-- morphism levels before object levels. See note [category theory universes].
variable {T : Type u₁} [Category.{v₁} T]
variable {D : Type u₂} [Category.{v₂} D]

lemma Over.ext_of_iso {X : T} {U V : Over X} (e : U ≅ V) (obj_left : U.left = V.left)
    (hom_left : e.hom.left = eqToHom obj_left) : U = V :=
  Comma.ext_of_iso e obj_left (by simp) hom_left (by cat_disch)
