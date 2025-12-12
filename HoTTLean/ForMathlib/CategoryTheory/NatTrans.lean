import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.TwoSquare
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import HoTTLean.ForMathlib
import Poly.ForMathlib.CategoryTheory.NatTrans

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory
namespace NatTrans

section
variable {A : Type u} [Category.{v} A] {B: Type u₁} [Groupoid.{v₁} B]
    {F G : A ⥤ B} (h : NatTrans F G)

-- NOTE not sure if this is the best way to organize this
@[simps] def isoOfCodGroupoid : F ≅ G where
  hom := h
  inv := {app a := Groupoid.inv (h.app a)}

def inv : G ⟶ F := h.isoOfCodGroupoid.inv

@[simp] lemma inv_vcomp : h.inv.vcomp h = NatTrans.id G := by
  ext a
  simp [NatTrans.inv]

@[simp] lemma vcomp_inv : h.vcomp h.inv = NatTrans.id F := by
  ext a
  simp [NatTrans.inv]

end

open Functor

lemma hext {A : Type u} [Category.{v} A] {B : Type u₁} [Category.{v₁} B]
    {F F' G G' : A ⥤ B} (α : F ⟶ G) (β : F' ⟶ G')
    (hF : F = F') (hG : G = G') (happ : ∀ x, α.app x ≍ β.app x) :
    α ≍ β := by
  aesop_cat

end NatTrans

instance {A : Type*} [Category A] {B : Type*} [Groupoid B] :
    Groupoid (A ⥤ B) where
  inv nt := nt.inv
  inv_comp := NatTrans.inv_vcomp
  comp_inv := NatTrans.vcomp_inv

end CategoryTheory

namespace CategoryTheory

universe v' u' v₄ v₅ v₆ v₇ v₈ u₄ u₅ u₆ u₇ u₈

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {K : Type*} [Category K] {D : Type*} [Category D]

namespace NatTrans
namespace IsCartesian

open TwoSquare

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
variable {C₅ : Type u₅} {C₆ : Type u₆} {C₇ : Type u₇} {C₈ : Type u₈}
  [Category.{v₅} C₅] [Category.{v₆} C₆] [Category.{v₇} C₇] [Category.{v₈} C₈]
  {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}

theorem vCompIsIso {w : TwoSquare T L R B} [IsIso w] {w' : TwoSquare B L' R'' B''} :
    IsCartesian w' → IsCartesian (w ≫ᵥ w') :=
  fun cw' =>
    (isCartesian_of_isIso _).comp <|
    (isCartesian_of_isIso _).comp <|
    (isCartesian_of_isIso _).comp <|
    (IsCartesian.whiskerLeft cw' _).comp
    (isCartesian_of_isIso _)
