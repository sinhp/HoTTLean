import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.TwoSquare
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import HoTTLean.ForMathlib

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
end NatTrans

instance {A : Type*} [Category A] {B : Type*} [Groupoid B] :
    Groupoid (A ⥤ B) where
  inv nt := nt.inv
  inv_comp := NatTrans.inv_vcomp
  comp_inv := NatTrans.vcomp_inv

end CategoryTheory


/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

open CategoryTheory Limits IsPullback

namespace CategoryTheory

universe v' u'

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {K : Type*} [Category K] {D : Type*} [Category D]

namespace NatTrans

open Functor

-- /-- A natural transformation is *cartesian*
-- if all its naturality squares are pullbacks. -/
-- def IsCartesian {F G : J ⥤ C} (α : F ⟶ G) : Prop :=
--   ∀ ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)

-- theorem isCartesian_of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : IsCartesian α :=
--   fun _ _ f => IsPullback.of_vert_isIso ⟨NatTrans.naturality _ f⟩

-- theorem isIso_of_isCartesian [HasTerminal J] {F G : J ⥤ C} (α : F ⟶ G) (hα : IsCartesian α)
--     [IsIso (α.app (⊤_ J))] : IsIso α := by
--   refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ α
--     (fun j ↦ isIso_snd_of_isIso <| hα <| terminal.from j)

-- theorem isCartesian_of_discrete {ι : Type*} {F G : Discrete ι ⥤ C}
--     (α : F ⟶ G) : IsCartesian α := by
--   rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
--   simp only [Discrete.functor_map_id]
--   exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

-- theorem isCartesian_of_isPullback_to_terminal [HasTerminal J] {F G : J ⥤ C} (α : F ⟶ G)
--     (pb : ∀ j,
--     IsPullback (F.map (terminal.from j)) (α.app j) (α.app (⊤_ J)) (G.map (terminal.from j))) :
--     IsCartesian α := by
--   intro i j f
--   apply IsPullback.of_right (h₁₂ := F.map (terminal.from j)) (h₂₂ := G.map (terminal.from j))
--   simpa [← F.map_comp, ← G.map_comp]  using (pb i)
--   exact α.naturality f
--   exact pb j

-- namespace IsCartesian

-- theorem comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : IsCartesian α) (hβ : IsCartesian β) :
--     IsCartesian (α ≫ β) :=
--   fun _ _ f => (hα f).paste_vert (hβ f)

-- theorem whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : IsCartesian α) (H : C ⥤ D)
--     [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) H] :
--     IsCartesian (whiskerRight α H) :=
--   fun _ _ f => (hα f).map H

-- theorem whiskerLeft {K : Type*} [Category K] {F G : J ⥤ C}
--     {α : F ⟶ G} (hα : IsCartesian α) (H : K ⥤ J) : IsCartesian (whiskerLeft H α) :=
--   fun _ _ f => hα (H.map f)

-- theorem hcomp {K : Type*} [Category K] {F G : J ⥤ C} {M N : C ⥤ K} {α : F ⟶ G} {β : M ⟶ N}
--     (hα : IsCartesian α) (hβ : IsCartesian β)
--     [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) M] :
--     IsCartesian (NatTrans.hcomp α β) := by
--   have ha := hα.whiskerRight M
--   have hb := hβ.whiskerLeft G
--   have hc := ha.comp hb
--   unfold IsCartesian
--   intros i j f
--   specialize hc f
--   simp only [Functor.comp_obj, Functor.comp_map, comp_app,
--     whiskerRight_app, whiskerLeft_app,
--     naturality] at hc
--   exact hc

-- open TwoSquare

-- universe v₄ v₅ v₆ v₇ v₈ u₄ u₅ u₆ u₇ u₈

-- variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
--   [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
--   {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
-- variable {C₅ : Type u₅} {C₆ : Type u₆} {C₇ : Type u₇} {C₈ : Type u₈}
--   [Category.{v₅} C₅] [Category.{v₆} C₆] [Category.{v₇} C₇] [Category.{v₈} C₈]
--   {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}

-- theorem vComp {w : TwoSquare T L R B} {w' : TwoSquare B L' R'' B''}
--     [∀ (i j : C₁) (f : j ⟶ i), PreservesLimit (cospan (w.app i) ((L ⋙ B).map f)) R''] :
--     IsCartesian w → IsCartesian w' → IsCartesian (w ≫ᵥ w') :=
--   fun cw cw' =>
--     (isCartesian_of_isIso _).comp <|
--     (cw.whiskerRight _).comp <|
--     (isCartesian_of_isIso _).comp <|
--     (cw'.whiskerLeft _).comp <|
--     (isCartesian_of_isIso _)

-- theorem hComp {w : TwoSquare T L R B} {w' : TwoSquare T' R R' B'}
--     [∀ (i j : C₁) (f : j ⟶ i), PreservesLimit (cospan (w.app i) ((L ⋙ B).map f)) B'] :
--     IsCartesian w → IsCartesian w' → IsCartesian (w ≫ₕ w') :=
--   fun cw cw' =>
--     (isCartesian_of_isIso _).comp <|
--     (cw'.whiskerLeft _).comp <|
--     (isCartesian_of_isIso _).comp <|
--     (cw.whiskerRight _).comp <|
--     (isCartesian_of_isIso _)

-- end IsCartesian

lemma hext {A : Type u} [Category.{v} A] {B: Type u₁} [Groupoid.{v₁} B]
    {F F' G G' : A ⥤ B} (α : F ⟶ G) (β : F' ⟶ G')
    (hF : F = F') (hG : G = G') (happ : ∀ x, α.app x ≍ β.app x) :
    α ≍ β := by
  aesop_cat

end NatTrans
