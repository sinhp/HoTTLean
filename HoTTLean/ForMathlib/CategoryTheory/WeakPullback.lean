import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

noncomputable section

namespace CategoryTheory

open Limits

structure WeakPullback {C : Type*} [Category C]
    {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    extends CommSq fst snd f g where
  lift {W : C} (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) : W ⟶ P
  lift_fst' {W : C} (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) : lift a b h ≫ fst = a
  lift_snd' {W : C} (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) : lift a b h ≫ snd = b

namespace WeakPullback

variable {C : Type*} [Category C]
    {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (wp : WeakPullback fst snd f g)

class IsCoherent : Prop where
  comp_left {W W' : C} {σ : W' ⟶ W}
    {a : W ⟶ X} {b : W ⟶ Y} (h : a ≫ f = b ≫ g)
    {a' : W' ⟶ X} {b' : W' ⟶ Y}
    (σ_a : σ ≫ a = a') (σ_b : σ ≫ b = b') :
    σ ≫ wp.lift a b h = wp.lift a' b' (by simp [h, ← σ_a, ← σ_b])

variable {W : C} (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g)

@[simp]
lemma lift_fst : wp.lift a b h ≫ fst = a := lift_fst' _ _ _ _

@[simp]
lemma lift_snd : wp.lift a b h ≫ snd = b := lift_snd' _ _ _ _

def coherentLift [HasPullback f g] : W ⟶ P :=
  pullback.lift a b h ≫ wp.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition

@[simp]
lemma coherentLift_fst [HasPullback f g] : wp.coherentLift a b h ≫ fst = a := by
  simp [coherentLift]

@[simp]
lemma coherentLift_snd [HasPullback f g] : wp.coherentLift a b h ≫ snd = b := by
  simp [coherentLift]

lemma coherentLift_comp_left [HasPullback f g]
    {W W' : C} {σ : W' ⟶ W}
    {a : W ⟶ X} {b : W ⟶ Y} (h : a ≫ f = b ≫ g)
    {a' : W' ⟶ X} {b' : W' ⟶ Y} (σ_a : σ ≫ a = a') (σ_b : σ ≫ b = b') :
    σ ≫ wp.coherentLift a b h =
    wp.coherentLift a' b' (by simp [h, ← σ_a, ← σ_b]) := by
  subst σ_a σ_b
  simp only [coherentLift, ← Category.assoc]
  congr 1; ext <;> simp

def coherent [HasPullback f g] :
    WeakPullback fst snd f g where
  w := wp.w
  lift a b h := coherentLift wp a b h
  lift_fst' a b h := coherentLift_fst wp a b h
  lift_snd' a b h := coherentLift_snd wp a b h

instance [HasPullback f g] : IsCoherent (coherent wp) where
  comp_left h _ _ σ_a σ_b :=
  coherentLift_comp_left wp h σ_a σ_b

end WeakPullback
end CategoryTheory
end
