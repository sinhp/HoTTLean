/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Relation of morphism properties with limits

The following predicates are introduces for morphism properties `P`:
* `IsStableUnderBaseChange`: `P` is stable under base change if in all pullback
  squares, the left map satisfies `P` if the right map satisfies it.
* `IsStableUnderCobaseChange`: `P` is stable under cobase change if in all pushout
  squares, the right map satisfies `P` if the left map satisfies it.

We define `P.universally` for the class of morphisms which satisfy `P` after any base change.

We also introduce properties `IsStableUnderProductsOfShape`, `IsStableUnderLimitsOfShape`,
`IsStableUnderFiniteProducts`, and similar properties for colimits and coproducts.

-/

universe w w' v u

namespace CategoryTheory

open Category Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

section

variable (P : MorphismProperty C)

/-- `P.HasPullbacksAlong f` states that for any morphism satifying `P` with the same codomain
as `f`, the pullback of that morphism along `f` exists. -/
protected class HasPullbacksAlong {X Y : C} (f : X ⟶ Y) : Prop where
  hasPullback {W} (g : W ⟶ Y) : P g → HasPullback g f

variable {P}

theorem baseChange_map' [IsStableUnderBaseChange P] {S S' X Y : C} (f : S' ⟶ S)
    {v₁₂ : X ⟶ S} {v₂₂ : Y ⟶ S} {g : X ⟶ Y} (hv₁₂ : v₁₂ = g ≫ v₂₂) [HasPullback v₁₂ f]
    [HasPullback v₂₂ f] (H : P g) : P (pullback.lift (f := v₂₂) (g := f) (pullback.fst v₁₂ f ≫ g)
    (pullback.snd v₁₂ f) (by simp [pullback.condition, ← hv₁₂])) := by
  subst hv₁₂
  refine of_isPullback (f' := pullback.fst (g ≫ v₂₂) f)
    (f := pullback.fst v₂₂ f) ?_ H
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback v₂₂ f)
  simpa using IsPullback.of_hasPullback (g ≫ v₂₂) f

local instance {S X Y : C} {f : X ⟶ S} [HasPullbacksAlong f] {g : Y ⟶ S} :
    HasPullback f g := hasPullback_symmetry g f

instance [P.HasPullbacks] {X Y : C} {f : X ⟶ Y} : P.HasPullbacksAlong f where
  hasPullback _ := hasPullback _

instance [P.IsStableUnderBaseChange] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] : P.HasPullbacksAlong (f ≫ g) where
  hasPullback h p :=
    have : HasPullback h g := HasPullbacksAlong.hasPullback h p
    have : HasPullback (pullback.snd h g) f := HasPullbacksAlong.hasPullback (pullback.snd h g)
      (P.pullback_snd h g p)
    IsPullback.hasPullback (IsPullback.paste_horiz (IsPullback.of_hasPullback
      (pullback.snd h g) f) (IsPullback.of_hasPullback h g))

/-- A morphism property satisfies `ContainsObjects` when any map `! : X ⟶ Y` to a terminal
object `Y` satisfies the morphism property. -/
class HasObjects (P : MorphismProperty C) : Prop where
  obj_mem {X Y} (f : X ⟶ Y) : Limits.IsTerminal Y → P f

end

end MorphismProperty

end CategoryTheory
