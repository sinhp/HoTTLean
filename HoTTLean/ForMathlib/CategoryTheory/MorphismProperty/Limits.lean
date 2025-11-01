import Mathlib.CategoryTheory.MorphismProperty.Limits

universe w w' v u

namespace CategoryTheory

open Category Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

section

variable (P : MorphismProperty C)

notation E " ⟶("P") " B => (p : E ⟶ B) ×' P p

/-- `P.HasPullback f` means that all morphisms satisfying morphism property `P`
have pullbacks along `f`. -/
protected class HasPullback {X Y : C} (f : X ⟶ Y) : Prop where
  hasPullback {W} (g : W ⟶ Y) : P g → HasPullback g f := by infer_instance

variable {P} in
/-- Bundling `g : W ⟶ Y` and `P g` into `g : W ⟶(P) Y` allows for typeclass inference
involving the proposition `P g`. -/
lemma hasPullback' {X Y : C} {f : X ⟶ Y}
    (h : ∀ {W} (g : W ⟶(P) Y), HasPullback g.1 f) : P.HasPullback f where
  hasPullback g hg := h ⟨g, hg⟩

instance {X Y : C} (f : X ⟶ Y) [P.HasPullback f] {W : C} (g : W ⟶(P) Y) : HasPullback g.1 f :=
  HasPullback.hasPullback g.1 g.2

instance {X Y : C} (f : X ⟶ Y) [∀ {W : C} (h : W ⟶(P) Y), HasPullback h.1 f] :
    P.HasPullback f := hasPullback' inferInstance

instance [P.IsStableUnderBaseChange] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.HasPullback f] [P.HasPullback g] : P.HasPullback (f ≫ g) :=
  hasPullback' <| fun h =>
  have {W : C} (h : W ⟶(P) Y) : HasPullback h.1 f := inferInstance
  IsPullback.hasPullback
    (IsPullback.paste_horiz (IsPullback.of_hasPullback
    (⟨ (pullback.snd h.1 g) , of_isPullback (IsPullback.of_hasPullback h.1 g) h.2 ⟩
    : (pullback h.1 g) ⟶(P) Y).1 f)
    (IsPullback.of_hasPullback h.1 g))

instance (priority := 900) [IsStableUnderBaseChange P] : RespectsIso P := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e hf
  refine MorphismProperty.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w)) hf

instance [P.IsStableUnderBaseChange] {X Y Z}
    (f : X ⟶ Y) (g : Y ⟶ Z) [P.HasPullback f] [P.HasPullback g] {W} (h : W ⟶(P) Z) :
    HasPullback (pullback.snd h.1 g) f :=
  let p : pullback h.1 g ⟶(P) Y := ⟨pullback.snd h.1 g, pullback_snd _ _ h.2⟩
  have {W} (h : W ⟶(P) Y) : HasPullback h.1 f := inferInstance
  inferInstanceAs (HasPullback p.1 f)

theorem pullback_map'
    [IsStableUnderBaseChange P] [P.IsStableUnderComposition] {S X X' Y Y' : C}
    {f : X ⟶ S} {g : Y ⟶ S} [∀ {W} (h : W ⟶ S), HasPullback f h]
    {f' : X' ⟶ S} {g' : Y' ⟶ S} [∀ {W} (h : W ⟶ S), HasPullback h g']
    {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'} (h₁ : P i₁) (h₂ : P i₂)
    (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂)) := by
  have inst {W} (h : W ⟶ _): HasPullback h f := hasPullback_symmetry _ _
  have inst {W} (h : W ⟶ _): HasPullback (Over.mk f).hom h := inferInstanceAs (HasPullback f h)
  have inst {W} (h : W ⟶ _): HasPullback h (Over.mk f).hom := hasPullback_symmetry _ _
  have :
    pullback.map f g f' g' i₁ i₂ (𝟙 _) ((Category.comp_id _).trans e₁)
        ((Category.comp_id _).trans e₂) =
      ((pullbackSymmetry _ _).hom ≫
          ((Over.pullback _).map (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g')).left) ≫
        (pullbackSymmetry _ _).hom ≫
          ((Over.pullback g').map (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f')).left := by
    ext <;> simp
  rw [this]
  apply P.comp_mem <;> rw [P.cancel_left_of_respectsIso]
  · simpa [pullback.map] using baseChange_map _ (Over.homMk _ e₂.symm : Over.mk g ⟶ Over.mk g') h₂
  · simpa [pullback.map] using baseChange_map _ (Over.homMk _ e₁.symm : Over.mk f ⟶ Over.mk f') h₁

end

/-- A morphism property satisfies `ContainsObjects` when any map `! : X ⟶ Y` to a terminal
object `Y` satisfies the morphism property. -/
class HasObjects (P : MorphismProperty C) : Prop where
  obj_mem {X Y} (f : X ⟶ Y) : Limits.IsTerminal Y → P f

end MorphismProperty
end CategoryTheory
