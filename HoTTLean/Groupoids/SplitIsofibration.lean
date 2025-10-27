import HoTTLean.ForMathlib.CategoryTheory.SplitIsofibration

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

namespace CategoryTheory

open Functor.Groupoidal

namespace Grpd

def SplitIsofibration : MorphismProperty Grpd :=
  fun _ _ F => ∃ I : F.ClovenIsofibration, I.IsSplit

namespace SplitIsofibration

variable {B A : Grpd} {F : B ⟶ A} (hF : SplitIsofibration F)

def splitIsofibration : F.ClovenIsofibration := hF.choose

instance : (splitIsofibration hF).IsSplit := hF.choose_spec

/-- The Grothendieck construction on the classifier is isomorphic to `E`,
now as objects in `Grpd`. -/
def grothendieckClassifierIso : Grpd.of (∫ hF.splitIsofibration.classifier) ≅ B :=
  Grpd.mkIso (Functor.ClovenIsofibration.grothendieckClassifierIso ..)

/-lemma ι_classifier_comp_forget {x} : ι I.classifier x ⋙ Groupoidal.forget =
    Fiber.fiberInclusion ⋙ F
    -/
lemma grothendieckClassifierIso_inv_comp_forget :
    hF.grothendieckClassifierIso.inv ⋙ homOf Functor.Groupoidal.forget = F := by
  apply Functor.ClovenIsofibration.grothendieckClassifierIso.inv_comp_forget


end SplitIsofibration

instance : SplitIsofibration.IsStableUnderBaseChange.{u,u} where
    of_isPullback pb hG :=
  ⟨ Functor.ClovenIsofibration.ofIsPullback _ _ _ _
    (Grpd.functorIsPullback pb) hG.splitIsofibration, inferInstance ⟩

instance : SplitIsofibration.IsMultiplicative where
  id_mem _ := ⟨ Functor.ClovenIsofibration.id _, inferInstance ⟩
  comp_mem _ _ hF hG := ⟨ Functor.ClovenIsofibration.comp
    hF.splitIsofibration hG.splitIsofibration, inferInstance ⟩

instance : SplitIsofibration.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun X Y F hF =>
  ⟨ Functor.ClovenIsofibration.iso {
    hom := F
    inv := have : IsIso F := hF; CategoryTheory.inv F
    hom_inv_id := by simp [← Grpd.comp_eq_comp]
    inv_hom_id := by simp [← Grpd.comp_eq_comp] },
    inferInstance⟩)
