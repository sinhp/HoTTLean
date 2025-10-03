import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import HoTTLean.ForMathlib.CategoryTheory.Grpd
import HoTTLean.ForMathlib.CategoryTheory.FreeGroupoid
import HoTTLean.Groupoids.Pi

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

namespace GroupoidModel.FunctorOperation.pi

open CategoryTheory Functor.Groupoidal

variable {Γ : Type u} {Δ : Type u} [Groupoid.{v} Γ] [Groupoid.{v} Δ] {σ : Δ ⥤ Γ}
  {A : Γ ⥤ Grpd.{u₁,u₁}} (B : ∫ A ⥤ Grpd.{u₁,u₁})

/-- lifts of `σ : Δ ⥤ Γ` along `forget : ∫ pi A B ⥤ Γ`
biject (since the Grothendieck construction is a pullback) with
lifts of `pi (σ ⋙ A) (pre A σ ⋙ B) : Δ ⥤ Grpd` along `forgetToGrpd : PGrpd ⥤ Grpd`
biject (via `lam` and `inversion`) with
lifts of `pre A σ ⋙ B : ∫ σ ⋙ A ⥤ Grpd` along `forgetToGrpd : PGrpd ⥤ Grpd`
biject (since the Grothendieck construction is a pullback) with
lifts of `pre A σ : ∫ σ ⋙ A ⥤ ∫ A` along `forget : ∫ B ⥤ ∫ A`.

The function `equivFun` is the forward direction in this bijection.
The function `equivInv` is the inverse direction in this bijection.
-/
def equivFun (F : Δ ⥤ ∫ pi A B) (hF : F ⋙ forget = σ) : ∫ σ ⋙ A ⥤ ∫ B :=
  (isPullback B).lift (inversion (pre A σ ⋙ B) (F ⋙ toPGrpd _) (by
    rw [Functor.assoc, toPGrpd_forgetToGrpd, ← Functor.assoc, hF, pi_naturality]))
  (pre A σ) (inversion_comp_forgetToGrpd ..)

lemma equivFun_comp_forget (F : Δ ⥤ ∫ pi A B) (hF : F ⋙ forget = σ) :
    equivFun B F hF ⋙ forget = pre A σ := by
  simp [equivFun, Functor.IsPullback.fac_right]

@[inherit_doc equivFun]
def equivInv (G : ∫ σ ⋙ A ⥤ ∫ B) (hG : G ⋙ forget = pre A σ) : Δ ⥤ ∫ pi A B :=
  (isPullback (pi A B)).lift (lam (σ ⋙ A) (G ⋙ toPGrpd _)) σ (by
    rw [lam_comp_forgetToGrpd, pi_naturality, Functor.assoc,
      toPGrpd_forgetToGrpd, ← Functor.assoc, hG])

lemma equivInv_comp_forget (G : ∫ σ ⋙ A ⥤ ∫ B) (hG : G ⋙ forget = pre A σ) :
    equivInv B G hG ⋙ forget = σ := by
  simp [equivInv, Functor.IsPullback.fac_right]

-- TODO: work out naturality equations for this bijection

end GroupoidModel.FunctorOperation.pi

namespace CategoryTheory

open Functor.Groupoidal

structure Functor.Isofibration {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D) where
  liftObj {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) : C
  liftIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) : X' ⟶ liftObj f hX'
  is_hom_lift_hom {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
    F.IsHomLift f (liftIso f hX')

namespace Functor.Isofibration

variable {Γ : Type u} {E : Type u} [Groupoid.{v} Γ] [Groupoid.{v} E] {F : E ⥤ Γ}
  (hF : F.Isofibration)

instance {X : Γ} : IsGroupoid (F.Fiber X) where
  all_isIso f := {
    out :=
    have := f.2
    ⟨Fiber.homMk F _ (CategoryTheory.inv f.1), by cat_disch, by cat_disch⟩ }

instance {X : Γ} : Groupoid (F.Fiber X) := Groupoid.ofIsGroupoid

/-- Any isofibration `F : E ⥤ Γ` of groupoids is classified by a functor `classifier : Γ ⥤ Grpd`.
-/
def classifier : Γ ⥤ Grpd.{v,u} where
  obj X := Grpd.of (F.Fiber X)
  map :=
    have : Isofibration F := hF -- TODO: remove. This is just to ensure variables used
    sorry -- use lifting of isomorphisms!
  map_id := sorry
  map_comp := sorry

/-- The Grothendieck construction on the classifier is isomorphic to `E`.
TODO: add commuting triangles for `Grothendieck.forget` and `F` with `.hom` and `.inv`.
TODO: draw pullback diagram. -/
def grothendieckClassifierIso : ∫ classifier hF ≅≅ E where
  hom :=
    sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

end Functor.Isofibration

namespace Grpd

attribute [simp] comp_eq_comp id_eq_id in
@[simps]
def Grpd.mkIso {Δ Γ : Grpd} (F : Δ ≅≅ Γ) : Δ ≅ Γ where
  hom := F.hom
  inv := F.inv
  hom_inv_id := by simp
  inv_hom_id := by simp

namespace IsIsofibration

def isofibration {B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) : F.Isofibration := sorry

/-- The Grothendieck construction on the classifier is isomorphic to `E`,
now as objects in `Grpd`. -/
def grothendieckClassifierIso {E Γ : Grpd} {F : E ⟶ Γ} (hF : IsIsofibration F) :
    Grpd.of (∫ hF.isofibration.classifier) ≅ E :=
  Grpd.mkIso (Functor.Isofibration.grothendieckClassifierIso ..)

end IsIsofibration

instance : IsIsofibration.IsStableUnderBaseChange := by
  dsimp [IsIsofibration]
  infer_instance

instance : IsIsofibration.IsMultiplicative := by
  dsimp [IsIsofibration]
  infer_instance

instance : IsIsofibration.HasObjects := by
  sorry

section

attribute [local instance] Grpd.IsIsofibration.isofibration

open Functor.Isofibration

def strictify {C B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : C ⟶ (Grpd.of <| ∫ classifier (hF.isofibration)) :=
  sorry

lemma isIsofibration_strictify {C B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : IsIsofibration (strictify hF hG) := sorry

/-- The object part (a groupoid) of the pushforward along `F`, of `G`,
defined as the Grothendieck construction applied to (unstructured) Pi-type construction
in the HoTTLean groupoid model. -/
def pushforwardLeft {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : Grpd :=
  Grpd.of <| ∫ (GroupoidModel.FunctorOperation.pi (hF.isofibration.classifier)
    (classifier (isIsofibration_strictify hF hG).isofibration))

/-- The morphism part (a functor) of the pushforward along `F`, of `G`.
This is defined as the forgetful functor from the Grothendieck construction. -/
def pushforwardHom {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : pushforwardLeft hF hG ⟶ A :=
  Grpd.homOf Functor.Groupoidal.forget

/-- The pushforward along `F`, of `G`, as an object in the over category. -/
abbrev pushforward {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : Over A :=
  Over.mk (pushforwardHom hF hG)

-- This is one step towards the equivalence `pushforwardHomEquiv`
def pushforwardHomEquivAux {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) (X : Over A) :
    (X ⟶ pushforward hF hG) ≃
    (f : ∫ X.hom ⋙ hF.isofibration.classifier ⥤ ∫ (isIsofibration_strictify hF hG).isofibration.classifier) ×'
    (f ⋙ Functor.Groupoidal.forget = pre hF.isofibration.classifier X.hom) where
  toFun f := ⟨GroupoidModel.FunctorOperation.pi.equivFun (σ := X.hom) _ f.left f.w,
    GroupoidModel.FunctorOperation.pi.equivFun_comp_forget (σ := X.hom) _ f.left f.w⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- The universal property of the pushforward, expressed as a (natural) bijection of hom sets. -/
def pushforwardHomEquiv {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) (X : Over A) :
    (X ⟶ pushforward hF hG) ≃ ((Over.pullback F).obj X ⟶ Over.mk G) := by
  dsimp [pushforward, pushforwardHom]
  sorry

/-- Naturality in the universal property of the pushforward. -/
lemma pushforwardHomEquiv_comp {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G)
    {X X' : Over A} (f : X ⟶ X') (g : X' ⟶ pushforward hF hG) :
    (pushforwardHomEquiv hF hG X) (f ≫ g) =
    (Over.pullback F).map f ≫ (pushforwardHomEquiv hF hG X') g := by
  sorry

instance : IsIsofibration.HasPushforwards IsIsofibration :=
  fun F _ G => {
    has_representation := ⟨pushforward F.2 G.2, ⟨{
      homEquiv := pushforwardHomEquiv ..
      homEquiv_comp f g := pushforwardHomEquiv_comp F.2 G.2 f g }⟩⟩ }

-- This should follow from `Groupoidal.forget` being an isofibration.
-- (If we manage to directly define the pushforward
-- as a grothendieck construction)
theorem isIsofibration_pushforward {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : IsIsofibration (pushforwardHom hF hG) :=
  sorry

/-  TODO: following instance can be proven like so
  1. any pushforward is isomorphic to a chosen pushforward
     This should be proven in general for pushforwards,
     and even more generally for partial right adjoint objects) :
     `(F.op ⋙ yoneda.obj X).IsRepresentable` and
     `(F.op ⋙ yoneda.obj Y).IsRepresentable` implies
     `X ≅ Y`.
  2. Isofibrations are stable under isomorphism (this is in mathlib, for any `rlp`)
    `MorphismProperty.rlp_isMultiplicative`
    `MorphismProperty.respectsIso_of_isStableUnderComposition`
  3. The chosen pushforward is an isofibration `isIsofibration_pushforward` -/
instance : IsIsofibration.IsStableUnderPushforward IsIsofibration where
  of_isPushforward F G P := sorry
