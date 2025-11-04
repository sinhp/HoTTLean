import HoTTLean.ForMathlib.CategoryTheory.ClovenIsofibration
import HoTTLean.Groupoids.Pi
import HoTTLean.ForMathlib.CategoryTheory.MorphismProperty.OverAdjunction

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

instance : SplitIsofibration.HasObjects where
  obj_mem {X Y} F G := sorry

section

open Functor.ClovenIsofibration

/-- The object part (a groupoid) of the pushforward along `F`, of `G`,
defined as the Grothendieck construction applied to (unstructured) Pi-type construction
in the HoTTLean groupoid model. -/
def pushforwardLeft {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) : Grpd :=
  Grpd.of <| Functor.ClovenIsofibration.pushforward hF.splitIsofibration hG.splitIsofibration

/-- The morphism part (a functor) of the pushforward along `F`, of `G`.
This is defined as the forgetful functor from the Grothendieck construction. -/
def pushforwardHom {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) : pushforwardLeft hF hG ⟶ A :=
  Grpd.homOf Functor.Groupoidal.forget

/-- The pushforward along `F`, of `G`, as an object in the over category. -/
abbrev pushforward {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) : Over A :=
  Over.mk (pushforwardHom hF hG)

lemma pushforward.hom {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) : (pushforward hF hG).hom = pushforwardHom .. :=
  rfl

open Limits in
lemma pullback_isPullback {B A} {F : B ⟶ A} (hF : SplitIsofibration F) (σ : Over A) :
    IsPullback (pullback.snd σ.hom F ≫ hF.grothendieckClassifierIso.inv) (pullback.fst σ.hom F)
    (homOf Functor.Groupoidal.forget) (homOf σ.hom) :=
  IsPullback.of_iso (IsPullback.of_hasPullback σ.hom F).flip (Iso.refl _)
    (hF.grothendieckClassifierIso ..).symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (by simpa using hF.grothendieckClassifierIso_inv_comp_forget.symm )
    (by simp)

lemma pre_classifier_isPullback {B A} {F : B ⟶ A} (hF : SplitIsofibration F) (σ : Over A) :
    IsPullback (homOf (pre hF.splitIsofibration.classifier σ.hom))
    (homOf Functor.Groupoidal.forget)
    (homOf Functor.Groupoidal.forget) (homOf σ.hom) := by
  have outer_pb := Functor.Groupoidal.isPullback (σ.hom ⋙ hF.splitIsofibration.classifier)
  have right_pb := Functor.Groupoidal.isPullback (hF.splitIsofibration.classifier)
  have left_pb := Functor.IsPullback.Paste.ofRight' outer_pb.comm_sq outer_pb right_pb.comm_sq
    right_pb (pre _ _) (by
    apply right_pb.hom_ext
    · simp [Functor.IsPullback.fac_left]
    · simp [Functor.IsPullback.fac_right, pre_comp_forget])
  exact Grpd.isPullback left_pb

/--
∫(σ ⋙ classifier) --> ∫ classifier ≅ B
      |                   |
      |                   | forget ≅ F
      |                   |
      V                   V
      Δ   ------------->  A
                  σ
The two versions of the pullback are isomorphic.
-/
def grothendieckIsoPullback {B A} {F : B ⟶ A} (hF : SplitIsofibration F) (σ : Over A) :
    Grpd.of (∫ σ.hom ⋙ hF.splitIsofibration.classifier) ≅ Limits.pullback σ.hom F :=
  (pre_classifier_isPullback hF σ).isoIsPullback _ _ (pullback_isPullback hF σ)

lemma grothendieckIsoPullback_inv_comp_forget {B A} {F : B ⟶ A} (hF : SplitIsofibration F)
    (σ : Over A) : (grothendieckIsoPullback hF σ).inv ⋙ Functor.Groupoidal.forget =
    Limits.pullback.fst σ.hom F := by
  exact (pre_classifier_isPullback hF σ).isoIsPullback_inv_snd _ _
    (pullback_isPullback hF σ)

lemma grothendiecIsoPullback_comp_hom_comp_snd {B A} {F : B ⟶ A} (hF : SplitIsofibration F)
    (σ : Over A) : (grothendieckIsoPullback hF σ).hom ⋙ Limits.pullback.snd σ.hom F =
    pre hF.splitIsofibration.classifier σ.hom ⋙ hF.grothendieckClassifierIso.hom := by
  have := (pre_classifier_isPullback hF σ).isoIsPullback_hom_fst _ _
    (pullback_isPullback hF σ)
  simp only [Functor.id_obj, Grpd.homOf, ← Category.assoc, Iso.comp_inv_eq] at this
  assumption


open GroupoidModel.FunctorOperation.pi Functor in
/-- The universal property of the pushforward, expressed as a (natural) bijection of hom sets. -/
--@[simps!]
def pushforwardHomEquiv {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) (σ : Over A) :
    (σ ⟶ pushforward hF hG) ≃ ((Over.pullback F).obj σ ⟶ Over.mk G) :=
  calc (σ ⟶ pushforward hF hG)
  _ ≃ {M : σ.left ⥤ hF.splitIsofibration.pushforward hG.splitIsofibration //
      M ⋙ Functor.Groupoidal.forget = σ.hom} :=
    { toFun M := ⟨M.left, M.w⟩
      invFun M := Over.homMk M.1 M.2 }
  _ ≃ {N : ∫ σ.hom ⋙ hF.splitIsofibration.classifier ⥤ C //
      N ⋙ G = pre hF.splitIsofibration.classifier σ.hom ⋙
      hF.splitIsofibration.grothendieckClassifierIso.hom} :=
    pushforward.homEquiv ..
  _ ≃ ((Over.pullback F).obj σ ⟶ Over.mk G) :=
    { toFun N := Over.homMk ((grothendieckIsoPullback hF σ).inv ≫ N.1) (by
        simp only [Over.pullback_obj_left, Functor.const_obj_obj, Over.mk_left, Functor.id_obj,
          grothendieckIsoPullback, comp_eq_comp, coe_of, Over.mk_hom, Functor.assoc, N.2,
          Over.pullback_obj_hom]
        rw [← Grpd.comp_eq_comp,Iso.inv_comp_eq]
        apply (Grpd.grothendiecIsoPullback_comp_hom_comp_snd ..).symm
        )
      invFun N := ⟨(grothendieckIsoPullback hF σ).hom ⋙ N.left, by
        have := N.w
        simp only [Over.pullback_obj_left, Functor.id_obj, Functor.const_obj_obj, Over.mk_left,
          Functor.id_map, Over.mk_hom, comp_eq_comp, Over.pullback_obj_hom,
          CostructuredArrow.right_eq_id, Discrete.functor_map_id, id_eq_id, simpCompId] at this
        simp only [Functor.id_obj, Functor.const_obj_obj, Functor.assoc, this]
        rw [Grpd.grothendiecIsoPullback_comp_hom_comp_snd]
        rfl ⟩
      left_inv := by
       intro a
       simp only [Functor.id_obj, Functor.const_obj_obj, Over.pullback_obj_left, Over.mk_left,
         comp_eq_comp, coe_of, Over.homMk_left, ← Functor.assoc]
       rw![← comp_eq_comp]
       simp[Iso.hom_inv_id]
      right_inv := by
       intro a
       simp[← Functor.assoc]
       rw![← comp_eq_comp] -- I do not need this, it attacks the outmost ⋙ first, maybe can use conv to get rid of
       rw![← comp_eq_comp]
       simp[Iso.inv_hom_id]
        }

/-- Naturality in the universal property of the pushforward. -/
lemma pushforwardHomEquiv_comp {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G)
    {X X' : Over A} (f : X ⟶ X') (g : X' ⟶ pushforward hF hG) :
    (pushforwardHomEquiv hF hG X) (f ≫ g) =
    (Over.pullback F).map f ≫ (pushforwardHomEquiv hF hG X') g := by
  ext
  simp[pushforwardHomEquiv]
  sorry

def pushforward_isPushforward  {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) : IsPushforward F (Over.mk G) (pushforward hF hG) where
  homEquiv := pushforwardHomEquiv ..
  homEquiv_comp f g := pushforwardHomEquiv_comp hF hG f g

instance : SplitIsofibration.HasPushforwards SplitIsofibration where
  hasPushforwardsAlong _ hF := { hasPushforward _ hG :=
    ⟨pushforward hF hG, ⟨pushforward_isPushforward hF hG⟩⟩ }

def isoPushforwardOfIsPushforward  {B A} {F : B ⟶ A} (hF : SplitIsofibration F)
 (G: Over B) (hG : SplitIsofibration G.hom) (G': Over A)
 (h: IsPushforward F G G') : G' ≅ pushforward hF hG :=
  CategoryTheory.Functor.RepresentableBy.uniqueUpToIso
  (F := (Over.pullback F).op ⋙ yoneda.obj G)
  (by simp[IsPushforward] at h; assumption)
  ({ homEquiv := pushforwardHomEquiv ..
     homEquiv_comp f g := by apply pushforwardHomEquiv_comp .. } )

theorem splitIsofibration_pushforward {C B A} {F : B ⟶ A} (hF : SplitIsofibration F)
    {G : C ⟶ B} (hG : SplitIsofibration G) :
    SplitIsofibration (pushforwardHom hF hG) := by
  unfold Grpd.pushforwardHom homOf
  exact ⟨ Functor.ClovenIsofibration.forget _ ,
          CategoryTheory.Functor.ClovenIsofibration.instIsSplitGroupoidalForget ⟩

-- FIXME. For some reason needed in the proof
-- `SplitIsofibration.IsStableUnderPushforward SplitIsofibration`
instance SplitIsofibration.RespectsIso : SplitIsofibration.RespectsIso := inferInstance

/--
1. any pushforward is isomorphic to a chosen pushforward
   This is proven in general for pushforwards,
   and holds even more generally for partial right adjoint objects:
   `(F.op ⋙ yoneda.obj X).IsRepresentable` and
   `(F.op ⋙ yoneda.obj Y).IsRepresentable` implies `X ≅ Y`.
2. SplitIsofibrations are stable under isomorphism
3. The chosen pushforward is an splitIsofibration `splitIsofibration_pushforward`.
  This is because under the hood, it is a Grothendieck construction. -/
instance : SplitIsofibration.IsStableUnderPushforward SplitIsofibration where
  of_isPushforward F hF G hG P hP := by
    have p : (Over.mk P) ≅ Grpd.pushforward (hF) (hG) :=
      isoPushforwardOfIsPushforward hF (Over.mk G) hG (Over.mk P) hP
    have i1 : SplitIsofibration (pushforwardHom (hF) (hG)) := by
      apply splitIsofibration_pushforward
    have e : P = (p.hom).left ≫ (pushforwardHom (hF) (hG)) := by
      have ee := Over.w p.hom
      simp at ee
      simp [ee]
    simp only[e]
    apply (SplitIsofibration.RespectsIso).precomp
    assumption
