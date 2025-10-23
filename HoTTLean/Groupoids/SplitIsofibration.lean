import HoTTLean.ForMathlib.CategoryTheory.SplitIsofibration
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

lemma equivInv_equivFun (F : Δ ⥤ ∫ pi A B) (hF : F ⋙ forget = σ) :
    equivInv B (equivFun B F hF) (equivFun_comp_forget B F hF) = F := by
  simp only [equivFun, equivInv]
  apply (isPullback _).hom_ext
  · rw [Functor.IsPullback.fac_left, Functor.IsPullback.fac_left, lam_inversion]
  · rw! [Functor.IsPullback.fac_right, hF]

lemma equivFun_equivInv (G : ∫ σ ⋙ A ⥤ ∫ B) (hG : G ⋙ forget = pre A σ) :
    equivFun B (equivInv B G hG) (equivInv_comp_forget B G hG) = G := by
  simp only [equivFun, equivInv]
  apply (isPullback B).hom_ext
  · have : pre A σ ⋙ B = (G ⋙ toPGrpd B) ⋙ PGrpd.forgetToGrpd := by
      rw [Functor.assoc, toPGrpd_forgetToGrpd, ← Functor.assoc, hG]
    rw! [Functor.IsPullback.fac_left, Functor.IsPullback.fac_left, this, inversion_lam]
  · rw [Functor.IsPullback.fac_right, hG]

-- TODO: work out naturality equations for this bijection

end GroupoidModel.FunctorOperation.pi

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

lemma grothendieckClassifierIso_inv_comp_forget :
    hF.grothendieckClassifierIso.inv ⋙ homOf Functor.Groupoidal.forget = F :=
  sorry

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
  obj_mem F G := sorry

section

open Functor.ClovenIsofibration

def strictify {C B A : Grpd} {F : B ⟶ A} (hF : SplitIsofibration F) (G : C ⟶ B) :
    C ⟶ Grpd.of (∫ classifier (hF.splitIsofibration)) :=
  G ≫ hF.grothendieckClassifierIso.inv

def splitIsofibration_strictify {C B A : Grpd} {F : B ⟶ A} (hF : SplitIsofibration F)
    {G : C ⟶ B} (hG : SplitIsofibration G) : (strictify hF G).ClovenIsofibration :=
  sorry

/-- The object part (a groupoid) of the pushforward along `F`, of `G`,
defined as the Grothendieck construction applied to (unstructured) Pi-type construction
in the HoTTLean groupoid model. -/
def pushforwardLeft {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) : Grpd :=
  Grpd.of <| ∫ (GroupoidModel.FunctorOperation.pi (hF.splitIsofibration.classifier)
    (classifier (splitIsofibration_strictify hF hG)))

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
    (hG : SplitIsofibration G) :
    (pushforward hF hG).hom = pushforwardHom .. := rfl

open Limits in
lemma pullback_isPullback {B A} {F : B ⟶ A} (hF : SplitIsofibration F) (σ : Over A) :
    IsPullback (pullback.snd σ.hom F ≫ hF.grothendieckClassifierIso.inv) (pullback.fst σ.hom F)
    (homOf Functor.Groupoidal.forget) (homOf σ.hom) :=
  IsPullback.of_iso (IsPullback.of_hasPullback σ.hom F).flip (Iso.refl _)
    (hF.grothendieckClassifierIso ..).symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by
      simpa using hF.grothendieckClassifierIso_inv_comp_forget.symm )
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
def pullbackIsoGrothendieck {B A} {F : B ⟶ A} (hF : SplitIsofibration F) (σ : Over A) :
    Grpd.of (∫ σ.hom ⋙ hF.splitIsofibration.classifier) ≅ Limits.pullback σ.hom F :=
  (pre_classifier_isPullback hF σ).isoIsPullback _ _ (pullback_isPullback hF σ)

open GroupoidModel.FunctorOperation.pi in
/-- `∫ σ.hom ⋙ hF.splitIsofibration.classifier` is the pullback of `F` along `σ`,
`∫ (splitIsofibration_strictify hF hG).classifier` is isomorphic to `G`.
So up to isomorphism this is the hom set bijection we want. -/
def pushforwardHomEquivAux1 {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) (σ : Over A) :
    (σ ⟶ pushforward hF hG) ≃
    {f : ∫ σ.hom ⋙ hF.splitIsofibration.classifier ⥤
      ∫ (splitIsofibration_strictify hF hG).classifier //
      f ⋙ Functor.Groupoidal.forget = pre hF.splitIsofibration.classifier σ.hom } where
  toFun f := ⟨equivFun _ f.left f.w, equivFun_comp_forget ..⟩
  invFun f := Over.homMk (equivInv _ f.1 f.2)
    (equivInv_comp_forget ..)
  left_inv f := by
    ext
    simp [equivInv_equivFun]
  right_inv f := by
    ext
    simp [equivFun_equivInv]

def pushforwardHomEquivAux2 {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) (σ : Over A) :
    { f : ∫ σ.hom ⋙ hF.splitIsofibration.classifier ⥤
      ∫ (splitIsofibration_strictify hF hG).classifier //
      f ⋙ Functor.Groupoidal.forget = pre hF.splitIsofibration.classifier σ.hom } ≃
    ((Over.pullback F).obj σ ⟶ Over.mk G) where
  toFun f := Over.homMk ((pullbackIsoGrothendieck hF σ).inv ≫ Grpd.homOf f.1 ≫
    ((splitIsofibration_strictify hF hG)).grothendieckClassifierIso.hom) sorry
  invFun f := ⟨ (pullbackIsoGrothendieck hF σ).hom ⋙ f.left ⋙
    ((splitIsofibration_strictify hF hG)).grothendieckClassifierIso.inv, sorry⟩
  left_inv := sorry
  right_inv := sorry

open GroupoidModel.FunctorOperation.pi in
/-- The universal property of the pushforward, expressed as a (natural) bijection of hom sets. -/
def pushforwardHomEquiv {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) (σ : Over A) :
    (σ ⟶ pushforward hF hG) ≃ ((Over.pullback F).obj σ ⟶ Over.mk G) :=
  calc (σ ⟶ pushforward hF hG)
  _ ≃ {f : ∫ σ.hom ⋙ hF.splitIsofibration.classifier ⥤
      ∫ (splitIsofibration_strictify hF hG).classifier //
      (f ⋙ Functor.Groupoidal.forget = pre hF.splitIsofibration.classifier σ.hom)} :=
    pushforwardHomEquivAux1 ..
  _ ≃ ((Over.pullback F).obj σ ⟶ Over.mk G) := pushforwardHomEquivAux2 ..


/-- Naturality in the universal property of the pushforward. -/
lemma pushforwardHomEquiv_comp {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G)
    {X X' : Over A} (f : X ⟶ X') (g : X' ⟶ pushforward hF hG) :
    (pushforwardHomEquiv hF hG X) (f ≫ g) =
    (Over.pullback F).map f ≫ (pushforwardHomEquiv hF hG X') g := by
  sorry


def pushforward_isPushforward  {C B A} {F : B ⟶ A} (hF : SplitIsofibration F) {G : C ⟶ B}
    (hG : SplitIsofibration G) : IsPushforward F (Over.mk G) (pushforward hF hG) where
  homEquiv := pushforwardHomEquiv ..
  homEquiv_comp f g := pushforwardHomEquiv_comp hF hG f g

instance : SplitIsofibration.HasPushforwards SplitIsofibration :=
  fun F _ G => {
    has_representation := ⟨pushforward F.2 G.2, ⟨pushforward_isPushforward F.2 G.2⟩⟩ }

def isoPushforwardOfIsPushforward  {B A} {F : B ⟶ A} (hF : SplitIsofibration F)
 (G: Over B) (hG : SplitIsofibration G.hom) (G': Over A)
 (h: IsPushforward F G G') : G' ≅ pushforward hF hG :=
  CategoryTheory.Functor.RepresentableBy.uniqueUpToIso
  (F := (Over.pullback F).op ⋙ yoneda.obj G)
  (by simp[IsPushforward] at h; assumption)
  ({
    homEquiv := pushforwardHomEquiv ..
    homEquiv_comp f g := by apply pushforwardHomEquiv_comp ..
  } )

-- This should follow from `Groupoidal.forget` being an splitIsofibration.
-- (If we manage to directly define the pushforward
-- as a grothendieck construction)
theorem splitIsofibration_pushforward {C B A} {F : B ⟶ A} (hF : SplitIsofibration F)
    {G : C ⟶ B} (hG : SplitIsofibration G) :
    SplitIsofibration (pushforwardHom hF hG) :=
  sorry

-- FIXME. For some reason needed in the proof
-- `SplitIsofibration.IsStableUnderPushforward SplitIsofibration`
instance SplitIsofibration.RespectsIso : SplitIsofibration.RespectsIso := inferInstance

/-  TODO: following instance can be proven like so
  1. any pushforward is isomorphic to a chosen pushforward
     This should be proven in general for pushforwards,
     and even more generally for partial right adjoint objects) :
     `(F.op ⋙ yoneda.obj X).IsRepresentable` and
     `(F.op ⋙ yoneda.obj Y).IsRepresentable` implies
     `X ≅ Y`.
  2. SplitIsofibrations are stable under isomorphism (this is in mathlib, for any `rlp`)
    `MorphismProperty.rlp_isMultiplicative`
    `MorphismProperty.respectsIso_of_isStableUnderComposition`
  3. The chosen pushforward is an splitIsofibration `splitIsofibration_pushforward` -/

instance : SplitIsofibration.IsStableUnderPushforward SplitIsofibration where
  of_isPushforward F G P := by
    intro h
    have p:  (Over.mk P) ≅ Grpd.pushforward (F.snd) (G.snd) :=
      isoPushforwardOfIsPushforward F.snd (Over.mk G.fst) G.snd (Over.mk P) h
    have i1 : SplitIsofibration (pushforwardHom (F.snd) (G.snd)) := by
     apply splitIsofibration_pushforward
    have e : P = (p.hom).left ≫ (pushforwardHom (F.snd) (G.snd)) := by
     have ee := Over.w p.hom
     simp at ee
     simp[ee]
    simp only[e]
    apply (SplitIsofibration.RespectsIso).precomp
    assumption
