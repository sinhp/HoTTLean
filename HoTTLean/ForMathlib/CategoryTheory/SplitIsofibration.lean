import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import HoTTLean.ForMathlib.CategoryTheory.Grpd

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

namespace CategoryTheory

namespace Functor

namespace Fiber

variable {Γ : Type u} {E : Type u} [Groupoid.{v} Γ] [Groupoid.{v} E] {F : E ⥤ Γ}

instance {X : Γ} : IsGroupoid (F.Fiber X) where
  all_isIso f := {
    out :=
    have := f.2
    ⟨Fiber.homMk F _ (CategoryTheory.inv f.1), by cat_disch, by cat_disch⟩ }

instance {X : Γ} : Groupoid (F.Fiber X) := Groupoid.ofIsGroupoid

end Fiber

variable {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]

structure ClovenIsofibration (F : C ⥤ D) where
  liftObj {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) : C
  liftIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) : X' ⟶ liftObj f hX'
  isHomLift {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
    F.IsHomLift f (liftIso f hX')

section
variable {F : C ⥤ D} (I : ClovenIsofibration F)

instance {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
  F.IsHomLift f (I.liftIso f hX') := I.isHomLift f hX'

lemma ClovenIsofibration.obj_liftObj {X Y : D} (f : X ⟶ Y) [IsIso f]
    {X' : C} (hX' : F.obj X' = X) : F.obj (I.liftObj f hX') = Y :=
  IsHomLift.codomain_eq F f (I.liftIso f hX')

lemma ClovenIsofibration.map_liftIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C}
    (hX' : F.obj X' = X) :
  eqToHom hX'.symm ≫ F.map (I.liftIso f hX') ≫ eqToHom (obj_liftObj ..) = f := by
  have i : F.IsHomLift f (I.liftIso f hX') := I.isHomLift ..
  symm
  apply IsHomLift.fac

lemma ClovenIsofibration.map_liftIso' {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
     F.map (I.liftIso f hX')  = eqToHom hX' ≫ f ≫ eqToHom (by simp[obj_liftObj]) := by
    simp[← map_liftIso I f hX']

lemma ClovenIsofibration.liftObjComp_aux {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C}
    (hX' : F.obj X' = X) (Y' : C) (hY' : I.liftObj f hX' = Y') : F.obj Y' = Y := by
  subst hY'
  apply ClovenIsofibration.obj_liftObj I f

end

structure SplitClovenIsofibration {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D) extends ClovenIsofibration F where
  liftObjId {X : D} {X' : C} (hX' : F.obj X' = X) : liftObj (𝟙 X) hX' = X'
  liftIsoId {X : D} {X' : C} (hX' : F.obj X' = X) : liftIso (𝟙 X) hX' = eqToHom (liftObjId hX').symm
  liftObjComp {X Y Z : D} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] {X' : C} (hX' : F.obj X' = X)
    (Y' : C) (hY' : liftObj f hX' = Y') : liftObj (f ≫ g) hX' = liftObj g (X' := Y')
      (toClovenIsofibration.liftObjComp_aux f hX' Y' hY')
  liftIsoComp {X Y Z : D} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [IsIso g] {X' : C} (hX' : F.obj X' = X)
    (Y' : C) (hY' : liftObj f hX' = Y') : liftIso (f ≫ g) hX' = liftIso f hX' ≫
    eqToHom hY' ≫
    liftIso g (X' := Y') (toClovenIsofibration.liftObjComp_aux f hX' Y' hY') ≫
    eqToHom (liftObjComp f g hX' Y' hY').symm

namespace SplitClovenIsofibration

variable {Γ : Type u} {E : Type u} [Groupoid.{v} Γ] [Groupoid.{v} E] {F : E ⥤ Γ}
  (I : SplitClovenIsofibration F)

/-- Any isofibration `F : E ⥤ Γ` of groupoids is classified by a functor `classifier : Γ ⥤ Grpd`.
-/
def classifier.map.obj {X Y : Γ} (f : X ⟶ Y) (a : F.Fiber X) : F.Fiber Y :=
  ⟨I.liftObj f a.2, by
    have p : F.IsHomLift f (I.liftIso f _) := I.isHomLift f (X' := a.1) a.2
    apply @IsHomLift.codomain_eq (f := f) (φ := I.liftIso (X' := a.1) f a.2) ⟩

def classifier.map.map  {X Y} (f: X ⟶ Y) {a b: F.Fiber X} (m: a ⟶ b) :
  map.obj I f a ⟶ map.obj I f b := by
  --let i1 : a ⟶ liftObj hF f a.2 := liftIso hF f a.2
  let i2 := I.liftIso f b.2
  --let i := m ≫ i2
  sorry

def classifier.map {X Y} (f : X ⟶ Y) : F.Fiber X ⥤ F.Fiber Y where
  obj := classifier.map.obj I f
  map {a b} m := classifier.map.map I f m
  map_id := sorry
  map_comp := sorry

def classifier : Γ ⥤ Grpd.{v,u} where
  obj X := Grpd.of (F.Fiber X)
  map f :=
    have : SplitClovenIsofibration F := I -- TODO: remove. This is just to ensure variables used
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
def grothendieckClassifierIso {B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) :
    Grpd.of (∫ hF.isofibration.classifier) ≅ B :=
  Grpd.mkIso (Functor.Isofibration.grothendieckClassifierIso ..)

-- lemma grothendieckClassifierIso_hom_comp_eq_forget {B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) :
--     hF.grothendieckClassifierIso.hom ⋙ F = homOf Functor.Groupoidal.forget :=
--   sorry

lemma grothendieckClassifierIso_inv_comp_forget {B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) :
    hF.grothendieckClassifierIso.inv ⋙ homOf Functor.Groupoidal.forget = F :=
  sorry

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

def strictify {C B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) (G : C ⟶ B) :
    C ⟶ Grpd.of (∫ classifier (hF.isofibration)) :=
  G ≫ hF.grothendieckClassifierIso.inv

def isIsofibration_strictify {C B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : IsIsofibration (strictify hF G) := sorry

def isofibration_strictify {C B A : Grpd} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : (strictify hF G).Isofibration := sorry

/-- The object part (a groupoid) of the pushforward along `F`, of `G`,
defined as the Grothendieck construction applied to (unstructured) Pi-type construction
in the HoTTLean groupoid model. -/
def pushforwardLeft {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : Grpd :=
  Grpd.of <| ∫ (GroupoidModel.FunctorOperation.pi (hF.isofibration.classifier)
    (classifier (isofibration_strictify hF hG)))

/-- The morphism part (a functor) of the pushforward along `F`, of `G`.
This is defined as the forgetful functor from the Grothendieck construction. -/
def pushforwardHom {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : pushforwardLeft hF hG ⟶ A :=
  Grpd.homOf Functor.Groupoidal.forget

/-- The pushforward along `F`, of `G`, as an object in the over category. -/
abbrev pushforward {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : Over A :=
  Over.mk (pushforwardHom hF hG)

lemma pushforward.hom {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) :
    (pushforward hF hG).hom = pushforwardHom .. := rfl

open Limits in
lemma pullback_isPullback {B A} {F : B ⟶ A} (hF : IsIsofibration F) (σ : Over A) :
    IsPullback (pullback.snd σ.hom F ≫ hF.grothendieckClassifierIso.inv) (pullback.fst σ.hom F)
    (homOf Functor.Groupoidal.forget) (homOf σ.hom) :=
  IsPullback.of_iso (IsPullback.of_hasPullback σ.hom F).flip (Iso.refl _)
    (hF.grothendieckClassifierIso ..).symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by
      simpa using hF.grothendieckClassifierIso_inv_comp_forget.symm )
    (by simp)

lemma pre_classifier_isPullback {B A} {F : B ⟶ A} (hF : IsIsofibration F) (σ : Over A) :
    IsPullback (homOf (pre hF.isofibration.classifier σ.hom)) (homOf Functor.Groupoidal.forget)
    (homOf Functor.Groupoidal.forget) (homOf σ.hom) := by
  have outer_pb := Functor.Groupoidal.isPullback (σ.hom ⋙ hF.isofibration.classifier)
  have right_pb := Functor.Groupoidal.isPullback (hF.isofibration.classifier)
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
def pullbackIsoGrothendieck {B A} {F : B ⟶ A} (hF : IsIsofibration F) (σ : Over A) :
    Grpd.of (∫ σ.hom ⋙ hF.isofibration.classifier) ≅ Limits.pullback σ.hom F :=
  (pre_classifier_isPullback hF σ).isoIsPullback _ _ (pullback_isPullback hF σ)

open GroupoidModel.FunctorOperation.pi in
/-- `∫ σ.hom ⋙ hF.isofibration.classifier` is the pullback of `F` along `σ`,
`∫ (isofibration_strictify hF hG).classifier` is isomorphic to `G`.
So up to isomorphism this is the hom set bijection we want. -/
def pushforwardHomEquivAux1 {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) (σ : Over A) :
    (σ ⟶ pushforward hF hG) ≃
    {f : ∫ σ.hom ⋙ hF.isofibration.classifier ⥤ ∫ (isofibration_strictify hF hG).classifier //
      f ⋙ Functor.Groupoidal.forget = pre hF.isofibration.classifier σ.hom } where
  toFun f := ⟨equivFun _ f.left f.w, equivFun_comp_forget ..⟩
  invFun f := Over.homMk (equivInv _ f.1 f.2)
    (equivInv_comp_forget ..)
  left_inv f := by
    ext
    simp [equivInv_equivFun]
  right_inv f := by
    ext
    simp [equivFun_equivInv]

def pushforwardHomEquivAux2 {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) (σ : Over A) :
    { f : ∫ σ.hom ⋙ hF.isofibration.classifier ⥤ ∫ (isofibration_strictify hF hG).classifier //
      f ⋙ Functor.Groupoidal.forget = pre hF.isofibration.classifier σ.hom } ≃
    ((Over.pullback F).obj σ ⟶ Over.mk G) where
  toFun f := Over.homMk ((pullbackIsoGrothendieck hF σ).inv ≫ Grpd.homOf f.1 ≫
    ((isIsofibration_strictify hF hG)).grothendieckClassifierIso.hom) sorry
  invFun f := ⟨(pullbackIsoGrothendieck hF σ).hom ≫ f.left ≫
    ((isIsofibration_strictify hF hG)).grothendieckClassifierIso.inv, sorry⟩
  left_inv := sorry
  right_inv := sorry

open GroupoidModel.FunctorOperation.pi in
/-- The universal property of the pushforward, expressed as a (natural) bijection of hom sets. -/
def pushforwardHomEquiv {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) (σ : Over A) :
    (σ ⟶ pushforward hF hG) ≃ ((Over.pullback F).obj σ ⟶ Over.mk G) :=
  calc (σ ⟶ pushforward hF hG)
  _ ≃ {f : ∫ σ.hom ⋙ hF.isofibration.classifier ⥤ ∫ (isofibration_strictify hF hG).classifier //
      (f ⋙ Functor.Groupoidal.forget = pre hF.isofibration.classifier σ.hom)} :=
    pushforwardHomEquivAux1 ..
  _ ≃ ((Over.pullback F).obj σ ⟶ Over.mk G) := pushforwardHomEquivAux2 ..



/-- Naturality in the universal property of the pushforward. -/
lemma pushforwardHomEquiv_comp {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G)
    {X X' : Over A} (f : X ⟶ X') (g : X' ⟶ pushforward hF hG) :
    (pushforwardHomEquiv hF hG X) (f ≫ g) =
    (Over.pullback F).map f ≫ (pushforwardHomEquiv hF hG X') g := by
  sorry


def pushforward_isPushforward  {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : IsPushforward F (Over.mk G) (pushforward hF hG) where
  homEquiv := pushforwardHomEquiv ..
  homEquiv_comp f g := pushforwardHomEquiv_comp hF hG f g

instance : IsIsofibration.HasPushforwards IsIsofibration :=
  fun F _ G => {
    has_representation := ⟨pushforward F.2 G.2, ⟨pushforward_isPushforward F.2 G.2⟩⟩ }

def isoPushforwardOfIsPushforward  {B A} {F : B ⟶ A} (hF : IsIsofibration F)
 (G: Over B) (hG : IsIsofibration G.hom) (G': Over A)
 (h: IsPushforward F G G') : G' ≅ pushforward hF hG :=
  CategoryTheory.Functor.RepresentableBy.uniqueUpToIso
  (F := (Over.pullback F).op ⋙ yoneda.obj G)
  (by simp[IsPushforward] at h; assumption)
  ({
    homEquiv := pushforwardHomEquiv ..
    homEquiv_comp f g := by apply pushforwardHomEquiv_comp ..
  } )

-- This should follow from `Groupoidal.forget` being an isofibration.
-- (If we manage to directly define the pushforward
-- as a grothendieck construction)
theorem isIsofibration_pushforward {C B A} {F : B ⟶ A} (hF : IsIsofibration F) {G : C ⟶ B}
    (hG : IsIsofibration G) : IsIsofibration (pushforwardHom hF hG) :=
  sorry

-- FIXME. For some reason needed in the proof
-- `IsIsofibration.IsStableUnderPushforward IsIsofibration`
instance IsIsofibration.RespectsIso : IsIsofibration.RespectsIso := inferInstance

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
  of_isPushforward F G P := by
    intro h
    have p:  (Over.mk P) ≅ Grpd.pushforward (F.snd) (G.snd) :=
      isoPushforwardOfIsPushforward F.snd (Over.mk G.fst) G.snd (Over.mk P) h
    have i1 : IsIsofibration (pushforwardHom (F.snd) (G.snd)) := by
     apply isIsofibration_pushforward
    have e : P = (p.hom).left ≫ (pushforwardHom (F.snd) (G.snd)) := by
     have ee := Over.w p.hom
     simp at ee
     simp[ee]
    simp only[e]
    apply (IsIsofibration.RespectsIso).precomp
    assumption
