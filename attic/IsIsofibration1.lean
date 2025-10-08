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

structure Functor.Isofibration {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D) where
  liftObj {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) : C
  liftIso {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) : X' ⟶ liftObj f hX'
  isHomLift {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X) :
    F.IsHomLift f (liftIso f hX')


lemma obj_liftObj {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D)  (hF : F.Isofibration) {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X):
    F.obj (hF.liftObj f hX') = Y := by
     have i : F.IsHomLift f (hF.liftIso f hX') := hF.isHomLift ..
     apply @IsHomLift.codomain_eq _ _ _ _ F _ _  _ _ f (hF.liftIso f hX')


lemma map_liftIso {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D)  (hF : F.Isofibration) {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X):
    eqToHom hX'.symm ≫ F.map (hF.liftIso f hX') ≫ eqToHom (obj_liftObj ..) = f := by
    have i : F.IsHomLift f (hF.liftIso f hX') := hF.isHomLift ..
    symm
    apply IsHomLift.fac


lemma map_liftIso' {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D)  (hF : F.Isofibration) {X Y : D} (f : X ⟶ Y) [IsIso f] {X' : C} (hX' : F.obj X' = X):
     F.map (hF.liftIso f hX')  = eqToHom hX' ≫ f ≫ eqToHom (by simp[obj_liftObj]) := by
    simp[← map_liftIso F hF f hX']


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

def classifier.map.obj.eq {X Y} (f : X ⟶ Y) (a : F.Fiber X)  :
 F.obj (hF.liftObj f a.2) = Y := by
   have p : F.IsHomLift f (hF.liftIso f _) := hF.isHomLift f (X' := a.1) a.2
   apply @IsHomLift.codomain_eq (f := f) (φ := liftIso (X' := a.1) hF f a.2)

def classifier.map.obj  {X Y} (f : X ⟶ Y) (a : F.Fiber X) : F.Fiber Y :=
  ⟨liftObj hF f a.2, classifier.map.obj.eq ..⟩

lemma Fiber.map {X} {a b: F.Fiber X} (m: a ⟶ b) :
  F.map m.1 = eqToHom a.2 ≫ 𝟙 X ≫ eqToHom b.2.symm := by
   have e:= m.2
   apply IsHomLift.fac'


def classifier.map.map  {X Y} (f: X ⟶ Y) {a b: F.Fiber X} (m: a ⟶ b) :
  map.obj hF f a ⟶ map.obj hF f b := by
  let i1 : a.1 ⟶ liftObj hF f a.2 := liftIso hF f a.2
  let i2 := liftIso hF f b.2
  let i := Groupoid.inv i1 ≫ m.1 ≫ i2
  have e :𝟙 Y = eqToHom (by simp[obj_liftObj]) ≫
     F.map (CategoryTheory.inv i1 ≫ m.1 ≫ i2) ≫ eqToHom (by simp[obj_liftObj])
     := by
      simp[i1, i2,Fiber.map, Functor.map_inv,map_liftIso']
  exact ⟨ i,
   by
   simp only[i, e]
   apply IsHomLift.of_fac _ _ _ (by apply classifier.map.obj.eq) (by apply classifier.map.obj.eq)
   simp
   ⟩


lemma classifier.map.map_id {X Y} (f: X ⟶ Y) (a: F.Fiber X):
  map.map hF f (𝟙 a) = 𝟙 (map.obj hF f a) := by
   simp[classifier.map.map]
   ext
   simp[Fiber.fiberInclusion]
   simp[CategoryStruct.id]
   simp[classifier.map.obj]

lemma classifier.map.map_comp {X Y} (f: X ⟶ Y) {a b c: F.Fiber X} (m1 : a ⟶ b) (m2: b ⟶ c):
  map.map hF f (m1 ≫ m2) = map.map hF f m1 ≫ map.map hF f m2 := by
   simp[classifier.map.map]
   ext
   simp[Fiber.fiberInclusion]
   simp[classifier.map.obj,CategoryStruct.comp]


def classifier.map {X Y} (f: X ⟶ Y) : (Grpd.of (F.Fiber X) ⟶ Grpd.of (F.Fiber Y)) where
  obj := classifier.map.obj hF f
  map := classifier.map.map hF f
  map_id := classifier.map.map_id hF f
  map_comp := classifier.map.map_comp hF f

lemma classifier.map_id (X : Γ) : classifier.map hF (𝟙 X) = 𝟙 (Grpd.of (F.Fiber X)) := sorry


def classifier : Γ ⥤ Grpd.{v,u} where
  obj X := Grpd.of (F.Fiber X)
  map := classifier.map hF
  map_id := classifier.map_id hF
  map_comp := by sorry

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
