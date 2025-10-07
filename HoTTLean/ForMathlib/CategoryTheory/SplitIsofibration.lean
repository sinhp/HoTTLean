import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import HoTTLean.Grothendieck.Groupoidal.IsPullback

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

open ClovenIsofibration

variable {Γ : Type u} {E : Type u} [Groupoid.{v} Γ] [Groupoid.{v} E] {F : E ⥤ Γ}
  (I : SplitClovenIsofibration F)

/-- Any isofibration `F : E ⥤ Γ` of groupoids is classified by a functor `classifier : Γ ⥤ Grpd`.
-/
def classifier.map.obj {X Y : Γ} (f : X ⟶ Y) (a : F.Fiber X) : F.Fiber Y :=
  ⟨I.liftObj f a.2, by
    have p : F.IsHomLift f (I.liftIso f _) := I.isHomLift f (X' := a.1) a.2
    apply @IsHomLift.codomain_eq (f := f) (φ := I.liftIso (X' := a.1) f a.2) ⟩

lemma classifier.fac' {X} {a b : F.Fiber X} (m : a ⟶ b) :
    F.map m.1 = eqToHom (by rw [a.2, b.2]) := by
  rw [@IsHomLift.fac' _ _ _ _ F _ _ _ _ (𝟙 X) _ m.2]
  simp

def classifier.map.map  {X Y} (f: X ⟶ Y) {a b : F.Fiber X} (m : a ⟶ b) :
    map.obj I f a ⟶ map.obj I f b :=
  let i1 : a.1 ⟶ I.liftObj f a.2 := I.liftIso f a.2
  let i2 := I.liftIso f b.2
  let i := Groupoid.inv i1 ≫ m.1 ≫ i2
  have e :𝟙 Y = eqToHom (by simp[obj_liftObj]) ≫
     F.map (CategoryTheory.inv i1 ≫ m.1 ≫ i2) ≫ eqToHom (by simp[obj_liftObj])
     := by
      simp[i1, i2, classifier.fac', Functor.map_inv,map_liftIso']
  have : F.IsHomLift (𝟙 Y) i := by
    simp only[i, e]
    apply IsHomLift.of_fac _ _ _ (ClovenIsofibration.obj_liftObj ..)
      (ClovenIsofibration.obj_liftObj ..)
    simp
  Fiber.homMk F _ i

lemma classifier.map.map_id {X Y} (f : X ⟶ Y) (a: F.Fiber X):
  map.map I f (𝟙 a) = 𝟙 (map.obj I f a) := by
   ext
   simp[classifier.map.map]
   simp[Fiber.fiberInclusion]
   simp[CategoryStruct.id]
   simp[classifier.map.obj]

lemma classifier.map.map_comp {X Y} (f: X ⟶ Y) {a b c: F.Fiber X} (m1 : a ⟶ b) (m2: b ⟶ c):
  map.map I f (m1 ≫ m2) = map.map I f m1 ≫ map.map I f m2 := by
   ext
   simp[classifier.map.map]
   simp[CategoryStruct.comp]

@[simps]
def classifier.map {X Y} (f : X ⟶ Y) : F.Fiber X ⥤ F.Fiber Y where
  obj := classifier.map.obj I f
  map := classifier.map.map I f
  map_id := classifier.map.map_id I f
  map_comp := classifier.map.map_comp I f

lemma classifier.map_id (X : Γ) : classifier.map I (𝟙 X) = 𝟙 (Grpd.of (F.Fiber X)) := by
  fapply Functor.ext
  · intro a
    apply Subtype.ext
    simp [map.obj, I.liftObjId]
  · intro a b f
    simp
    ext
    simp [map.map, I.liftIsoId, eqToHom_map, Grpd.id_eq_id, ← heq_eq_eq]
    rfl


lemma classifier.map_comp {X Y Z: Γ} (f : X⟶ Y) (g : Y ⟶ Z):
 classifier.map I (f ≫ g) = classifier.map I f ⋙ classifier.map I g := by
  fapply Functor.ext
  · intro a
    simp[map.obj, I.liftObjComp]
  · intro a b f
    simp
    ext
    simp [map.map,  eqToHom_map, Grpd.id_eq_id, ← heq_eq_eq,← Category.assoc]
    simp[I.liftIsoComp,← Category.assoc]
    congr 1
    simp[Category.assoc]
    congr
    simp[]



def classifier : Γ ⥤ Grpd.{v,u} where
  obj X := Grpd.of (F.Fiber X)
  map f := Grpd.homOf (classifier.map I f)
  map_id _ := classifier.map_id ..
  map_comp := by
   apply classifier.map_comp

open CategoryTheory.Functor.Groupoidal

/-- The Grothendieck construction on the classifier is isomorphic to `E`.
TODO: add commuting triangles for `Grothendieck.forget` and `F` with `.hom` and `.inv`.
TODO: draw pullback diagram. -/

def grothendieckClassifierIso.hom.obj (pair: ∫ I.classifier) : E := pair.fiber.1


lemma grothendieckClassifierIso.hom.map_aux
 {X Y: Γ} (f: X ⟶ Y) (a: I.classifier.obj X)
 : (I.classifier.map f).obj a = ⟨I.liftObj (X' := a.1) f a.2, obj_liftObj ..⟩ := by
  simp[classifier,classifier.map.obj]


-- lemma grothendieckClassifierIso.hom.hom.map_aux
--  {X Y: Γ} (f: X ⟶ Y) (a: I.classifier.obj X) (b: I.classifier.obj Y)
--  (h: (I.classifier.map f).obj a ⟶ b )
--  : (I.classifier.map f).obj a = sorry := by

--   simp[classifier,classifier.map.obj]
--   sorry


/-

Want: F.obj ↑p1.fiber = p1.base

p1 : ∫ I.classifier

p1.base : Γ

p1.fiber : I.classifier.obj p1.base

 Grpd.of (F.Fiber p1.base) =
I.classifier.obj p1.base = F.Fiber p1.base

p1.fiber : F.Fiber p1.base

F.obj p1.fiber = p1.base

-/

lemma grothendieckClassifierIso.hom.map_aux2
 (X: Γ) (a: I.classifier.obj X) : F.obj a.1 = X := by
  simp[classifier] at a
  simp[a.2]


def grothendieckClassifierIso.hom.map {p1 p2: ∫ I.classifier} (h: p1 ⟶ p2) :
 (p1.fiber.1 ⟶ p2.fiber.1) :=
  I.liftIso h.base
   (hom.map_aux2 ..) ≫ (eqToHom (by simp[grothendieckClassifierIso.hom.map_aux] )) ≫
   h.fiber.1


def grothendieckClassifierIso.hom.map' {p1 p2: ∫ I.classifier} (h: p1 ⟶ p2) :
 (p1.fiber.1 ⟶ p2.fiber.1) :=
  I.liftIso h.base
   (hom.map_aux2 ..) ≫
   (eqToHom (by simp[grothendieckClassifierIso.hom.map_aux,Fiber.fiberInclusion] )) ≫
   Fiber.fiberInclusion.map h.fiber ≫
   (eqToHom (by simp[Fiber.fiberInclusion] ))



lemma grothendieckClassifierIso.hom.map_id (X : ∫ I.classifier) :
hom.map I (𝟙 X) = 𝟙 _ := by
 convert_to _ ≫ _ ≫ Fiber.fiberInclusion.map (Hom.fiber (𝟙 X)) = _
 simp [liftIsoId, eqToHom_map]
 --convert_to
 -- rw! (castMode := .all) [Grpd.id_eq_id,hom.map_aux,liftObjId]


lemma grothendieckClassifierIso.hom.map_comp {X Y Z: ∫ I.classifier} (f : X ⟶ Y) (g : Y ⟶ Z) :
hom.map' I (f ≫ g) = hom.map' I f ≫ hom.map' I g := by
 simp [map', liftIsoComp, eqToHom_map, classifier, classifier.map.map]
 rfl
 --convert_to _ ≫ _ ≫ Fiber.fiberInclusion.map (Hom.fiber (𝟙 X)) = _

--  simp [map', liftIsoComp]
--  simp [map',liftIsoComp,classifier]
--  congr 1
--  convert_to _ ≫ _ ≫ _ ≫ _ ≫ _ = _
--  simp[← Category.assoc]
--  congr 1
--  simp[classifier.map.map]
--  simp[← Category.assoc]
--  congr
--  simp[Category.assoc]
--  simp[Hom.fiber]
--  congr
 --simp[Category.assoc]

--  sorry
 --convert_to _ ≫ eqToHom _ ≫ Fiber.fiberInclusion.map _ ≫ _ = _


def grothendieckClassifierIso.hom' : ∫ I.classifier ⥤  E :=
  Groupoidal.functorFrom (fun x => Fiber.fiberInclusion) (fun f => sorry) sorry sorry

def grothendieckClassifierIso.hom : ∫ I.classifier ⥤  E where
  obj p := p.fiber.1
  map := grothendieckClassifierIso.hom.map I
  map_id X := by apply grothendieckClassifierIso.hom.map_id ..
  map_comp := sorry--grothendieckClassifierIso.hom.map_comp I


def grothendieckClassifierIso.inv : E ⥤ ∫ I.classifier where
  obj := sorry
  map := sorry
  map_id := sorry
  map_comp := sorry


def grothendieckClassifierIso : ∫ I.classifier ≅≅ E where
  hom := grothendieckClassifierIso.hom ..
  inv := grothendieckClassifierIso.inv ..
  hom_inv_id := sorry
  inv_hom_id := sorry



/-- `IsMultiplicative` 1/2 -/
def id.liftObj {A : Type u} [Category.{v} A] {X Y}
 (f : X ⟶ Y) [IsIso f]  {X' : A} (e : (𝟭 A).obj X' = X) : A := X

def id {A : Type u} [Category.{v} A] :
    SplitClovenIsofibration (𝟭 A) where
  liftObj := id.liftObj
  liftIso := sorry
  isHomLift := sorry
  liftObjId := sorry
  liftIsoId := sorry
  liftObjComp := sorry
  liftIsoComp := sorry

/-- `IsMultiplicative` 1/2 -/
def comp {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C] {F : A ⥤ B}
    (IF : SplitClovenIsofibration F) {G : B ⥤ C} (IG : SplitClovenIsofibration G) :
    SplitClovenIsofibration (F ⋙ G) where
  liftObj := sorry
  liftIso := sorry
  isHomLift := sorry
  liftObjId := sorry
  liftIsoId := sorry
  liftObjComp := sorry
  liftIsoComp := sorry

/-- `IsStableUnderBaseChange` -/
def ofIsPullback {A B A' B' : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} A']
    [Category.{v} B'] (top : A' ⥤ A) (F' : A' ⥤ B') (F : A ⥤ B) (bot : B' ⥤ B)
    (isPullback : Functor.IsPullback top F' F bot) (IF : SplitClovenIsofibration F) :
    SplitClovenIsofibration F' where
  liftObj := sorry
  liftIso := sorry
  isHomLift := sorry
  liftObjId := sorry
  liftIsoId := sorry
  liftObjComp := sorry
  liftIsoComp := sorry

-- def toTerminal {A : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} A']
--     [Category.{v} B'] (top : A' ⥤ A) (F' : A' ⥤ B') (F : A ⥤ B) (bot : B' ⥤ B)
--     (isPullback : Functor.IsPullback top F' F bot) (IF : SplitClovenIsofibration F) :
--     SplitClovenIsofibration F' where
--   liftObj := sorry
--   liftIso := sorry
--   isHomLift := sorry
--   liftObjId := sorry
--   liftIsoId := sorry
--   liftObjComp := sorry
--   liftIsoComp := sorry

#exit
namespace IsIsofibration

def isofibration B A : Grpd {F : B ⟶ A} (hF : IsIsofibration F) : F.Isofibration := sorry

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
