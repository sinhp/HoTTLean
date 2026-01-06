import HoTTLean.ForMathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Functor.TwoSquare
import HoTTLean.ForMathlib.CategoryTheory.Comma.Over.Pushforward
import HoTTLean.ForMathlib.CategoryTheory.MorphismProperty.Limits
import HoTTLean.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import HoTTLean.ForMathlib
import HoTTLean.ForMathlib.CategoryTheory.NatTrans
import Mathlib.Tactic.DepRewrite
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.BeckChevalley
import HoTTLean.ForMathlib.CategoryTheory.Yoneda
import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Presheaf
import HoTTLean.ForMathlib.CategoryTheory.Adjunction.PartialAdjoint
import HoTTLean.ForMathlib.CategoryTheory.Comma.Presheaf.Basic
import HoTTLean.ForMathlib.CategoryTheory.Functor.FullyFaithful

universe w v u v₁ u₁

noncomputable section

namespace CategoryTheory

open Category Limits MorphismProperty

variable {C : Type u} [Category.{v} C] {C' : Type u₁} [Category.{v₁} C'] (F : C ⥤ C')

class Functor.PreservesMorphismProperty (R : MorphismProperty C) (R' : MorphismProperty C') where
  map_mem {X Y : C} (f : X ⟶ Y) : R f → R' (F.map f)

abbrev Functor.map_mem {R : MorphismProperty C} {R' : MorphismProperty C'}
    [F.PreservesMorphismProperty R R'] {X Y : C} (f : X ⟶ Y) : R f → R' (F.map f) :=
  PreservesMorphismProperty.map_mem f

class Functor.PreservesPullbacksOf (R : MorphismProperty C) where
  pb {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) :
  R snd → IsPullback fst snd f g → IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g)

-- NOTE this definition should refactor NaturalModel.Universe
structure RepresentableChosenPullbacks {X Y : Psh C} (f : X ⟶ Y) where
  ext {Γ : C} (A : y(Γ) ⟶ Y) : C
  disp {Γ : C} (A : y(Γ) ⟶ Y) : ext A ⟶ Γ
  var {Γ : C} (A : y(Γ) ⟶ Y) : y(ext A) ⟶ X
  disp_pullback {Γ : C} (A : y(Γ) ⟶ Y) :
    IsPullback (var A) ym(disp A) f A

open Functor in
theorem NatTrans.isIso_of_whiskerRight_isIso {C D E : Type*} [Category C] [Category D] [Category E]
    {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso (whiskerRight α F)] [F.ReflectsIsomorphisms] :
    IsIso α := by
  rw [NatTrans.isIso_iff_isIso_app] at *
  intro
  apply (config := {allowSynthFailures:= true}) Functor.ReflectsIsomorphisms.reflects F
  cat_disch

namespace MorphismProperty

variable (R : MorphismProperty C)

section pullback

variable {R} [R.HasPullbacks] {X : C}

variable (X)

end pullback

abbrev chosenTerminal [R.ContainsIdentities] (X) : R.Over ⊤ X := .mk ⊤ (𝟙 X) (R.id_mem _)

def Over.pullback_obj_chosenTerminal [R.IsStableUnderBaseChange] [R.ContainsIdentities]
    {X Y : C} (f : X ⟶ Y) [R.HasPullbacksAlong f] :
    (Over.pullback R ⊤ f).obj (R.chosenTerminal Y) ≅ R.chosenTerminal X :=
  have : HasPullback (𝟙 Y) f := HasPullbacksAlong.hasPullback (𝟙 Y) (R.id_mem Y)
  MorphismProperty.Over.isoMk (IsPullback.id_vert f).isoPullback.symm

variable [R.HasPullbacks] [R.IsStableUnderBaseChange]

@[simp]
protected abbrev Over.yoneda (X : C) : R.Over ⊤ X ⥤ CategoryTheory.Over y(X) :=
  Over.forget _ _ _ ⋙ CategoryTheory.Over.post yoneda

-- @[simps]
-- protected def Over.yoneda (X : C) : R.Over ⊤ X ⥤ CategoryTheory.Over y(X) where
--   obj A := .mk ym(A.hom)
--   map {A1 A2} f := CategoryTheory.Over.homMk ym(f.left)

-- instance (X : C) : (Over.yoneda R X).Full where
--   map_surjective {A B} f :=
--   ⟨Over.homMk (yoneda.preimage f.left) (by
--     apply yoneda.map_injective; simpa using CategoryTheory.Over.w f),
--   by cat_disch⟩

-- instance (X : C) : (Over.yoneda R X).Faithful where
--   map_injective {A B} f f' hf := by
--     ext
--     apply yoneda.map_injective
--     exact Functor.congr_map (CategoryTheory.Over.forget _) hf

variable (F : Psh C)

instance : (⊤ : MorphismProperty C).HasOfPostcompProperty ⊤ where
  of_postcomp := by simp

instance (P : MorphismProperty C) {X} : P.HasPullbacksAlong (𝟙 X) where
  hasPullback g hg :=
  have : IsPullback (𝟙 _) g g (𝟙 X) := IsPullback.of_horiz_isIso (by simp)
  IsPullback.hasPullback this

/-- `Over.pullback` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
noncomputable def Over.pullbackId (P Q : MorphismProperty C) (X)
    [Q.IsMultiplicative] [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    [Q.RespectsIso] : Over.pullback P Q (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (asIso (pullback.fst X.hom (𝟙 _)))
    (by simp [pullback.condition]))

def pullbackPullbackTwoSquare {T : Type u} [Category.{v} T] {R : MorphismProperty T}
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W) (sq : h ≫ g = f ≫ k)
    [R.IsStableUnderBaseChangeAlong h] [R.IsStableUnderBaseChangeAlong f]
    [R.IsStableUnderBaseChangeAlong g] [R.IsStableUnderBaseChangeAlong k]
    [R.HasPullbacksAlong h] [R.HasPullbacksAlong f] [R.HasPullbacksAlong g]
    [R.HasPullbacksAlong k] : TwoSquare (Over.pullback R ⊤ k) (Over.pullback R ⊤ g)
    (Over.pullback R ⊤ f) (Over.pullback R ⊤ h) :=
  (Over.pullbackComp _ _).inv ≫ (Over.pullbackCongr sq).inv ≫ (Over.pullbackComp _ _).hom

@[simp]
lemma pullbackPullbackTwoSquare_app_left {T : Type u} [Category.{v} T] {R : MorphismProperty T}
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W) (sq : h ≫ g = f ≫ k)
    [R.IsStableUnderBaseChangeAlong h] [R.IsStableUnderBaseChangeAlong f]
    [R.IsStableUnderBaseChangeAlong g] [R.IsStableUnderBaseChangeAlong k]
    [R.HasPullbacksAlong h] [R.HasPullbacksAlong f] [R.HasPullbacksAlong g]
    [R.HasPullbacksAlong k] (A : R.Over ⊤ W) :
    ((pullbackPullbackTwoSquare h f g k sq).app A).left =
    pullback.lift (pullback.map _ _ _ _ (pullback.fst _ _) h k
      (by simp [pullback.condition]) sq.symm) (pullback.snd _ _) (by cat_disch) := by
  dsimp [pullbackPullbackTwoSquare]
  ext <;> simp

/-- Fixing a commutative square,
```
   Y - k → W
   ∧        ∧
 f |        | g
   |        |
   X - h → Z
```
`pullbackMapTwoSquare` is the Beck-Chevalley natural transformation for `Over.map` between
the `MorphismProperty.Over` categories,
of type `pullback f ⋙ map h ⟶ map k ⋙ pullback g`.
```
           map k
 R.Over Y --------> R.Over W
    |                  |
    |                  |
pullback f     ↗    pullback g
    |                  |
    v                  V
 R.Over X  --------> R.Over Z
            map h
```
-/
def pullbackMapTwoSquare {T : Type u} [Category.{v} T] (R : MorphismProperty T)
    [R.IsStableUnderComposition]
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W) (rk : R k) (rh : R h)
    [R.IsStableUnderBaseChangeAlong h] [R.IsStableUnderBaseChangeAlong f]
    [R.IsStableUnderBaseChangeAlong g] [R.IsStableUnderBaseChangeAlong k]
    [R.HasPullbacksAlong h] [R.HasPullbacksAlong f] [R.HasPullbacksAlong g] [R.HasPullbacksAlong k]
    (sq : h ≫ g = f ≫ k) :
    TwoSquare (MorphismProperty.Over.pullback R ⊤ f) (MorphismProperty.Over.map ⊤ rk)
    (MorphismProperty.Over.map ⊤ rh)
    (MorphismProperty.Over.pullback R ⊤ g) :=
  (mateEquiv (MorphismProperty.Over.mapPullbackAdj k rk trivial)
    (MorphismProperty.Over.mapPullbackAdj h rh trivial)).symm <|
    pullbackPullbackTwoSquare _ _ _ _ sq

@[simp]
lemma pullbackMapTwoSquare_app_left {T : Type u} [Category.{v} T] (R : MorphismProperty T)
    [R.IsStableUnderComposition] {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W)
    (rk : R k) (rh : R h) (sq : h ≫ g = f ≫ k)
    [R.IsStableUnderBaseChangeAlong h] [R.IsStableUnderBaseChangeAlong f]
    [R.IsStableUnderBaseChangeAlong g] [R.IsStableUnderBaseChangeAlong k]
    [R.HasPullbacksAlong h] [R.HasPullbacksAlong f] [R.HasPullbacksAlong g] [R.HasPullbacksAlong k]
    (A : R.Over ⊤ Y) :
    have : HasPullback (A.hom ≫ k) g :=
      HasPullbacksAlong.hasPullback (A.hom ≫ k) (R.comp_mem _ _ A.prop rk)
    ((R.pullbackMapTwoSquare h f g k rk rh sq).app A).left =
    pullback.map A.hom f (A.hom ≫ k) g (𝟙 _) (by cat_disch) k (by cat_disch) (by cat_disch) := by
  have : HasPullback (A.hom ≫ k) g :=
    HasPullbacksAlong.hasPullback (A.hom ≫ k) (R.comp_mem _ _ A.prop rk)
  apply pullback.hom_ext <;> simp [pullbackMapTwoSquare]

theorem isCartesian_pullbackMapTwoSquare {T : Type u} [Category.{v} T] (R : MorphismProperty T)
    [R.IsStableUnderComposition]
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W) (rk : R k) (rh : R h)
    [R.IsStableUnderBaseChangeAlong h] [R.IsStableUnderBaseChangeAlong f]
    [R.IsStableUnderBaseChangeAlong g] [R.IsStableUnderBaseChangeAlong k]
    [R.HasPullbacksAlong h] [R.HasPullbacksAlong f] [R.HasPullbacksAlong g] [R.HasPullbacksAlong k]
    (sq : h ≫ g = f ≫ k) : (pullbackMapTwoSquare R h f g k rk rh sq).IsCartesian := by
  intro A B t
  apply Functor.reflect_isPullback (Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _)
  have (X : R.Over ⊤ Y) : HasPullback (X.hom ≫ k) g :=
     HasPullbacksAlong.hasPullback (X.hom ≫ k) (R.comp_mem _ _ X.prop rk)
  rw [CategoryTheory.IsPullback.flip_iff]
  fapply CategoryTheory.IsPullback.of_right (v₁₃ := t.left)
    (h₁₂ := pullback.fst (A.hom ≫ k) g) (h₂₂ := (pullback.fst (B.hom ≫ k) g))
  · convert_to (CategoryTheory.IsPullback (pullback.fst A.hom f)
      (pullback.lift (pullback.fst A.hom f ≫ t.left) (pullback.snd A.hom f)
      (by simp[pullback.condition])) t.left (pullback.fst B.hom f))
    · simp
    · simp
    · apply CategoryTheory.IsPullback.of_bot _ (by simp) (IsPullback.of_hasPullback B.hom f)
      convert_to (IsPullback (pullback.fst A.hom f) (pullback.snd A.hom f) A.hom f)
      · simp
      · simp
      · exact (IsPullback.of_hasPullback A.hom f)
  · ext <;> simp
  · convert_to
      (CategoryTheory.IsPullback
       (pullback.fst (A.hom ≫ k) g)
       (pullback.map (A.hom ≫ k) g (B.hom ≫ k) g t.left (𝟙 _) (𝟙 _) (by simp only [Functor.id_obj,
         Functor.const_obj_obj, comp_id, CategoryTheory.Over.w_assoc]) (by simp)) t.left
       (pullback.fst (B.hom ≫ k) g) )
    · simp [pullback.map]
    · apply CategoryTheory.IsPullback.of_bot _ (by simp) (IsPullback.of_hasPullback (B.hom ≫ k) g)
      convert_to (IsPullback (pullback.fst (A.hom ≫ k) g)
        (pullback.snd (A.hom ≫ k) g) (A.hom ≫ k) g)
      · simp
      · simp
      · exact (IsPullback.of_hasPullback (A.hom ≫ k) g)

/--
The Beck-Chevalley two-square `pushforwardPullbackTwoSquare` is a natural isomorphism
```
           map k
 R.Over Y --------> R.Over W
    |                  |
    |                  |
pullback f     ≅    pullback g
    |                  |
    v                  V
 R.Over X  --------> R.Over Z
            map h
```
when the commutativity
condition is strengthened to a pullback condition.
```
   Y - k → W
   ∧        ∧
 f |  (pb)  | g
   |        |
   X - h → Z
```
-/
instance pullbackMapTwoSquare_isIso {T : Type u} [Category.{v} T] (R : MorphismProperty T)
    [R.HasPullbacks] [R.IsStableUnderBaseChange] [R.IsStableUnderComposition]
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W)
    (rk : R k) (rh : R h) (pb : IsPullback h f g k) :
    IsIso <| pullbackMapTwoSquare R h f g k rk rh pb.w := by
  apply (config := {allowSynthFailures:= true}) NatIso.isIso_of_isIso_app
  intro A
  have : HasPullback (A.hom ≫ k) g :=
    HasPullbacksAlong.hasPullback (A.hom ≫ k) (R.comp_mem _ _ A.prop rk)
  apply (config := {allowSynthFailures:= true}) Functor.ReflectsIsomorphisms.reflects
    (Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _)
  simp only [Functor.comp_obj, Comma.forget_obj, Over.forget_obj, Over.map_obj_left,
    Over.pullback_obj_left, Over.map_obj_hom, Functor.comp_map, Comma.forget_map, Over.forget_map,
    pullbackMapTwoSquare_app_left, Functor.id_obj, Functor.const_obj_obj]
  apply CategoryTheory.IsPullback.pullback.map_isIso_of_pullback_right_of_comm_cube
  · cat_disch
  · assumption

@[simps]
def _root_.CategoryTheory.ExponentiableMorphism.isPushforward
    {T : Type u} [Category.{v} T] [HasPullbacks T]
    {X Y : T} (f : X ⟶ Y) [ExponentiableMorphism f] (h : Over X) :
    IsPushforward f h ((ExponentiableMorphism.pushforward f).obj h) where
  homEquiv := ((ExponentiableMorphism.adj f).homEquiv _ _).symm
  homEquiv_comp := by intros; simp [Adjunction.homEquiv_naturality_left_symm]

def _root_.CategoryTheory.ExponentiableMorphism.hasPushforward
    {T : Type u} [Category.{v} T] [HasPullbacks T]
    {X Y : T} (f : X ⟶ Y) [ExponentiableMorphism f] (h : Over X) :
    HasPushforward f h where
  has_representation := ⟨(ExponentiableMorphism.pushforward f).obj h,
    ⟨ExponentiableMorphism.isPushforward f h⟩⟩

attribute [local instance] ExponentiableMorphism.hasPushforward

instance {T : Type u} [Category.{v} T] (R : MorphismProperty T) {X Y : T} (f : X ⟶ Y)
    [HasPullbacksAlong f] [HasPushforwardsAlong f] : R.HasPushforwardsAlong f where
  hasPushforward := inferInstance

/-- Given an exponentiable morphism, global pushforward (defined using the
`ExponentiableMorphism` API) commutes with local pushforward
(defined using the `HasPushforward` API). -/
def pushforwardCompForget' {T : Type u} [Category.{v} T] [HasFiniteWidePullbacks T]
    {R : MorphismProperty T} {X Y : T} (f : X ⟶ Y) [ExponentiableMorphism f]
    [R.IsStableUnderPushforwardsAlong f] : R.pushforward f ⋙ Over.forget R ⊤ Y ≅
    Over.forget R ⊤ X ⋙ ExponentiableMorphism.pushforward f :=
  calc R.pushforward f ⋙ Over.forget R ⊤ Y
  _ ≅ R.pushforwardPartial f := pushforwardCompForget ..
  _ ≅ pushforwardPartial.lift R f ⋙ ObjectProperty.ι _ ⋙ ExponentiableMorphism.pushforward f :=
    (Functor.isoWhiskerLeft _
    (Functor.isoPartialRightAdjoint _ _ (Functor.rightAdjoint.partialRightAdjoint _))).symm
  _ ≅ Over.forget R ⊤ X ⋙ ExponentiableMorphism.pushforward f := Iso.refl _

def pullbackPostYonedaIso {T : Type u} [Category.{v} T]
    {X Y : T} (f : X ⟶ Y) [HasPullbacksAlong f] :
    CategoryTheory.Over.pullback f ⋙ Over.post yoneda ≅
    Over.post yoneda ⋙ CategoryTheory.Over.pullback ym(f) :=
  NatIso.ofComponents
  (fun A => CategoryTheory.Over.isoMk (PreservesPullback.iso yoneda A.hom f))
  (fun {A B} g => by
    apply (CategoryTheory.Over.forget _).map_injective
    apply pullback.hom_ext <;> simp)

def pullbackYonedaIso {T : Type u} [Category.{max u v} T]
    (R : MorphismProperty T) [R.HasPullbacks] [R.IsStableUnderBaseChange]
    {X Y : T} (f : X ⟶ Y) : Over.pullback R ⊤ f ⋙ Over.yoneda R X ≅
    Over.yoneda R Y ⋙ CategoryTheory.Over.pullback ym(f) :=
  NatIso.ofComponents
  (fun A => CategoryTheory.Over.isoMk (PreservesPullback.iso yoneda A.hom f))
  (fun {A B} g => by
    apply (CategoryTheory.Over.forget _).map_injective
    apply pullback.hom_ext <;> simp)

/-- The inclusions of `Over.yoneda` commute with pushforward. -/
def pushforwardYonedaIso {T : Type u} [Category.{u} T]
    (R : MorphismProperty T) [R.HasPullbacks] [R.IsStableUnderBaseChange]
    {X Y : T} (f : X ⟶ Y) [HasPullbacksAlong f]
    [R.HasPushforwardsAlong f] [R.IsStableUnderPushforwardsAlong f] :
    R.pushforward f ⋙ Over.yoneda R Y ≅
    Over.yoneda R X ⋙ ExponentiableMorphism.pushforward ym(f) :=
  -- instead of proving directly that
  -- `R.pushforward f ⋙ Over.yoneda R Y ≅ Over.yoneda R X ⋙ ExponentiableMorphism.pushforward ym(f)`
  -- e.g. using the universal property of `ExponentiableMorphism.pushforward ym(f)`
  -- which is universal among *all* objects of `Over y(Y)`,
  -- we prove that both sides are universal among objects of `Over Y`
  -- (rather, their images under `Over.post yoneda`). This is `Over.yonedaNatIsoMk`
  Over.yonedaNatIsoMk <|
  let postFF {X} := (Functor.FullyFaithful.ofFullyFaithful (Over.post (X := X) yoneda)).homIso
  -- `Over y(Y) (Over.post yoneda (-), Over.yoneda (R.pushforward f (⋆)))`
  calc (R.pushforward f ⋙ Over.yoneda R Y) ⋙ yoneda ⋙
      (Functor.whiskeringLeft _ _ _).obj (Over.post yoneda).op
    _ ≅ R.pushforward f ⋙ Over.forget _ _ _ ⋙ Over.post yoneda ⋙ yoneda ⋙
      (Functor.whiskeringLeft _ _ _).obj (Over.post yoneda).op :=
      Functor.associator .. ≪≫ Functor.isoWhiskerLeft _ (Functor.associator ..)
    -- `Over Y (-, Over.forget (R.pushforward f (⋆)))`
    _ ≅ R.pushforward f ⋙ Over.forget _ _ _ ⋙ yoneda :=
      -- `Over.post yoneda` is fully faithful
      (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ postFF)).symm
    -- `Over Y (pullback f (-), Over.forget (⋆))`
    _ ≅ Over.forget _ _ _ ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Over.pullback f).op :=
      -- homIso for partial adjunction `Over.pullback f ∂⊣ R.pushforward f`
      pushforward.homIso.symm
    -- `Over (y(Y)) (pullback f ⋙ Over.post yoneda (-), Over.forget ⋙ Over.post yoneda (⋆))`
    _ ≅ Over.forget _ _ _ ⋙ (Over.post yoneda ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj ((Over.post yoneda).op)) ⋙
        (Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Over.pullback f).op :=
      -- `Over.post yoneda` is fully faithful
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight postFF _)
    _ ≅ Over.forget _ _ _ ⋙ Over.post yoneda ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
        (CategoryTheory.Over.pullback f ⋙ Over.post yoneda).op :=
      Functor.isoWhiskerLeft _ (Functor.associator .. ≪≫ Functor.isoWhiskerLeft _
        (Functor.isoWhiskerLeft _ ((Functor.whiskeringLeftObjCompIso ..).symm ≪≫
        Functor.mapIso _ (Functor.opComp ..).symm)))
    -- `Over (y(Y)) (pullback f ⋙ Over.post yoneda (-), Over.yoneda (⋆))`
    _ ≅ Over.yoneda R X ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
        (CategoryTheory.Over.pullback f ⋙ Over.post yoneda).op :=
      (Functor.associator ..).symm
    -- `Over (y(Y)) (pullback ym(f) (-), pushforward ym(f) (Over.yoneda (⋆)))`
    _ ≅ Over.yoneda R X ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
        (Over.post yoneda ⋙ CategoryTheory.Over.pullback ym(f)).op :=
      -- `Over.post yoneda` preserves pullback
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.mapIso _
        (NatIso.op (pullbackPostYonedaIso ..).symm)))
    _ ≅ Over.yoneda R X ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Over.pullback ym(f)).op ⋙
        (Functor.whiskeringLeft _ _ _).obj (Over.post yoneda).op :=
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (Functor.mapIso _ (Functor.opComp ..) ≪≫ Functor.whiskeringLeftObjCompIso ..))
    -- `Over (y(Y)) (Over.post yoneda (-), pushforward ym(f) (Over.yoneda (⋆)))`
    _ ≅ Over.yoneda R X ⋙ ExponentiableMorphism.pushforward ym(f) ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (Over.post yoneda).op :=
    -- by homIso for adjunction `pullback ym(f) ⊣ pushforward ym(f)`
      Functor.isoWhiskerLeft _ ((Functor.associator ..).symm ≪≫ (Functor.isoWhiskerRight
        (ExponentiableMorphism.adj ym(f)).homIso _) ≪≫ Functor.associator ..)
    _ ≅ (Over.yoneda R X ⋙ ExponentiableMorphism.pushforward ym(f)) ⋙ yoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (Over.post yoneda).op :=
      (Functor.associator ..).symm

/-- Fixing a pullback square,
```
   Z - g → W
   ∧        ∧
 h |  (pb)  | k
   |        |
   X - f → Y
```
`pushforwardPullbackIso` is the Beck-Chevalley natural isomorphism for pushforwards between
the `MorphismProperty.Over` categories,
of type `pushforward g ⋙ pullback k ≅ pullback h ⋙ pushforward f`.
```
      R.Over ⊤ Z - pushforward g → R.Over ⊤ W
           |                           |
pullback h |           ↙≅             | pullback k
           V                           V
      R.Over ⊤ X - pushforward f → R.Over ⊤ Y
```
-/
def pushforwardPullbackIso {T : Type u} [Category.{u} T] {R : MorphismProperty T}
    [R.HasPullbacks] [R.IsStableUnderBaseChange]
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    [R.HasPushforwardsAlong f] [R.IsStableUnderPushforwardsAlong f]
    [R.HasPushforwardsAlong g] [R.IsStableUnderPushforwardsAlong g]
    (pb : IsPullback h f g k) :
    R.pushforward g ⋙ Over.pullback R ⊤ k ≅ Over.pullback R ⊤ h ⋙ R.pushforward f :=
  -- since `Over.yoneda R Y : R.Over ⊤ Y ⥤ Over y(Y)` is fully faithful,
  -- it suffices to define an isomorphism between the post-composed functors
  (Functor.FullyFaithful.whiskeringRight
    (Functor.FullyFaithful.ofFullyFaithful (Over.yoneda R Y)) (R.Over ⊤ Z)).preimageIso <|
  calc (R.pushforward g ⋙ Over.pullback R ⊤ k) ⋙ Over.yoneda R Y
  _ ≅ R.pushforward g ⋙ Over.pullback R ⊤ k ⋙ Over.yoneda R Y := Functor.associator _ _ _
  _ ≅ R.pushforward g ⋙ Over.yoneda R W ⋙ CategoryTheory.Over.pullback ym(k) :=
    -- pullback commutes with `Over.yoneda`
    Functor.isoWhiskerLeft _ (pullbackYonedaIso R k)
  _ ≅ (R.pushforward g ⋙ Over.yoneda R W) ⋙ CategoryTheory.Over.pullback ym(k) :=
      (Functor.associator _ _ _).symm
  _ ≅ (Over.yoneda R Z ⋙ ExponentiableMorphism.pushforward ym(g)) ⋙
      CategoryTheory.Over.pullback ym(k) :=
    -- pushforward commutes with `Over.yoneda`
    Functor.isoWhiskerRight (pushforwardYonedaIso ..) _
  _ ≅ Over.yoneda R Z ⋙ ExponentiableMorphism.pushforward ym(g) ⋙
      CategoryTheory.Over.pullback ym(k) := Functor.associator _ _ _
  _ ≅ Over.yoneda R Z ⋙ CategoryTheory.Over.pullback ym(h) ⋙
      ExponentiableMorphism.pushforward ym(f) :=
    -- Beck-Chevalley isomorphism in `Psh T`
    Functor.isoWhiskerLeft _ (pushforwardPullbackIsoSquare (Functor.map_isPullback _ pb))
  _ ≅ (Over.yoneda R Z ⋙ CategoryTheory.Over.pullback ym(h)) ⋙
      ExponentiableMorphism.pushforward ym(f) := (Functor.associator _ _ _).symm
  _ ≅ (Over.pullback R ⊤ h ⋙ Over.yoneda R X) ⋙ ExponentiableMorphism.pushforward ym(f) :=
    -- pullback commutes with `Over.yoneda`
    Functor.isoWhiskerRight (pullbackYonedaIso R h).symm _
  _ ≅ Over.pullback R ⊤ h ⋙ Over.yoneda R X ⋙ ExponentiableMorphism.pushforward ym(f) :=
    Functor.associator _ _ _
  _ ≅ Over.pullback R ⊤ h ⋙ R.pushforward f ⋙ Over.yoneda R Y :=
    -- pushforward commutes with `Over.yoneda`
    Functor.isoWhiskerLeft _ (pushforwardYonedaIso ..).symm
  _ ≅ (Over.pullback R ⊤ h ⋙ R.pushforward f) ⋙ Over.yoneda R Y := (Functor.associator _ _ _).symm

/-- Fixing a commutative square,
```
   Z - g → W
   ∧        ∧
 h |        | k
   |        |
   X - f → Y
```
`pushforwardPullbackTwoSquare` is the Beck-Chevalley natural transformation for pushforwards between
the `MorphismProperty.Over` categories,
of type `pushforward g ⋙ pullback k ⟶ pullback h ⋙ pushforward f`.
```
      R.Over ⊤ Z - pushforward g → R.Over ⊤ W
           |                           |
pullback h |           ↙              | pullback k
           V                           V
      R.Over ⊤ X - pushforward f → R.Over ⊤ Y
```
It is the mate of the square of pullback functors
`pullback k ⋙ pullback g ⟶ pullback f ⋙ pullback h`.
-/
def pushforwardPullbackTwoSquare {T : Type u} [Category.{v} T] {R : MorphismProperty T}
    [R.HasPullbacks] [R.IsStableUnderBaseChange] {X Y Z W : T}
    (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W) (sq : h ≫ g = f ≫ k)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    [R.HasPushforwardsAlong f] [R.IsStableUnderPushforwardsAlong f]
    [R.HasPushforwardsAlong g] [R.IsStableUnderPushforwardsAlong g] :
    TwoSquare (pushforward R g) (Over.pullback R ⊤ h) (Over.pullback R ⊤ k)
    (pushforward R f) :=
  mateEquiv (pullbackPushforwardAdjunction R g) (pullbackPushforwardAdjunction R f)
    (pullbackPullbackTwoSquare _ _ _ _ sq)

lemma pushforwardPullbackTwoSquare_app {T : Type u} [Category.{v} T] {R : MorphismProperty T}
    [R.HasPullbacks] [R.IsStableUnderBaseChange] {X Y Z W : T}
    (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W) (sq : h ≫ g = f ≫ k)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    [R.HasPushforwardsAlong f] [R.IsStableUnderPushforwardsAlong f]
    [R.HasPushforwardsAlong g] [R.IsStableUnderPushforwardsAlong g]
    (A : R.Over ⊤ Z) :
    (pushforwardPullbackTwoSquare h f g k sq).app A = sorry := by
  simp [pushforwardPullbackTwoSquare]
  -- apply ((pullbackPushforwardAdjunction R f).homEquiv _ _).symm.injective
  ext
  simp
  -- erw [commaCategory.id]
  -- simp [- EmbeddingLike.apply_eq_iff_eq, pullbackPushforwardAdjunction]
  -- rw [pushforward.homEquiv_map_comp]
  -- erw [pushforward.homEquiv.apply_symm_apply]
  -- erw [Category.id_comp]
  -- apply (pushforwardPullbackAdjunction.homEquiv i p).injective
  sorry

-- TODO: currently this theorem is unnecessary,
-- but it would be nice to show that these two definitions actually line up.
-- We have both definitions because
-- `pushforwardPullbackTwoSquare` can be defined under more general conditions,
-- without a pullback condition on the commuting square
-- but constructing an isomorphism directly `pushforwardPullbackIso` is easier
-- than showing `pushforwardPullbackTwoSquare` is an isomorphism.

/-
/--
The Beck-Chevalley two-square `pushforwardPullbackTwoSquare` is a natural isomorphism
```
      R.Over ⊤ Z - pushforward g → R.Over ⊤ W
           |                           |
pullback h |            ≅              | pullback k
           V                           V
      R.Over ⊤ X - pushforward f → R.Over ⊤ Y
```
when the commutativity
condition is strengthened to a pullback condition.
```
   Z - g → W
   ∧        ∧
 h |  (pb)  | k
   |        |
   X - f → Y
```
TODO: in what generality does this theorem hold?
NOTE: we know it holds when for π-clans with `R = Q = the π-clan`
([Joyal, Notes on Clans and Tribes, Cor 2.4.11](https://arxiv.org/pdf/1710.10238)).
NOTE: we also know it holds in a category with pullbacks with `R = ⊤` and `Q = ExponentiableMaps`.
-/
theorem pushforwardPullbackTwoSquare_isIso {T : Type u} [Category.{u} T]
    (R : MorphismProperty T)
    [R.HasPullbacks] [R.IsStableUnderBaseChange]
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    [R.HasPushforwardsAlong f] [R.IsStableUnderPushforwardsAlong f]
    [R.HasPushforwardsAlong g] [R.IsStableUnderPushforwardsAlong g]
    (pb : IsPullback h f g k) :
    IsIso (pushforwardPullbackTwoSquare (R := R) h f g k pb.w) := by
  have eq : (pushforwardPullbackTwoSquare h f g k pb.w) =
      (pushforwardPullbackIso (R := R) h f g k pb).hom := by
    ext A : 1
    -- simp [pushforwardPullbackTwoSquare, pushforwardPullbackIso]
    sorry
  rw [eq]
  infer_instance
-/
