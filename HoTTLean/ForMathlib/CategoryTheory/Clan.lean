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

@[simp]
def Local (X : C) : MorphismProperty (R.Over ⊤ X) := fun _ _ f => R f.left

section pullback

variable {R} [R.HasPullbacks] {X : C}

lemma Local.hasPullback {U V W : R.Over ⊤ X} {f : U ⟶ W} (g : V ⟶ W) (rf : R f.left) :
    HasPullback f.left g.left :=
  MorphismProperty.HasPullbacks.hasPullback (g.left) (f:= f.left) rf

variable [R.IsStableUnderComposition] [R.IsStableUnderBaseChange]

def Local.pullback {U V W : R.Over ⊤ X} {f : U ⟶ W} (g : V ⟶ W) (rf : R f.left) : R.Over ⊤ X :=
  have := Local.hasPullback g rf
  .mk ⊤ ((pullback.snd f.left g.left) ≫ V.hom)
  (R.comp_mem _ _ (R.of_isPullback (IsPullback.of_hasPullback f.left g.left) rf) V.prop)

def Local.pullback.fst {U V W : R.Over ⊤ X} {f : U ⟶ W} (g : V ⟶ W) (rf : R f.left) :
    Local.pullback g rf ⟶ U :=
  have := Local.hasPullback g rf
  Over.homMk (Limits.pullback.fst f.left g.left) (by
    simp only [pullback, ← Over.w f, Limits.pullback.condition_assoc]
    simp)

def Local.pullback.snd {U V W : R.Over ⊤ X} {f : U ⟶ W} (g : V ⟶ W) (rf : R f.left) :
    Local.pullback g rf ⟶ V :=
  have := Local.hasPullback g rf
  Over.homMk (Limits.pullback.snd f.left g.left)

theorem Local.pullback.isPullback {U V W : R.Over ⊤ X} {f : U ⟶ W} (g : V ⟶ W) (rf : R f.left) :
    IsPullback (Local.pullback.fst g rf) (Local.pullback.snd g rf) f g := by
  have := Local.hasPullback g rf
  have : (CostructuredArrow.proj (𝟭 C) X).Faithful := CostructuredArrow.proj_faithful -- why?
  have : ReflectsLimitsOfShape WalkingCospan (CostructuredArrow.proj (𝟭 C) X) := inferInstance -- why?
  apply Functor.reflect_isPullback (Over.forget R ⊤ X ⋙ CostructuredArrow.proj (Functor.id C) X)
  simpa [fst, snd, Comma.Hom.hom_left] using IsPullback.of_hasPullback f.left g.left

variable (X)

instance : (Local R X).HasPullbacks where
  hasPullback {U V W} f g rf := by
    have := Local.hasPullback g rf
    let pbinC := IsPullback.of_hasPullback f.left g.left
    --  let P : R.Over ⊤ X := .mk ⊤ ((pullback.snd f.left g.left) ≫ V.hom)
    -- (by apply R.comp_mem
    --   sorry)
    --  apply IsPullback.hasPullback
    sorry

    -- let F := CostructuredArrow.proj (Functor.id C) X
    -- have p00:  PreservesLimit (cospan f g) (Over.forget R ⊤ X) := sorry
    -- have p0 :  PreservesLimit (cospan f g ⋙ Over.forget R ⊤ X)
    --     (CostructuredArrow.proj (𝟭 C) X) := sorry

    -- have p1 : @PreservesLimit
    --     (R.Over ⊤ X) _ C _ WalkingCospan _ (cospan f g)
    --     (Over.forget R ⊤ X ⋙ (CostructuredArrow.proj (Functor.id C) X)) := by
    --      apply CategoryTheory.Limits.comp_preservesLimit

    -- have p: IsPullback fst.left snd.left f.left g.left := by
    --    apply Functor.map_isPullback
    --          (Over.forget R ⊤ X ⋙ CostructuredArrow.proj (Functor.id C) X) i
    -- simp[Local] at *
    -- apply R.of_isPullback p rf

instance : (Local R X).IsStableUnderBaseChange where
  of_isPullback {W V P K} g f fst snd i rf := by
    have := Local.hasPullback g rf
    rw [← IsPullback.isoIsPullback_hom_snd _ _ i (Local.pullback.isPullback g rf), Local]
    exact RespectsIso.precomp _ _ _ (R.of_isPullback (IsPullback.of_hasPullback f.left g.left) rf)

end pullback

instance (X : C) [R.IsStableUnderComposition] [R.IsStableUnderBaseChange] :
  (Local R X).IsStableUnderBaseChange := sorry

instance (X : C) : (Local R X).HasObjects := sorry

instance (X : C) [R.ContainsIdentities] : (Local R X).ContainsIdentities where
  id_mem _ := R.id_mem _

instance (X : C) [R.IsStableUnderComposition] :
    (Local R X).IsStableUnderComposition where
  comp_mem _ _ := R.comp_mem _ _

abbrev chosenTerminal [R.ContainsIdentities] (X) : R.Over ⊤ X := .mk ⊤ (𝟙 X) (R.id_mem _)

@[simps!]
protected def Over.post (R : MorphismProperty C) (R' : MorphismProperty C')
    [F.PreservesMorphismProperty R R'] (X : C) : R.Over ⊤ X ⥤ R'.Over ⊤ (F.obj X) where
  obj X := MorphismProperty.Over.mk ⊤ (F.map X.hom) (F.map_mem _ X.prop)
  map f := MorphismProperty.Over.homMk (F.map f.left) (by simp [← F.map_comp])
  map_id := sorry
  map_comp := sorry

instance {R' : MorphismProperty C'} [F.PreservesMorphismProperty R R'] (X : C) :
    (Over.post F R R' X).PreservesMorphismProperty (Local R X) (Local R' (F.obj X)) where
  map_mem _ := F.map_mem _

instance {R' : MorphismProperty C'} [F.PreservesMorphismProperty R R'] [F.PreservesPullbacksOf R]
    (X : C) : (Over.post F R R' X).PreservesPullbacksOf (Local R X) where
  pb := sorry

@[simp]
lemma localFunctor_obj_chosenTerminal [R.ContainsIdentities] {R' : MorphismProperty C'}
    [R'.ContainsIdentities] [F.PreservesMorphismProperty R R'] (X : C) :
    (Over.post F R R' X).obj (R.chosenTerminal X) = R'.chosenTerminal (F.obj X) := by
  cat_disch

instance [R.IsStableUnderBaseChange] {X Y : C} (f : X ⟶ Y) [R.HasPullbacksAlong f] :
    (Over.pullback R ⊤ f).PreservesMorphismProperty (Local R Y) (Local R X) := sorry

instance [R.IsStableUnderBaseChange] {X Y : C} (f : X ⟶ Y) [R.HasPullbacksAlong f] :
    (Over.pullback R ⊤ f).PreservesPullbacksOf (Local R Y) := sorry

def Over.pullback_obj_chosenTerminal [R.IsStableUnderBaseChange] [R.ContainsIdentities]
    {X Y : C} (f : X ⟶ Y) [R.HasPullbacksAlong f] :
    (Over.pullback R ⊤ f).obj (R.chosenTerminal Y) ≅ R.chosenTerminal X :=
  have : HasPullback (𝟙 Y) f := HasPullbacksAlong.hasPullback (𝟙 Y) (R.id_mem Y)
  MorphismProperty.Over.isoMk (IsPullback.id_vert f).isoPullback.symm

structure RepresentableFibrantChosenPullbacks {X Y : Psh C} (f : X ⟶ Y)
    extends RepresentableChosenPullbacks f where
  fibrant {Γ : C} (b : y(Γ) ⟶ Y) : R (disp b)

-- this is a preclan, does not satisfy HasObjects
def ExtendedFibration : MorphismProperty (Psh C) :=
  fun _ _ f => Nonempty (RepresentableFibrantChosenPullbacks R f)

instance : (ExtendedFibration R).IsStableUnderBaseChange := sorry

instance : (ExtendedFibration R).HasPullbacks := sorry

instance [R.ContainsIdentities] : (ExtendedFibration R).ContainsIdentities where
  id_mem _ := sorry

instance [R.IsStableUnderComposition] : (ExtendedFibration R).IsStableUnderComposition where
  comp_mem _ _ hf hg := sorry

notation:max R"^("F")"  => Local (ExtendedFibration R) F

namespace ExtendedFibration

variable [R.HasPullbacks] [R.IsStableUnderBaseChange]

def yonedaRepresentableFibrantChosenPullbacks (X Y : C) (f : X ⟶ Y) (rf : R f) :
    R.RepresentableFibrantChosenPullbacks (CategoryTheory.yoneda.map f) :=
  have h {Γ} (A : Γ ⟶ Y) : HasPullback f A := HasPullbacks.hasPullback _ rf
  { ext A := pullback f (yoneda.preimage A)
    disp A := pullback.snd _ _
    var _ := ym(pullback.fst _ _)
    disp_pullback := sorry
    fibrant A := IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) rf }

/-- This is the functor `R(X) -> R^(X)`. -/
@[simps]
protected def yoneda (X : C) : R.Over ⊤ X ⥤ (ExtendedFibration R).Over ⊤ y(X) where
  obj A := .mk ⊤ ym(A.hom) ⟨yonedaRepresentableFibrantChosenPullbacks R _ _ _ A.prop⟩
  map {A B} f := Over.homMk ym(f.left)
  map_id := sorry
  map_comp := sorry

instance (X : C) : (ExtendedFibration.yoneda R X).Full where
  map_surjective {A B} f :=
  ⟨Over.homMk (yoneda.preimage f.left) (by apply yoneda.map_injective; simp; exact Over.w f),
   by cat_disch⟩

instance (X : C) : (ExtendedFibration.yoneda R X).Faithful where
  map_injective {A B} f f' hf := by
    ext
    apply yoneda.map_injective
    exact Functor.congr_map (Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _) hf

variable (F : Psh C)

example [R.IsStableUnderComposition] : (R^(F)).HasPullbacks := inferInstance
example [R.IsStableUnderComposition] : (R^(F)).IsStableUnderBaseChange := inferInstance
example : (R^(F)).HasObjects := inferInstance
example [R.ContainsIdentities] : (R^(F)).ContainsIdentities := inferInstance
example [R.IsStableUnderComposition] : (R^(F)).IsStableUnderComposition := inferInstance

example (X : C) : (ExtendedFibration.yoneda R X).ReflectsIsomorphisms := inferInstance

end ExtendedFibration

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
theorem pullbackMapTwoSquare_isIso {T : Type u} [Category.{v} T] (R : MorphismProperty T)
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

-- lemma pushforwardPullbackTwoSquare_ {T : Type u} [Category.{v} T] {R : MorphismProperty T}
--     [R.HasPullbacks] [R.IsStableUnderBaseChange] {X Y Z W : T}
--     (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W) (sq : h ≫ g = f ≫ k)
--     [HasPullbacksAlong f] [HasPullbacksAlong g]
--     [R.HasPushforwardsAlong f] [R.IsStableUnderPushforwardsAlong f]
--     [R.HasPushforwardsAlong g] [R.IsStableUnderPushforwardsAlong g] (A : R.Over ⊤ Z) :
--     (pushforwardPullbackTwoSquare h f g k sq).app A = sorry := by
--   apply (Over.forget R ⊤ Y).map_injective
--   simp [pushforwardPullbackTwoSquare, ← Functor.map_comp]
--   rw [pushforward.homEquiv_symm_comp]
--   rw [Equiv.symm_apply_eq]
--   simp
--   erw [Category.id_comp]
--   ext
--   simp
--   ext
--   · simp
--     sorry
--   · sorry

def pullbackForgetTwoSquare {T : Type u} [Category.{v} T] [HasFiniteWidePullbacks T]
    [LocallyCartesianClosed T] {R : MorphismProperty T} {X Y : T} (f : X ⟶ Y)
    [R.IsStableUnderBaseChangeAlong f] :
    Over.pullback R ⊤ f ⋙ Over.forget R ⊤ X ≅ Over.forget R ⊤ Y ⋙ CategoryTheory.Over.pullback f :=
  sorry

@[simps]
def _root_.CategoryTheory.ExponentiableMorphism.pullbackRepresentableByPushforward
    {T : Type u} [Category.{v} T] [HasPullbacks T]
    {X Y : T} (f : X ⟶ Y) [ExponentiableMorphism f] (h : Over X) :
    ((CategoryTheory.Over.pullback f).op ⋙ y(h)).RepresentableBy
    ((ExponentiableMorphism.pushforward f).obj h) where
  homEquiv := ((ExponentiableMorphism.adj f).homEquiv _ _).symm
  homEquiv_comp := by intros; simp [Adjunction.homEquiv_naturality_left_symm]

def _root_.CategoryTheory.ExponentiableMorphism.hasPushforward
    {T : Type u} [Category.{v} T] [HasPullbacks T]
    {X Y : T} (f : X ⟶ Y) [ExponentiableMorphism f] (h : Over X) :
    HasPushforward f h where
  has_representation := ⟨(ExponentiableMorphism.pushforward f).obj h,
    ⟨ExponentiableMorphism.pullbackRepresentableByPushforward f h⟩⟩

attribute [local instance] ExponentiableMorphism.hasPushforward

instance {T : Type u} [Category.{v} T] (R : MorphismProperty T) {X Y : T} (f : X ⟶ Y)
    [HasPullbacksAlong f] [HasPushforwardsAlong f] : R.HasPushforwardsAlong f where
  hasPushforward := inferInstance

/-- In a locally cartesian closed category, global pushforward (defined using the
`ExponentiableMorphism` API) commutes with local pushforward
(defined using the `HasPushforward` API). -/
def pushforwardForgetTwoSquare {T : Type u} [Category.{v} T] [HasFiniteWidePullbacks T]
    [LocallyCartesianClosed T] {R : MorphismProperty T} {X Y : T} (f : X ⟶ Y)
    [R.IsStableUnderPushforwardsAlong f] :
    Over.forget R ⊤ X ⋙ ExponentiableMorphism.pushforward f ≅
    R.pushforward f ⋙ Over.forget R ⊤ Y :=
  calc Over.forget R ⊤ X ⋙ ExponentiableMorphism.pushforward f
  _ ≅ pushforwardPartial.lift R f ⋙ ObjectProperty.ι _ ⋙ ExponentiableMorphism.pushforward f :=
    Iso.refl _
  _ ≅ _ := Functor.isoWhiskerLeft _
    (Functor.isoPartialRightAdjoint _ _ (Functor.rightAdjoint.partialRightAdjoint _))
  _ ≅ R.pushforward f ⋙ Over.forget R ⊤ Y := (pushforwardCompForget ..).symm

theorem pushforwardPullbackTwoSquare_isIso_extendedFibration {T : Type u} [Category.{max u v} T]
    (R : MorphismProperty T)
    [R.HasPullbacks] [R.IsStableUnderBaseChange]
    {X Y Z W : Psh T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W) (sq : h ≫ g = f ≫ k)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    [(ExtendedFibration R).HasPushforwardsAlong f] -- TODO: should be automatic in Psh T
    [(ExtendedFibration R).IsStableUnderPushforwardsAlong f]
    -- TODO: should follow from [R.IsStableUnderPushforwardsAlong f]
    [(ExtendedFibration R).HasPushforwardsAlong g] -- TODO: should be automatic in Psh T
    [(ExtendedFibration R).IsStableUnderPushforwardsAlong g]
    -- TODO: should follow from [R.IsStableUnderPushforwardsAlong g]
    (pb : IsPullback h f g k) :
    IsIso (pushforwardPullbackTwoSquare (R := ExtendedFibration R) h f g k pb.w) := by
  let α : (R.ExtendedFibration.pushforward g ⋙ Over.pullback R.ExtendedFibration ⊤ k) ⋙
    Over.forget R.ExtendedFibration ⊤ Y ⟶
    (Over.pullback R.ExtendedFibration ⊤ h ⋙ R.ExtendedFibration.pushforward f) ⋙
    Over.forget R.ExtendedFibration ⊤ Y := sorry
  -- TODO: define α as the following composition. All should be either x.hom for some iso x or
    -- a morphism such that IsIso x
  -- (R.pushforward g ⋙ Over.pullback R ⊤ k) ⋙ ExtendedFibration.yoneda R Y
  -- ≅ R.pushforward g ⋙ Over.pullback R ⊤ k ⋙ ExtendedFibration.yoneda R Y
  -- ≅ R.pushforward g ⋙ ExtendedFibration.yoneda R W ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(k)
  -- ≅ (R.pushforward g ⋙ ExtendedFibration.yoneda R W) ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(k)
  -- ≅ (ExtendedFibration.yoneda R Z ⋙ (ExtendedFibration R).pushforward ym(g)) ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(k)
  -- ≅ ExtendedFibration.yoneda R Z ⋙ (ExtendedFibration R).pushforward ym(g) ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(k)
  -- use `pushforwardPullbackTwoSquare_isIso_extendedFibration` here
  -- ≅ ExtendedFibration.yoneda R Z ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(h) ⋙ (ExtendedFibration R).pushforward f
  -- ≅ (ExtendedFibration.yoneda R Z ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(h)) ⋙ (ExtendedFibration R).pushforward f
  -- ≅ (Over.pullback R ⊤ h ⋙ ExtendedFibration.yoneda R X) ⋙ (ExtendedFibration R).pushforward f
  -- ≅ Over.pullback R ⊤ h ⋙ ExtendedFibration.yoneda R X ⋙ (ExtendedFibration R).pushforward f
  -- ≅ Over.pullback R ⊤ h ⋙ R.pushforward f ⋙ ExtendedFibration.yoneda R Y
  -- ≅ (Over.pullback R ⊤ h ⋙ R.pushforward f) ⋙ ExtendedFibration.yoneda R Y
  have : IsIso α := sorry -- should be automatic by infer_instance. Then remove.
  have eq : Functor.whiskerRight (pushforwardPullbackTwoSquare h f g k pb.w)
      (Over.forget R.ExtendedFibration ⊤ Y) = α := sorry
  have : IsIso (Functor.whiskerRight (pushforwardPullbackTwoSquare h f g k pb.w)
      (Over.forget R.ExtendedFibration ⊤ Y)) := by rw [eq]; infer_instance
  apply NatTrans.isIso_of_whiskerRight_isIso _ (Over.forget _ _ _)
  -- apply (config := {allowSynthFailures:= true}) NatIso.isIso_of_isIso_app
  -- intro A
  -- apply (config := {allowSynthFailures:= true}) Functor.ReflectsIsomorphisms.reflects
  --   (ExtendedFibration.yoneda R Y ⋙ Over.forget _ _ _)
  -- -- apply (config := {allowSynthFailures:= true}) yoneda.map_isIso
  -- -- simp
  -- have pb : IsPullback ym(h) ym(f) ym(g) ym(k) := sorry
  -- have l := CategoryTheory.Over.pushforwardPullbackTwoSquare ym(h) ym(f) ym(g) ym(k) pb.toCommSq
  -- have li := CategoryTheory.pushforwardPullbackTwoSquare_of_isPullback_isIso pb
  -- have lii := NatIso.isIso_app_of_isIso
  --   (CategoryTheory.Over.pushforwardPullbackTwoSquare ym(h) ym(f) ym(g) ym(k) pb.toCommSq)
  --   ((ExtendedFibration.yoneda R Z ⋙ Over.forget _ _ _).obj A)
  -- have : IsIso l := inferInstanceAs $ IsIso $ CategoryTheory.Over.pushforwardPullbackTwoSquare ym(h) ym(f) ym(g) ym(k) pb.toCommSq
  -- sorry

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
theorem pushforwardPullbackTwoSquare_isIso {T : Type u} [Category.{max u v} T]
    (R : MorphismProperty T)
    [R.HasPullbacks] [R.IsStableUnderBaseChange]
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W) (sq : h ≫ g = f ≫ k)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    [R.HasPushforwardsAlong f] [R.IsStableUnderPushforwardsAlong f]
    [R.HasPushforwardsAlong g] [R.IsStableUnderPushforwardsAlong g]
    (pb : IsPullback h f g k) :
    IsIso (pushforwardPullbackTwoSquare (R := R) h f g k pb.w) := by
  let α : (R.pushforward g ⋙ Over.pullback R ⊤ k) ⋙ ExtendedFibration.yoneda R Y ⟶
    (Over.pullback R ⊤ h ⋙ R.pushforward f) ⋙ ExtendedFibration.yoneda R Y := sorry
  -- TODO: define α as the following composition. All should be either x.hom for some iso x or
    -- a morphism such that IsIso x
  -- (R.pushforward g ⋙ Over.pullback R ⊤ k) ⋙ ExtendedFibration.yoneda R Y
  -- ≅ R.pushforward g ⋙ Over.pullback R ⊤ k ⋙ ExtendedFibration.yoneda R Y
  -- ≅ R.pushforward g ⋙ ExtendedFibration.yoneda R W ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(k)
  -- ≅ (R.pushforward g ⋙ ExtendedFibration.yoneda R W) ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(k)
  -- ≅ (ExtendedFibration.yoneda R Z ⋙ (ExtendedFibration R).pushforward ym(g)) ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(k)
  -- ≅ ExtendedFibration.yoneda R Z ⋙ (ExtendedFibration R).pushforward ym(g) ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(k)
  -- use `pushforwardPullbackTwoSquare_isIso_extendedFibration` here
  -- ≅ ExtendedFibration.yoneda R Z ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(h) ⋙ (ExtendedFibration R).pushforward f
  -- ≅ (ExtendedFibration.yoneda R Z ⋙ Over.pullback (ExtendedFibration R) ⊤ ym(h)) ⋙ (ExtendedFibration R).pushforward f
  -- ≅ (Over.pullback R ⊤ h ⋙ ExtendedFibration.yoneda R X) ⋙ (ExtendedFibration R).pushforward f
  -- ≅ Over.pullback R ⊤ h ⋙ ExtendedFibration.yoneda R X ⋙ (ExtendedFibration R).pushforward f
  -- ≅ Over.pullback R ⊤ h ⋙ R.pushforward f ⋙ ExtendedFibration.yoneda R Y
  -- ≅ (Over.pullback R ⊤ h ⋙ R.pushforward f) ⋙ ExtendedFibration.yoneda R Y
  have : IsIso α := sorry -- should be automatic by infer_instance. Then remove.
  have eq : Functor.whiskerRight (pushforwardPullbackTwoSquare h f g k pb.w)
      (ExtendedFibration.yoneda R Y) = α := sorry
  have : IsIso (Functor.whiskerRight (pushforwardPullbackTwoSquare h f g k pb.w)
      (ExtendedFibration.yoneda R Y)) := by rw [eq]; infer_instance
  apply NatTrans.isIso_of_whiskerRight_isIso _ (ExtendedFibration.yoneda R Y)

/-
theorem pushforwardPullbackTwoSquare_isIso {T : Type u} [Category.{max u v} T]
    (R : MorphismProperty T)
    [R.HasPullbacks] [R.IsStableUnderBaseChange]
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W) (sq : h ≫ g = f ≫ k)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    [R.HasPushforwardsAlong f] [R.IsStableUnderPushforwardsAlong f]
    [R.HasPushforwardsAlong g] [R.IsStableUnderPushforwardsAlong g]
    (pb : IsPullback h f g k) :
    IsIso (pushforwardPullbackTwoSquare (R := R) h f g k pb.w) := by
  apply (config := {allowSynthFailures:= true}) NatIso.isIso_of_isIso_app
  intro A
  apply (config := {allowSynthFailures:= true}) Functor.ReflectsIsomorphisms.reflects
    (ExtendedFibration.yoneda R Y ⋙ Over.forget _ _ _)
  -- apply (config := {allowSynthFailures:= true}) yoneda.map_isIso
  -- simp
  have pb : IsPullback ym(h) ym(f) ym(g) ym(k) := sorry
  have l := CategoryTheory.Over.pushforwardPullbackTwoSquare ym(h) ym(f) ym(g) ym(k) pb.toCommSq
  have li := CategoryTheory.pushforwardPullbackTwoSquare_of_isPullback_isIso pb
  have lii := NatIso.isIso_app_of_isIso
    (CategoryTheory.Over.pushforwardPullbackTwoSquare ym(h) ym(f) ym(g) ym(k) pb.toCommSq)
    ((ExtendedFibration.yoneda R Z ⋙ Over.forget _ _ _).obj A)
  -- have : IsIso l := inferInstanceAs $ IsIso $ CategoryTheory.Over.pushforwardPullbackTwoSquare ym(h) ym(f) ym(g) ym(k) pb.toCommSq
  sorry
-/
