import HoTTLean.ForMathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Functor.TwoSquare
import HoTTLean.ForMathlib.CategoryTheory.Comma.Over.Pushforward
import HoTTLean.ForMathlib.CategoryTheory.MorphismProperty.Limits
import HoTTLean.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import HoTTLean.ForMathlib
import HoTTLean.ForMathlib.CategoryTheory.NatTrans
import Mathlib.Tactic.DepRewrite
import Poly.ForMathlib.CategoryTheory.NatTrans
import HoTTLean.Model.Natural.NaturalModel

universe w v u v₁ u₁

noncomputable section

namespace CategoryTheory

open Category Limits MorphismProperty

variable {C : Type u} [Category.{v} C] {X Y : Psh C}

structure RepresentableChosenPullbacks (f : X ⟶ Y) where
  ext {Γ : C} (A : y(Γ) ⟶ Y) : C
  disp {Γ : C} (A : y(Γ) ⟶ Y) : ext A ⟶ Γ
  var {Γ : C} (A : y(Γ) ⟶ Y) : y(ext A) ⟶ X
  disp_pullback {Γ : C} (A : y(Γ) ⟶ Y) :
    IsPullback (var A) ym(disp A) f A

namespace MorphismProperty

variable (R : MorphismProperty C)

def LocalPreclan (X : C) : MorphismProperty (R.Over ⊤ X) := fun _ _ f => R f.left

instance (X : C) [R.IsStableUnderComposition] [R.IsStableUnderBaseChange] :
  (LocalPreclan R X).IsStableUnderBaseChange := sorry

instance (X : C) [R.IsStableUnderComposition] [R.HasPullbacks] [R.IsStableUnderBaseChange] :
    (LocalPreclan R X).HasPullbacks := sorry

instance (X : C) : (LocalPreclan R X).HasObjects := sorry

instance (X : C) [R.ContainsIdentities] : (LocalPreclan R X).ContainsIdentities where
  id_mem _ := R.id_mem _

instance (X : C) [R.IsStableUnderComposition] : (LocalPreclan R X).IsStableUnderComposition where
  comp_mem _ _ hf hg := R.comp_mem _ _ hf hg

structure RepresentableFibrantChosenPullbacks (f : X ⟶ Y)
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

notation:max R"^("F")"  => LocalPreclan (ExtendedFibration R) F

namespace ExtendedFibration

variable (F : Psh C)

example [R.IsStableUnderComposition] : (R ^(F)).HasPullbacks := inferInstance
example [R.IsStableUnderComposition] : (R ^(F)).IsStableUnderBaseChange := inferInstance
example : (R ^(F)).HasObjects := inferInstance
example [R.ContainsIdentities] : (R ^(F)).ContainsIdentities := inferInstance
example [R.IsStableUnderComposition] : (R ^(F)).IsStableUnderComposition := inferInstance

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
    [R.IsStableUnderBaseChange] [R.IsStableUnderComposition]
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W)
    (rk : R k) (rh : R h)
    [R.HasPullbacksAlong h] [R.HasPullbacksAlong f] [R.HasPullbacksAlong g] [R.HasPullbacksAlong k]
    (sq : f ≫ k = h ≫ g) :
    TwoSquare (MorphismProperty.Over.pullback R ⊤ f) (MorphismProperty.Over.map ⊤ rk)
    (MorphismProperty.Over.map ⊤ rh)
    (MorphismProperty.Over.pullback R ⊤ g) :=
  (mateEquiv (MorphismProperty.Over.mapPullbackAdj R ⊤ k rk trivial)
    (MorphismProperty.Over.mapPullbackAdj R ⊤ h rh trivial)).symm <|
    ((MorphismProperty.Over.pullbackComp _ _).inv ≫
    eqToHom (by rw! [sq]) ≫
    (MorphismProperty.Over.pullbackComp _ _).hom)

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
TODO: in what generality does this theorem hold?
NOTE: we know it holds when `R` is a clan
([Joyal, Notes on Clans and Tribes, Cor 2.4.11](https://arxiv.org/pdf/1710.10238)).
NOTE: we also know it holds in a category with pullbacks with `R = ⊤`.
-/
theorem pullbackMapTwoSquare_isIso {T : Type u} [Category.{v} T] (R : MorphismProperty T)
    [R.IsStableUnderBaseChange] [R.IsStableUnderComposition]
    {X Y Z W : T} (h : X ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ W) (k : Y ⟶ W)
    (rk : R k) (rh : R h)
    [R.HasPullbacksAlong h] [R.HasPullbacksAlong f] [R.HasPullbacksAlong g] [R.HasPullbacksAlong k]
    (pb : IsPullback f h k g) :
    NatTrans.IsCartesian <| pullbackMapTwoSquare R h f g k rk rh pb.w :=
  sorry

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
    [R.HasPullbacks] [R.IsStableUnderBaseChange] {Q : MorphismProperty T} [Q.HasPullbacks]
    [R.HasPushforwards Q] [R.IsStableUnderPushforward Q] {X Y Z W : T}
    (h : X ⟶ Z) {f : X ⟶ Y} {g : Z ⟶ W} (k : Y ⟶ W) (sq : h ≫ g = f ≫ k)
    (hf : Q f) (hg : Q g) :
    TwoSquare (pushforward (P := R) hg) (Over.pullback R ⊤ h) (Over.pullback R ⊤ k)
    (pushforward (P := R) hf) :=
  let pullbackTwoSquare : TwoSquare (Over.pullback R ⊤ k) (Over.pullback R ⊤ g)
      (Over.pullback R ⊤ f) (Over.pullback R ⊤ h) :=
    ((Over.pullbackComp _ _).inv ≫
    eqToHom (by rw! [sq]) ≫
    (Over.pullbackComp _ _).hom)
  mateEquiv (pullbackPushforwardAdjunction R hg)
  (pullbackPushforwardAdjunction R hf)
  pullbackTwoSquare

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
theorem pushforwardPullbackTwoSquare_isIso {T : Type u} [Category.{v} T] (R : MorphismProperty T)
    [R.HasPullbacks] [R.IsStableUnderBaseChange] {Q : MorphismProperty T} [Q.HasPullbacks]
    [R.HasPushforwards Q] [R.IsStableUnderPushforward Q]
    {X Y Z W : T} (h : X ⟶ Z) {f : X ⟶ Y} {g : Z ⟶ W} (k : Y ⟶ W) (sq : h ≫ g = f ≫ k)
    (hf : Q f) (hg : Q g) (pb : IsPullback h f g k) :
    IsIso (pushforwardPullbackTwoSquare (R := R) h k pb.w hf hg) :=
  sorry
