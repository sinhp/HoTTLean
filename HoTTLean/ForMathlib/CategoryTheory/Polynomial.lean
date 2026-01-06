import HoTTLean.ForMathlib.CategoryTheory.Clan
import HoTTLean.ForMathlib.CategoryTheory.Comma.Over.Basic

universe v u v₁ u₁

noncomputable section

namespace CategoryTheory

open Category Limits MorphismProperty

variable {C : Type u} [Category.{u} C]

namespace MorphismProperty

open NatTrans MorphismProperty.Over in
/-- The counit of the adjunction `mapPullbackAdj` is a pullback square,
since it is the pullback computed by `P.Over.pullback`. -/
lemma isCartesian_mapPullbackAdj_counit {P : MorphismProperty C} {X Y : C} {f : X ⟶ Y}
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    [P.HasPullbacksAlong f] (hPf : P f) : IsCartesian (mapPullbackAdj (Q := ⊤) f hPf trivial).counit := by
  intro A B U
  apply (MorphismProperty.Over.forget P ⊤ Y).reflect_isPullback
  apply (CategoryTheory.Over.forget Y).reflect_isPullback
  apply IsPullback.flip
  simp only [Functor.comp_obj, Comma.forget_obj, Over.forget_obj, map_obj_left, pullback_obj_left,
    Functor.id_obj, mapPullbackAdj, Adjunction.mkOfHomEquiv, Equiv.invFun_as_coe,
    Adjunction.mk'_counit, Comma.forget_map, Over.forget_map,
    mapPullbackAdjHomEquiv_symm_apply_left, Comma.id_hom, CategoryTheory.Comma.id_left, id_comp,
    Functor.comp_map, map_map_left, pullback_map_left, Functor.id_map]
  apply IsPullback.of_bot (v₂₁ := (pullback.snd B.hom f)) (h₃₁ := f) (v₂₂ := B.hom) _ _
    (IsPullback.of_hasPullback B.hom f)
  · convert IsPullback.of_hasPullback A.hom f <;> simp
  · simp

namespace PolynomialPartialAdjunction

variable {T : Type u} [Category.{v} T] {R : MorphismProperty T}
  [R.HasPullbacks] [R.IsStableUnderBaseChange]
  {E I B : T} (i : E ⟶ I) (p : E ⟶ B)
  [HasPullbacksAlong p] [R.HasPushforwardsAlong p]
  [R.IsStableUnderPushforwardsAlong p]

/-- The partial right adjoint representing a multivariate polynomial. -/
abbrev partialRightAdjoint := Over.pullback R ⊤ i ⋙ pushforward R p

/-- The left adjoint in the partial adjunction. -/
abbrev leftAdjoint := CategoryTheory.Over.pullback p ⋙ CategoryTheory.Over.map i

/-- `pullback R ⊤ i ⋙ pushforward R p` is a partial right adjoint to
`CategoryTheory.Over.pullback p.1 ⋙ CategoryTheory.Over.map i`
  ```
         pullback i       pushforward p
   R.Over I ------> R.Over E -----> R.Over B
      |               |                |
      |       ⊥       |        ⊥       |
      |               |                |
      V               V                V
     C/I <--------- C/E <------------ C/B
            map i         pullback p
  ```

On paper this is written `C/B (X, p⁎ (i* Y)) ≃ C/I (i! (p* X), Y)`.
-/
def homEquiv {X : Over B} {Y : R.Over ⊤ I} :
    (X ⟶ ((partialRightAdjoint i p).obj Y).toComma) ≃
    ((leftAdjoint i p).obj X ⟶ Y.toComma) :=
  calc (X ⟶ ((R.pushforward p).obj ((Over.pullback R ⊤ i).obj Y)).toComma)
  _ ≃ ((CategoryTheory.Over.pullback p).obj X ⟶ ((Over.pullback R ⊤ i).obj Y).toComma) :=
    pushforward.homEquiv
  _ ≃ ((CategoryTheory.Over.map i).obj
      ((CategoryTheory.Over.pullback p).obj X) ⟶ Y.toComma) :=
    pullback.homEquiv _

lemma homEquiv_comp {X X' : Over B} {Y : R.Over ⊤ I}
    (f : X' ⟶ ((partialRightAdjoint i p).obj Y).toComma) (g : X ⟶ X') :
    homEquiv i p (g ≫ f) =
    (leftAdjoint i p).map g ≫ homEquiv i p f := by
  unfold homEquiv
  simp only [Functor.comp_obj, Equiv.trans_def, Equiv.trans_apply]
  erw [pushforward.homEquiv_comp, pullback.homEquiv_comp]
  rfl

lemma homEquiv_map_comp {X : Over B} {Y Y' : R.Over ⊤ I}
    (f : X ⟶ ((partialRightAdjoint i p).obj Y).toComma) (g : Y ⟶ Y') :
    homEquiv i p (f ≫ Comma.Hom.hom ((partialRightAdjoint i p).map g)) =
    homEquiv i p f ≫ Comma.Hom.hom g := by
  unfold homEquiv
  simp only [Functor.comp_obj, Equiv.trans_def, Equiv.trans_apply]
  erw [pushforward.homEquiv_map_comp, pullback.homEquiv_map_comp]
  rfl

lemma homEquiv_symm_comp {X : Over B} {Y Y' : R.Over ⊤ I}
    (f : (leftAdjoint i p).obj X ⟶ Y.toComma) (g : Y ⟶ Y') :
    (homEquiv i p).symm f ≫ Comma.Hom.hom ((partialRightAdjoint i p).map g) =
    (homEquiv i p).symm (f ≫ Comma.Hom.hom g) := by
  unfold homEquiv
  simp
  erw [pushforward.homEquiv_symm_comp, pullback.homEquiv_symm_comp]
  rfl

lemma comp_homEquiv_symm {X X' : Over B} {Y : R.Over ⊤ I}
    (f : (leftAdjoint i p).obj X' ⟶ Y.toComma) (g : X ⟶ X') :
    g ≫ (homEquiv i p).symm f =
    (homEquiv i p).symm ((leftAdjoint i p).map g ≫ f) := by
  unfold homEquiv
  simp
  erw [pushforward.homEquiv_comp_symm, pullback.comp_homEquiv_symm]
  rfl

/-- The counit of the partial adjunction is given by evaluating the equivalence of
hom-sets at the identity.
On paper we write this as `counit : i! p* p∗ i* => Over.forget : R.Over ⊤ I ⥤ Over I`
-/
def counit :
    partialRightAdjoint i p ⋙ Over.forget R ⊤ B ⋙ leftAdjoint i p ⟶ Over.forget R ⊤ I where
  app _ := homEquiv i p (𝟙 _)
  naturality X Y f := by
    apply (homEquiv i p).symm.injective
    conv => left; erw [← comp_homEquiv_symm]
    conv => right; erw [← homEquiv_symm_comp]
    simp

/-- A commutative diagram
```
      I
    ↗  ↖
 i /      \ i'
  /   ρ    \
 E -------> E'
  \        /
 p \      / p'
    ↘  ↙
      B
```
induces a natural transformation `partialRightAdjoint i p ⟶ partialRightAdjoint i' p'`
obtained by pasting the following 2-cells
```
        pullback i'        pushforward p'
R.Over ⊤ I ---->  R.Over ⊤ E' ----> R.Over ⊤ B
    ‖                 |                  ‖
    ‖                 |                  ‖
    ‖       ↙        |ρ*      ↙        ‖
    ‖                 |                  ‖
    ‖                 V                  ‖
R.Over ⊤ I ---->  R.Over ⊤ E  ----> R.Over ⊤ B
        pullback i         pushforward p
```
-/
def partialRightAdjointMap {E' : T} (i' : E' ⟶ I) (p' : E' ⟶ B)
    [HasPullbacksAlong p'] [R.HasPushforwardsAlong p']
    [R.IsStableUnderPushforwardsAlong p'] (ρ)
    (hi : i = ρ ≫ i') (hρ : p = ρ ≫ p') :
    partialRightAdjoint (R := R) i' p' ⟶ partialRightAdjoint i p :=
  -- let cellLeftIso : Over.pullback R ⊤ i' ⋙ Over.pullback R ⊤ ρ ≅ Over.pullback R ⊤ i :=
  --   (Over.pullbackComp ρ i').symm ≪≫ eqToIso (by rw [hi])
  let cellLeft : TwoSquare (Over.pullback R ⊤ i') (𝟭 _)
      (Over.pullback R ⊤ ρ) (Over.pullback R ⊤ i) :=
    ((Functor.leftUnitor _) ≪≫ Over.pullbackCongr hi ≪≫ (Over.pullbackComp ρ i')).symm.hom
  let cellRight := pushforwardPullbackTwoSquare (R := R) ρ p p' (𝟙 _) (by simp [← hρ])
  Functor.whiskerLeft (partialRightAdjoint i' p') (Over.pullbackId R ⊤ B).inv ≫
  cellLeft.hComp cellRight

lemma partialRightAdjointMap_obj {E' : T} (i' : E' ⟶ I) (p' : E' ⟶ B)
    [HasPullbacksAlong p'] [R.HasPushforwardsAlong p']
    [R.IsStableUnderPushforwardsAlong p'] (ρ)
    (hi : i = ρ ≫ i') (hρ : p = ρ ≫ p') (X : R.Over ⊤ I) :
    Comma.Hom.hom ((partialRightAdjointMap i p i' p' ρ hi hρ).app X) = sorry := by
  simp [partialRightAdjointMap]
  -- apply (homEquiv i p).injective
  -- simp [Functor.comp_obj, - EmbeddingLike.apply_eq_iff_eq, homEquiv, Trans.trans,
  --   partialRightAdjointMap]
  -- ext
  -- simp only [CategoryTheory.Over.map_obj_left, CategoryTheory.Over.pullback_obj_left,
  --   pullback.homEquiv_apply_left]
  -- congr 3
  -- ext
  -- apply partialRightAdjoint.homEquiv
  sorry

end PolynomialPartialAdjunction

variable (P : MorphismProperty C)

namespace Over

@[simps]
def equivalenceOfHasObjects' (R : MorphismProperty C) [R.HasObjects]
    {X : C} (hX : IsTerminal X) : R.Over ⊤ X ≌ Over X where
  functor := MorphismProperty.Over.forget _ _ _
  inverse := Comma.lift (𝟭 _) (by intro; apply HasObjects.obj_mem _ hX) (by simp) (by simp)
  unitIso := eqToIso rfl
  counitIso := eqToIso rfl
  functor_unitIso_comp := by simp

@[simp]
def equivalenceOfHasObjects (R : MorphismProperty C) [R.HasObjects]
    {X : C} (hX : IsTerminal X) : R.Over ⊤ X ≌ C :=
  (equivalenceOfHasObjects' R hX).trans (Over.equivalenceOfIsTerminal hX)

variable {P : MorphismProperty C} {E B : C}

@[simps]
def ofMorphismProperty {p : E ⟶ B} (hp : P p) : P.Over ⊤ B where
  left := E
  right := ⟨⟨⟩⟩
  hom := p
  prop := hp

@[simps]
def homMkTop {p q : P.Over ⊤ B} (left : p.left ⟶ q.left) (hleft : left ≫ q.hom = p.hom) :
    p ⟶ q where
  left := left
  right := eqToHom (by simp)
  w := by simp [hleft]
  prop_hom_left := trivial
  prop_hom_right := trivial

/--
Convert an object `p` in `R.Over ⊤ B` to a morphism in `R.Over ⊤ O` by composing with `o`.
     p
 E -----> B
  \      /
   \    /o
    \  /
     VV
     O
-/
@[simp]
def homOfMorphismProperty [P.IsStableUnderComposition] {O} (p : P.Over ⊤ B) {o : B ⟶ O} (ho : P o) :
    (map ⊤ ho).obj p ⟶ Over.ofMorphismProperty ho :=
  Over.homMk p.hom (by simp)

end Over

end MorphismProperty

open MorphismProperty.Over

/-- `P : MvPoly R H I O` is a the signature for a multivariate polynomial functor,
consisting of the following maps
```
         p
      E ---> B
  i ↙         ↘ o
  I               O
```
We can lazily read this as `∑ b : B, X ^ (E b)`,
for some `X` in the (`P`-restricted) slice over `I`.

In full detail:
Viewing such an `X` as a series of variables `X_k` indexed by `k ∈ I`,
and `B` as a family of types `B_k` indexed by `j ∈ O`
this can be further viewed as `O`-many `I`-ary polynomials `∑ b : B_j, X_(i b) ^ (E b)`

To explain the need for two morphism properties,
consider the following two use-cases:
1. `R = ⊤` is all maps and the category has all pullbacks.
  `H` is the class of exponentiable maps - it follows from all maps having pullbacks that `H`
  also has pullbacks.
2. `R = H` is a π-clan, [see Joyal, def 2.4.1](https://arxiv.org/pdf/1710.10238).

This will typically be used with the following instances

- For pullback of `R`-maps along `i`, `p` and `o` we need
  `[R.IsStableUnderBaseChange] [R.HasPullbacks]`
- For the left adjoint to pullback for `o` we need `[R.IsStableUnderComposition]`
- For pushforward of `R`-maps along `p` we need
  `[R.IsStableUnderPushforward H] [R.HasPushforwards H]`
- For pushforward of `R`-maps along `p` we also assume `[H.HasPullbacks]`.
  This is useful - it makes the `R`-restricted pushforward of `R`-maps along `p`
  a partial left adjoint to *global* pullback along `p`,
  ```
        pushforward p
   R.Over E -----> R.Over B
      |              |
      |       ⊥      |
      |              |
      V              V
     C/E <--------- C/B
         pullback p
  ```
  which is strictly stronger than just having a left adjoint to `R`-restricted pullback
  `(pullback : R.Over B ⥤ R.Over E) ⊣ (pushforward : R.Over E ⥤ R.Over B)`.
-/
structure MvPoly (R : MorphismProperty C) (I O E B : C) where
  (i : E ⟶ I)
  (hi : R i)
  (p : E ⟶ B)
  (o : B ⟶ O)
  (ho : R o)

namespace MvPoly

variable {R : MorphismProperty C}

instance {B O : C} {i : B ⟶ O} (hi : R i) [R.HasPullbacks] [R.IsStableUnderBaseChange]
    [R.IsStableUnderComposition] : (pullback R ⊤ i).IsRightAdjoint :=
  (mapPullbackAdj (Q := ⊤) i hi ⟨⟩).isRightAdjoint

variable {I O E B : C} (P : MvPoly R I O E B) [R.HasPullbacks] [R.IsStableUnderBaseChange]
    [HasPullbacksAlong P.p] [R.HasPushforwardsAlong P.p] [R.IsStableUnderPushforwardsAlong P.p]

open PolynomialPartialAdjunction

/-- (Ignoring the indexing from `i` and `o`)
This is the first projection morphism from `P @ X = ∑ b : B, X ^ (E b)` to `B`,
as an object in the `P`-restricted slice over `B`. -/
abbrev fstProj (X : R.Over ⊤ I) : R.Over ⊤ B :=
  (partialRightAdjoint P.i P.p).obj X

/-- The counit of the adjunction `pullback p ⋙ map i ⊣ pullback i ⋙ pushforward p` evaluated at `X`.
Ignoring the indexing from `i` and `o`,
this can be viewed as the second projection morphism from `P @ X = ∑ b : B, X ^ (E b)`
to `X^ (E b)`.

```
     X ----------> I
     ∧             ∧
     |             |
 sndProj           | i
     |             |
     • ----------> E
     |             |
     |    (pb)     |
     |             |p
     V    fstProj  V
   P @ X --------> B
       ⟍          |
          ⟍       |o
             ⟍    |
                ↘ V
                   O
```
-/
def sndProj (X : R.Over ⊤ I) :
    (leftAdjoint P.i P.p).obj (fstProj P X).toComma ⟶ X.toComma :=
  (counit P.i P.p).app X

section

variable {X Y : R.Over ⊤ I} (f : X ⟶ Y)

@[reassoc (attr := simp)]
lemma map_fstProj :
    ((partialRightAdjoint P.i P.p).map f).left ≫ (fstProj P Y).hom = (fstProj P X).hom := by
  simp

lemma sndProj_comp_hom : (sndProj P X).left ≫ X.hom = pullback.snd _ _ ≫ P.i := by
  simp [sndProj]

lemma sndProj_comp : (sndProj P X).left ≫ f.left =
    pullback.map _ _ _ _
      ((partialRightAdjoint P.i P.p).map f).left (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      (sndProj P Y).left := by
  have := congr_arg CommaMorphism.left <| (counit P.i P.p).naturality f
  simpa [pullback.map] using this.symm

end

variable [R.IsStableUnderComposition]
/-- A multivariate polynomial signature
```
         p
      E ---> B
  i ↙         ↘ o
  I               O
```
gives rise to a functor
```
                         pushforward p
                R.Over ⊤ E ---------> R.Over ⊤ B
     pullback i ↗                              ⟍ map o
             ⟋                                    ⟍
          ⟋                                          ↘
  R.Over ⊤ I                                      R.Over ⊤ O
```
-/
def functor : R.Over ⊤ I ⥤ R.Over ⊤ O :=
  pullback R ⊤ P.i ⋙ MorphismProperty.pushforward R P.p ⋙ map ⊤ P.ho

/-- The action of a univariate polynomial on objects. -/
def apply : R.Over ⊤ I → R.Over ⊤ O := (functor P).obj

@[inherit_doc]
infix:90 " @ " => apply

namespace Equiv

variable {P} {Γ : Over O} {X : R.Over ⊤ I}

def fst (pair : Γ ⟶ (P @ X).toComma) : Over B := Over.mk (pair.left ≫ (fstProj P X).hom)

abbrev sndDom (pair : Γ ⟶ (P @ X).toComma) : Over I := (leftAdjoint P.i P.p).obj (fst pair)

def snd (pair : Γ ⟶ (P @ X).toComma) : sndDom pair ⟶ X.toComma :=
  homEquiv P.i P.p (Over.homMk (pair.left))

lemma snd_eq (pair : Γ ⟶ (P @ X).toComma) : snd pair =
    (leftAdjoint P.i P.p).map (Over.homMk (pair.left)) ≫ sndProj P X := by
  erw [Equiv.apply_eq_iff_eq_symm_apply, ← comp_homEquiv_symm]
  simp [sndProj, counit]

def mk (f : Over B) (hf : Γ = (Over.map P.o).obj f)
    (s : (leftAdjoint P.i P.p).obj f ⟶ X.toComma) :
    Γ ⟶ (P @ X).toComma :=
  eqToHom hf ≫ (Over.map P.o).map ((homEquiv P.i P.p).symm s)

@[simp]
lemma fst_mk (f : Over B) (hf : Γ = (Over.map P.o).obj f)
    (s : (leftAdjoint P.i P.p).obj f ⟶ X.toComma) : fst (mk f hf s) = f := by
  subst hf; simp [fst, mk]

lemma snd_mk (f : Over B) (hf : Γ = (Over.map P.o).obj f)
    (s : (leftAdjoint P.i P.p).obj f ⟶ X.toComma) : snd (mk f hf s) =
    eqToHom (by simp) ≫ s := calc snd (mk f hf s)
  _ = (leftAdjoint P.i P.p).map (eqToHom (fst_mk f hf s)) ≫ s := by
    erw [Equiv.apply_eq_iff_eq_symm_apply, ← comp_homEquiv_symm]
    ext
    simp [mk]
  _ = eqToHom _ ≫ s := by
    simp only [eqToHom_map]

@[simp]
lemma map_fst (pair : Γ ⟶ (P @ X).toComma) : (Over.map P.o).obj (fst pair) = Γ := by
  have := pair.w
  simp only [Functor.id_obj, Functor.const_obj_obj, Functor.id_map,
    CostructuredArrow.right_eq_id, Functor.const_obj_map, comp_id] at this
  simp [Over.map, Comma.mapRight, fst]
  congr

@[simp]
lemma mk_fst_snd (pair : Γ ⟶ (P @ X).toComma) : mk (fst pair) (by simp) (snd pair) = pair := by
  ext
  simp [mk, snd]

end Equiv

-- -- NOTE: please leave the commented out subgoals, it makes debugging this easier
-- instance (P : MvPoly R H I O E B) : PreservesLimitsOfShape WalkingCospan
--     (MorphismProperty.Over.pullback R ⊤ P.i ⋙ R.pushforward P.hp ⋙
--     MorphismProperty.Over.map ⊤ P.ho) :=
--   have : (MorphismProperty.Over.pullback R ⊤ P.i).IsRightAdjoint :=
--     Adjunction.isRightAdjoint (MorphismProperty.Over.mapPullbackAdj R ⊤ P.i P.hi trivial)
--   -- have : PreservesLimitsOfShape WalkingCospan (MorphismProperty.Over.pullback R ⊤ P.i) :=
--   --   inferInstance
--   -- have : PreservesLimitsOfShape WalkingCospan (R.pushforward P.hp) :=
--   --   inferInstance
--   -- have : PreservesLimitsOfShape WalkingCospan (MorphismProperty.Over.map ⊤ P.ho) :=
--   --   inferInstance
--   inferInstance

-- instance (P : MvPoly R H I O E B) :
--     Limits.PreservesLimitsOfShape WalkingCospan (MvPoly.functor P) := by
--   dsimp [functor]
--   infer_instance

/-- A commutative triangle
```
      I
    ↗  ↖
P.i/      \Q.i
  /    ρ   \
 E -------> F
  \        /
P.p\      / Q.p
    ↘  ↙
      B
```
induces a natural transformation `Q.functor ⟶ P.functor` when `Q.o = P.o`,
obtained by pasting the following 2-cells
```
        pullback Q.i     pushforward Q.p.1     map Q.o.1
R.Over ⊤ I ---->  R.Over ⊤ F ----> R.Over ⊤ B -----> R.Over ⊤ O
    ‖                 |                  ‖                ‖
    ‖                 |                  ‖                ‖
    ‖       ↙        |ρ*      ↙        ‖       =        ‖
    ‖                 |                  ‖                ‖
    ‖                 V                  ‖                ‖
R.Over ⊤ I ---->  R.Over ⊤ E ----> R.Over ⊤ B -----> R.Over ⊤ O
        pullback P.i     pushforward P.p.1     map P.o
```
-/
def verticalNatTrans {F : C} (P : MvPoly R I O E B) (Q : MvPoly R I O F B)
    [HasPullbacksAlong P.p] [R.HasPushforwardsAlong P.p] [R.IsStableUnderPushforwardsAlong P.p]
    [HasPullbacksAlong Q.p] [R.HasPushforwardsAlong Q.p] [R.IsStableUnderPushforwardsAlong Q.p]
    (ρ : E ⟶ F) (hi : P.i = ρ ≫ Q.i) (hp : P.p = ρ ≫ Q.p) (ho : P.o = Q.o) :
    Q.functor ⟶ P.functor :=
  (Functor.associator _ _ _).inv ≫
  ((PolynomialPartialAdjunction.partialRightAdjointMap P.i P.p Q.i Q.p ρ hi hp) ◫
  (eqToHom (by rw! [ho]))) ≫
  (Functor.associator _ _ _).hom

lemma verticalNatTrans_hom {F : C} (P : MvPoly R I O E B) (Q : MvPoly R I O F B)
    [HasPullbacksAlong P.p] [R.HasPushforwardsAlong P.p] [R.IsStableUnderPushforwardsAlong P.p]
    [HasPullbacksAlong Q.p] [R.HasPushforwardsAlong Q.p] [R.IsStableUnderPushforwardsAlong Q.p]
    (ρ : E ⟶ F) (hi : P.i = ρ ≫ Q.i) (hp : P.p = ρ ≫ Q.p) (ho : P.o = Q.o) (X) :
    ((verticalNatTrans P Q ρ hi hp ho).app X).hom = sorry := by
  -- simp [verticalNatTrans, partialRightAdjointMap, pushforwardPullbackTwoSquare]
  -- erw [id_comp]
  sorry

section

variable {F} (Q : MvPoly R I O F B) [HasPullbacksAlong Q.p] [R.HasPushforwardsAlong Q.p]
    [R.IsStableUnderPushforwardsAlong Q.p]
    (ρ : E ⟶ F) (hi : P.i = ρ ≫ Q.i) (hp : P.p = ρ ≫ Q.p) (ho : P.o = Q.o)

def fstVerticalNatTransAppIso {Γ} {X} (pair : Γ ⟶ (Q @ X).toComma) :
    Equiv.fst (pair ≫ ((verticalNatTrans P Q ρ hi hp ho).app X).hom) ≅ Equiv.fst pair :=
  Over.isoMk (Iso.refl _) (by simp [Equiv.fst, verticalNatTrans]; erw [id_comp])

lemma fst_verticalNatTrans_app {Γ} {X} (pair : Γ ⟶ (Q @ X).toComma) :
    Equiv.fst (pair ≫ ((verticalNatTrans P Q ρ hi hp ho).app X).hom) = Equiv.fst pair :=
  Over.ext_of_iso (fstVerticalNatTransAppIso P Q ρ hi hp ho pair) rfl rfl

lemma snd_verticalNatTrans_app {Γ} {X} (pair : Γ ⟶ (Q @ X).toComma) :
    Equiv.snd (pair ≫ ((verticalNatTrans P Q ρ hi hp ho).app X).hom) =
    Over.homMk (pullback.map _ _ _ _ (fstVerticalNatTransAppIso P Q ρ hi hp ho pair).hom.left
      ρ (𝟙 _) (by cat_disch) (by cat_disch)) ≫ Equiv.snd pair := by
  simp [Equiv.snd]
  -- rw [Over.homMk_comp]
  -- rw [homEquiv_comp]
  -- rw [comp_homEquiv_symm]
  -- rw [Equiv.snd_eq]
  -- rw [Equiv.snd_eq]
  -- dsimp [sndProj, counit]
  -- simp
  sorry

-- lemma mk'_comp_verticalNatTrans_app {Γ : Over O} {X : R.Over ⊤ I} (f : Over B)
--     (hf : Γ = (Over.map Q.o.1).obj f) (s : (leftAdjoint Q.i.1 Q.p).obj f ⟶ X.toComma) :
--     Equiv.mk f hf s ≫ ((verticalNatTrans P Q ρ hi hp ho).app X).hom =
--     Equiv.mk f (sorry) sorry ≫ sorry
--      :=
--   sorry

end

open TwoSquare

/-- A cartesian map
```
               P.p
          E  -------->  B
  P.i ↙  |             |  ↘ P.o
     I   φ|    (pb)     | δ  O
  P'.i ↖ v             v  ↗ P'.o
          E' -------->  B'
               P'.p
```
induces a natural transformation between their associated functors obtained by pasting the following
2-cells
```
        pullback P'.i      pushforward P'.p       map P'.o
R.Over I ------ >  R.Over E' --------> R.Over B' --------> R.Over O
    ‖                |                     |                  ‖
    ‖                |                     |                  ‖
    ‖       ↗    pullback φ   ↗     pullback δ     ↗       ‖
    ‖                |                     |                  ‖
    ‖                v                     v                  ‖
R.Over I ------ >  R.Over E  --------> R.Over B  --------> R.Over O
        pullback P.i       pushforward P.p        map P.o
```
-/
def cartesianNatTrans {E' B' : C} (P : MvPoly R I O E B) (P' : MvPoly R I O E' B')
    [HasPullbacksAlong P.p] [R.HasPushforwardsAlong P.p] [R.IsStableUnderPushforwardsAlong P.p]
    [HasPullbacksAlong P'.p] [R.HasPushforwardsAlong P'.p] [R.IsStableUnderPushforwardsAlong P'.p]
    (δ : B ⟶ B') (φ : E ⟶ E') (hφ : P.i = φ ≫ P'.i) (pb : IsPullback φ P.p P'.p δ)
    (hδ : δ ≫ P'.o = P.o) :
    P.functor ⟶ P'.functor :=
  let cellLeft : TwoSquare (𝟭 (R.Over ⊤ I)) (MorphismProperty.Over.pullback R ⊤ P'.i)
      (MorphismProperty.Over.pullback R ⊤ P.i) (MorphismProperty.Over.pullback R ⊤ φ) :=
    (eqToIso (by simp [hφ, Functor.id_comp]) ≪≫ (MorphismProperty.Over.pullbackComp φ P'.i)).hom
  let cellMid : TwoSquare (MorphismProperty.Over.pullback R ⊤ φ)
    (R.pushforward P'.p) (R.pushforward P.p) (MorphismProperty.Over.pullback R ⊤ δ) :=
    (pushforwardPullbackIso φ P.p P'.p δ pb).inv
  let cellRight : TwoSquare (MorphismProperty.Over.pullback R ⊤ δ)
      (MorphismProperty.Over.map ⊤ P'.ho) (MorphismProperty.Over.map ⊤ P.ho) (𝟭 _) :=
    (pullbackMapTwoSquare R P.o δ (𝟙 _) P'.o P'.ho P.ho (by simp [hδ])) ≫
    Functor.whiskerLeft _ (MorphismProperty.Over.pullbackId R ⊤ O).hom
  cellLeft ≫ᵥ cellMid ≫ᵥ cellRight

-- TODO: This name is not quite correct, because the functor is not cartesian
-- rather, it takes a commutative square in `R.Over I` that is a pullback in the (whole!)
-- over category `Over I` to
-- a commutative square that is a pullback in the over category `Over O`
-- This subtlety can be ignored when `R.Over I = Over I`, like in the π-clan `UvPoly` case.

-- Here are some relevant facts:
-- 1. partial right adjoints preserve limits in the whole category of diagrams from the subcategory
-- whole limit also lands in the subcategory,
-- hence `pullback i : R.Over I -> R.Over E` and
-- `pushforward p : R.Over E -> R.Over B` both preserve pullbacks in `Over I`
-- that are from `R.Over I`.
-- 2. `map : R.Over E -> R.Over O` also has this pullback preservation property.

open NatTrans in
theorem isCartesian_cartesianNatTrans {E' B' : C} (P : MvPoly R I O E B) (P' : MvPoly R I O E' B')
    [HasPullbacksAlong P.p] [R.HasPushforwardsAlong P.p] [R.IsStableUnderPushforwardsAlong P.p]
    [HasPullbacksAlong P'.p] [R.HasPushforwardsAlong P'.p] [R.IsStableUnderPushforwardsAlong P'.p]
    (δ : B ⟶ B') (φ : E ⟶ E') (hφ : P.i = φ ≫ P'.i) (pb : IsPullback φ P.p P'.p δ)
    (hδ : δ ≫ P'.o = P.o) :
    (cartesianNatTrans P P' δ φ hφ pb hδ).IsCartesian :=
  IsCartesian.vCompIsIso <|
  IsCartesian.vCompIsIso <|
  IsCartesian.comp
  (isCartesian_pullbackMapTwoSquare ..)
  (IsCartesian.whiskerLeft (isCartesian_of_isIso _) _)

  -- dsimp [cartesianNatTrans]
  -- repeat apply IsCartesian.vComp
  -- · apply IsCartesian.comp
  --   · apply isCartesian_of_isIso
  --   · sorry --apply isCartesian_of_isIso
  -- · apply isCartesian_of_isIso
  -- · -- apply IsCartesian.whiskerLeft
  --   sorry

  -- NOTE: this lemma could be extracted, but `repeat' apply IsCartesian.comp` will unfold past it.
  -- have : NatTrans.IsCartesian
  --     (pullbackMapTwoSquare R P.o δ (𝟙 _) P'.o.1 P'.o.2 P.ho (by simp [hδ])) := by
  --   -- unfold pullbackMapTwoSquare
  --   -- simp only [mateEquiv_symm_apply]
  --   repeat' apply IsCartesian.comp
  --   -- have (i j : R.Over ⊤ B') (f : j ⟶ i) :
  --   -- PreservesLimit
  --   --   (cospan ((mapPullbackAdj R ⊤ P'.o.fst P'.o.snd trivial).unit.app i)
  --   --     ((MorphismProperty.Over.map ⊤ P'.o.2 ⋙ MorphismProperty.Over.pullback R ⊤ P'.o.fst).map f))
  --   --   (MorphismProperty.Over.pullback R ⊤ δ ⋙ MorphismProperty.Over.map ⊤ P.ho) := sorry
  --   any_goals apply isCartesian_of_isIso
  --   · sorry --refine IsCartesian.whiskerRight _ _
  --   · apply IsCartesian.whiskerLeft
  --     apply isCartesian_mapPullbackAdj_counit

  -- repeat' apply IsCartesian.comp
  -- any_goals apply isCartesian_of_isIso
  -- apply IsCartesian.whiskerLeft
  -- repeat' apply IsCartesian.comp
  -- any_goals apply isCartesian_of_isIso
  -- apply IsCartesian.whiskerLeft
  -- repeat' apply IsCartesian.comp
  -- any_goals apply isCartesian_of_isIso
  -- · sorry -- apply IsCartesian.whiskerRight
  -- · apply IsCartesian.whiskerLeft
  --   apply isCartesian_mapPullbackAdj_counit


end MvPoly

/-- `P : UvPoly R E B` is the type of signatures for polynomial functors
         p
      E ---> B

We read this as `∑ b : B, X ^ (E b)`,
for some `R`-object `X` (meaning the unique map to the terminal object is in `R`).

This notion of polynomial makes sense when `R` is a π-clan,
[see Joyal, def 2.4.1](https://arxiv.org/pdf/1710.10238).
Therefore it will typically be used with the following instances

- For pullback of `R`-maps along `p` we need
  `[R.IsStableUnderBaseChange] [R.HasPullbacks]`
- For the left adjoint to pullback along `B`, we assume `[R.IsStableUnderComposition]`
  and `[R.HasObjects]`, meaning the unique map `B ⟶ ⊤_ C` is in `R`.
  For this, we will also assume `[ChosenTerminal C]`.
- For pushforward of `R`-maps along `p` we need
  `[R.IsStableUnderPushforward R] [R.HasPushforwards R]`
- For pushforward of `R`-maps along `p` we also assume `[R.HasPullbacks]`.
  This is useful - it makes the `R`-restricted pushforward of `R`-maps along `p`
  a partial left adjoint to *global* pullback along `p`,
  ```
        pushforward p
   R.Over E -----> R.Over B
      |              |
      |       ⊥      |
      |              |
      V              V
     C/E <--------- C/B
         pullback p
  ```
  which is strictly stronger than just having a left adjoint to `R`-restricted pullback
  `(pullback : R.Over B ⥤ R.Over E) ⊣ (pushforward : R.Over E ⥤ R.Over B)`.
-/
structure UvPoly (R : MorphismProperty C) (E B : C) where
  (p : E ⟶ B)
  (morphismProperty : R p)

namespace UvPoly

section

variable {R : MorphismProperty C} {E B : C}

variable [ChosenTerminal C]

open ChosenTerminal

variable (P : UvPoly R E B)
  [R.IsStableUnderComposition] [R.HasPullbacks] [R.IsStableUnderBaseChange] [R.HasObjects]
  [HasPullbacksAlong P.p] [R.IsStableUnderPushforwardsAlong P.p] [R.HasPushforwardsAlong P.p]

instance (P : UvPoly R E B) : HasPullbacksAlong P.p :=
  hasPullbacksAlong_of_hasPullbacks P.morphismProperty

instance (P : UvPoly R E B) {Γ : C} (A : Γ ⟶ B) : HasPullback P.p A :=
  hasPullback_symmetry _ _

lemma isTerminal_from (X : C) : R (isTerminal.from X) :=
  HasObjects.obj_mem _ ChosenTerminal.isTerminal

@[simp]
abbrev toOverTerminal : C ⥤ R.Over ⊤ (𝟭_ C) :=
  (equivalenceOfHasObjects R isTerminal).inverse

@[simp]
abbrev fromOverTerminal : R.Over ⊤ (𝟭_ C) ⥤ C :=
  (equivalenceOfHasObjects R isTerminal).functor

@[simps]
def mvPoly : MvPoly R (𝟭_ C) (𝟭_ C) E B where
  i := isTerminal.from _
  hi := isTerminal_from _
  p := P.p
  o := isTerminal.from _
  ho := isTerminal_from _

instance : HasPullbacksAlong P.mvPoly.p :=
  inferInstanceAs <| HasPullbacksAlong P.p

instance : R.HasPushforwardsAlong P.mvPoly.p :=
  inferInstanceAs <| R.HasPushforwardsAlong P.p

instance : R.IsStableUnderPushforwardsAlong P.mvPoly.p :=
  inferInstanceAs <| R.IsStableUnderPushforwardsAlong P.p

def functor : C ⥤ C :=
  toOverTerminal ⋙
  MvPoly.functor P.mvPoly ⋙
  fromOverTerminal

/-- The action of a univariate polynomial on objects. -/
def apply [ChosenTerminal C] : C → C := P.functor.obj

@[inherit_doc]
infix:90 " @ " => apply

-- instance [ChosenTerminal C] (P : UvPoly R E B) :
--     Limits.PreservesLimitsOfShape WalkingCospan P.functor := by
--   unfold functor
--   infer_instance

variable (B)

/-- The identity polynomial functor in single variable. -/
@[simps!]
def id (R : MorphismProperty C) [R.ContainsIdentities] (B) : UvPoly R B B := ⟨𝟙 B, R.id_mem _ ⟩

@[simps!]
def vcomp [R.IsStableUnderComposition] {A B C} (P : UvPoly R A B) (Q : UvPoly R B C) :
    UvPoly R A C :=
  ⟨ P.p ≫ Q.p, R.comp_mem _ _ P.morphismProperty Q.morphismProperty ⟩

variable {B}

/-- The fstProjection morphism from `∑ b : B, X ^ (E b)` to `B` again. -/
def fstProj (X : C) : P @ X ⟶ B :=
  (P.mvPoly.fstProj (toOverTerminal.obj X)).hom

@[reassoc (attr := simp)]
lemma map_fstProj {X Y : C} (f : X ⟶ Y) :
    P.functor.map f ≫ fstProj P Y = fstProj P X :=
  P.mvPoly.map_fstProj (toOverTerminal.map f)

/-- The second projection morphism from `P @ X = ∑ b : B, X ^ (E b)` to `X^ (E b)`. -/
def sndProj (X : C) :
    Limits.pullback (fstProj P X) P.p ⟶ X :=
  (P.mvPoly.sndProj (toOverTerminal.obj X)).left

lemma sndProj_comp {X Y : C} (f : X ⟶ Y) : sndProj P X ≫ f =
    pullback.map _ _ _ _ (P.functor.map f) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ sndProj P Y :=
  P.mvPoly.sndProj_comp (toOverTerminal.map f)

open TwoSquare

/-- A commutative triangle
```
      I
    ↗  ↖
P.i/      \Q.i
  /    ρ   \
 E -------> F
  \        /
P.p\      / Q.p
    ↘  ↙
      B
```
induces a natural transformation `Q.functor ⟶ P.functor ` obtained by pasting the following 2-cells
```
                  Q.mvPoly.functor
C --- ≅ ---> R.Over ⊤ 1 ----> R.Over ⊤ 1 --- ≅ ---> C
‖                ‖                 ‖                ‖
‖                ‖                 ‖                ‖
‖                ‖        ↓       ‖                ‖
‖                ‖                 ‖                ‖
‖                ‖                 ‖                ‖
C --- ≅ ---> R.Over ⊤ 1 ----> R.Over ⊤ 1 --- ≅ ---> C
                 P.mvPoly.functor
```
-/
def verticalNatTrans {F : C} (Q : UvPoly R F B) (ρ : E ⟶ F)
    [R.IsStableUnderPushforwardsAlong Q.p] [R.HasPushforwardsAlong Q.p]
    (h : P.p = ρ ≫ Q.p) : Q.functor ⟶ P.functor :=
  let mv : Q.mvPoly.functor ⟶ P.mvPoly.functor :=
    MvPoly.verticalNatTrans P.mvPoly Q.mvPoly ρ (isTerminal.hom_ext ..) h (isTerminal.hom_ext ..)
  (toOverTerminal).whiskerLeft (Functor.whiskerRight mv fromOverTerminal)

open TwoSquare

/-- A cartesian map of polynomials
```
           φ
      E  -------->  E'
      |             |
  P.p |    (pb)     | P'.p
      v             v
      B  -------->  B'
            δ
```
induces a natural transformation between their associated functors obtained by pasting the following
2-cells
```
                   P'.p
C --- >  R.Over E' ----> R.Over B' -----> C
‖           |               |             ‖
‖    ↗     | φ*     ≅      | δ*    ↗    ‖
‖           v               v             ‖
C --- >  R.Over E -----> R.Over B  -----> C
                   P.p
```
-/
def cartesianNatTrans {E' B' : C} (P' : UvPoly R E' B')
    [R.IsStableUnderPushforwardsAlong P'.p] [R.HasPushforwardsAlong P'.p]
    (δ : B ⟶ B') (φ : E ⟶ E') (pb : IsPullback φ P.p P'.p δ) : P.functor ⟶ P'.functor :=
  let mv := P.mvPoly.cartesianNatTrans P'.mvPoly δ φ (isTerminal.hom_ext ..)
    pb (isTerminal.hom_ext ..)
  (toOverTerminal).whiskerLeft (Functor.whiskerRight mv fromOverTerminal)

-- TODO: this is cartesian. Unlike with the MvPoly case there is no distinction between
-- `C` and `Over.terminal` and `R.Over terminal`, since `R` has objects.

open NatTrans in
theorem isCartesian_cartesianNatTrans {D F : C} (Q : UvPoly R F D)
    [R.IsStableUnderPushforwardsAlong Q.p] [R.HasPushforwardsAlong Q.p]
    (δ : B ⟶ D) (φ : E ⟶ F) (pb : IsPullback φ P.p Q.p δ) :
    (cartesianNatTrans P Q δ φ pb).IsCartesian := by
  apply IsCartesian.whiskerLeft
  apply IsCartesian.whiskerRight
  apply MvPoly.isCartesian_cartesianNatTrans

/-- A morphism from a polynomial `P` to a polynomial `Q` is a pair of morphisms `e : E ⟶ E'`
and `b : B ⟶ B'` such that the diagram
```
      E -- P.p ->  B
      ^            |
   ρ  |            |
      |     ψ      |
      Pb --------> B
      |            |
   φ  |            | δ
      v            v
      F -- Q.p ->  D
```
is a pullback square. -/
structure Hom {F D : C} (P : UvPoly R E B) (Q : UvPoly R F D) where
  Pb : C
  δ : B ⟶ D
  φ : Pb ⟶ F
  ψ : Pb ⟶ B
  ρ : Pb ⟶ E
  is_pb : IsPullback ψ φ δ Q.p
  w : ρ ≫ P.p = ψ

namespace Hom

open IsPullback

/-- The identity morphism in the category of polynomials. -/
def id (P : UvPoly R E B) : Hom P P := ⟨E, 𝟙 B, 𝟙 _ , P.p , 𝟙 _, IsPullback.of_id_snd, by simp⟩

end Hom

/-- The domain of the composition of two polynomial signatures.
See `UvPoly.comp`. -/
def compDom {E' B' : C} (P' : UvPoly R E' B')
    [R.IsStableUnderPushforwardsAlong P'.p] [R.HasPushforwardsAlong P'.p] : C :=
  Limits.pullback (sndProj P B') P'.p

/--
The composition of two polynomial signatures. See `UvPoly.comp`.
Note that this is not just composition in the category `C`,
instead it is functor composition in the category `C ⥤ C`,
meaning it satisfies `P.functor ⋙ P'.functor ≅ (comp P P').functor`.

   E' <---- compDom
   |           |
p' |   (pb)    |
   |           |
   V           V
   B' <-----   • -------> E
      sndProj  |          |
               |   (pb)   |p
               |          |
               V          V
             P @ B' -----> B
                    fstProj
-/
def comp {E' B' : C} (P' : UvPoly R E' B')
    [R.IsStableUnderPushforwardsAlong P'.p] [R.HasPushforwardsAlong P'.p] :
    UvPoly R (compDom P P') (P @ B') where
  p := Limits.pullback.fst (sndProj P B') P'.p ≫ pullback.fst (fstProj P B') P.p
  morphismProperty := R.comp_mem _ _
   (R.of_isPullback (IsPullback.of_hasPullback (sndProj P B') P'.p).flip P'.morphismProperty)
   (R.of_isPullback (IsPullback.of_hasPullback (fstProj P B') P.p).flip P.morphismProperty)

namespace Equiv

variable {P} {Γ X Y : C}

/-- Convert the morphism `pair` into a morphism in the over category `Over (𝟭_ C)` -/
@[simp]
abbrev homMk (pair : Γ ⟶ P @ X) : Over.mk (isTerminal.from Γ) ⟶
    ((toOverTerminal ⋙ MvPoly.functor P.mvPoly).obj X).toComma :=
  Over.homMk pair (isTerminal.hom_ext ..)

/--
A morphism `pair : Γ ⟶ P @ X` is equivalent to a pair of morphisms
`fst : Γ ⟶ B` and `snd : pb ⟶ X` in the following diagram
```
    snd
B <---- pb ------> E
        |          |
        |          |p
        |          |
        V          V
        Γ -------> B
             fst
```
The following API allows users to convert back and forth along this (natural) bijection.
-/
def fst (pair : Γ ⟶ P @ X) : Γ ⟶ B :=
  (MvPoly.Equiv.fst (homMk pair)).hom

lemma fst_eq (pair : Γ ⟶ P @ X) : fst pair = pair ≫ P.fstProj X := by
  aesop_cat

def snd (pair : Γ ⟶ P @ X) : Limits.pullback (fst pair) P.p ⟶ X :=
  (MvPoly.Equiv.snd (homMk pair)).left

lemma snd_eq (pair : Γ ⟶ P @ X) : snd pair =
    Limits.pullback.map (fst pair) P.p (P.fstProj X) P.p pair (𝟙 E) (𝟙 B) (by simp [fst_eq])
    (by simp) ≫ sndProj P X := by
  simpa [Limits.pullback.map] using congrArg CommaMorphism.left (MvPoly.Equiv.snd_eq (homMk pair))

def snd' (pair : Γ ⟶ P @ X) {pb f g} (H : IsPullback (P := pb) f g (fst pair) P.p) : pb ⟶ X :=
  H.isoPullback.hom ≫ snd pair

theorem snd_eq_snd' (pair : Γ ⟶ P @ X) : snd pair = snd' pair (.of_hasPullback ..) :=
  by simp [snd']

/-- Convert the morphism `x` into a morphism in the over category `Over (𝟭_ C)` -/
@[simp]
abbrev mkAux (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    (PolynomialPartialAdjunction.leftAdjoint P.mvPoly.i P.mvPoly.p).obj (Over.mk b) ⟶
    ((toOverTerminal (R := R)).obj X).toComma :=
  Over.homMk x (isTerminal.hom_ext ..)

def mk (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) : Γ ⟶ P @ X :=
  (MvPoly.Equiv.mk (P := P.mvPoly) (Γ := Over.mk (isTerminal.from Γ))
    (Over.mk b) (by congr; apply isTerminal.hom_ext) (mkAux b x)).left

def mk' (b : Γ ⟶ B) {pb f g} (H : IsPullback (P := pb) f g b P.p) (x : pb ⟶ X) : Γ ⟶ P @ X :=
  mk b (H.isoPullback.inv ≫ x)

theorem mk_eq_mk' (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    mk b x = mk' b (.of_hasPullback ..) x := by simp [mk']

@[simp]
lemma fst_mk (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    fst (mk b x) = b := by
  simp only [fst, mk, Over.homMk_eta]
  rw! (castMode := .all) [MvPoly.Equiv.fst_mk]
  simp [← heq_eq_eq]; rfl

@[simp]
lemma fst_mk' (b : Γ ⟶ B) {pb f g} (H : IsPullback (P := pb) f g b P.p) (x : pb ⟶ X) :
    fst (mk' b H x) = b := by
  simp [mk']

@[simp]
lemma mk'_comp_fstProj (b : Γ ⟶ B) {pb f g} (H : IsPullback (P := pb) f g b P.p) (x : pb ⟶ X) :
    mk' b H x ≫ P.fstProj X = b := by
  simp [← fst_eq]

theorem fst_comp_left (pair : Γ ⟶ P @ X) {Δ} (f : Δ ⟶ Γ) :
    fst (f ≫ pair) = f ≫ fst pair := by simp [fst_eq]

theorem fst_comp_right (pair : Γ ⟶ P @ X) (f : X ⟶ Y) :
    fst (pair ≫ P.functor.map f) = fst pair := by
  simp [fst_eq]

lemma snd'_eq (pair : Γ ⟶ P @ X) {pb f g} (H : IsPullback (P := pb) f g (fst pair) P.p) :
    snd' pair H = pullback.lift (f ≫ pair) g (by simpa using H.w) ≫ sndProj P X := by
  rw [snd', snd_eq, ← Category.assoc]
  congr 1
  ext <;> simp

/-- Switch the selected pullback `pb` used in `UvPoly.Equiv.snd'` with a different pullback `pb'`. -/
lemma snd'_eq_snd' (pair : Γ ⟶ P @ X) {pb f g} (H : IsPullback (P := pb) f g (fst pair) P.p)
    {pb' f' g'} (H' : IsPullback (P := pb') f' g' (fst pair) P.p) :
    snd' pair H = (H.isoIsPullback _ _ H').hom ≫ snd' pair H' := by
  simp [snd'_eq, ← Category.assoc]
  congr 2
  ext <;> simp

@[simp]
lemma snd_mk (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) : snd (mk b x) =
    eqToHom (by simp) ≫ x := by
  have := MvPoly.Equiv.snd_mk (P := P.mvPoly) (Γ := Over.mk (isTerminal.from Γ))
    (Over.mk b) (by congr; apply isTerminal.hom_ext) (mkAux b x)
  convert congr_arg CommaMorphism.left this
  simp

@[simp]
lemma snd'_mk' (b : Γ ⟶ B) {pb f g} (H : IsPullback (P := pb) f g b P.p) (x : pb ⟶ X) :
    snd' (mk' b H x) (by rwa [fst_mk']) = x := by
  simp only [snd', mk', snd_mk]
  rw! [fst_mk]
  simp

@[simp]
lemma snd'_mk'' (b : Γ ⟶ B) {pb f g} (H : IsPullback (P := pb) f g b P.p) (x : pb ⟶ X)
   {pb' f' g'} (H' : IsPullback (P := pb') f' g' (fst (mk' b H x)) P.p := by exact H) :
    snd' (mk' b H x) H' = H.lift f' g' (by rw [fst_mk'] at H'; simp [H'.w]) ≫ x := by
  simp only [snd', mk', snd_mk]
  rw! [fst_mk]
  simp [← Category.assoc]
  congr 1
  apply H.hom_ext <;> simp


lemma snd_mk_heq (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) :
    snd (mk b x) ≍ x := by
  simp

theorem snd'_comp_left (pair : Γ ⟶ P @ X)
    {pb f g} (H : IsPullback (P := pb) f g (fst pair) P.p)
    {Δ} (σ : Δ ⟶ Γ)
    {pb' f' g'} (H' : IsPullback (P := pb') f' g' (σ ≫ fst pair) P.p) :
    snd' (σ ≫ pair) (by convert H'; rw [fst_comp_left]) =
    H.lift (f' ≫ σ) g' (by simp [H'.w]) ≫ snd' pair H := by
  simp only [snd'_eq, ← Category.assoc]
  congr 2
  ext
  · simp
  · simp

theorem snd'_comp_right (pair : Γ ⟶ P @ X) (f : X ⟶ Y)
    {pb f1 f2} (H : IsPullback (P := pb) f1 f2 (fst pair) P.p) :
    snd' (pair ≫ P.functor.map f) (by rwa [fst_comp_right]) =
    snd' pair H ≫ f := by
  simp only [snd'_eq, assoc]
  conv => right; rw [sndProj_comp, ← Category.assoc]
  congr 1
  ext <;> simp

theorem snd_comp_right (pair : Γ ⟶ P @ X) (f : X ⟶ Y) : snd (pair ≫ P.functor.map f) =
    eqToHom (by congr 1; apply fst_comp_right) ≫ snd pair ≫ f := by
  simp only [snd_eq, assoc, sndProj_comp]
  conv => right; simp only [← Category.assoc]
  congr 1
  have : fst (pair ≫ P.functor.map f) = fst pair := by simp [fst_eq]
  rw! [this]
  ext <;> simp

@[simp]
lemma mk_fst_snd (pair : Γ ⟶ P @ X) :
    mk (fst pair) (snd pair) = pair := by
  have := MvPoly.Equiv.mk_fst_snd (P := P.mvPoly) (Γ := Over.mk (isTerminal.from Γ)) (homMk pair)
  exact congr_arg CommaMorphism.left this

@[simp]
lemma mk'_fst_snd' (pair : Γ ⟶ P @ X)
    {pb f1 f2} (H : IsPullback (P := pb) f1 f2 (fst pair) P.p) :
    mk' (fst pair) H (snd' pair H) = pair := by
  simp only [mk', snd']
  simp

lemma ext' {pair₁ pair₂ : Γ ⟶ P @ X}
    {pb f g} (H : IsPullback (P := pb) f g (fst pair₁) P.p)
    (h1 : fst pair₁ = fst pair₂)
    (h2 : snd' pair₁ H = snd' pair₂ (by rwa [h1] at H)) :
    pair₁ = pair₂ := by
  rw [← mk'_fst_snd' pair₁ H, ← mk'_fst_snd' pair₂ (by rwa [h1] at H), h2]
  rw! [h1]

/-- Switch the selected pullback `pb` used in `UvPoly.Equiv.mk'` with a different pullback `pb'`. -/
theorem mk'_eq_mk' (b : Γ ⟶ B) {pb f g} (H : IsPullback (P := pb) f g b P.p) (x : pb ⟶ X)
    {pb' f' g'} (H' : IsPullback (P := pb') f' g' b P.p) :
    mk' b H x = mk' b H' ((IsPullback.isoIsPullback _ _ H H').inv ≫ x) := by
  apply ext' (R := R) (f := f) (g := g) (by convert H; simp)
  · have : ∀ h, H'.lift f g h ≫ (IsPullback.isoIsPullback Γ E H H').inv = 𝟙 pb := by
      intro ; apply H.hom_ext <;> simp
    simp [← Category.assoc, this]
  · simp

lemma mk'_comp_right (b : Γ ⟶ B) {pb f1 f2} (H : IsPullback (P := pb) f1 f2 b P.p) (x : pb ⟶ X)
    (f : X ⟶ Y) : mk' b H x ≫ P.functor.map f = mk' b H (x ≫ f) := by
  refine .symm <| ext' (by rwa [fst_mk']) (by simp [fst_comp_right]) ?_
  rw [snd'_comp_right (H := by rwa [fst_mk'])]; simp

lemma mk_comp_right (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) (f : X ⟶ Y) :
    mk b x ≫ P.functor.map f = mk b (x ≫ f) := by
  simp [mk_eq_mk', mk'_comp_right]

theorem mk'_comp_left {Δ}
    (b : Γ ⟶ B) {pb f g} (H : IsPullback f g b P.p) (x : pb ⟶ X) (σ : Δ ⟶ Γ)
    (σb) (eq : σ ≫ b = σb)
    {pb' f' g'} (H' : IsPullback (P := pb') f' g' σb P.p) :
    σ ≫ UvPoly.Equiv.mk' b H x = UvPoly.Equiv.mk' σb H'
    (H.lift (f' ≫ σ) g' (by simp [eq, H'.w]) ≫ x) := by
  apply ext' (f := f') (g := g') (H := by convert H'; simp [eq, fst_eq])
  · rw [snd'_comp_left (H := by convert H; rw [fst_mk']) (H' := by convert H'; rw [← eq, fst_mk'])]
    simp
  · simp [eq, fst_comp_left]

theorem mk_comp_left {Δ} (b : Γ ⟶ B) (x : pullback b P.p ⟶ X) (σ: Δ ⟶ Γ) :
    σ ≫ UvPoly.Equiv.mk b x =
    UvPoly.Equiv.mk (σ ≫ b)
      (pullback.map _ _ _ _ σ (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ x) := by
  simp only [mk_eq_mk']
  rw [mk'_comp_left (H := .of_hasPullback _ _) (H' := .of_hasPullback _ _) (eq := rfl)]
  congr 2; ext <;> simp

lemma mk'_comp_cartesianNatTrans_app {E' B' Γ X : C} {P' : UvPoly R E' B'}
    [R.IsStableUnderPushforwardsAlong P'.p] [R.HasPushforwardsAlong P'.p]
    (y : Γ ⟶ B) (pb f g) (H : IsPullback (P := pb) f g y P.p)
    (x : pb ⟶ X) (e : E ⟶ E') (b : B ⟶ B')
    (hp : IsPullback P.p e b P'.p) :
    Equiv.mk' y H x ≫ (P.cartesianNatTrans P' b e hp.flip).app X =
    Equiv.mk' (y ≫ b) (H.paste_vert hp) x := by
  sorry
  -- have : fst (Equiv.mk' y H x ≫ (P.cartesianNatTrans P' b e hp.flip).app X) = y ≫ b := by
  --   rw [fst_eq, Category.assoc, cartesianNatTrans_fstProj, ← Category.assoc, mk'_comp_fstProj]
  -- refine ext' _ _ (this ▸ H.paste_vert hp) (by simpa) ?_
  -- simp; rw [snd'_eq]
  -- have := snd'_mk' P X y H x
  -- rw [snd'_eq, ← fan_snd_map' _ _ X hp] at this
  -- refine .trans ?_ this
  -- simp only [← Category.assoc]; congr 1; ext <;> simp

end Equiv

namespace compDomEquiv

variable {Γ E' B' : C} {P} {P' : UvPoly R E' B'}
  [R.IsStableUnderPushforwardsAlong P'.p] [R.HasPushforwardsAlong P'.p]

/-
```
   Γ
   |
   |triple
   V
 compDom
   |⟍
   |   ⟍
   |      ⟍
   V         ↘
   • -------> E
   |          |
   |   (pb)   |p
   |          |
   V          V
P @ B' -----> B
       fstProj
```
This produces a map `fst : Γ ⟶ E`,
and a map `(triple ≫ P.comp P').p : Γ ⟶ P @ B'`,
which we can further break up using `UvPoly.Equiv.fst` and `UvPoly.Equiv.snd`.
```
  dependent
B <---- pb ------> E
        |          |
        |          |p
        |          |
        V          V
        Γ -------> B
            base
```
-/
def fst (triple : Γ ⟶ compDom P P') : Γ ⟶ E :=
  triple ≫ pullback.fst _ _ ≫ pullback.snd _ _

@[simp]
abbrev base (triple : Γ ⟶ compDom P P') : Γ ⟶ B := Equiv.fst (triple ≫ (P.comp P').p)

theorem fst_comp_p (triple : Γ ⟶ compDom P P') :
    fst triple ≫ P.p = base triple := by
  simp [fst, Equiv.fst_eq, pullback.condition, comp]

abbrev dependent (triple : Γ ⟶ compDom P P') {pb} (f : pb ⟶ Γ) (g : pb ⟶ E)
    (H : IsPullback f g (fst triple ≫ P.p) P.p) : pb ⟶ B' :=
  Equiv.snd' (triple ≫ (P.comp P').p) (by convert H; simp only [fst_comp_p])

def snd (triple : Γ ⟶ compDom P P') : Γ ⟶ E' :=
  triple ≫ pullback.snd _ _

theorem snd_comp_p (triple : Γ ⟶ compDom P P')
    {pb} (f : pb ⟶ Γ) (g : pb ⟶ E) (H : IsPullback f g (fst triple ≫ P.p) P.p) :
    snd triple ≫ P'.p =
    H.lift (𝟙 Γ) (fst triple) (by simp) ≫ dependent triple f g H :=
  calc (triple ≫ pullback.snd _ _) ≫ P'.p
  _ = triple ≫ pullback.fst _ _ ≫ sndProj P B' := by
    simp [pullback.condition]
  _ = H.lift (𝟙 Γ) (fst triple) (by simp) ≫ dependent triple f g H := by
    simp only [← assoc, dependent, comp, Equiv.snd'_eq]
    congr 1
    ext <;> simp [fst]

def mk (b : Γ ⟶ B) (e : Γ ⟶ E) (he : e ≫ P.p = b)
    {pb} (f : pb ⟶ Γ) (g : pb ⟶ E) (H : IsPullback f g b P.p)
    (b' : pb ⟶ B') (e' : Γ ⟶ E') (he' : e' ≫ P'.p = H.lift (𝟙 Γ) e (by simp [he]) ≫ b') :
    Γ ⟶ P.compDom P' :=
  pullback.lift (pullback.lift (Equiv.mk' b H b') e) e' (by
    have : b' = Equiv.snd' (Equiv.mk' b H b') (by convert H; simp) := by rw [Equiv.snd'_mk']
    conv => right; rw [he', this, Equiv.snd'_eq, ← Category.assoc]
    congr 1
    ext <;> simp )

lemma mk_comp (b : Γ ⟶ B) (e : Γ ⟶ E) (he : e ≫ P.p = b)
    {pb} (f : pb ⟶ Γ) (g : pb ⟶ E) (H : IsPullback f g b P.p)
    (b' : pb ⟶ B') (e' : Γ ⟶ E') (he' : e' ≫ P'.p = H.lift (𝟙 Γ) e (by simp [he]) ≫ b') :
    mk b e he f g H b' e' he' ≫ (P.comp P').p = Equiv.mk' b H b' := by
  simp [mk, comp]

@[simp]
lemma base_mk (b : Γ ⟶ B) (e : Γ ⟶ E) (he : e ≫ P.p = b)
    {pb} (f : pb ⟶ Γ) (g : pb ⟶ E) (H : IsPullback f g b P.p)
    (b' : pb ⟶ B') (e' : Γ ⟶ E') (he' : e' ≫ P'.p = H.lift (𝟙 Γ) e (by simp [he]) ≫ b') :
  base (mk b e he f g H b' e' he') = b := by simp [mk, comp]

@[simp]
lemma fst_mk (b : Γ ⟶ B) (e : Γ ⟶ E) (he : e ≫ P.p = b)
    {pb} (f : pb ⟶ Γ) (g : pb ⟶ E) (H : IsPullback f g b P.p)
    (b' : pb ⟶ B') (e' : Γ ⟶ E') (he' : e' ≫ P'.p = H.lift (𝟙 Γ) e (by simp [he]) ≫ b') :
  fst (mk b e he f g H b' e' he') = e := by
  simp [mk, fst]

@[simp]
lemma dependent_mk (b : Γ ⟶ B) (e : Γ ⟶ E) (he : e ≫ P.p = b)
    {pb} (f : pb ⟶ Γ) (g : pb ⟶ E) (H : IsPullback f g b P.p)
    (b' : pb ⟶ B') (e' : Γ ⟶ E') (he' : e' ≫ P'.p = H.lift (𝟙 Γ) e (by simp [he]) ≫ b')
    {pb'} (f' : pb' ⟶ Γ) (g' : pb' ⟶ E)
    (H' : IsPullback f' g' (fst (mk b e he f g H b' e' he') ≫ P.p) P.p) :
  dependent (mk b e he f g H b' e' he') f' g' H' = H.lift f' g' (by simp [← H'.w, he]) ≫ b' := by
  simp [mk, dependent, comp]

@[simp]
lemma snd_mk (b : Γ ⟶ B) (e : Γ ⟶ E) (he : e ≫ P.p = b)
    {pb} (f : pb ⟶ Γ) (g : pb ⟶ E) (H : IsPullback f g b P.p)
    (b' : pb ⟶ B') (e' : Γ ⟶ E') (he' : e' ≫ P'.p = H.lift (𝟙 Γ) e (by simp [he]) ≫ b') :
  snd (mk b e he f g H b' e' he') = e' := by
  simp [mk, snd]

@[simp]
lemma mk_fst_snd (triple : Γ ⟶ compDom P P') {pb} (f : pb ⟶ Γ) (g : pb ⟶ E)
    (H : IsPullback f g (base triple) P.p) (b' : pb ⟶ B')
    (hbase' : b' = Equiv.snd' (triple ≫ (P.comp P').p) H) :
    mk (base triple) (fst triple) (fst_comp_p ..) f g H b' (snd triple) (by
      simp only [snd, assoc, ← pullback.condition, base, comp]
      simp only [hbase', Equiv.snd'_eq, ← Category.assoc]
      congr 1
      ext <;> simp [fst, comp]) = triple := by
  apply pullback.hom_ext
  · ext
    · simp [mk]
      conv => right; rw [← Equiv.mk'_fst_snd'
        (triple ≫ pullback.fst (P.sndProj B') P'.p ≫ pullback.fst (P.fstProj B') P.p) H]
      congr
    · simp [mk, fst]
  · simp [mk, snd]

lemma ext (triple triple' : Γ ⟶ compDom P P')
    (hfst : fst triple = fst triple')
    (hsnd : snd triple = snd triple')
    {pb} (f : pb ⟶ Γ) (g : pb ⟶ E)
    (H : IsPullback f g (fst triple ≫ P.p) P.p)
    (hd : dependent triple f g H = dependent triple' f g (by rwa [← hfst])) :
    triple = triple' := by
  rw [← mk_fst_snd triple f g (by convert H; simp [fst_comp_p]) (dependent triple f g H) rfl,
    ← mk_fst_snd triple' f g (by rwa [← fst_comp_p, ← hfst])
    (dependent triple' f g (by rwa [← hfst])) rfl]
  have : base triple = base triple' := by
    rw [← fst_comp_p, ← fst_comp_p, hfst]
  rw! [hsnd, hd, hfst, this]

lemma fst_comp {Δ} (σ : Δ ⟶ Γ) (triple : Γ ⟶ compDom P P') :
    fst (σ ≫ triple) = σ ≫ fst triple := by
  simp [fst]

lemma snd_comp {Δ} (σ : Δ ⟶ Γ) (triple : Γ ⟶ compDom P P') :
    snd (σ ≫ triple) = σ ≫ snd triple := by
  simp [snd]

lemma dependent_comp {Δ} (σ : Δ ⟶ Γ) (triple : Γ ⟶ compDom P P')
    {pb'} (f' : pb' ⟶ Γ) (g' : pb' ⟶ E) (H' : IsPullback f' g' (fst triple ≫ P.p) P.p)
    {pb} (f : pb ⟶ Δ) (g : pb ⟶ E) (H : IsPullback f g (fst (σ ≫ triple) ≫ P.p) P.p) :
    dependent (σ ≫ triple) f g H = H'.lift (f ≫ σ) g (by simp [← H.w, fst_comp]) ≫
    dependent triple f' g' H' := by
  simp only [dependent, comp, ← assoc, Equiv.snd'_eq]
  congr
  ext <;> simp

lemma comp_mk {Δ} (σ : Δ ⟶ Γ) (b : Γ ⟶ B) (e : Γ ⟶ E) (he : e ≫ P.p = b)
    {pb'} (f' : pb' ⟶ Γ) (g' : pb' ⟶ E) (H' : IsPullback f' g' b P.p)
    {pb} (f : pb ⟶ Δ) (g : pb ⟶ E) (H : IsPullback f g (σ ≫ b) P.p)
    (b' : pb' ⟶ B') (e' : Γ ⟶ E') (he' : e' ≫ P'.p = H'.lift (𝟙 Γ) e (by simp [he]) ≫ b') :
    σ ≫ mk b e he f' g' H' b' e' he' =
    mk (σ ≫ b) (σ ≫ e) (by simp [he]) f g H (H'.lift (f ≫ σ) g (by simp[← H.w]) ≫ b') (σ ≫ e')
    (by simp [he']; simp [← assoc]; congr 1; apply H'.hom_ext <;> simp) := by
  simp [mk]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
      rw [Equiv.mk'_comp_left]
      rfl
    · simp
  · simp

end compDomEquiv

section

variable {F : C} (Q : UvPoly R F B)
    [R.HasPushforwardsAlong Q.p] [R.IsStableUnderPushforwardsAlong Q.p]
    (ρ : E ⟶ F) (h : P.p = ρ ≫ Q.p)

lemma fst_verticalNatTrans_app {Γ : C} (X : C) (pair : Γ ⟶ Q @ X) :
    Equiv.fst (pair ≫ (verticalNatTrans P Q ρ h).app X) = Equiv.fst pair := by
  dsimp [Equiv.fst]
  sorry

lemma snd'_verticalNatTrans_app {Γ : C} (X : C) (pair : Γ ⟶ Q @ X) {R f g}
    (H : IsPullback (P := R) f g (Equiv.fst pair) Q.p) {R' f' g'}
    (H' : IsPullback (P := R') f' g' (Equiv.fst pair) P.p) :
    Equiv.snd' (pair ≫ (verticalNatTrans P Q ρ h).app X) (by
      rw [← fst_verticalNatTrans_app P Q] at H'
      exact H') =
    (H.lift f' (g' ≫ ρ) (by simp [H'.w, h])) ≫
    Equiv.snd' pair H :=
  sorry

lemma mk'_comp_verticalNatTrans_app {Γ : C} (X : C) (b : Γ ⟶ B) {R f g}
    (H : IsPullback (P := R) f g b Q.p) (x : R ⟶ X) {R' f' g'}
    (H' : IsPullback (P := R') f' g' b P.p) :
    Equiv.mk' b H x ≫ (verticalNatTrans P Q ρ h).app X = Equiv.mk'  b H'
    (H.lift f' (g' ≫ ρ) (by simp [H'.w, h]) ≫ x) :=
  sorry

end

-- instance preservesPullbacks (P : UvPoly R E B) {Pb X Y Z : C} (fst : Pb ⟶ X) (snd : Pb ⟶ Y)
--     (f : X ⟶ Z) (g : Y ⟶ Z) (h: IsPullback fst snd f g) :
--     IsPullback (P.functor.map fst) (P.functor.map snd) (P.functor.map f) (P.functor.map g) :=
--   P.functor.map_isPullback h
