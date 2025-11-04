/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.MorphismProperty.Comma
import HoTTLean.ForMathlib.CategoryTheory.MorphismProperty.Limits
import HoTTLean.ForMathlib.CategoryTheory.Comma.Over.Pushforward

/-!
# Adjunction of pushforward and pullback in `P.Over Q X`

Under suitable assumptions on `P`, `Q` and `f`,
a morphism `f : X ⟶ Y` defines two functors:

- `Over.map`: post-composition with `f`
- `Over.pullback`: base-change along `f`

such that `Over.map` is the left adjoint to `Over.pullback`.
-/

namespace CategoryTheory.MorphismProperty

open Limits

variable {T : Type*} [Category T] (P Q : MorphismProperty T)
variable {X Y Z : T}

section Map

variable {P} [P.IsStableUnderComposition] [Q.IsMultiplicative]

/-- If `P` is stable under composition and `f : X ⟶ Y` satisfies `P`,
this is the functor `P.Over Q X ⥤ P.Over Q Y` given by composing with `f`. -/
@[simps! obj_left obj_hom map_left]
def Over.map {f : X ⟶ Y} (hPf : P f) : P.Over Q X ⥤ P.Over Q Y :=
  Comma.mapRight _ (Discrete.natTrans fun _ ↦ f) <| fun X ↦ P.comp_mem _ _ X.prop hPf

lemma Over.map_comp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) :
    map Q (P.comp_mem f g hf hg) = map Q hf ⋙ map Q hg := by
  fapply Functor.ext
  · simp [map, Comma.mapRight, CategoryTheory.Comma.mapRight, Comma.lift]
  · intro U V k
    ext
    simp

/-- `Over.map` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
def Over.mapComp {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) [Q.RespectsIso] :
    map Q (P.comp_mem f g hf hg) ≅ map Q hf ⋙ map Q hg :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (Iso.refl _))

end Map

section Pullback

variable [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange] [Q.IsMultiplicative]

instance (f : X ⟶ Y) [P.HasPullbacksAlong f] (A : P.Over Q Y) : HasPullback A.hom f :=
  HasPullbacksAlong.hasPullback A.hom A.prop

instance [P.IsStableUnderBaseChange] {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) [P.HasPullbacksAlong f]
    [P.HasPullbacksAlong g] (A : P.Over Q Z) : HasPullback (pullback.snd A.hom g) f :=
  HasPullbacksAlong.hasPullback (pullback.snd A.hom g)
  (P.of_isPullback (IsPullback.of_hasPullback A.hom g) A.prop)

/-- If `P` and `Q` are stable under base change and pullbacks along `f` exist for morphisms in `P`,
this is the functor `P.Over Q Y ⥤ P.Over Q X` given by base change along `f`. -/
@[simps! obj_left obj_hom map_left]
noncomputable def Over.pullback (f : X ⟶ Y) [P.HasPullbacksAlong f] :
    P.Over Q Y ⥤ P.Over Q X where
  obj A := Over.mk Q (Limits.pullback.snd A.hom f)
    (pullback_snd A.hom f A.prop)
  map {A B} g := Over.homMk (pullback.lift (pullback.fst A.hom f ≫ g.left)
    (pullback.snd A.hom f) (by simp [pullback.condition])) (by simp)
    (baseChange_map' _ _ g.prop_hom_left)

variable {P} {Q}

/-- `Over.pullback` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
noncomputable def Over.pullbackComp (f : X ⟶ Y) [P.HasPullbacksAlong f] (g : Y ⟶ Z)
    [P.HasPullbacksAlong g] [Q.RespectsIso] : Over.pullback P Q (f ≫ g) ≅
    Over.pullback P Q g ⋙ Over.pullback P Q f :=
  NatIso.ofComponents
    (fun X ↦ Over.isoMk ((pullbackLeftPullbackSndIso X.hom g f).symm) (by simp))

lemma Over.pullbackComp_left_fst_fst (f : X ⟶ Y) [P.HasPullbacksAlong f] (g : Y ⟶ Z)
    [P.HasPullbacksAlong g] [Q.RespectsIso] (A : P.Over Q Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫ pullback.fst (pullback.snd A.hom g) f ≫
    pullback.fst A.hom g = pullback.fst A.hom (f ≫ g) := by
  simp

/-- If `f = g`, then base change along `f` is naturally isomorphic to base change along `g`. -/
noncomputable def Over.pullbackCongr {f : X ⟶ Y} [P.HasPullbacksAlong f] {g : X ⟶ Y} (h : f = g) :
    have : P.HasPullbacksAlong g := by subst h; infer_instance
    Over.pullback P Q f ≅ Over.pullback P Q g :=
  NatIso.ofComponents (fun X ↦ eqToIso (by simp [h]))

@[reassoc (attr := simp)]
lemma Over.pullbackCongr_hom_app_left_fst {f : X ⟶ Y} [P.HasPullbacksAlong f] {g : X ⟶ Y}
    (h : f = g) (A : P.Over Q Y) :
    have : P.HasPullbacksAlong g := by subst h; infer_instance
    ((Over.pullbackCongr h).hom.app A).left ≫ pullback.fst A.hom g = pullback.fst A.hom f := by
  subst h
  simp [pullbackCongr]

end Pullback

section Adjunction

variable [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/-- `P.Over.map` is left adjoint to `P.Over.pullback` if `f` satisfies `P` and `Q`. -/
noncomputable def Over.mapPullbackAdj (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [Q.HasOfPostcompProperty Q] (hPf : P f) (hQf : Q f) :
    Over.map Q hPf ⊣ Over.pullback P Q f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A B ↦
        { toFun := fun g ↦
            Over.homMk (pullback.lift g.left A.hom <| by simp) (by simp) <| by
              apply Q.of_postcomp (W' := Q)
              · exact Q.pullback_fst B.hom f hQf
              · simpa using g.prop_hom_left
          invFun := fun h ↦ Over.homMk (h.left ≫ pullback.fst B.hom f)
            (by
              simp only [map_obj_left, Functor.const_obj_obj, pullback_obj_left, Functor.id_obj,
                Category.assoc, pullback.condition, map_obj_hom, ← pullback_obj_hom, Over.w_assoc])
            (Q.comp_mem _ _ h.prop_hom_left (Q.pullback_fst _ _ hQf))
          left_inv := by cat_disch
          right_inv := fun h ↦ by
            ext
            dsimp
            ext
            · simp
            · simpa using h.w.symm } }

end Adjunction

/-- Pushforward along a morphism `f` (for which all pullbacks exist) exists relative to `P`
when pushforwards exist along `f` for all morphisms satisfying `P`. -/
protected class HasPushforwardsAlong {S S' : T} {f : S ⟶ S'}
    (hpb : HasPullbacksAlong f) : Prop where
  hasPushforward : ∀ {W} (h : W ⟶ S), P h → HasPushforward f (.mk h)

lemma hasPullbacksAlong_of_hasPullbacks {Q : MorphismProperty T} [Q.HasPullbacks]
    {S S' : T} {q : S ⟶ S'} (hq : Q q) : HasPullbacksAlong q :=
  fun h => have := (Q.hasPullback h hq); hasPullback_symmetry q h

variable {P Q} in
lemma hasPullbacksAlong_of_hasPullbacks' [Q.HasPullbacks] {S S' : T} {f : S ⟶ S'} (hf : Q f) :
    P.HasPullbacksAlong f where
  hasPullback g _ := hasPullbacksAlong_of_hasPullbacks hf g

/-- Morphisms satisfying `P` have pushforwards along morphisms satisfying `Q`.
We require that `[H.HasPullbacks]` so that we can define the universal property of
pushforward along `p` relative to the pullback.
-/
protected class HasPushforwards [Q.HasPullbacks] : Prop where
  hasPushforwardsAlong : ∀ {S S' : T} (q : S ⟶ S') (hq : Q q),
    P.HasPushforwardsAlong (hasPullbacksAlong_of_hasPullbacks hq)

variable {P Q} in
lemma HasPushforwards.hasPushforward [Q.HasPullbacks] [P.HasPushforwards Q]
    {S S' W : T} {f : S ⟶ S'} (hf : Q f) {g : W ⟶ S} (hg : P g) :
    @HasPushforward _ _ _ _ f (fun h => hasPullbacksAlong_of_hasPullbacks hf h) (.mk g) :=
  (HasPushforwards.hasPushforwardsAlong f hf).hasPushforward g hg

/-- Morphisms satisfying `P` are stable under pushforward along morphisms satisfying `Q`
if whenever pushforward along a morphism in `Q` exists it is in `P`. -/
class IsStableUnderPushforward [Q.HasPullbacks] : Prop where
  of_isPushforward {S S' X Y : T} (q : S ⟶ S') (hq : Q q) (f : X ⟶ S) (hf : P f) {g : Y ⟶ S'}
  (isPushforward : IsPushforward (inst_hasPullback := hasPullbacksAlong_of_hasPullbacks hq)
    q (.mk f) (.mk g)) : P g

noncomputable section

/-- If `P` has pushforwards along `q` then there is a partial left adjoint `P.Over ⊤ S ⥤ Over S'`
of the pullback functor `pullback q : Over S' ⥤ Over S`.
-/
noncomputable def pushforwardPartial {S S' : T} (q : S ⟶ S')
    (hpb : HasPullbacksAlong q)
    (hpf : P.HasPushforwardsAlong hpb) :
    P.Over ⊤ S ⥤ Over S' :=
  ObjectProperty.lift _ (Over.forget P ⊤ S)
    (fun X => HasPushforwardsAlong.hasPushforward X.hom X.prop) ⋙
    (CategoryTheory.Over.pullback q).partialRightAdjoint

/-- When `P` has pushforwards along `Q` and is stable under pushforwards along `Q`,
the pushforward functor along any morphism `q` satisfying `Q` can be defined. -/
noncomputable def pushforward {Q : MorphismProperty T} [Q.HasPullbacks] [P.HasPushforwards Q]
    [P.IsStableUnderPushforward Q] {S S' : T} {q : S ⟶ S'} (hq : Q q) :
    P.Over ⊤ S ⥤ P.Over ⊤ S' :=
  Comma.lift (pushforwardPartial P q (hasPullbacksAlong_of_hasPullbacks hq)
    (HasPushforwards.hasPushforwardsAlong q hq)
    ) (fun X => IsStableUnderPushforward.of_isPushforward q hq X.hom X.prop
      ((have : HasPullbacksAlong q := hasPullbacksAlong_of_hasPullbacks hq
        have : HasPushforward q X.toComma := HasPushforwards.hasPushforward hq X.prop
        pushforward.isPushforward q (X.toComma))))
  (by simp) (by simp)

section homEquiv

open Over

variable {P} {Q : MorphismProperty T} [Q.HasPullbacks] [P.HasPushforwards Q]
  [P.IsStableUnderPushforward Q] {S S' : T} {q : S ⟶ S'} (hq : Q q)

@[simp]
abbrev Over.pullback' := @CategoryTheory.Over.pullback _ _ _ _ q (hasPullbacksAlong_of_hasPullbacks hq)

/-- The pushforward functor is a partial right adjoint to pullback in the sense that
there is a natural bijection of hom-sets `T / S (pullback q X, Y) ≃ T / S' (X, pushforward q Y)`. -/
def pushforward.homEquiv {X : Over S'} {Y : P.Over ⊤ S} :
    (X ⟶ ((pushforward P hq).obj Y).toComma) ≃
    ((pullback' hq).obj X ⟶
    Y.toComma) :=
  (Functor.partialRightAdjointHomEquiv ..)

lemma pushforward.homEquiv_comp {X X' : Over S'} {Y : P.Over ⊤ S}
    (f : X' ⟶ ((pushforward P hq).obj Y).toComma) (g : X ⟶ X') :
    pushforward.homEquiv hq (g ≫ f) =
    (pullback' hq).map g ≫ homEquiv hq f :=
  Functor.partialRightAdjointHomEquiv_comp ..

lemma pushforward.homEquiv_map_comp {X : Over S'} {Y Y' : P.Over ⊤ S}
    (f : X ⟶ ((pushforward P hq).obj Y).toComma) (g : Y ⟶ Y') :
    homEquiv hq (f ≫ Comma.Hom.hom ((P.pushforward hq).map g)) =
    homEquiv hq f ≫ Comma.Hom.hom g :=
  Functor.partialRightAdjointHomEquiv_map_comp ..

lemma pushforward.homEquiv_symm_comp {X : Over S'} {Y Y' : P.Over ⊤ S}
    (f : (pullback' hq).obj X ⟶ Y.toComma) (g : Y ⟶ Y') :
    (homEquiv hq).symm f ≫ Comma.Hom.hom ((P.pushforward hq).map g) =
    (homEquiv hq).symm (f ≫ Comma.Hom.hom g) :=
  Functor.partialRightAdjointHomEquiv_symm_comp ..

lemma pushforward.homEquiv_comp_symm {X X' : Over S'} {Y : P.Over ⊤ S}
    (f : (pullback' hq).obj X' ⟶ Y.toComma) (g : X ⟶ X') :
    g ≫ (homEquiv hq).symm f =
    (homEquiv hq).symm ((pullback' hq).map g ≫ f) :=
  Functor.partialRightAdjointHomEquiv_comp_symm ..

end homEquiv

section

open MorphismProperty.Over

variable {Q} [P.IsStableUnderBaseChange] {S S' : T} {f : S ⟶ S'} (hf : Q f)
    [Q.HasPullbacks] [P.HasPushforwards Q] [P.IsStableUnderPushforward Q]

@[simp]
abbrev Over.pullback'' := @Over.pullback _ _ P ⊤ _ _ _ _ _ f
  (hasPullbacksAlong_of_hasPullbacks' hf)

/-- The `pullback ⊣ pushforward` adjunction. -/
def pullbackPushforwardAdjunction : @Over.pullback _ _ P ⊤ _ _ _ _ _ f
  (hasPullbacksAlong_of_hasPullbacks' hf)  ⊣ pushforward P hf :=
  Adjunction.mkOfHomEquiv {
    homEquiv X Y :=
      calc ((pullback'' P hf).obj X ⟶ Y)
      _ ≃ (((pullback'' P hf).obj X).toComma ⟶ Y.toComma) :=
        (Functor.FullyFaithful.ofFullyFaithful (Over.forget P ⊤ S)).homEquiv
      _ ≃ (X.toComma ⟶ ((P.pushforward hf).obj Y).toComma) :=
        (pushforward.homEquiv hf).symm
      _ ≃ _ := Equiv.cast (by dsimp) -- why?
      _ ≃ (X ⟶ (P.pushforward hf).obj Y) :=
        (Functor.FullyFaithful.ofFullyFaithful (Over.forget P ⊤ S')).homEquiv.symm
    homEquiv_naturality_left_symm g f := by
      simp only [Equiv.trans_def, Equiv.cast_refl, Equiv.trans_refl,
        Equiv.symm_trans_apply, Equiv.symm_symm]
      erw [Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.homEquiv_symm_apply,
        Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.homEquiv_symm_apply,
        Functor.map_comp, pushforward.homEquiv_comp]
      apply Functor.FullyFaithful.map_injective
        (Functor.FullyFaithful.ofFullyFaithful (Over.forget P ⊤ S))
      simp only [Functor.FullyFaithful.map_preimage, Functor.map_comp]
      simp only [Comma.forget_obj, Comma.forget_map]
      congr 1
    homEquiv_naturality_right f g := by
      simp only [Comma.forget_obj, Equiv.trans_def, Equiv.cast_refl, Equiv.trans_refl,
        Equiv.trans_apply]
      erw [Functor.FullyFaithful.homEquiv_symm_apply, Functor.FullyFaithful.homEquiv_symm_apply,
        Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.homEquiv_apply]
      apply Functor.FullyFaithful.map_injective
        (Functor.FullyFaithful.ofFullyFaithful (Over.forget P ⊤ S'))
      simp only [Functor.FullyFaithful.map_preimage, Functor.map_comp]
      erw [pushforward.homEquiv_symm_comp]
      rfl
  }

instance : (pullback'' P hf).IsLeftAdjoint :=
  Adjunction.isLeftAdjoint (pullbackPushforwardAdjunction P hf)

instance : (pushforward P hf).IsRightAdjoint :=
  Adjunction.isRightAdjoint (pullbackPushforwardAdjunction P hf)

end

section homEquiv

variable {P} [P.HasPullbacks] [P.IsStableUnderBaseChange] {S S' : T} (i : S ⟶ S')

/-- `MorphismProperty.Over.pullback P ⊤ f` is a partial right adjoint to `Over.map f`. -/
@[simps!]
def pullback.homEquiv {X : Over S} {Y : P.Over ⊤ S'} :
    (X ⟶ ((Over.pullback P ⊤ i).obj Y).toComma) ≃
    ((CategoryTheory.Over.map i).obj X ⟶ Y.toComma) where
  toFun v := CategoryTheory.Over.homMk (v.left ≫ pullback.fst _ _) <| by
            simp only [Category.assoc, pullback.condition,
              CategoryTheory.Over.map_obj_hom]
            erw [← CategoryTheory.Over.w v]
            simp
  invFun u := CategoryTheory.Over.homMk (pullback.lift u.left X.hom <| by simp)
  left_inv v := by
    ext; dsimp; ext
    · simp
    · simpa using (CategoryTheory.Over.w v).symm
  right_inv u := by cat_disch

lemma pullback.homEquiv_comp {X X' : Over S} {Y : P.Over ⊤ S'}
    (f : X' ⟶ ((Over.pullback P ⊤ i).obj Y).toComma) (g : X ⟶ X') :
    homEquiv i (g ≫ f) =
    (CategoryTheory.Over.map i).map g ≫ homEquiv i f := by
  ext; simp

lemma pullback.homEquiv_map_comp {X : Over S} {Y Y' : P.Over ⊤ S'}
    (f : X ⟶ ((Over.pullback P ⊤ i).obj Y).toComma) (g : Y ⟶ Y') :
    homEquiv i (f ≫ Comma.Hom.hom ((Over.pullback P ⊤ i).map g)) =
    homEquiv i f ≫ Comma.Hom.hom g := by
  ext; simp

lemma pullback.homEquiv_symm_comp {X : Over S} {Y Y' : P.Over ⊤ S'}
    (f : (CategoryTheory.Over.map i).obj X ⟶ Y.toComma) (g : Y ⟶ Y') :
    (homEquiv i).symm f ≫ Comma.Hom.hom ((Over.pullback P ⊤ i).map g) =
    (homEquiv i).symm (f ≫ Comma.Hom.hom g) := by
  ext; dsimp; ext
  · simp
  · simp

lemma pullback.homEquiv_comp_symm {X X' : Over S} {Y : P.Over ⊤ S'}
    (f : (CategoryTheory.Over.map i).obj X' ⟶ Y.toComma) (g : X ⟶ X') :
    g ≫ (homEquiv i).symm f =
    (homEquiv i).symm ((CategoryTheory.Over.map i).map g ≫ f) := by
  ext; dsimp; ext
  · simp
  · simp

end homEquiv

end

end CategoryTheory.MorphismProperty
