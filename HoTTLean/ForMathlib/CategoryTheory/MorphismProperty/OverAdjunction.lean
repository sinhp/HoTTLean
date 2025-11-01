/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.MorphismProperty.Limits
import HoTTLean.ForMathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Adjunction of pushforward and pullback in `P.Over Q X`

Under suitable assumptions on `P`, `Q` and `f`,
a morphism `f : X ⟶ Y` defines two functors:

- `Over.map`: post-composition with `f`
- `Over.pullback`: base-change along `f`

such that `Over.map` is the left adjoint to `Over.pullback`.
We say that `P` is *stable* under pushforward if `Over.pullback`
also is a left adjoint.
We say that `P` is *closed* under pushforward if `Over.pullback`
also is a left adjoint for any `f` satisfying `P`.

-/

namespace CategoryTheory.MorphismProperty

open Limits

variable {T : Type*} [Category T] (P Q : MorphismProperty T) [Q.IsMultiplicative]
variable {X Y Z : T} (f : X ⟶ Y)

section Map

variable {P} [P.IsStableUnderComposition] (hPf : P f)

variable {f}

/-- If `P` is stable under composition and `f : X ⟶ Y` satisfies `P`,
this is the functor `P.Over Q X ⥤ P.Over Q Y` given by composing with `f`. -/
@[simps! obj_left obj_hom map_left]
def Over.map : P.Over Q X ⥤ P.Over Q Y :=
  Comma.mapRight _ (Discrete.natTrans fun _ ↦ f) <| fun X ↦ P.comp_mem _ _ X.prop hPf

lemma Over.map_comp {X Y Z : T} {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) :
    map Q (P.comp_mem f g hf hg) = map Q hf ⋙ map Q hg := by
  fapply Functor.ext
  · simp [map, Comma.mapRight, CategoryTheory.Comma.mapRight, Comma.lift]
  · intro U V k
    ext
    simp

/-- `Over.map` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
def Over.mapComp {X Y Z : T} {f : X ⟶ Y} (hf : P f) {g : Y ⟶ Z} (hg : P g) [Q.RespectsIso] :
    map Q (P.comp_mem f g hf hg) ≅ map Q hf ⋙ map Q hg :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (Iso.refl _))

end Map

section Pullback

variable [P.HasPullback f] [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]

variable {P Q} in
@[simps]
def Over.morphismProperty (f : P.Over Q X) : f.left ⟶(P) X := ⟨ f.hom , f.prop ⟩

instance (A : P.Over Q Y) : HasPullback A.hom f :=
  inferInstanceAs (HasPullback (A.morphismProperty).1 f)

/-- If `P` and `Q` are stable under base change and pullbacks exist in `T`,
this is the functor `P.Over Q Y ⥤ P.Over Q X` given by base change along `f`. -/
@[simps! obj_left obj_hom map_left]
noncomputable def Over.pullback : P.Over Q Y ⥤ P.Over Q X where
  obj A := Over.mk Q (Limits.pullback.snd A.morphismProperty.1 f)
    (baseChange_obj f A.toComma A.prop)
  map {A B} g := Over.homMk (pullback.map _ f _ f g.left (𝟙 _) (𝟙 _) (by simp) (by simp))
    (by simp) (baseChange_map f ⟨g.left, g.right, _⟩ g.prop_hom_left)

variable {P} {Q}

instance [P.IsStableUnderBaseChange] {X Y Z}
    (f : X ⟶ Y) (g : Y ⟶ Z) [P.HasPullback f] [P.HasPullback g] (A : P.Over Q Z) :
    HasPullback (pullback.snd A.hom g) f :=
  inferInstanceAs <| HasPullback (pullback.snd A.morphismProperty.1 g) f

lemma Over.hom_pullback_map [∀ {W : T} (h : W ⟶ Y), HasPullback h f] {A B} (g : A ⟶ B) :
    Comma.Hom.hom ((Over.pullback P Q f).map g) =
    (CategoryTheory.Over.pullback f).map (Comma.Hom.hom g) := by
  simp [Over.pullback, CategoryTheory.Over.pullback, pullback.map]

/-- `Over.pullback` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
noncomputable def Over.pullbackComp (g : Y ⟶ Z) [P.HasPullback g]
    [Q.RespectsIso] : Over.pullback P Q (f ≫ g) ≅ Over.pullback P Q g ⋙ Over.pullback P Q f :=
  NatIso.ofComponents
    (fun X ↦
      Over.isoMk ((pullbackLeftPullbackSndIso X.hom g f).symm) (by simp))

lemma Over.pullbackComp_left_fst_fst (g : Y ⟶ Z) [P.HasPullback g]
    [Q.RespectsIso] (A : P.Over Q Z) : ((Over.pullbackComp f g).hom.app A).left ≫
      pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g =
        pullback.fst A.hom (f ≫ g) := by
  simp

variable {f}
/-- If `f = g`, then base change along `f` is naturally isomorphic to base change along `g`. -/
noncomputable def Over.pullbackCongr {g : X ⟶ Y} (h : f = g) :
    have : P.HasPullback g := by subst h; infer_instance
    Over.pullback P Q f ≅ Over.pullback P Q g :=
  NatIso.ofComponents (fun X ↦ eqToIso (by simp [h]))

@[reassoc (attr := simp)]
lemma Over.pullbackCongr_hom_app_left_fst {g : X ⟶ Y} (h : f = g) (A : P.Over Q Y) :
    have : P.HasPullback g := by subst h; infer_instance
    ((Over.pullbackCongr h).hom.app A).left ≫ pullback.fst A.hom g =
      pullback.fst A.hom f := by
  subst h
  simp [pullbackCongr]

end Pullback

section Adjunction

variable [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
  [Q.IsStableUnderBaseChange] [P.HasPullback f]

/-- `P.Over.map` is left adjoint to `P.Over.pullback` if `f` satisfies `P`. -/
noncomputable def Over.mapPullbackAdj [Q.HasOfPostcompProperty Q] (hPf : P f) (hQf : Q f) :
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
protected abbrev HasPushforward (P : MorphismProperty T) {S S' : T} (f : S ⟶ S')
    [∀ {W} (h : W ⟶ S'), HasPullback h f] : Prop :=
  ∀ {W} (h : W ⟶(P) S), HasPushforward f (.mk h.1)

/-- Morphisms satisfying `P` have pushforwards along morphisms satisfying `Q`.
We require that `[H.HasPullbacks]` so that we can define the universal property of
pushforward along `p` relative to the pullback.
-/
protected abbrev HasPushforwards (P : MorphismProperty T)
    (Q : MorphismProperty T) [Q.HasPullbacks] : Prop :=
  ∀ {S S' : T} (q : S ⟶(Q) S'), P.HasPushforward q.1

/-- Morphisms satisfying `P` are stable under pushforward along morphisms satisfying `Q`
if whenever pushforward along a morphism in `Q` exists it is in `P`. -/
class IsStableUnderPushforward (P : MorphismProperty T)
    (Q : MorphismProperty T) [Q.HasPullbacks] : Prop where
  of_isPushforward {S S' X Y : T} (q : S ⟶(Q) S') (f : X ⟶(P) S) (g : Y ⟶ S')
    (isPushforward : IsPushforward q.1 (.mk f.1) (.mk g)) : P g

noncomputable section

/-- If `P` has pushforwards along `q` then there is a partial left adjoint `P.Over ⊤ S ⥤ Over S'`
of the pullback functor `pullback q : Over S' ⥤ Over S`.
-/
noncomputable def pushforwardPartial (P : MorphismProperty T)
    {S S' : T} (q : S ⟶ S') [∀ {W} (h : W ⟶ S'), HasPullback h q] [P.HasPushforward q] :
    P.Over ⊤ S ⥤ Over S' := by
  refine Functor.PartialRightAdjointSource.lift (Over.forget P ⊤ S) ?_ ⋙
    (CategoryTheory.Over.pullback q).partialRightAdjoint
  intro X
  let X' : _ ⟶(P) S := ⟨ X.hom , X.prop ⟩
  convert_to ((CategoryTheory.Over.pullback q).op ⋙
    yoneda.obj (CategoryTheory.Over.mk X'.fst)).IsRepresentable
  infer_instance

-- section homEquiv

-- variable {P} {S S' : T} (q : S ⟶ S')
--     [∀ {W} (h : W ⟶ S'), HasPullback h q] [P.HasPushforward q] {X : Over S'} {Y : P.Over ⊤ S}

-- /-- The pushforward functor is a partial right adjoint to pullback in the sense that
-- there is a natural bijection of hom-sets
-- `T / S (pullback q X, Y) ≃ T / S' (X, pushforward q Y)`. -/
-- abbrev pushforwardPartial.homEquiv :
--     (X ⟶ (pushforwardPartial P q).obj Y) ≃
--     ((CategoryTheory.Over.pullback q).obj X ⟶ Y.toComma) :=
--   Functor.partialRightAdjointHomEquiv _

-- lemma pushforwardPartial.homEquiv_comp {S S' : T} (q : S ⟶ S')
--     [∀ {W} (h : W ⟶ S'), HasPullback h q] [P.HasPushforward q] {X X' : Over S'} {Y : P.Over ⊤ S}
--     (f : X' ⟶ (pushforwardPartial P q).obj Y) (g : X ⟶ X') :
--     pushforwardPartial.homEquiv q (g ≫ f) =
--     (CategoryTheory.Over.pullback q).map g ≫ pushforwardPartial.homEquiv q f :=
--   Functor.partialRightAdjointHomEquiv_comp ..

-- lemma pushforwardPartial.homEquiv_map_comp {S S' : T} (q : S ⟶ S')
--     [∀ {W} (h : W ⟶ S'), HasPullback h q] [P.HasPushforward q] {X : Over S'} {Y Y' : P.Over ⊤ S}
--     (f : X ⟶ (pushforwardPartial P q).obj Y) (g : Y ⟶ Y') :
--     pushforwardPartial.homEquiv q (f ≫ (P.pushforwardPartial q).map g) =
--     pushforwardPartial.homEquiv q f ≫ g.toCommaMorphism :=
--   Functor.partialRightAdjointHomEquiv_map_comp ..

-- end homEquiv

/-- When `P` has pushforwards along `Q` and is stable under pushforwards along `Q`,
the pushforward functor along any morphism `q` satisfying `Q` can be defined. -/
noncomputable def pushforward {Q : MorphismProperty T} [Q.HasPullbacks] [P.HasPushforwards Q]
    [P.IsStableUnderPushforward Q] {S S' : T} (q : S ⟶(Q) S') : P.Over ⊤ S ⥤ P.Over ⊤ S' :=
  Comma.lift (pushforwardPartial P q.1) (fun X =>
    let X' : _ ⟶(P) S := ⟨ X.hom , X.prop ⟩
    IsStableUnderPushforward.of_isPushforward q X' _
        (pushforward.isPushforward q.fst (CategoryTheory.Over.mk X'.fst)))
  (by simp) (by simp)

section homEquiv

variable {P} {Q : MorphismProperty T} [Q.HasPullbacks] [P.HasPushforwards Q]
  [P.IsStableUnderPushforward Q] {S S' : T} (q : S ⟶(Q) S')

/-- The pushforward functor is a partial right adjoint to pullback in the sense that
there is a natural bijection of hom-sets `T / S (pullback q X, Y) ≃ T / S' (X, pushforward q Y)`. -/
def pushforward.homEquiv {X : Over S'} {Y : P.Over ⊤ S} :
    (X ⟶ ((pushforward P q).obj Y).toComma) ≃
    ((CategoryTheory.Over.pullback q.1).obj X ⟶ Y.toComma) :=
  (Functor.partialRightAdjointHomEquiv ..)

lemma pushforward.homEquiv_comp {X X' : Over S'} {Y : P.Over ⊤ S}
    (f : X' ⟶ ((pushforward P q).obj Y).toComma) (g : X ⟶ X') :
    pushforward.homEquiv q (g ≫ f) =
    (CategoryTheory.Over.pullback q.fst).map g ≫ homEquiv q f :=
  Functor.partialRightAdjointHomEquiv_comp ..

lemma pushforward.homEquiv_map_comp {X : Over S'} {Y Y' : P.Over ⊤ S}
    (f : X ⟶ ((pushforward P q).obj Y).toComma) (g : Y ⟶ Y') :
    homEquiv q (f ≫ Comma.Hom.hom ((P.pushforward q).map g)) =
    homEquiv q f ≫ Comma.Hom.hom g :=
  Functor.partialRightAdjointHomEquiv_map_comp ..

lemma pushforward.homEquiv_symm_comp {X : Over S'} {Y Y' : P.Over ⊤ S}
    (f : (CategoryTheory.Over.pullback q.1).obj X ⟶ Y.toComma) (g : Y ⟶ Y') :
    (homEquiv q).symm f ≫ Comma.Hom.hom ((P.pushforward q).map g) =
    (homEquiv q).symm (f ≫ Comma.Hom.hom g) :=
  Functor.partialRightAdjointHomEquiv_symm_comp ..

lemma pushforward.homEquiv_comp_symm {X X' : Over S'} {Y : P.Over ⊤ S}
    (f : (CategoryTheory.Over.pullback q.1).obj X' ⟶ Y.toComma) (g : X ⟶ X') :
    g ≫ (homEquiv q).symm f =
    (homEquiv q).symm ((CategoryTheory.Over.pullback q.fst).map g ≫ f) :=
  Functor.partialRightAdjointHomEquiv_comp_symm ..

end homEquiv

section

open MorphismProperty.Over

variable [P.IsStableUnderBaseChange] {S S' : T} (f : S ⟶(Q) S')
    [Q.HasPullbacks] [P.HasPushforwards Q] [P.IsStableUnderPushforward Q]

/-- The `pullback ⊣ pushforward` adjunction. -/
def pullbackPushforwardAdjunction : pullback P ⊤ f.1 ⊣ pushforward P f :=
  Adjunction.mkOfHomEquiv {
    homEquiv X Y :=
      calc ((pullback P ⊤ f.1).obj X ⟶ Y)
      _ ≃ (((Over.pullback P ⊤ f.fst).obj X).toComma ⟶ Y.toComma) :=
        (Functor.FullyFaithful.ofFullyFaithful (Over.forget P ⊤ S)).homEquiv
      _ ≃ (X.toComma ⟶ ((P.pushforward f).obj Y).toComma) :=
        (pushforward.homEquiv f).symm
      _ ≃ _ := Equiv.cast (by dsimp) -- why?
      _ ≃ (X ⟶ (P.pushforward f).obj Y) :=
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
      simp only [Comma.forget_obj, Comma.forget_map, hom_pullback_map]
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

instance : (pullback P ⊤ f.1).IsLeftAdjoint :=
  Adjunction.isLeftAdjoint (pullbackPushforwardAdjunction P Q f)

instance : (pushforward P f).IsRightAdjoint :=
  Adjunction.isRightAdjoint (pullbackPushforwardAdjunction P Q f)

end

section homEquiv

variable {P} [P.HasPullbacks] [P.IsStableUnderBaseChange] {S S' : T} (i : S ⟶ S')

/-- `MorphismProperty.Over.pullback P ⊤ f` is a partial right adjoint to `Over.map f`. -/
@[simps!]
def pullback.homEquiv {X : Over S} {Y : P.Over ⊤ S'} :
    (X ⟶ ((Over.pullback P ⊤ i).obj Y).toComma) ≃
    ((CategoryTheory.Over.map i).obj X ⟶ Y.toComma) where
  toFun v := CategoryTheory.Over.homMk (v.left ≫ pullback.fst _ _) <| by
            simp only [Over.morphismProperty_fst, Category.assoc, pullback.condition,
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
