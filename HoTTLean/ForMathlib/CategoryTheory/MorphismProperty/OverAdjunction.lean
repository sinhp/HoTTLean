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

lemma Over.forget_preimage {S} {X Y : P.Over ⊤ S} (g : X.toComma ⟶ Y.toComma) :
    (Functor.FullyFaithful.ofFullyFaithful (Over.forget P ⊤ S)).preimage g =
    Over.homMk g.left := by
  simp [Functor.FullyFaithful.ofFullyFaithful]
  apply (Over.forget P ⊤ S).map_injective
  rw [Functor.map_preimage]
  simp

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

/-- A morphism property is `IsStableUnderBaseChangeAlong f` if the base change along `f` of such
a morphism still falls in the class. -/
class IsStableUnderBaseChangeAlong {X S : T} (f : X ⟶ S) : Prop where
  of_isPullback {Y Y' : T} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (pb : IsPullback f' g' g f) (hg : P g) : P g'

instance [P.IsStableUnderBaseChange] {X S : T} (f : X ⟶ S) : P.IsStableUnderBaseChangeAlong f where
  of_isPullback := P.of_isPullback

variable [Q.IsStableUnderBaseChange] [Q.IsMultiplicative] (f : X ⟶ Y) [P.HasPullbacksAlong f]
  [P.IsStableUnderBaseChangeAlong f]

instance (A : P.Over Q Y) : HasPullback A.hom f :=
  HasPullbacksAlong.hasPullback A.hom A.prop

instance {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong g] [P.HasPullbacksAlong g] : P.HasPullbacksAlong (f ≫ g) where
  hasPullback p hp :=
  have := HasPullbacksAlong.hasPullback (f := g) p hp
  have right := IsPullback.of_hasPullback p g
  have := HasPullbacksAlong.hasPullback (f := f) (pullback.snd p g)
    (IsStableUnderBaseChangeAlong.of_isPullback right hp)
  (IsPullback.paste_horiz (IsPullback.of_hasPullback (pullback.snd p g) f) right).hasPullback

instance {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g] [P.HasPullbacksAlong g] :
    P.IsStableUnderBaseChangeAlong (f ≫ g) where
  of_isPullback {_ _ p _ _} pb hp :=
  have := HasPullbacksAlong.hasPullback (f := g) p hp
  have right := IsPullback.of_hasPullback p g
  IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_right' pb right)
    (IsStableUnderBaseChangeAlong.of_isPullback right hp)

instance {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g]
    (A : P.Over Q Z) : HasPullback (pullback.snd A.hom g) f :=
  HasPullbacksAlong.hasPullback (pullback.snd A.hom g)
  (IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback A.hom g) A.prop)

/-- If `P` and `Q` are stable under base change and pullbacks along `f` exist for morphisms in `P`,
this is the functor `P.Over Q Y ⥤ P.Over Q X` given by base change along `f`. -/
@[simps! obj_left obj_hom map_left]
noncomputable def Over.pullback :
    P.Over Q Y ⥤ P.Over Q X where
  obj A := Over.mk Q (Limits.pullback.snd A.hom f)
    (IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback A.hom f) A.prop)
  map {A B} g := Over.homMk (pullback.lift (pullback.fst A.hom f ≫ g.left)
    (pullback.snd A.hom f) (by simp [pullback.condition])) (by simp)
    (baseChange_map' _ _ g.prop_hom_left)

variable {P} {Q} (f : X ⟶ Y) [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    (g : Y ⟶ Z) [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong g]

/-- `Over.pullback` commutes with composition. -/
@[simps! hom_app_left inv_app_left]
noncomputable def Over.pullbackComp [Q.RespectsIso] :
    Over.pullback P Q (f ≫ g) ≅
    Over.pullback P Q g ⋙ Over.pullback P Q f :=
  NatIso.ofComponents
    (fun X ↦ Over.isoMk ((pullbackLeftPullbackSndIso X.hom g f).symm) (by simp))

lemma Over.pullbackComp_left_fst_fst (A : P.Over Q Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫ pullback.fst (pullback.snd A.hom g) f ≫
    pullback.fst A.hom g = pullback.fst A.hom (f ≫ g) := by
  simp

variable {f} {g}

/-- If `f = g`, then base change along `f` is naturally isomorphic to base change along `g`. -/
@[simps!]
noncomputable def Over.pullbackCongr {g : X ⟶ Y} (h : f = g) :
    have : P.HasPullbacksAlong g := by subst h; infer_instance
    have : P.IsStableUnderBaseChangeAlong g := by subst h; infer_instance
    Over.pullback P Q f ≅ Over.pullback P Q g :=
  have : P.HasPullbacksAlong g := by subst h; infer_instance
  NatIso.ofComponents (fun _ ↦ Over.isoMk (pullback.congrHom rfl h))

end Pullback

section Adjunction

variable {P Q} [P.IsStableUnderComposition] [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/-- `P.Over.map` is left adjoint to `P.Over.pullback` if `f` satisfies `P` and `Q`. -/
@[simps!]
noncomputable def Over.mapPullbackAdjHomEquiv (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [Q.HasOfPostcompProperty Q] (hPf : P f) (hQf : Q f)
    (A : P.Over Q X) (B : P.Over Q Y) : ((map Q hPf).obj A ⟶ B) ≃ (A ⟶ (pullback P Q f).obj B) :=
  { toFun g := Over.homMk (pullback.lift g.left A.hom <| by simp) (by simp) <| by
        apply Q.of_postcomp (W' := Q)
        · exact Q.pullback_fst B.hom f hQf
        · simpa using g.prop_hom_left
    invFun h := Over.homMk (h.left ≫ pullback.fst B.hom f) (by
        simp only [map_obj_left, Functor.const_obj_obj, pullback_obj_left, Functor.id_obj,
          Category.assoc, pullback.condition, map_obj_hom, ← pullback_obj_hom, Over.w_assoc])
      (Q.comp_mem _ _ h.prop_hom_left (Q.pullback_fst _ _ hQf))
    left_inv := by cat_disch
    right_inv h := by
      ext
      dsimp
      ext
      · simp
      · simpa using h.w.symm }

/-- `P.Over.map` is left adjoint to `P.Over.pullback` if `f` satisfies `P` and `Q`. -/
noncomputable def Over.mapPullbackAdj (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] [Q.HasOfPostcompProperty Q] (hPf : P f) (hQf : Q f) :
    Over.map Q hPf ⊣ Over.pullback P Q f :=
  Adjunction.mkOfHomEquiv
    { homEquiv A B := Over.mapPullbackAdjHomEquiv f hPf hQf A B }

variable (f : X ⟶ Y) [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [Q.HasOfPostcompProperty Q] (hPf : P f) (hQf : Q f)
    (A : P.Over Q X) (B : P.Over Q Y)

@[simp]
lemma Over.mapPullbackAdj_homEquiv_apply_left (g : (map Q hPf).obj A ⟶ B) :
    ((Over.mapPullbackAdj f hPf hQf).homEquiv A B g).left =
    pullback.lift g.left A.hom (by cat_disch) := by
  simp [mapPullbackAdj]

@[simp]
lemma Over.mapPullbackAdj_homEquiv_symm_apply_left (g) :
    (((Over.mapPullbackAdj f hPf hQf).homEquiv A B).symm g).left =
    g.left ≫ pullback.fst B.hom f := by
  simp [mapPullbackAdj]

@[simp]
lemma Over.mapPullbackAdj_unit_app_left (A) : ((Over.mapPullbackAdj f hPf hQf).unit.app A).left =
    pullback.lift (𝟙 A.left) A.hom (by cat_disch) :=
  rfl

@[simp]
lemma Over.mapPullbackAdj_counit_app_left (A) : ((Over.mapPullbackAdj f hPf hQf).counit.app A).left =
    pullback.fst A.hom f := by
  simp [mapPullbackAdj]

end Adjunction

/-- Pushforward along a morphism `f` (for which all pullbacks exist) exists relative to `P`
when pushforwards exist along `f` for all morphisms satisfying `P`. -/
protected class HasPushforwardsAlong {S S' : T} (f : S ⟶ S') [hpb : HasPullbacksAlong f] where
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
    have : HasPullbacksAlong q := hasPullbacksAlong_of_hasPullbacks hq
    P.HasPushforwardsAlong q

/-- Morphisms satisfying `P` are stable under pushforward along morphism `f`
if whenever pushforward along `f` exists it is in `P`. -/
class IsStableUnderPushforwardsAlong {S S' : T} (q : S ⟶ S') [HasPullbacksAlong q] : Prop where
  of_isPushforward {X Y : T} (f : X ⟶ S) (hf : P f) {g : Y ⟶ S'}
  (isPushforward : IsPushforward q (.mk f) (.mk g)) : P g

lemma IsStableUnderPushforwardsAlong.of_respectsIso [P.RespectsIso] {S S' : T} (q : S ⟶ S')
    [HasPullbacksAlong q] (g : {X : T} → (f : X ⟶ S) → P f → Over S')
    (pg : {X : T} → (f : X ⟶ S) → (pf : P f) → P (g f pf).hom)
    (isPushforward : {X : T} → (f : X ⟶ S) → (pf : P f) → IsPushforward q (.mk f) (g f pf)) :
    P.IsStableUnderPushforwardsAlong q where
  of_isPushforward f pf g' isPushforward' :=
    have : g' = ((isPushforward f pf).uniqueUpToIso isPushforward').inv.left ≫ (g f pf).hom :=
      by cat_disch
    this ▸ RespectsIso.precomp _ _ _ (pg ..)

-- lemma IsStableUnderPushforwardsAlong.of_isLeftAdjoint [P.RespectsIso] {S S' : T} (q : S ⟶ S')
--     [HasPullbacksAlong q] [P.IsStableUnderBaseChangeAlong q]
--     [isLeftAdjoint : (Over.pullback P ⊤ q).IsLeftAdjoint] :
--     P.IsStableUnderPushforwardsAlong q where
--   of_isPushforward {X Y} f pf g isPushforward :=
--     -- have : ((Over.pullback P ⊤ q).op ⋙ yoneda.obj (Over.mk ⊤ f pf)).RepresentableBy (Over.mk ⊤ g ) := sorry
--     -- have h := isPushforward.uniqueUpToIso
--     let i : CategoryTheory.Over.mk g ≅
--       ((Over.pullback P ⊤ q).rightAdjoint.obj (Over.mk ⊤ f pf)).toComma :=
--       sorry
--     have : g = i.hom.left ≫ ((Over.pullback P ⊤ q).rightAdjoint.obj (Over.mk ⊤ f pf)).hom :=
--       sorry
--     this ▸ RespectsIso.precomp _ _ _ (Comma.prop ..)

/-- Morphisms satisfying `P` are stable under pushforward along morphisms satisfying `Q`
if whenever pushforward along a morphism in `Q` exists it is in `P`. -/
class IsStableUnderPushforwards [Q.HasPullbacks] : Prop where
  of_isPushforward {S S' : T} (q : S ⟶ S') (hq : Q q) :
  have : HasPullbacksAlong q := hasPullbacksAlong_of_hasPullbacks hq
  IsStableUnderPushforwardsAlong P q

noncomputable section

abbrev pushforwardPartial.lift {S S' : T} (q : S ⟶ S')
    [HasPullbacksAlong q] [P.HasPushforwardsAlong q] :
    P.Over ⊤ S ⥤ (CategoryTheory.Over.pullback q).PartialRightAdjointSource :=
  ObjectProperty.lift _ (Over.forget P ⊤ S)
    (fun X => HasPushforwardsAlong.hasPushforward X.hom X.prop)

/-- If `P` has pushforwards along `q` then there is a partial left adjoint `P.Over ⊤ S ⥤ Over S'`
of the pullback functor `pullback q : Over S' ⥤ Over S`.
-/
noncomputable def pushforwardPartial {S S' : T} (q : S ⟶ S') [HasPullbacksAlong q]
    [P.HasPushforwardsAlong q] : P.Over ⊤ S ⥤ Over S' :=
  pushforwardPartial.lift P q ⋙ (CategoryTheory.Over.pullback q).partialRightAdjoint

/-- When `P` has pushforwards along `Q` and is stable under pushforwards along `Q`,
the pushforward functor along any morphism `q` satisfying `Q` can be defined. -/
noncomputable def pushforward {S S' : T} (q : S ⟶ S') [HasPullbacksAlong q]
    [P.HasPushforwardsAlong q] [P.IsStableUnderPushforwardsAlong q] :
    P.Over ⊤ S ⥤ P.Over ⊤ S' :=
  Comma.lift (pushforwardPartial P q) (fun X =>
    IsStableUnderPushforwardsAlong.of_isPushforward (q := q) X.hom X.prop
      ((have : HasPushforward q X.toComma := HasPushforwardsAlong.hasPushforward _ X.prop
        pushforward.isPushforward q (X.toComma))))
  (by simp) (by simp)

def pushforwardCompForget {S S' : T} (q : S ⟶ S') [HasPullbacksAlong q]
    [P.HasPushforwardsAlong q] [P.IsStableUnderPushforwardsAlong q] :
    pushforward P q ⋙ Over.forget _ _ _ ≅ pushforwardPartial P q :=
  Iso.refl _

section homEquiv

variable {P} {S S' : T} {q : S ⟶ S'} [HasPullbacksAlong q]
  [P.HasPushforwardsAlong q] [P.IsStableUnderPushforwardsAlong q]

/-- The pushforward functor is a partial right adjoint to pullback in the sense that
there is a natural bijection of hom-sets `T / S (pullback q X, Y) ≃ T / S' (X, pushforward q Y)`. -/
def pushforward.homEquiv {X : Over S'} {Y : P.Over ⊤ S} :
    (X ⟶ ((pushforward P q).obj Y).toComma) ≃
    ((CategoryTheory.Over.pullback q).obj X ⟶ Y.toComma) :=
  Functor.partialRightAdjointHomEquiv ..

@[reassoc]
lemma pushforward.homEquiv_comp {X X' : Over S'} {Y : P.Over ⊤ S}
    (f : X' ⟶ ((pushforward P q).obj Y).toComma) (g : X ⟶ X') :
    pushforward.homEquiv (g ≫ f) =
    (CategoryTheory.Over.pullback q).map g ≫ homEquiv f :=
  Functor.partialRightAdjointHomEquiv_comp ..

@[reassoc]
lemma pushforward.homEquiv_map_comp {X : Over S'} {Y Y' : P.Over ⊤ S}
    (f : X ⟶ ((pushforward P q).obj Y).toComma) (g : Y ⟶ Y') :
    homEquiv (f ≫ Comma.Hom.hom ((P.pushforward q).map g)) =
    homEquiv f ≫ Comma.Hom.hom g :=
  Functor.partialRightAdjointHomEquiv_map_comp ..

@[reassoc]
lemma pushforward.homEquiv_symm_comp {X : Over S'} {Y Y' : P.Over ⊤ S}
    (f : (CategoryTheory.Over.pullback q).obj X ⟶ Y.toComma) (g : Y ⟶ Y') :
    homEquiv.symm f ≫ Comma.Hom.hom ((P.pushforward q).map g) =
    homEquiv.symm (f ≫ Comma.Hom.hom g) :=
  Functor.partialRightAdjointHomEquiv_symm_comp ..

@[reassoc]
lemma pushforward.homEquiv_comp_symm {X X' : Over S'} {Y : P.Over ⊤ S}
    (f : (CategoryTheory.Over.pullback q).obj X' ⟶ Y.toComma) (g : X ⟶ X') :
    g ≫ homEquiv.symm f =
    homEquiv.symm ((CategoryTheory.Over.pullback q).map g ≫ f) :=
  Functor.partialRightAdjointHomEquiv_comp_symm ..

end homEquiv

section

open MorphismProperty.Over

variable {P} [P.IsStableUnderBaseChange] {S S' : T} {f : S ⟶ S'}
    [HasPullbacksAlong f] [P.HasPushforwardsAlong f] [P.IsStableUnderPushforwardsAlong f]

instance : P.HasPullbacksAlong f where
  hasPullback := inferInstance

def pullbackPushforwardAdjunctionHomEquiv (X : P.Over ⊤ S') (Y : P.Over ⊤ S) :
    ((Over.pullback P ⊤ f).obj X ⟶ Y) ≃ (X ⟶ (P.pushforward f).obj Y) :=
  calc ((pullback P ⊤ f).obj X ⟶ Y)
      _ ≃ (((pullback P ⊤ f).obj X).toComma ⟶ Y.toComma) :=
        (Functor.FullyFaithful.ofFullyFaithful (Over.forget P ⊤ S)).homEquiv
      _ ≃ (X.toComma ⟶ ((P.pushforward f).obj Y).toComma) :=
        pushforward.homEquiv.symm
      _ ≃ _ := Iso.homCongr (Iso.refl X.toComma) (by exact Iso.refl _)
      _ ≃ (X ⟶ (P.pushforward f).obj Y) :=
        (Functor.FullyFaithful.ofFullyFaithful (Over.forget P ⊤ S')).homEquiv.symm

@[simp]
lemma pullbackPushforwardAdjunctionHomEquiv_apply {X : P.Over ⊤ S'} {Y : P.Over ⊤ S}
    (g : (Over.pullback P ⊤ f).obj X ⟶ Y) :
    (pullbackPushforwardAdjunctionHomEquiv X Y g).toCommaMorphism =
    pushforward.homEquiv.symm (Comma.Hom.hom g) := by
  simp only [pullbackPushforwardAdjunctionHomEquiv, Trans.trans, Comma.forget_obj,
    Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Iso.refl_hom, Category.comp_id,
    Category.id_comp]
  erw [Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.homEquiv_symm_apply]
  simp [Over.forget_preimage]
  rfl

@[simp]
lemma pullbackPushforwardAdjunctionHomEquiv_symm_apply {X : P.Over ⊤ S'} {Y : P.Over ⊤ S}
    (g : X ⟶ (P.pushforward f).obj Y) :
    ((pullbackPushforwardAdjunctionHomEquiv X Y).symm g).toCommaMorphism =
    pushforward.homEquiv (Comma.Hom.hom g) := by
  simp only [pullbackPushforwardAdjunctionHomEquiv, Trans.trans, Comma.forget_obj,
    Equiv.symm_trans_apply, Equiv.symm_symm, Iso.homCongr_symm, Iso.refl_symm, Iso.homCongr_apply,
    Iso.refl_inv, Iso.refl_hom, Category.comp_id, Category.id_comp]
  erw [Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.homEquiv_symm_apply]
  simp [Over.forget_preimage]
  rfl

variable (P) (f) in
/-- The `pullback ⊣ pushforward` adjunction. -/
def pullbackPushforwardAdjunction : Over.pullback P ⊤ f ⊣ pushforward P f :=
  Adjunction.mkOfHomEquiv {
    homEquiv X Y := pullbackPushforwardAdjunctionHomEquiv X Y
    homEquiv_naturality_left_symm g₁ g₂ := by
      ext
      simp only [pullback_obj_left, pullbackPushforwardAdjunctionHomEquiv_symm_apply,
        Comma.comp_hom, CategoryTheory.Comma.comp_left, pullback_map_left]
      rw [pushforward.homEquiv_comp]
      simp
    homEquiv_naturality_right g₁ g₂ := by
      ext
      simp only [pullbackPushforwardAdjunctionHomEquiv_apply, Comma.comp_hom,
        CategoryTheory.Comma.comp_left]
      convert_to _ = ((pushforward.homEquiv.symm (Comma.Hom.hom g₁)) ≫
        (Comma.Hom.hom ((P.pushforward f).map g₂))).left
      rw [pushforward.homEquiv_symm_comp] }

@[simp]
lemma pullbackPushforwardAdjunction_apply {X : P.Over ⊤ S'} {Y : P.Over ⊤ S}
    (g : (Over.pullback P ⊤ f).obj X ⟶ Y) :
    ((pullbackPushforwardAdjunction P f).homEquiv X Y g).toCommaMorphism =
    pushforward.homEquiv.symm (Comma.Hom.hom g) := by
  simp [pullbackPushforwardAdjunction, pullbackPushforwardAdjunctionHomEquiv_apply]

@[simp]
lemma pullbackPushforwardAdjunction_symm_apply {X : P.Over ⊤ S'} {Y : P.Over ⊤ S}
    (g : X ⟶ (P.pushforward f).obj Y) :
    (((pullbackPushforwardAdjunction P f).homEquiv X Y).symm g).toCommaMorphism =
    pushforward.homEquiv (Comma.Hom.hom g) := by
  simp [pullbackPushforwardAdjunction, pullbackPushforwardAdjunctionHomEquiv_symm_apply]

@[simp]
lemma pullbackPushforwardAdjunction_unit_app_toCommaMorphism {X : P.Over ⊤ S'} :
    ((pullbackPushforwardAdjunction P f).unit.app X).toCommaMorphism =
    pushforward.homEquiv.symm (𝟙 ((Over.pullback P ⊤ f).obj X).toComma) := by
  simp [pullbackPushforwardAdjunction, pullbackPushforwardAdjunctionHomEquiv_apply]

@[simp]
lemma pullbackPushforwardAdjunction_counit_app_toCommaMorphism {Y : P.Over ⊤ S} :
    ((pullbackPushforwardAdjunction P f).counit.app Y).toCommaMorphism =
    pushforward.homEquiv (𝟙 ((P.pushforward f).obj Y).toComma) := by
  simp [pullbackPushforwardAdjunction, pullbackPushforwardAdjunctionHomEquiv_symm_apply]

instance : (pullback P ⊤ f).IsLeftAdjoint :=
  Adjunction.isLeftAdjoint (pullbackPushforwardAdjunction P f)

instance : (pushforward P f).IsRightAdjoint :=
  Adjunction.isRightAdjoint (pullbackPushforwardAdjunction P f)

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
