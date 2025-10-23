import HoTTLean.Groupoids.UnstructuredModel
import HoTTLean.Model.Unstructured.Hurewicz

import HoTTLean.ForMathlib.CategoryTheory.RepPullbackCone

universe w v u v₁ u₁ v₂ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory

lemma Discrete.functor_ext' {X C : Type*} [Category C] {F G : X → C} (h : ∀ x : X, F x = G x) :
    Discrete.functor F = Discrete.functor G := by
  have : F = G := by aesop
  subst this
  rfl

lemma Discrete.functor_eq {X C : Type*} [Category C] {F : Discrete X ⥤ C} :
    F = Discrete.functor fun x ↦ F.obj ⟨x⟩ := by
  fapply CategoryTheory.Functor.ext
  · aesop
  · intro x y f
    cases x ; rcases f with ⟨⟨h⟩⟩
    cases h
    simp

lemma Discrete.functor_ext {X C : Type*} [Category C] (F G : Discrete X ⥤ C)
    (h : ∀ x : X, F.obj ⟨x⟩ = G.obj ⟨x⟩) :
    F = G :=
  calc F
    _ = Discrete.functor (fun x => F.obj ⟨x⟩) := Discrete.functor_eq
    _ = Discrete.functor (fun x => G.obj ⟨x⟩) := Discrete.functor_ext' h
    _ = G := Discrete.functor_eq.symm

-- lemma Discrete.ext {X : Type*} {x y : Discrete X} (h : x.as = y.as) : x = y := by
--   cases x; cases h
--   rfl

end CategoryTheory

namespace FunctorOperation

variable {Γ : Type u} [Groupoid.{v} Γ] {Δ : Type u₂} [Groupoid.{v₂} Δ] (σ : Δ ⥤ Γ)
  {A : Γ ⥤ Grpd.{v₁,u₁}} {a0 a1 : Γ ⥤ PGrpd.{v₁,u₁}}
  (a0_tp : a0 ⋙ PGrpd.forgetToGrpd = A) (a1_tp : a1 ⋙ PGrpd.forgetToGrpd = A)

/-- The identity type former takes a (family of) groupoid(s) `A` with two points `a0 a1`
to the (family of) set(s) of isomorphisms
between its two given points `A(a0,a1)`. -/
def idObj (x : Γ) : Grpd :=
  Grpd.of <| Discrete <| PGrpd.objFiber' a0_tp x ⟶ PGrpd.objFiber' a1_tp x

def idMap {x y : Γ} (f : x ⟶ y) : idObj a0_tp a1_tp x ⥤ idObj a0_tp a1_tp y :=
  Discrete.functor <| fun g =>
  ⟨inv (PGrpd.mapFiber' a0_tp f) ≫ (A.map f).map g ≫ PGrpd.mapFiber' a1_tp f⟩

def Id : Γ ⥤ Grpd where
  obj := idObj a0_tp a1_tp
  map := idMap a0_tp a1_tp
  map_id := by
    intro x
    apply Discrete.functor_ext
    intro g
    apply Discrete.ext
    simp [idMap]
  map_comp := by
    intro x y z f1 f2
    subst a0_tp
    apply Discrete.functor_ext
    intro g
    apply Discrete.ext
    simp only [Functor.comp_obj, Functor.Grothendieck.forget_obj, PGrpd.objFiber'_rfl, idMap,
      Functor.comp_map, Functor.Grothendieck.forget_map, PGrpd.mapFiber'_rfl,
      Discrete.functor_obj_eq_as, Grpd.comp_eq_comp, Functor.map_comp, Functor.map_inv,
      Category.assoc, IsIso.eq_inv_comp]
    simp only [PGrpd.mapFiber, PGrpd.map_comp_fiber, Functor.Grothendieck.forget_obj,
      Functor.Grothendieck.forget_map, ← Category.assoc, IsIso.inv_comp, inv_eqToHom,
      PGrpd.mapFiber', Functor.comp_obj, Functor.comp_map, PGrpd.objFiber'EqToHom,
      PGrpd.mapFiber'EqToHom, Functor.map_comp, eqToHom_map, eqToHom_trans, IsIso.hom_inv_id,
      Category.id_comp, Functor.Grothendieck.Hom.comp_base, Grpd.comp_eq_comp, eqToHom_naturality,
      Category.comp_id, ← heq_eq_eq]
    congr 1
    rw! [Functor.map_comp]
    simp only [Functor.Grothendieck.Hom.comp_base, Grpd.comp_eq_comp, Functor.comp_obj,
      eqToHom_refl, Functor.comp_map, Category.id_comp, Category.assoc, ← heq_eq_eq]
    congr 1
    have h := Functor.congr_hom a1_tp f2
    simp only [Functor.comp_obj, Functor.Grothendieck.forget_obj, Functor.comp_map,
      Functor.Grothendieck.forget_map, Grpd.comp_eq_comp] at h
    rw! [h]
    simp only [← Grpd.comp_eq_comp, Grpd.comp_obj, ← Functor.comp_map, ← heq_eq_eq,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff, eqToHom_comp_heq_iff]
    simp [Grpd.eqToHom_hom]

lemma Id_comp : Id (A := σ ⋙ A) (a0 := σ ⋙ a0) (a1 := σ ⋙ a1)
    (by simp[Functor.assoc, a0_tp]) (by simp[Functor.assoc, a1_tp]) =
    σ ⋙ Id a0_tp a1_tp :=
  rfl

open CategoryTheory.Prod in
def unPath (p : Γ × Codiscrete Bool ⥤ PGrpd) (p_tp : p ⋙ PGrpd.forgetToGrpd = fst _ _ ⋙ A) :
    Γ ⥤ PGrpd :=
  let p' : Γ ⥤ Codiscrete Bool ⥤ PGrpd := Functor.curry.obj p
  Functor.curry.obj p ⋙ sorry

open CategoryTheory.Prod in
def unPath' (p : Γ × Grpd.Interval ⥤ PGrpd) (p_tp : p ⋙ PGrpd.forgetToGrpd = fst _ _ ⋙ A) :
    Γ ⥤ PGrpd :=
  sorry


-- p' : ↑Interval × ↑Γ ⥤ PGrpd
-- ⊢ ↑Γ ⥤ PGrpd

end FunctorOperation

namespace GroupoidModel

open Grpd Model.UnstructuredUniverse

def cylinder : Cylinder Grpd := .ofCartesianMonoidalCategoryRight Interval δ0 δ1

namespace UId

variable {Γ Δ : Grpd} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.{v}.Ty} (a0 a1 : Γ ⟶ U.Tm)
    (a0_tp : a0 ≫ U.tp = A) (a1_tp : a1 ≫ U.tp = A)

def Id : Γ ⟶ U.{v}.Ty :=
  toCoreAsSmallEquiv.symm (FunctorOperation.Id (A := toCoreAsSmallEquiv A)
    (a0 := toCoreAsSmallEquiv a0) (a1 := toCoreAsSmallEquiv a1)
    (by rw [← a0_tp, Grpd.comp_eq_comp, U.tp, toCoreAsSmallEquiv_apply_comp_right])
    (by rw [← a1_tp, Grpd.comp_eq_comp, U.tp, toCoreAsSmallEquiv_apply_comp_right]))

lemma Id_comp :
    UId.Id (A := σ ≫ A) (σ ≫ a0) (σ ≫ a1) (by simp only [Category.assoc, a0_tp, U_Ty])
      (by simp only [Category.assoc, a1_tp, U_Ty]) = σ ≫ UId.Id a0 a1 a0_tp a1_tp := by
  dsimp only [U_Ty, comp_eq_comp, Id]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, ← FunctorOperation.Id_comp]

def unPath (p : cylinder.I.obj Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = cylinder.π.app Γ ≫ A) :
    Γ ⟶ U.{v}.Tm := by
  -- have p' := toCoreAsSmallEquiv p
  -- dsimp [cylinder, Cylinder.ofCartesianMonoidalCategoryRight, MonoidalCategoryStruct.tensorObj,
  --   CartesianMonoidalCategory.ofChosenFiniteProducts.tensorObj, prodCone] at p'
  refine toCoreAsSmallEquiv.symm ?_
  -- convert_to p ≫ U.tp = CartesianMonoidalCategory.fst _ _ ≫ A at p_tp
  -- dsimp [CartesianMonoidalCategory.snd, prodCone] at p_tp
  refine FunctorOperation.unPath' (A := toCoreAsSmallEquiv A) (toCoreAsSmallEquiv p) ?_
  rw [← toCoreAsSmallEquiv_apply_comp_left]
  rw [← toCoreAsSmallEquiv_apply_comp_right,
    EmbeddingLike.apply_eq_iff_eq]
  exact p_tp

end UId

open UId

def UPath : GroupoidModel.U.{v}.Path cylinder where
  Id := UId.Id
  Id_comp := Id_comp
  unPath := unPath
  unPath_comp := sorry
  unPath_tp := sorry
  path := sorry
  path_tp := sorry
  δ0_path := sorry
  δ1_path := sorry
  path_unPath := sorry
  unPath_path := sorry


end GroupoidModel

#exit
/-
This is the equivelant of Id above
-/

-- TODO tidy up this definition. remove tactic mode + use yonedaCategoryEquiv
def Id' : y(GroupoidModel.U.ext (GroupoidModel.π.{u,u})) ⟶ smallU.Ty.{u,u} :=
  yonedaCategoryEquiv.symm (sorry)
  -- dsimp[GroupoidModel.U.ext,GroupoidModel.U,GroupoidModel.Ctx.ofCategory]
  -- refine AsSmall.up.map ?_
  -- dsimp [Quiver.Hom]
  -- refine Core.functorToCore ?_
  -- refine ?_ ⋙ AsSmall.up
  -- refine ?_ ⋙ Id
  -- dsimp [BPGrpd]
  -- let F : (GroupoidModel.Ctx.toGrpd.obj GroupoidModel.E) ⥤ PGrpd := by sorry
  --   -- dsimp[GroupoidModel.E,GroupoidModel.Ctx.ofCategory]
  --   -- refine ?_ ⋙ Core.inclusion PGrpd
  --   -- refine Core.map' ?_
  --   -- exact AsSmall.down
  -- let h : F ⋙ PGrpd.forgetToGrpd = (GroupoidModel.U.classifier GroupoidModel.π) := by sorry
  --   -- exact rfl
  -- rw[<-h]
  -- exact Grothendieck.Groupoidal.pre PGrpd.forgetToGrpd F

def Refl' : GroupoidModel.E.{u,u} ⟶ GroupoidModel.E.{u,u} :=
  AsSmall.up.map (𝟭 (Core (AsSmall PGrpd)))

/- Lean is gas lighting me -/
def Diag' : GroupoidModel.E.{v,u} ⟶ GroupoidModel.U.ext (GroupoidModel.π.{v,u}) := by
  refine IsPullback.lift (GroupoidModel.IsPullback.SmallU.isPullback_disp_π.{v,u} (GroupoidModel.π.{v,u})) ?_ ?_ ?_
  . refine eqToHom sorry
  . refine eqToHom sorry
  . simp



namespace smallUId

def id : Limits.pullback smallU.{v}.tp smallU.{v}.tp ⟶ smallU.{v}.Ty := sorry

def refl: smallU.{v}.Tm ⟶ smallU.{v}.Tm := sorry

def comm: Limits.pullback.lift (𝟙 smallU.Tm) (𝟙 smallU.Tm) rfl ≫ id = refl ≫ smallU.tp := sorry

-- TODO: make sure universe levels are most general
-- TODO: make namespaces consistent with Sigma file
def smallUIdBase : Universe.IdIntro smallU.{u,u} where
  k := y(GroupoidModel.U.ext GroupoidModel.π.{u,u})
  k1 := sorry -- smallU.{u,u}.var GroupoidModel.π.{u,u}
  k2 := sorry -- ym(smallU.{u,u}.disp GroupoidModel.π.{u,u})
  isKernelPair := sorry
  Id := Id'
  refl := sorry
  refl_tp := sorry

end smallUId

end GroupoidModel
