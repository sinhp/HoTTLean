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
def IdObj (x : Γ) : Grpd :=
  Grpd.of <| Discrete <| PGrpd.objFiber' a0_tp x ⟶ PGrpd.objFiber' a1_tp x

def IdMap {x y : Γ} (f : x ⟶ y) : IdObj a0_tp a1_tp x ⥤ IdObj a0_tp a1_tp y :=
  Discrete.functor <| fun g =>
  ⟨inv (PGrpd.mapFiber' a0_tp f) ≫ (A.map f).map g ≫ PGrpd.mapFiber' a1_tp f⟩

lemma IdMap_id (X : Γ) : IdMap a0_tp a1_tp (𝟙 X) = 𝟙 (IdObj a0_tp a1_tp X) := by
  apply Discrete.functor_ext
  intro g
  apply Discrete.ext
  simp [IdMap]

lemma IdMap_comp {X Y Z : Γ} (f1 : X ⟶ Y) (f2 : Y ⟶ Z) : IdMap a0_tp a1_tp (f1 ≫ f2) =
    IdMap a0_tp a1_tp f1 ⋙ IdMap a0_tp a1_tp f2 := by
  subst a0_tp
  apply Discrete.functor_ext
  intro g
  apply Discrete.ext
  simp only [Functor.comp_obj, Functor.Grothendieck.forget_obj, PGrpd.objFiber'_rfl, IdMap,
    Functor.comp_map, Functor.Grothendieck.forget_map, PGrpd.mapFiber'_rfl,
    Discrete.functor_obj_eq_as, Functor.map_comp, Functor.map_inv,
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

def Id : Γ ⥤ Grpd where
  obj := IdObj a0_tp a1_tp
  map := IdMap a0_tp a1_tp
  map_id := IdMap_id a0_tp a1_tp
  map_comp := IdMap_comp a0_tp a1_tp

lemma Id_comp : Id (A := σ ⋙ A) (a0 := σ ⋙ a0) (a1 := σ ⋙ a1)
    (by simp[Functor.assoc, a0_tp]) (by simp[Functor.assoc, a1_tp]) =
    σ ⋙ Id a0_tp a1_tp :=
  rfl

section

open CategoryTheory.Prod

lemma _root_.CategoryTheory.Prod.sectR_snd {C : Type u₁} [Category.{v₁} C] (Z : C)
    (D : Type u₂) [Category.{v₂} D] : sectR Z D ⋙ snd C D = 𝟭 D :=
  rfl

theorem _root_.CategoryTheory.Functor.Grothendieck.congr
    {C : Type u} [Category.{v, u} C] {F : C ⥤ Cat}
    {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

theorem _root_.CategoryTheory.PGrpd.congr
    {X Y : PGrpd} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

-- open PGrpd in
-- theorem _root_.CategoryTheory.PGrpd.mapFiber'_comp' {A : Γ ⥤ Grpd.{v₁,u₁}} {α : Γ ⥤ PGrpd.{v₁,u₁}}
--     (h : α ⋙ PGrpd.forgetToGrpd = A) {x y z} (f : x ⟶ y) (g : y ⟶ z) : mapFiber' h (f ≫ g)
--     = eqToHom (by rw [mapFiber'_comp_aux1 h f g]; simp [Grpd.forgetToCat]) ≫
--     (eqToHom (mapFiber'_comp_aux0 h)).map ((α.map g).base.map (α.map f).fiber)
--     ≫ (eqToHom (mapFiber'_comp_aux0 h)).map (α.map g).fiber := by
--   simp [mapFiber', eqToHom_map, mapFiber'EqToHom]

variable (p : Grpd.Interval × Γ ⥤ PGrpd)

abbrev ff (x : Γ) : Grpd.Interval × Γ := ⟨⟨⟨.false⟩⟩, x⟩
abbrev ffm {x y : Γ} (f : x ⟶ y) : ff x ⟶ ff y := ⟨⟨⟨⟩⟩, f⟩
abbrev tt (x : Γ) : Grpd.Interval × Γ := ⟨⟨⟨.true⟩⟩, x⟩
abbrev ttm {x y : Γ} (f : x ⟶ y) : tt x ⟶ tt y := ⟨⟨⟨⟩⟩, f⟩
abbrev ft (x : Γ) : ff x ⟶ tt x := ⟨⟨⟨⟩⟩, 𝟙 x⟩

abbrev unPath0 : Γ ⥤ PGrpd := sectR ⟨⟨.false⟩⟩ _ ⋙ p

abbrev unPath1 : Γ ⥤ PGrpd := sectR ⟨⟨.true⟩⟩ _ ⋙ p

variable {p} (p_tp : p ⋙ PGrpd.forgetToGrpd = snd _ _ ⋙ A)

include p_tp in
@[simp]
lemma unPath0_comp_forgetToGrpd : unPath0 p ⋙ PGrpd.forgetToGrpd = A := by
  rw [Functor.assoc, p_tp, ← Functor.assoc, sectR_snd, Functor.id_comp]

include p_tp in
@[simp]
lemma unPath1_comp_forgetToGrpd : unPath1 p ⋙ PGrpd.forgetToGrpd = A := by
  rw [Functor.assoc, p_tp, ← Functor.assoc, sectR_snd, Functor.id_comp]

lemma objFiber'_unPath0 (x) : PGrpd.objFiber' (unPath0_comp_forgetToGrpd p_tp) x =
    PGrpd.objFiber' p_tp (ff x) := by
  dsimp [PGrpd.objFiber', PGrpd.objFiber]

@[simp]
abbrev unPathId : Γ ⥤ Grpd :=
  Id (A := A) (a0 := unPath0 p) (a1 := unPath1 p)
  (unPath0_comp_forgetToGrpd p_tp) (unPath1_comp_forgetToGrpd p_tp)

@[simps!]
def unPathFibObj (x : Γ) : @IdObj _ _ A (unPath0 p) (unPath1 p) (unPath0_comp_forgetToGrpd p_tp)
    (unPath1_comp_forgetToGrpd p_tp) x :=
  ⟨eqToHom (by simp [objFiber'_unPath0 p_tp]) ≫ PGrpd.mapFiber' p_tp (ft x)⟩

lemma unPathFibObj_comp (x : Δ) : unPathFibObj (A := σ ⋙ A) (p := Functor.prod (𝟭 _) σ ⋙ p)
    (by simp [Functor.assoc, p_tp]; rfl) x = unPathFibObj p_tp (σ.obj x) := by
  apply Discrete.ext
  simp only [Functor.comp_obj, unPathFibObj_as, Functor.comp_map, PGrpd.mapFiber', snd_obj, snd_map,
    Functor.prod_obj, Functor.id_obj, Functor.Grothendieck.forget_obj, PGrpd.objFiber'EqToHom,
    Functor.prod_map, Functor.id_map, PGrpd.mapFiber'EqToHom, Grpd.eqToHom_hom, eqToHom_trans_assoc]
  rw! [CategoryTheory.Functor.map_id]

def unPathFibMap {x y : Γ} (f : x ⟶ y) :
    (IdMap (unPath0_comp_forgetToGrpd p_tp) (unPath1_comp_forgetToGrpd p_tp) f).obj
    (unPathFibObj p_tp x) ⟶ unPathFibObj p_tp y := by
  refine ⟨⟨?_⟩⟩
  dsimp [IdMap]
  have comm : ft x ≫ ttm f = ffm f ≫ ft y := by ext; rfl; simp
  have h0 := Functor.congr_map p comm
  have h1 := (PGrpd.mapFiber'_comp p_tp (ft x) (ttm f)).symm
  have h2 := PGrpd.mapFiber'_comp p_tp (ffm f) (ft y)
  -- have h3 : (p.map (ttm f)).base = eqToHom (Functor.congr_obj p_tp _) ≫
  --   A.map f ≫ eqToHom (Functor.congr_obj p_tp _).symm := Functor.congr_hom p_tp (ffm f)
  rw! [comm, h2] at h1
  simp only [IsIso.inv_comp_eq]
  simp only [Functor.comp_obj, Functor.comp_map,
    Functor.Grothendieck.forget_obj, ← heq_eq_eq] at h1
  simp only [PGrpd.mapFiber', PGrpd.mapFiber'EqToHom, Category.assoc, PGrpd.objFiber'EqToHom]
  simp only [heq_eqToHom_comp_iff, eqToHom_comp_heq_iff] at h1

  -- simp only [Functor.map_comp] at h0
  -- have h2 := Functor.congr_hom p_tp (ttm f)
  -- simp at h2
  -- simp [PGrpd.mapFiber', eqToHom_map, PGrpd.mapFiber'EqToHom]
  -- -- simp [← Functor.comp_map]
  -- have h1 := PGrpd.congr h0
  -- simp [Grpd.forgetToCat] at h1
  -- rw! (castMode := .all) [h2] at h1
  -- simp at h1
  -- -- simp [PGrpd.mapFiber', PGrpd.mapFiber'EqToHom, eqToHom_map]

  -- -- simp [Grpd.eqToHom_hom]
  -- -- simp [← heq_eq_eq]
  sorry

lemma unPathFibMap_id (x : Γ) : unPathFibMap p_tp (𝟙 x) = eqToHom (by simp [IdMap_id]) := by
  aesop_cat

lemma unPathFibMap_comp {x y z : Γ} (f1 : x ⟶ y) (f2 : y ⟶ z) :
    unPathFibMap p_tp (f1 ≫ f2) =
    eqToHom (by simp only [IdMap_comp]; rfl) ≫
    ((unPathId p_tp).map f2).map (unPathFibMap p_tp f1) ≫ unPathFibMap p_tp f2 := by
  aesop_cat

def unPath : Γ ⥤ PGrpd :=
  PGrpd.functorTo (unPathId p_tp) (unPathFibObj p_tp) (unPathFibMap p_tp)
    (unPathFibMap_id p_tp) (fun f1 f2 => by dsimp only; aesop_cat)

lemma unPath_comp : unPath (A := σ ⋙ A) (p := Functor.prod (𝟭 _) σ ⋙ p)
    (by simp [Functor.assoc, p_tp]; rfl) = σ ⋙ unPath p_tp := by
  -- rw [PGrpd.functorTo]
  apply PGrpd.Functor.hext
  · rfl
  · intro x
    simp only [unPath, Functor.comp_obj, heq_eq_eq]
    -- rw [PGrpd.functorTo_obj_fiber] --FIXME why timeout?
    convert_to unPathFibObj (A := σ ⋙ A) (p := Functor.prod (𝟭 _) σ ⋙ p)
      (by simp [Functor.assoc, p_tp]; rfl) x =
      unPathFibObj (A := A) (p := p) p_tp (σ.obj x)
    rw [unPathFibObj_comp]
  · intro x y f
    simp only [unPath, Functor.comp_map]
    -- rw [PGrpd.functorTo_map_fiber]
    convert_to unPathFibMap (A := σ ⋙ A) (p := Functor.prod (𝟭 _) σ ⋙ p)
      (by simp [Functor.assoc, p_tp]; rfl) f ≍
      unPathFibMap (A := A) (p := p) p_tp (σ.map f)
    rw! (castMode := .all) [unPathFibObj_comp _ p_tp]
    rw! (castMode := .all) [unPathFibObj_comp _ p_tp]
    rfl

lemma unPath_comp_forgetToGrpd : unPath p_tp ⋙ PGrpd.forgetToGrpd =
    Id (a0 := unPath0 p) (a1 := unPath1 p) (unPath0_comp_forgetToGrpd p_tp)
    (unPath1_comp_forgetToGrpd p_tp) :=
  rfl

end

end FunctorOperation

namespace GroupoidModel

open Grpd Model.UnstructuredUniverse

def cylinder : Cylinder Grpd := .ofCartesianMonoidalCategoryLeft Interval δ0 δ1

namespace UId

variable {Γ Δ : Grpd} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.{v}.Ty} (a0 a1 : Γ ⟶ U.Tm)
    (a0_tp : a0 ≫ U.tp = A) (a1_tp : a1 ≫ U.tp = A)
    (p : cylinder.I.obj Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = cylinder.π.app Γ ≫ A)

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

def unPath : Γ ⟶ U.{v}.Tm := by
  -- have p' := toCoreAsSmallEquiv p
  -- dsimp [cylinder, Cylinder.ofCartesianMonoidalCategoryLeft, MonoidalCategoryStruct.tensorObj,
  --   CartesianMonoidalCategory.ofChosenFiniteProducts.tensorObj, prodCone] at p'
  refine toCoreAsSmallEquiv.symm ?_
  -- convert_to p ≫ U.tp = CartesianMonoidalCategory.fst _ _ ≫ A at p_tp
  -- dsimp [CartesianMonoidalCategory.snd, prodCone] at p_tp
  refine FunctorOperation.unPath (A := toCoreAsSmallEquiv A) (p := toCoreAsSmallEquiv p) ?_
  rw [← toCoreAsSmallEquiv_apply_comp_left]
  rw [← toCoreAsSmallEquiv_apply_comp_right,
    EmbeddingLike.apply_eq_iff_eq]
  exact p_tp

lemma unPath_comp : unPath (A := σ ≫ A) (cylinder.I.map σ ≫ p) (by rw [Category.assoc, p_tp,
    ← Category.assoc, cylinder.π.naturality, Category.assoc, Functor.id_map]) =
    σ ≫ unPath p p_tp := by
  dsimp [unPath]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, ← FunctorOperation.unPath_comp]

lemma unPath_tp (δ0_p : cylinder.δ0.app Γ ≫ p = a0) (δ1_p : cylinder.δ1.app Γ ≫ p = a1) :
    unPath p p_tp ≫ U.tp = UId.Id (A := A) a0 a1
    (by rw [← δ0_p, Category.assoc, p_tp, Cylinder.δ0_π'_app_assoc])
    (by rw [← δ1_p, Category.assoc, p_tp, Cylinder.δ1_π'_app_assoc]) := by
  dsimp [unPath, U.tp, Id]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_right, FunctorOperation.unPath_comp_forgetToGrpd]
  congr 2
  · rw [← δ0_p, Grpd.comp_eq_comp, toCoreAsSmallEquiv_apply_comp_left]
    rfl
  · rw [← δ1_p, Grpd.comp_eq_comp, toCoreAsSmallEquiv_apply_comp_left]
    rfl

end UId

open UId

def UPath : GroupoidModel.U.{v}.Path cylinder where
  Id := UId.Id
  Id_comp := Id_comp
  unPath := unPath
  unPath_comp := unPath_comp
  unPath_tp := unPath_tp
  path := sorry
  path_tp := sorry
  δ0_path := sorry
  δ1_path := sorry
  path_unPath := sorry
  unPath_path := sorry


end GroupoidModel
