import HoTTLean.Groupoids.UnstructuredModel
import HoTTLean.Model.Unstructured.Hurewicz

import HoTTLean.ForMathlib.CategoryTheory.RepPullbackCone

universe w v u v₁ u₁ v₂ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory

open Prod in
lemma Prod.sectR_snd {C : Type u₁} [Category.{v₁} C] (Z : C)
    (D : Type u₂) [Category.{v₂} D] : sectR Z D ⋙ snd C D = 𝟭 D :=
  rfl

theorem Functor.Grothendieck.congr
    {C : Type u} [Category.{v, u} C] {F : C ⥤ Cat}
    {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

theorem PGrpd.congr
    {X Y : PGrpd} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

-- def Grpd.Interval.rec {α : Type*} (a b : α) (x : Grpd.Interval) : α :=
--   match x with
--   | ⟨⟨.true⟩⟩ => a
--   | ⟨⟨.false⟩⟩ => b

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

@[simps!]
def Id : Γ ⥤ Grpd where
  obj := IdObj a0_tp a1_tp
  map := IdMap a0_tp a1_tp
  map_id := IdMap_id a0_tp a1_tp
  map_comp := IdMap_comp a0_tp a1_tp

lemma Id_comp : Id (A := σ ⋙ A) (a0 := σ ⋙ a0) (a1 := σ ⋙ a1)
    (by simp[Functor.assoc, a0_tp]) (by simp[Functor.assoc, a1_tp]) =
    σ ⋙ Id a0_tp a1_tp :=
  rfl

namespace Path

open CategoryTheory.Prod

section

variable (p : Grpd.Interval × Γ ⥤ PGrpd)

abbrev ff (x : Γ) : Grpd.Interval × Γ := ⟨⟨⟨.false⟩⟩, x⟩
abbrev ffm {x y : Γ} (f : x ⟶ y) : ff x ⟶ ff y := ⟨𝟙 _, f⟩
abbrev tt (x : Γ) : Grpd.Interval × Γ := ⟨⟨⟨.true⟩⟩, x⟩
abbrev ttm {x y : Γ} (f : x ⟶ y) : tt x ⟶ tt y := ⟨𝟙 _, f⟩
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
  have h1 := (PGrpd.mapFiber'_comp' p_tp (ft x) (ttm f)).symm
  rw! [comm, PGrpd.mapFiber'_comp' p_tp (ffm f) (ft y)] at h1
  simp only [Functor.comp_obj, snd_obj, prod_comp, Functor.comp_map, snd_map, Grpd.map_id_map,
    Category.assoc, eqToHom_trans_assoc, ← heq_eq_eq, heq_eqToHom_comp_iff,
    eqToHom_comp_heq_iff] at h1
  simp only [PGrpd.mapFiber'_naturality p_tp (sectR ⟨⟨.false⟩⟩ _), sectR_obj, sectR_map,
    Functor.map_comp, eqToHom_map, PGrpd.mapFiber'_naturality p_tp (sectR ⟨⟨.true⟩⟩ _),
    Category.assoc, IsIso.inv_comp_eq]
  rw! [h1]
  simp

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

section

variable {p : Γ ⥤ PGrpd}
  (p_tp : p ⋙ PGrpd.forgetToGrpd = FunctorOperation.Id a0_tp a1_tp)

def pathFibObj : (x : Grpd.Interval × Γ) → A.obj x.2
| ⟨⟨⟨.false⟩⟩, x2⟩ => PGrpd.objFiber' a0_tp x2
| ⟨⟨⟨.true⟩⟩, x2⟩ => PGrpd.objFiber' a1_tp x2

def pathFibMap : {x y : Grpd.Interval × Γ} → (f : x ⟶ y) →
    ((A.map f.2).obj (pathFibObj a0_tp a1_tp x) ⟶ pathFibObj a0_tp a1_tp y)
| ⟨⟨⟨.false⟩⟩, _⟩, ⟨⟨⟨.false⟩⟩, _⟩, f => PGrpd.mapFiber' a0_tp f.2
| ⟨⟨⟨.false⟩⟩, _⟩, ⟨⟨⟨.true⟩⟩, y2⟩, f => (PGrpd.mapFiber' a0_tp f.2) ≫ (PGrpd.objFiber' p_tp y2).1
| ⟨⟨⟨.true⟩⟩, _⟩, ⟨⟨⟨.false⟩⟩, y2⟩, f =>
  (PGrpd.mapFiber' a1_tp f.2) ≫ inv (PGrpd.objFiber' p_tp y2).1
| ⟨⟨⟨.true⟩⟩, _⟩, ⟨⟨⟨.true⟩⟩, _⟩, f => PGrpd.mapFiber' a1_tp f.2

lemma pathFibMap_id (x : Grpd.Interval × Γ) : pathFibMap a0_tp a1_tp p_tp (𝟙 x) =
    eqToHom (by simp) := by
  rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩ <;> simp [pathFibMap]


-- def pathObj : Grpd.Interval × Γ → PGrpd
--   | ⟨⟨⟨.false⟩⟩, x2⟩ => .mk (A.obj x2) (PGrpd.objFiber' a0_tp x2)
--   | ⟨⟨⟨.true⟩⟩, x2⟩ => .mk (A.obj x2) (PGrpd.objFiber' a1_tp x2)

-- lemma pathObj_base : (x : Grpd.Interval × Γ) → (pathObj a0_tp a1_tp x).base = A.obj x.2
--   | ⟨⟨⟨.false⟩⟩, _⟩ => rfl
--   | ⟨⟨⟨.true⟩⟩, _⟩ => rfl

-- def pathMap : {x y : Grpd.Interval × Γ} → (f : x ⟶ y) →
--     pathObj a0_tp a1_tp x ⟶ pathObj a0_tp a1_tp y
--   | ⟨⟨⟨.false⟩⟩, _⟩, ⟨⟨⟨.false⟩⟩, _⟩, f => .mk (A.map f.2) (PGrpd.mapFiber' a0_tp f.2)
--   | ⟨⟨⟨.false⟩⟩, _⟩, ⟨⟨⟨.true⟩⟩, y2⟩, f =>
--     .mk (A.map f.2) ((PGrpd.mapFiber' a0_tp f.2) ≫ (PGrpd.objFiber' p_tp y2).1)
--   | ⟨⟨⟨.true⟩⟩, _⟩, ⟨⟨⟨.false⟩⟩, y2⟩, f =>
--     .mk (A.map f.2) ((PGrpd.mapFiber' a1_tp f.2) ≫ inv (PGrpd.objFiber' p_tp y2).1)
--     -- refine .mk (A.map f.2) (inv ((A.map f.2).map (PGrpd.objFiber' p_tp x2).1) ≫ (PGrpd.mapFiber' a0_tp f.2))
--     -- have h := (PGrpd.objFiber' p_tp y2).1
--     -- dsimp [pathObj, Grpd.forgetToCat] at *
--   | ⟨⟨⟨.true⟩⟩, _⟩, ⟨⟨⟨.true⟩⟩, _⟩, f => .mk (A.map f.2) (PGrpd.mapFiber' a1_tp f.2)

-- lemma pathMap_id (x : Grpd.Interval × Γ) :
--     pathMap a0_tp a1_tp p_tp (𝟙 x) = 𝟙 (pathObj a0_tp a1_tp x) := by
--   rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩
--   all_goals apply Functor.Grothendieck.Hom.ext <;> simp [pathMap, pathObj]

open PGrpd in
lemma map_objFiber_mapFiber' {x y} (f : x ⟶ y) :
    (A.map f).map (objFiber' p_tp x).as ≫ mapFiber' a1_tp f =
    mapFiber' a0_tp f ≫ (objFiber' p_tp y).as := by
  simpa using (mapFiber' p_tp f).1.1

open PGrpd in
lemma map_objFiber_mapFiber'_inv_objFiber {x y} (f : x ⟶ y) : (A.map f).map (objFiber' p_tp x).as ≫
    mapFiber' a1_tp f ≫ inv (objFiber' p_tp y).as = mapFiber' a0_tp f := by
  slice_lhs 1 2 => rw [map_objFiber_mapFiber']
  simp

open PGrpd in
lemma mapFiber'_inv_objFiber {x y} (f : x ⟶ y) : mapFiber' a1_tp f ≫ inv (objFiber' p_tp y).as =
    inv ((A.map f).map (objFiber' p_tp x).as) ≫ mapFiber' a0_tp f := by
  rw [IsIso.eq_inv_comp]
  slice_lhs 1 2 => rw [map_objFiber_mapFiber']
  simp

attribute [simp] pathFibMap pathFibObj PGrpd.mapFiber'_comp' Grpd.forgetToCat in
lemma pathFibMap_comp {x y z : Grpd.Interval × Γ} (f : x ⟶ y) (g : y ⟶ z) :
    pathFibMap a0_tp a1_tp p_tp (f ≫ g) =
    eqToHom (by simp) ≫ (A.map g.2).map (pathFibMap a0_tp a1_tp p_tp f) ≫
    pathFibMap a0_tp a1_tp p_tp g := by
  rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩
  · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩ <;> simp
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩ <;> simp [map_objFiber_mapFiber'_inv_objFiber,
        map_objFiber_mapFiber']
  · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩
      · simp; simp [mapFiber'_inv_objFiber]
      · simp only [prod_comp, pathFibObj, pathFibMap, PGrpd.mapFiber'_comp', Functor.map_comp,
          Functor.map_inv, Category.assoc]
        slice_rhs 3 4 => rw [← mapFiber'_inv_objFiber]
        simp
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩ <;> simp


-- attribute [simp] pathMap pathObj PGrpd.mapFiber'_comp' Grpd.forgetToCat in
-- lemma pathMap_comp {x y z : Grpd.Interval × Γ} (f : x ⟶ y) (g : y ⟶ z) :
--     pathMap a0_tp a1_tp p_tp (f ≫ g) =
--     pathMap a0_tp a1_tp p_tp f ≫ pathMap a0_tp a1_tp p_tp g := by
--   rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩
--   · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
--     · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩
--       all_goals apply Functor.Grothendieck.Hom.ext <;> simp
--     · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩
--       · apply Functor.Grothendieck.Hom.ext <;> simp [map_objFiber_mapFiber'_inv_objFiber]
--       · apply Functor.Grothendieck.Hom.ext <;> simp [map_objFiber_mapFiber']
--   · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
--     · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩
--       · apply Functor.Grothendieck.Hom.ext <;> simp; rw [mapFiber'_inv_objFiber]
--       · apply Functor.Grothendieck.Hom.ext <;> simp
--         slice_rhs 2 3 => rw [← mapFiber'_inv_objFiber]
--         simp
--     · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩
--       all_goals apply Functor.Grothendieck.Hom.ext <;> simp

-- def path : Grpd.Interval × Γ ⥤ PGrpd where
--   obj := pathObj a0_tp a1_tp
--   map := pathMap a0_tp a1_tp p_tp
--   map_id := pathMap_id a0_tp a1_tp p_tp
--   map_comp := pathMap_comp a0_tp a1_tp p_tp

def path : Grpd.Interval × Γ ⥤ PGrpd :=
  Functor.Grothendieck.functorTo (snd _ _ ⋙ A) (pathFibObj a0_tp a1_tp)
    (pathFibMap a0_tp a1_tp p_tp) (pathFibMap_id a0_tp a1_tp p_tp)
    (pathFibMap_comp a0_tp a1_tp p_tp)

@[simp]
lemma path_comp_forgetToGrpd : path a0_tp a1_tp p_tp ⋙ PGrpd.forgetToGrpd = snd _ _ ⋙ A := by
  rfl

end

end Path

end FunctorOperation

namespace GroupoidModel

open Grpd Model.UnstructuredUniverse

def cylinder : Cylinder Grpd := .ofCartesianMonoidalCategoryLeft Interval δ0 δ1

namespace UId

variable {Γ Δ : Grpd} (σ : Δ ⟶ Γ) {A : Γ ⟶ U.{v}.Ty} (a0 a1 : Γ ⟶ U.Tm)
    (a0_tp : a0 ≫ U.tp = A) (a1_tp : a1 ≫ U.tp = A)

include a0_tp in
lemma pt_tp : toCoreAsSmallEquiv a0 ⋙ PGrpd.forgetToGrpd = toCoreAsSmallEquiv A := by
  rw [← a0_tp, Grpd.comp_eq_comp, U.tp, toCoreAsSmallEquiv_apply_comp_right]

def Id : Γ ⟶ U.{v}.Ty :=
  toCoreAsSmallEquiv.symm (FunctorOperation.Id (A := toCoreAsSmallEquiv A)
    (a0 := toCoreAsSmallEquiv a0) (a1 := toCoreAsSmallEquiv a1)
    (pt_tp a0 a0_tp)
    (pt_tp a1 a1_tp))

lemma Id_comp :
    UId.Id (A := σ ≫ A) (σ ≫ a0) (σ ≫ a1) (by simp only [Category.assoc, a0_tp, U_Ty])
      (by simp only [Category.assoc, a1_tp, U_Ty]) = σ ≫ UId.Id a0 a1 a0_tp a1_tp := by
  dsimp only [U_Ty, comp_eq_comp, Id]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, ← FunctorOperation.Id_comp]

section

variable (p : cylinder.I.obj Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = cylinder.π.app Γ ≫ A)

def unPath : Γ ⟶ U.{v}.Tm := by
  -- have p' := toCoreAsSmallEquiv p
  -- dsimp [cylinder, Cylinder.ofCartesianMonoidalCategoryLeft, MonoidalCategoryStruct.tensorObj,
  --   CartesianMonoidalCategory.ofChosenFiniteProducts.tensorObj, prodCone] at p'
  refine toCoreAsSmallEquiv.symm ?_
  -- convert_to p ≫ U.tp = CartesianMonoidalCategory.fst _ _ ≫ A at p_tp
  -- dsimp [CartesianMonoidalCategory.snd, prodCone] at p_tp
  refine FunctorOperation.Path.unPath (A := toCoreAsSmallEquiv A) (p := toCoreAsSmallEquiv p) ?_
  rw [← toCoreAsSmallEquiv_apply_comp_left]
  rw [← toCoreAsSmallEquiv_apply_comp_right,
    EmbeddingLike.apply_eq_iff_eq]
  exact p_tp

lemma unPath_comp : unPath (A := σ ≫ A) (cylinder.I.map σ ≫ p) (by rw [Category.assoc, p_tp,
    ← Category.assoc, cylinder.π.naturality, Category.assoc, Functor.id_map]) =
    σ ≫ unPath p p_tp := by
  dsimp [unPath]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, ← FunctorOperation.Path.unPath_comp]

lemma unPath_tp (δ0_p : cylinder.δ0.app Γ ≫ p = a0) (δ1_p : cylinder.δ1.app Γ ≫ p = a1) :
    unPath p p_tp ≫ U.tp = UId.Id (A := A) a0 a1
    (by rw [← δ0_p, Category.assoc, p_tp, Cylinder.δ0_π'_app_assoc])
    (by rw [← δ1_p, Category.assoc, p_tp, Cylinder.δ1_π'_app_assoc]) := by
  dsimp [unPath, U.tp, Id]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_right, FunctorOperation.Path.unPath_comp_forgetToGrpd]
  congr 2
  · rw [← δ0_p, Grpd.comp_eq_comp, toCoreAsSmallEquiv_apply_comp_left]
    rfl
  · rw [← δ1_p, Grpd.comp_eq_comp, toCoreAsSmallEquiv_apply_comp_left]
    rfl

end

section

variable (p : Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = UId.Id a0 a1 a0_tp a1_tp)

def path : cylinder.I.obj Γ ⟶ U.{v}.Tm :=
  have p_tp' : toCoreAsSmallEquiv p ⋙ PGrpd.forgetToGrpd =
      FunctorOperation.Id (pt_tp a0 a0_tp) (pt_tp a1 a1_tp) := by
    dsimp [U.tp, Id] at p_tp
    rw [← toCoreAsSmallEquiv_apply_comp_right, p_tp, Equiv.apply_symm_apply]
  toCoreAsSmallEquiv.symm <| FunctorOperation.Path.path _ _ p_tp'

lemma path_tp : path a0 a1 a0_tp a1_tp p p_tp ≫ U.tp = cylinder.π.app Γ ≫ A := by
  dsimp [path, U.tp]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_right, toCoreAsSmallEquiv.symm_apply_eq,
    toCoreAsSmallEquiv_apply_comp_left, FunctorOperation.Path.path_comp_forgetToGrpd]
  rfl

end
end UId

open UId

def UPath : GroupoidModel.U.{v}.Path cylinder where
  Id := UId.Id
  Id_comp := Id_comp
  unPath := unPath
  unPath_comp := unPath_comp
  unPath_tp := unPath_tp
  path := path
  path_tp := path_tp
  δ0_path := sorry
  δ1_path := sorry
  path_unPath := sorry
  unPath_path := sorry


end GroupoidModel
