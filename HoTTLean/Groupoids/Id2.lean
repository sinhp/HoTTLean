import HoTTLean.Groupoids.UnstructuredModel
import HoTTLean.Model.Unstructured.Hurewicz
import HoTTLean.ForMathlib.CategoryTheory.SplitIsofibration

import HoTTLean.ForMathlib.CategoryTheory.RepPullbackCone

universe w v u v₁ u₁ v₂ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory

namespace Functor.Grothendieck

variable {C : Type*} [Category C] {A : C ⥤ Cat}
    {x y : ∫ A} (f : x ⟶ y) [IsIso f]

instance : IsIso f.base := by
  refine ⟨ (CategoryTheory.inv f).base , ?_, ?_ ⟩
  · simp [← Grothendieck.Hom.comp_base]
  · simp [← Grothendieck.Hom.comp_base]

def invFiber : y.fiber ⟶ (A.map f.base).obj x.fiber :=
  eqToHom (by simp [← Functor.comp_obj, ← Cat.comp_eq_comp, ← Functor.map_comp,
      ← Grothendieck.Hom.comp_base]) ≫
    (A.map f.base).map (CategoryTheory.inv f).fiber

@[simp]
lemma fiber_comp_invFiber : f.fiber ≫ invFiber f = 𝟙 ((A.map f.base).obj x.fiber) := by
  have h := Functor.Grothendieck.Hom.comp_fiber f (CategoryTheory.inv f)
  rw! [IsIso.hom_inv_id] at h
  have h0 : A.map (CategoryTheory.inv f).base ⋙ A.map f.base = 𝟭 _ := by
    simp [← Cat.comp_eq_comp, ← Functor.map_comp, ← Grothendieck.Hom.comp_base, Cat.id_eq_id]
  have h1 := Functor.congr_map (A.map f.base) h
  simp [← heq_eq_eq, eqToHom_map, ← Functor.comp_map, Functor.congr_hom h0] at h1
  dsimp [invFiber]
  rw! [← h1]
  simp

@[simp]
lemma invFiber_comp_fiber : invFiber f ≫ f.fiber = 𝟙 _ := by
  have h := Functor.Grothendieck.Hom.comp_fiber (CategoryTheory.inv f) f
  rw! [IsIso.inv_hom_id] at h
  simp [invFiber]
  convert h.symm
  · simp
  · simp
  · simpa using (eqToHom_heq_id_cod _ _ _).symm

instance {C : Type*} [Category C] (A : C ⥤ Cat)
    {x y : ∫ A} (f : x ⟶ y) [IsIso f] : IsIso f.fiber :=
  ⟨invFiber f , fiber_comp_invFiber f, invFiber_comp_fiber f⟩

lemma inv_base {C : Type*} [Category C] (A : C ⥤ Cat)
    {x y : ∫ A} (f : x ⟶ y) [IsIso f] :
    CategoryTheory.inv f.base = Grothendieck.Hom.base (CategoryTheory.inv f) := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← Hom.comp_base]

lemma inv_fiber {C : Type*} [Category C] (A : C ⥤ Cat)
    {x y : ∫ A} (f : x ⟶ y) [IsIso f] :
    CategoryTheory.inv f.fiber = invFiber f := by
  apply IsIso.inv_eq_of_hom_inv_id
  simp

end Functor.Grothendieck

lemma Grpd.comp_heq_comp {C C' : Grpd} (hC : C ≍ C') {X Y Z : C} {X' Y' Z' : C'}
    (hX : X ≍ X') (hY : Y ≍ Y') (hZ : Z ≍ Z') {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y ⟶ Z} {g' : Y' ⟶ Z'} (hf : f ≍ f') (hg : g ≍ g') :
    f ≫ g ≍ f' ≫ g' := by
  aesop_cat

lemma Grpd.inv_heq_of_heq_inv {C C' : Grpd} (hC : C ≍ C') {X Y : C} {X' Y' : C'}
    (hX : X ≍ X') (hY : Y ≍ Y') {f : X ⟶ Y} {g : Y' ⟶ X'} (hf : f ≍ inv g) :
    inv f ≍ g := by
  aesop_cat

lemma Discrete.as_heq_as {α α' : Type u} (hα : α ≍ α') (x : Discrete α) (x' : Discrete α')
    (hx : x ≍ x') : x.as ≍ x'.as := by
  aesop_cat

open Prod in
lemma Prod.sectR_comp_snd {C : Type u₁} [Category.{v₁} C] (Z : C)
    (D : Type u₂) [Category.{v₂} D] : sectR Z D ⋙ snd C D = 𝟭 D :=
  rfl

theorem Functor.Grothendieck.congr
    {C : Type u} [Category.{v, u} C] {F : C ⥤ Cat}
    {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

theorem PGrpd.mapFiber_inv {Γ : Type u₂} [Category.{v₂} Γ] (α : Γ ⥤ PGrpd.{v₁,u₁})
    {x y} (f : x ⟶ y) [IsIso f] :
    mapFiber α (inv f) = eqToHom (Functor.map_inv α f ▸ rfl) ≫ (inv (α.map f)).fiber := by
  simp [mapFiber, Functor.Grothendieck.congr (Functor.map_inv α f)]

theorem PGrpd.inv_mapFiber_heq {Γ : Type u₂} [Category.{v₂} Γ] (α : Γ ⥤ PGrpd.{v₁,u₁})
    {x y} (f : x ⟶ y) [IsIso f] :
    inv (mapFiber α f) ≍ ((α ⋙ forgetToGrpd).map f).map (mapFiber α (inv f)) := by
  rw [mapFiber_inv]
  simp [eqToHom_map, mapFiber]
  rw [Functor.Grothendieck.inv_fiber, Functor.Grothendieck.invFiber]
  simp [Grpd.forgetToCat]

theorem PGrpd.congr
    {X Y : PGrpd} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

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

lemma Discrete.hext {X Y : Type u} (a : Discrete X) (b : Discrete Y) (hXY : X ≍ Y)
    (hab : a.1 ≍ b.1) : a ≍ b := by
  aesop_cat

lemma Discrete.Hom.hext {α β : Type u} {x y : Discrete α} (x' y' : Discrete β) (hαβ : α ≍ β)
    (hx : x ≍ x') (hy : y ≍ y') (f : x ⟶ y) (f' : x' ⟶ y') : f ≍ f' := by
  aesop_cat

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
abbrev tf (x : Γ) : tt x ⟶ ff x := ⟨⟨⟨⟩⟩, 𝟙 x⟩

abbrev unPath0 : Γ ⥤ PGrpd := sectR ⟨⟨.false⟩⟩ _ ⋙ p

abbrev unPath1 : Γ ⥤ PGrpd := sectR ⟨⟨.true⟩⟩ _ ⋙ p

variable {p} (p_tp : p ⋙ PGrpd.forgetToGrpd = snd _ _ ⋙ A)

include p_tp in
@[simp]
lemma unPath0_comp_forgetToGrpd : unPath0 p ⋙ PGrpd.forgetToGrpd = A := by
  rw [Functor.assoc, p_tp, ← Functor.assoc, sectR_comp_snd, Functor.id_comp]

include p_tp in
@[simp]
lemma unPath1_comp_forgetToGrpd : unPath1 p ⋙ PGrpd.forgetToGrpd = A := by
  rw [Functor.assoc, p_tp, ← Functor.assoc, sectR_comp_snd, Functor.id_comp]

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

lemma IdMap_unPath {x y} (f : x ⟶ y) :
    ((IdMap (unPath0_comp_forgetToGrpd p_tp) (unPath1_comp_forgetToGrpd p_tp) f).obj
      (unPathFibObj p_tp x)).as = (unPathFibObj p_tp y).as := by
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

def unPathFibMap {x y : Γ} (f : x ⟶ y) :
    (IdMap (unPath0_comp_forgetToGrpd p_tp) (unPath1_comp_forgetToGrpd p_tp) f).obj
    (unPathFibObj p_tp x) ⟶ unPathFibObj p_tp y :=
  ⟨⟨IdMap_unPath ..⟩⟩

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

@[simp]
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

open PGrpd in
lemma map_objFiber'_mapFiber' {x y} (f : x ⟶ y) :
    (A.map f).map (objFiber' p_tp x).as ≫ mapFiber' a1_tp f =
    mapFiber' a0_tp f ≫ (objFiber' p_tp y).as := by
  simpa using (mapFiber' p_tp f).1.1

open PGrpd in
lemma map_objFiber'_mapFiber'_inv_objFiber' {x y} (f : x ⟶ y) :
    (A.map f).map (objFiber' p_tp x).as ≫ mapFiber' a1_tp f ≫ inv (objFiber' p_tp y).as =
    mapFiber' a0_tp f := by
  slice_lhs 1 2 => rw [map_objFiber'_mapFiber']
  simp

open PGrpd in
lemma mapFiber'_inv_objFiber' {x y} (f : x ⟶ y) : mapFiber' a1_tp f ≫ inv (objFiber' p_tp y).as =
    inv ((A.map f).map (objFiber' p_tp x).as) ≫ mapFiber' a0_tp f := by
  rw [IsIso.eq_inv_comp]
  slice_lhs 1 2 => rw [map_objFiber'_mapFiber']
  simp

attribute [simp] pathFibMap pathFibObj PGrpd.mapFiber'_comp' Grpd.forgetToCat in
lemma pathFibMap_comp {x y z : Grpd.Interval × Γ} (f : x ⟶ y) (g : y ⟶ z) :
    pathFibMap a0_tp a1_tp p_tp (f ≫ g) =
    eqToHom (by simp) ≫ (A.map g.2).map (pathFibMap a0_tp a1_tp p_tp f) ≫
    pathFibMap a0_tp a1_tp p_tp g := by
  rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩
  · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩ <;> simp
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩ <;> simp [map_objFiber'_mapFiber'_inv_objFiber',
        map_objFiber'_mapFiber']
  · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩
      · simp; simp [mapFiber'_inv_objFiber']
      · simp only [prod_comp, pathFibObj, pathFibMap, PGrpd.mapFiber'_comp', Functor.map_comp,
          Functor.map_inv, Category.assoc]
        slice_rhs 3 4 => rw [← mapFiber'_inv_objFiber']
        simp
    · rcases z with ⟨⟨⟨_|_⟩⟩ , z⟩ <;> simp

def path : Grpd.Interval × Γ ⥤ PGrpd :=
  Functor.Grothendieck.functorTo (snd _ _ ⋙ A) (pathFibObj a0_tp a1_tp)
    (pathFibMap a0_tp a1_tp p_tp) (pathFibMap_id a0_tp a1_tp p_tp)
    (pathFibMap_comp a0_tp a1_tp p_tp)

@[simp]
lemma path_comp_forgetToGrpd : path a0_tp a1_tp p_tp ⋙ PGrpd.forgetToGrpd = snd _ _ ⋙ A := by
  rfl

@[simp]
lemma sectR_false_comp_path : sectR ⟨⟨.false⟩⟩ _ ⋙ path a0_tp a1_tp p_tp = a0 := by
  apply Functor.Grothendieck.FunctorTo.hext
  · rw [Functor.assoc, path, Functor.Grothendieck.functorTo_forget, ← Functor.assoc,
      sectR_comp_snd, a0_tp, Functor.id_comp]
  · intro x
    simp [path, PGrpd.objFiber', PGrpd.objFiber, Grpd.eqToHom_obj]
  · intro x y f
    simp [path, PGrpd.mapFiber', PGrpd.mapFiber'EqToHom, Grpd.eqToHom_hom]
    apply HEq.trans (eqToHom_comp_heq _ _)
    simp

@[simp]
lemma sectR_true_comp_path : sectR ⟨⟨.true⟩⟩ _ ⋙ path a0_tp a1_tp p_tp = a1 := by
  apply Functor.Grothendieck.FunctorTo.hext
  · rw [Functor.assoc, path, Functor.Grothendieck.functorTo_forget, ← Functor.assoc,
      sectR_comp_snd, a1_tp, Functor.id_comp]
  · intro x
    simp [path, PGrpd.objFiber', PGrpd.objFiber, Grpd.eqToHom_obj]
  · intro x y f
    simp [path, PGrpd.mapFiber', PGrpd.mapFiber'EqToHom, Grpd.eqToHom_hom]
    apply HEq.trans (eqToHom_comp_heq _ _)
    simp

lemma unPath0_path : unPath0 (path a0_tp a1_tp p_tp) = a0 := by
  apply Functor.Grothendieck.FunctorTo.hext
  · simp
  · intro x
    simpa [path] using PGrpd.objFiber'_heq a0_tp
  · intro x y f
    simpa [path] using PGrpd.mapFiber'_heq a0_tp f

lemma unPath1_path : unPath1 (path a0_tp a1_tp p_tp) = a1 := by
  apply Functor.Grothendieck.FunctorTo.hext
  · simp
  · intro x
    simpa [path] using PGrpd.objFiber'_heq a1_tp
  · intro x y f
    simpa [path] using PGrpd.mapFiber'_heq a1_tp f

lemma unPathFibObj_path (x) : unPathFibObj (path_comp_forgetToGrpd a0_tp a1_tp p_tp) x =
    PGrpd.objFiber' p_tp x := by
  dsimp only [unPathFibObj]
  apply Discrete.ext
  simp [PGrpd.mapFiber, path]

lemma mapFiber_path_ft (x) : PGrpd.mapFiber (path a0_tp a1_tp p_tp) (ft x) =
    eqToHom (by simp [PGrpd.mapObjFiber, path, PGrpd.objFiber]) ≫
    (PGrpd.objFiber' p_tp x).as := by
  dsimp [path, PGrpd.mapFiber]
  simp

lemma unPath_path : unPath (A := A) (path_comp_forgetToGrpd a0_tp a1_tp p_tp) = p := by
  apply Functor.Grothendieck.FunctorTo.hext
  · rw [unPath_comp_forgetToGrpd, p_tp]
    rw! [unPath0_path, unPath1_path]
  · intro x
    exact heq_of_eq_of_heq (unPathFibObj_path ..) (PGrpd.objFiber'_heq p_tp)
  · intro x y f
    dsimp only [unPath]
    apply heq_of_eq_of_heq (PGrpd.functorTo_map_fiber _ _ _ _ (unPathFibMap_comp _) _)
    dsimp only [unPathFibMap]
    apply HEq.trans _ (PGrpd.mapFiber'_heq p_tp f)
    apply Discrete.Hom.hext
    · simp
    · simp only [heq_eq_eq]
      ext
      simp [IdMap_unPath, map_objFiber'_mapFiber', mapFiber_path_ft]
    · simp [unPathFibObj_path]

end

section

variable {p : Grpd.Interval × Γ ⥤ PGrpd} (p_tp : p ⋙ PGrpd.forgetToGrpd = snd _ _ ⋙ A)
    (δ0_p : unPath0 p = a0) (δ1_p : unPath1 p = a1)

include δ0_p p_tp in
lemma a0_comp_forgetToGrpd : a0 ⋙ PGrpd.forgetToGrpd = A := by
  rw [← δ0_p, unPath0, Functor.assoc, p_tp, ← Functor.assoc, sectR_comp_snd, Functor.id_comp]

include δ1_p p_tp in
lemma a1_comp_forgetToGrpd : a1 ⋙ PGrpd.forgetToGrpd = A := by
  rw [← δ1_p, unPath1, Functor.assoc, p_tp, ← Functor.assoc, sectR_comp_snd, Functor.id_comp]

lemma obj_ff_fiber (x) : (p.obj (ff x)).fiber ≍
    PGrpd.objFiber' (a0_comp_forgetToGrpd p_tp δ0_p) x := by
  symm
  convert PGrpd.objFiber'_heq (unPath0_comp_forgetToGrpd p_tp) (x := x)
  rw [← δ0_p]

lemma obj_tt_fiber (x) : (p.obj (tt x)).fiber ≍
    PGrpd.objFiber' (a1_comp_forgetToGrpd p_tp δ1_p) x := by
  symm
  convert PGrpd.objFiber'_heq (unPath1_comp_forgetToGrpd p_tp) (x := x)
  rw [← δ1_p]

lemma map_ff_fiber {x y : Γ} (f : ff x ⟶ ff y) : (p.map f).fiber ≍
    PGrpd.mapFiber' (a0_comp_forgetToGrpd p_tp δ0_p) f.2 := by
  symm
  convert PGrpd.mapFiber'_heq p_tp f
  · rw! [← obj_ff_fiber p_tp δ0_p x]
    rw! [PGrpd.objFiber'_heq p_tp]
  · rw! [← obj_ff_fiber p_tp δ0_p y]
    rw! [PGrpd.objFiber'_heq p_tp]
  · rw! [← δ0_p, unPath0, PGrpd.mapFiber'_naturality p_tp (sectR { down := { as := false } } Γ)]
    rw! [PGrpd.mapFiber'_heq p_tp]
    rw! [PGrpd.mapFiber'_heq p_tp f]
    rfl

lemma map_tt_fiber {x y : Γ} (f : tt x ⟶ tt y) : (p.map f).fiber ≍
    PGrpd.mapFiber' (a1_comp_forgetToGrpd p_tp δ1_p) f.2 := by
  symm
  convert PGrpd.mapFiber'_heq p_tp f
  · rw! [← obj_tt_fiber p_tp δ1_p x]
    rw! [PGrpd.objFiber'_heq p_tp]
  · rw! [← obj_tt_fiber p_tp δ1_p y]
    rw! [PGrpd.objFiber'_heq p_tp]
  · rw! [← δ1_p, unPath1, PGrpd.mapFiber'_naturality p_tp (sectR { down := { as := true } } Γ)]
    rw! [PGrpd.mapFiber'_heq p_tp]
    rw! [PGrpd.mapFiber'_heq p_tp f]
    rfl

lemma mapFiber'_ffm {x y : Γ} (f : x ⟶ y) : PGrpd.mapFiber' p_tp (ffm f) ≍
    PGrpd.mapFiber' (a0_comp_forgetToGrpd p_tp δ0_p) f := by
  rw! [← δ0_p, PGrpd.mapFiber'_naturality p_tp (sectR ..)]
  simp

lemma mapFiber'_ttm {x y : Γ} (f : x ⟶ y) : PGrpd.mapFiber' p_tp (ttm f) ≍
    PGrpd.mapFiber' (a1_comp_forgetToGrpd p_tp δ1_p) f := by
  rw! [← δ1_p, PGrpd.mapFiber'_naturality p_tp (sectR ..)]
  simp

@[simp]
lemma objFiber_unPath (x) : PGrpd.objFiber (unPath p_tp) x = unPathFibObj p_tp x :=
  rfl

lemma objFiber'_unPath_as (x) : (PGrpd.objFiber' (unPath_comp_forgetToGrpd p_tp) x).as =
    eqToHom (by simp [objFiber'_unPath0 p_tp]) ≫ PGrpd.mapFiber' p_tp (ft x) := by
  rfl

lemma mapFiber_ft (x) : PGrpd.mapFiber p (ft x) ≍
    (PGrpd.objFiber' (unPath_comp_forgetToGrpd p_tp) x).as := by
  symm
  rw [objFiber'_unPath_as]
  simp only [Functor.comp_obj, snd_obj, Functor.comp_map, snd_map, PGrpd.mapFiber',
    Grpd.forgetToCat, Functor.Grothendieck.forget_obj, PGrpd.objFiber'EqToHom,
    PGrpd.mapFiber'EqToHom, Grpd.eqToHom_hom, eqToHom_trans_assoc, PGrpd.mapFiber]
  apply HEq.trans (eqToHom_comp_heq ..)
  simp

include p_tp in
lemma map_ft_base (x) : (p.map (ft x)).base = eqToHom (by
    have h0 := Functor.congr_obj p_tp (ff x)
    have h1 := Functor.congr_obj p_tp (tt x)
    simp at *
    rw [h0, h1]) := by
  simpa using Functor.congr_hom p_tp (ft x)

include p_tp in
lemma map_tf_base (x) : (p.map (tf x)).base = eqToHom (by
    have h0 := Functor.congr_obj p_tp (ff x)
    have h1 := Functor.congr_obj p_tp (tt x)
    simp at *
    rw [h0, h1]) := by
  simpa using Functor.congr_hom p_tp (tf x)

include p_tp in
lemma inv_mapFiber_tf_heq (y : Γ) :
    inv (PGrpd.mapFiber p (tf y)) ≍ PGrpd.mapFiber p (ft y) := by
  have : inv (tf y : tt y ⟶ (ff y : Grpd.Interval × Γ)) = ft y := by
    apply IsIso.inv_eq_of_hom_inv_id
    aesop_cat
  rw [← this]
  rw [PGrpd.mapFiber_inv]
  apply HEq.trans _ (eqToHom_comp_heq ..).symm
  rw! [PGrpd.inv_mapFiber_heq]
  simp only [Grpd.forgetToCat, Functor.Grothendieck.forget_obj, Functor.comp_obj, Functor.comp_map,
    Functor.Grothendieck.forget_map, Cat.of_α, id_eq, cast_heq_iff_heq]
  rw! [map_tf_base p_tp, Grpd.eqToHom_hom]
  simp only [Grpd.forgetToCat, PGrpd.mapFiber, cast_heq_iff_heq]
  rw! (castMode := .all) [Functor.map_inv]
  simp

open PGrpd in
lemma path_map_ft_fiber {x y} (f : ff x ⟶ tt y) :
    ((path (a0_comp_forgetToGrpd p_tp δ0_p) (a1_comp_forgetToGrpd p_tp δ1_p)
    (p := FunctorOperation.Path.unPath p_tp)
    (by rw [unPath_comp_forgetToGrpd]; congr)).map f).fiber ≍ (p.map f).fiber := by
  simp only [Grpd.forgetToCat, path, Functor.Grothendieck.functorTo_obj_base,
    Functor.comp_obj, snd_obj, Cat.of_α, Functor.Grothendieck.functorTo_map_base,
    Functor.comp_map, snd_map, id_eq, Functor.Grothendieck.functorTo_obj_fiber, pathFibObj,
    Functor.Grothendieck.functorTo_map_fiber, pathFibMap]
  -- have hf : f = ttm f.2 ≫ ft y := by aesop_cat
  -- TODO: mwe and report: this should not type check
  have hf : f = ffm f.2 ≫ ft y := by aesop_cat
  conv => rhs; rw! (castMode := .all) [hf]
  simp only [heq_eqRec_iff_heq]
  convert_to _ ≍ mapFiber _ _
  erw [mapFiber_comp]
  rw! [← mapFiber'_ffm p_tp δ0_p]
  apply HEq.trans _ (eqToHom_comp_heq ..).symm
  apply Grpd.comp_heq_comp
  · erw [Functor.congr_obj p_tp (tt y)]
    simp
  · have H := Functor.congr_hom p_tp (ffm f.2)
    simp only [Grpd.forgetToCat, Functor.comp_obj, Functor.Grothendieck.forget_obj,
      Functor.comp_map, Functor.Grothendieck.forget_map, snd_obj, snd_map,
      Grpd.comp_eq_comp] at H
    erw [Functor.congr_hom p_tp (ft y)]
    rw! [← δ0_p, unPath0, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq]
    simp [mapObjFiber, Grpd.eqToHom_obj, objFiber, Functor.congr_obj H,
      Grpd.eqToHom_obj]
  · simp only [Functor.Grothendieck.forget_map]
    rw! [← δ0_p, unPath0, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq,
      map_ft_base p_tp, Grpd.eqToHom_obj]
    simp [objFiber]
  · rw! [← δ1_p, unPath1, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq]
    simp [objFiber]
  · simp only [Functor.comp_obj, snd_obj, Functor.comp_map, snd_map, Grpd.forgetToCat,
      Functor.Grothendieck.forget_obj, Functor.Grothendieck.forget_map, cast_heq_iff_heq]
    rw! [map_ft_base p_tp, mapFiber'_heq]
    simp [Grpd.eqToHom_hom, mapFiber]
  · rw! [mapFiber_ft p_tp y]
    simp only [Grpd.forgetToCat, Functor.Grothendieck.forget_obj, Functor.Grothendieck.forget_map,
      objFiber'_rfl, heq_cast_iff_heq]
    apply Discrete.as_heq_as
    · congr
      · symm; assumption
      · symm; assumption
    · apply (objFiber'_heq ..).trans
      simp [objFiber]

open PGrpd in
lemma path_map_tf_fiber {x y} (f : tt x ⟶ ff y) :
    ((path (a0_comp_forgetToGrpd p_tp δ0_p) (a1_comp_forgetToGrpd p_tp δ1_p)
    (p := FunctorOperation.Path.unPath p_tp)
    (by rw [unPath_comp_forgetToGrpd]; congr)).map f).fiber ≍ (p.map f).fiber := by
  simp only [Grpd.forgetToCat, path, Functor.Grothendieck.functorTo_obj_base, Functor.comp_obj,
    snd_obj, Cat.of_α, Functor.Grothendieck.functorTo_map_base, Functor.comp_map, snd_map, id_eq,
    Functor.Grothendieck.functorTo_obj_fiber, pathFibObj, Functor.Grothendieck.functorTo_map_fiber,
    pathFibMap]
  have hf : f = ttm f.2 ≫ tf y := by aesop_cat
  conv => rhs; rw! (castMode := .all) [hf]
  simp only [heq_eqRec_iff_heq]
  convert_to _ ≍ mapFiber _ _
  erw [mapFiber_comp]
  rw! [← mapFiber'_ttm p_tp δ1_p f.2]
  apply HEq.trans _ (eqToHom_comp_heq ..).symm
  have : A.obj y ≍ forgetToGrpd.obj (p.obj (ff y)) := by erw [Functor.congr_obj p_tp (ff y)]; simp
  have : objFiber' (a0_comp_forgetToGrpd p_tp δ0_p) y ≍ objFiber p (ff y) := by
    rw! [← δ0_p, unPath0, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq]
    simp [objFiber]
  apply Grpd.comp_heq_comp
  · assumption
  · have H := Functor.congr_hom p_tp (ttm f.2)
    simp only [Grpd.forgetToCat, Functor.comp_obj, Functor.Grothendieck.forget_obj,
      Functor.comp_map, Functor.Grothendieck.forget_map, snd_obj, snd_map,
      Grpd.comp_eq_comp] at H
    erw [Functor.congr_hom p_tp (tf y)]
    rw! [← δ1_p, unPath1, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq]
    simp [mapObjFiber, Grpd.eqToHom_obj, objFiber, Functor.congr_obj H,
      Grpd.eqToHom_obj]
  · simp only [Functor.Grothendieck.forget_map]
    rw! [← δ1_p, unPath1, objFiber'_naturality (sectR ..) p_tp, objFiber'_heq,
      map_tf_base p_tp, Grpd.eqToHom_obj]
    simp [objFiber]
  · assumption
  · simp only [Functor.comp_obj, snd_obj, Functor.comp_map, snd_map, Grpd.forgetToCat,
      Functor.Grothendieck.forget_obj, Functor.Grothendieck.forget_map, cast_heq_iff_heq]
    rw! [map_tf_base p_tp, mapFiber'_heq]
    simp [Grpd.eqToHom_hom, mapFiber]
  · apply Grpd.inv_heq_of_heq_inv
    · assumption
    · assumption
    · rw! [← obj_tt_fiber p_tp δ1_p]
      simp [mapObjFiber, objFiber, map_tf_base p_tp, Grpd.eqToHom_obj]
    · simp [objFiber', Grpd.eqToHom_obj]
      apply HEq.trans (b := (unPathFibObj p_tp y).as)
      · apply Discrete.as_heq_as
        · congr 1
          · rw! [← δ0_p]
            simp [unPath0, objFiber_naturality, Grpd.eqToHom_obj, objFiber']
          · rw! [← δ1_p]
            simp [unPath1, objFiber_naturality, Grpd.eqToHom_obj, objFiber']
        · simp
      · simp
        apply HEq.trans (eqToHom_comp_heq ..)
        rw! [inv_mapFiber_tf_heq p_tp, mapFiber'_heq]
        simp [mapFiber]

lemma path_unPath : path (a0_comp_forgetToGrpd p_tp δ0_p) (a1_comp_forgetToGrpd p_tp δ1_p)
    (p := FunctorOperation.Path.unPath p_tp) (by rw [unPath_comp_forgetToGrpd]; congr) = p := by
  apply Functor.Grothendieck.FunctorTo.hext
  · simp only [path, Functor.Grothendieck.functorTo_forget, p_tp]
  · intro x
    rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩
    · simpa [path] using (obj_ff_fiber p_tp δ0_p x).symm
    · simpa [path] using (obj_tt_fiber p_tp δ1_p x).symm
  · intro x y f
    rcases x with ⟨⟨⟨_|_⟩⟩ , x⟩
    · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
      · simpa [path] using (map_ff_fiber p_tp δ0_p f).symm
      · exact path_map_ft_fiber p_tp δ0_p δ1_p f
    · rcases y with ⟨⟨⟨_|_⟩⟩ , y⟩
      · exact path_map_tf_fiber p_tp δ0_p δ1_p f
      · simpa [path] using (map_tt_fiber p_tp δ1_p f).symm

end

-- section

-- variable (y : ↑Γ ⥤ PGrpd) (p : Grpd.Interval × Γ ⥤ Grpd)
--     (y_tp : y ⋙ PGrpd.forgetToGrpd = Prod.sectR ⟨⟨.false⟩⟩ Γ ⋙ p)

-- def liftFibObj : (x : Grpd.Interval × Γ) → (p.obj x)
-- | ⟨⟨⟨.false⟩⟩, x2⟩ => PGrpd.objFiber' y_tp x2
-- | ⟨⟨⟨.true⟩⟩, x2⟩ => sorry -- Functor.Grothendieck.tsorry


-- def lift  : Grpd.Interval × Γ ⥤ PGrpd :=
--   PGrpd.functorTo p sorry sorry sorry sorry

-- end

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

def unPath : Γ ⟶ U.{v}.Tm := toCoreAsSmallEquiv.symm <|
  FunctorOperation.Path.unPath (A := toCoreAsSmallEquiv A) (p := toCoreAsSmallEquiv p) (by
    rw [← toCoreAsSmallEquiv_apply_comp_left]
    rw [← toCoreAsSmallEquiv_apply_comp_right,
      EmbeddingLike.apply_eq_iff_eq]
    exact p_tp)

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

lemma δ0_path : cylinder.δ0.app Γ ≫ path a0 a1 a0_tp a1_tp p p_tp = a0 := by
  dsimp [path]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, toCoreAsSmallEquiv.symm_apply_eq]
  apply FunctorOperation.Path.sectR_false_comp_path

lemma δ1_path : cylinder.δ1.app Γ ≫ path a0 a1 a0_tp a1_tp p p_tp = a1 := by
  dsimp [path]
  rw [← toCoreAsSmallEquiv_symm_apply_comp_left, toCoreAsSmallEquiv.symm_apply_eq]
  apply FunctorOperation.Path.sectR_true_comp_path

lemma unPath_path : unPath (A := A) (path a0 a1 a0_tp a1_tp p p_tp) (path_tp ..) = p := by
  dsimp [unPath, path]
  rw [toCoreAsSmallEquiv.symm_apply_eq]
  rw! (transparency := .default) [toCoreAsSmallEquiv.apply_symm_apply]
  apply FunctorOperation.Path.unPath_path

end

lemma path_unPath (p : cylinder.I.obj Γ ⟶ U.Tm) (p_tp : p ≫ U.tp = cylinder.π.app Γ ≫ A)
    (δ0_p : cylinder.δ0.app Γ ≫ p = a0) (δ1_p : cylinder.δ1.app Γ ≫ p = a1) :
    path (A := A) a0 a1 (by simp [← δ0_p, - Grpd.comp_eq_comp, p_tp])
    (by simp [← δ1_p, - Grpd.comp_eq_comp, p_tp]) (unPath p p_tp)
    (unPath_tp a0 a1 p p_tp δ0_p δ1_p) = p := by
  dsimp [path, unPath]
  rw [toCoreAsSmallEquiv.symm_apply_eq]
  rw! (transparency := .default) [toCoreAsSmallEquiv.apply_symm_apply]
  apply FunctorOperation.Path.path_unPath
  · simp [FunctorOperation.Path.unPath0, ← toCoreAsSmallEquiv_apply_comp_left, ← δ0_p]
    rfl
  · simp [FunctorOperation.Path.unPath1, ← toCoreAsSmallEquiv_apply_comp_left, ← δ1_p]
    rfl

namespace hurewiczUTp

variable (p0 : Γ ⟶ U.{v}.Tm) (p : cylinder.I.obj Γ ⟶ U.Ty)
    (p0_tp : p0 ≫ U.tp = cylinder.δ0.app Γ ≫ p)

@[simp]
def liftObj : Grpd.Interval × Γ → U.{v}.Tm
| ⟨⟨⟨.false⟩⟩, x2⟩ => p0.obj x2
| ⟨⟨⟨.true⟩⟩, x2⟩ => tpClovenIsofibration.liftObj (p.map (FunctorOperation.Path.ft x2))
    (Functor.congr_obj p0_tp x2)

def liftMap0 {x2 : Γ} {y : Grpd.Interval × Γ} (f : FunctorOperation.Path.ff x2 ⟶ y) :=
  tpClovenIsofibration.liftIso (X' := p0.obj x2) (p.map f) (Functor.congr_obj p0_tp x2)

open FunctorOperation.Path

def liftMap : {x y : Grpd.Interval × Γ} → (f : x ⟶ y) →
    liftObj p0 p p0_tp x ⟶ liftObj p0 p p0_tp y
| ⟨⟨⟨.false⟩⟩, x2⟩, ⟨⟨⟨.false⟩⟩, y2⟩, f => p0.map f.2
| ⟨⟨⟨.false⟩⟩, x2⟩, ⟨⟨⟨.true⟩⟩, y2⟩, f => p0.map f.2 ≫ liftMap0 p0 p p0_tp (ft y2)
  -- have : f = ffm f.2 ≫ ft y2 := by ext; rfl; simp
| ⟨⟨⟨.true⟩⟩, x2⟩, ⟨⟨⟨.false⟩⟩, y2⟩, f => by
  dsimp
  refine ?_ ≫ p0.map f.2

  sorry
| ⟨⟨⟨.true⟩⟩, x2⟩, ⟨⟨⟨.true⟩⟩, y2⟩, f => sorry

def lift : cylinder.I.obj Γ ⟶ U.{v}.Tm where
  obj := liftObj p0 p p0_tp
  map := liftMap p0 p p0_tp
  map_id := sorry
  map_comp := sorry

-- def lift : cylinder.I.obj Γ ⟶ U.{v}.Tm :=
--   let y' := toCoreAsSmallEquiv y
--   let p' := toCoreAsSmallEquiv p
--   have y'_tp : y' ⋙ PGrpd.forgetToGrpd = Prod.sectR ⟨⟨.false⟩⟩ _ ⋙ p' := by
--     unfold y'
--     dsimp [U.tp] at y_tp
--     rw [← toCoreAsSmallEquiv_apply_comp_right, y_tp, toCoreAsSmallEquiv_apply_comp_left]
--     rfl
--   toCoreAsSmallEquiv.symm sorry

end hurewiczUTp

end UId

open UId

def UPath : GroupoidModel.U.{v}.Path cylinder where
  Id := Id
  Id_comp := Id_comp
  unPath := unPath
  unPath_comp := unPath_comp
  unPath_tp := unPath_tp
  path := path
  path_tp := path_tp
  δ0_path := δ0_path
  δ1_path := δ1_path
  path_unPath := path_unPath
  unPath_path := unPath_path

def hurewiczUTp : cylinder.Hurewicz U.tp where
  lift := hurewiczUTp.lift
  lift_comp_self := sorry
  δ0_comp_lift := sorry

def UId : GroupoidModel.U.{v, max (v + 1) (v₁ + 1) u}.PolymorphicIdElim UPath.polymorphicIdIntro
    GroupoidModel.U.{v₁, max (v + 1) (v₁ + 1) u} :=
  @UPath.polymorphicIdElim _ _ _ _ sorry sorry sorry _ sorry sorry sorry

end GroupoidModel
