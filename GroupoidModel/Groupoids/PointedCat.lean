import Mathlib.CategoryTheory.Category.Grpd

/-!
Here we define pointed categories and pointed groupoids as well as prove some basic lemmas.
-/

universe u v u₁ v₁ u₂ v₂

namespace CategoryTheory

noncomputable section PointedCategories

/-- A typeclass for pointed categories. -/
class PointedCategory.{w,z} (C : Type z) extends Category.{w} C where
  pt : C

/-- A constructor that makes a pointed category from a category and a point. -/
def PointedCategory.of (C : Type*) (pt : C) [Category C] : PointedCategory C where
  pt := pt

/-- The structure of a functor from C to D
along with a morphism from the image of the point of C to the point of D. -/
structure PointedFunctor (C D : Type*) [cp : PointedCategory C] [dp : PointedCategory D]
    extends C ⥤ D where
  point : obj (cp.pt) ⟶ (dp.pt)

namespace PointedFunctor

/-- The identity `PointedFunctor` whose underlying functor is the identity functor-/
@[simps!]
def id (C : Type*) [PointedCategory C] : PointedFunctor C C where
  toFunctor := Functor.id C
  point := 𝟙 PointedCategory.pt

variable {C D E : Type*} [cp : PointedCategory C] [PointedCategory D] [PointedCategory E]

/-- Composition of `PointedFunctor` composes the underlying functors and the point morphisms. -/
@[simps!]
def comp (F : PointedFunctor C D) (G : PointedFunctor D E) : PointedFunctor C E where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  point := (G.map F.point) ≫ (G.point)

theorem congr_func {F G: PointedFunctor C D} (eq : F = G) : F.toFunctor = G.toFunctor :=
  congrArg toFunctor eq

theorem congr_point {F G: PointedFunctor C D} (eq : F = G) :
      F.point = (eqToHom (Functor.congr_obj (congr_func eq) cp.pt)) ≫ G.point := by
    have h :=
      (Functor.conj_eqToHom_iff_heq
        F.point G.point (Functor.congr_obj (congr_func eq) cp.pt) rfl).mpr
    simp at h
    apply h
    rw [eq]

/-- The extensionality principle for pointed functors-/
@[ext]
theorem ext (F G: PointedFunctor C D) (h_func : F.toFunctor = G.toFunctor)
    (h_point : F.point = (eqToHom (Functor.congr_obj h_func cp.pt)) ≫ G.point) : F = G := by
  rcases F with ⟨F.func,F.point⟩
  rcases G with ⟨G.func,G.point⟩
  congr
  simp at h_point
  have temp : G.point = G.point ≫ (eqToHom rfl) := by simp
  rw [temp] at h_point
  exact
    (Functor.conj_eqToHom_iff_heq F.point G.point
          (congrFun (congrArg Prefunctor.obj (congrArg Functor.toPrefunctor h_func))
            PointedCategory.pt)
          rfl).mp
      h_point

end PointedFunctor

/-- The category of pointed categorys and pointed functors-/
def PCat.{w,z} :=
  Bundled PointedCategory.{w, z}

namespace PCat

instance : CoeSort PCat.{v,u} (Type u) :=
  ⟨Bundled.α⟩

instance str (C : PCat.{v, u}) : PointedCategory.{v, u} C :=
  Bundled.str C

/-- Construct a bundled `PCat` from the underlying type and the typeclass. -/
def of (C : Type u) [PointedCategory C] : PCat.{v, u} :=
  Bundled.of C

instance category : LargeCategory.{max v u} PCat.{v, u} where
  Hom C D := PointedFunctor C D
  id C := PointedFunctor.id C
  comp f g := PointedFunctor.comp f g
  comp_id f := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.id,PointedFunctor.comp,Functor.comp_id]
  id_comp f := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.id,PointedFunctor.comp,Functor.id_comp]
  assoc f g h := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.comp,Functor.assoc]

/-- The functor that takes PCat to Cat by forgetting the points-/
def forgetPoint : PCat ⥤ Cat where
  obj x := Cat.of x
  map f := f.toFunctor

end PCat

/-- The class of pointed pointed groupoids. -/
class PointedGroupoid.{w,z} (C : Type z) extends Groupoid.{w} C, PointedCategory.{w,z} C

/-- A constructor that makes a pointed groupoid from a groupoid and a point. -/
def PointedGroupoid.of (C : Type*) (pt : C) [Groupoid C]: PointedGroupoid C where
  pt := pt

/-- The category of pointed groupoids and pointed functors-/
def PGrpd.{w,z} :=
  Bundled PointedGroupoid.{w, z}

namespace PGrpd

instance : CoeSort PGrpd.{v,u} (Type u) :=
  ⟨Bundled.α⟩

instance str (C : PGrpd.{v, u}) : PointedGroupoid.{v, u} C :=
  Bundled.str C

/-- Construct a bundled `PGrpd` from the underlying type and the typeclass. -/
def of (C : Type u) [PointedGroupoid C] : PGrpd.{v, u} :=
  Bundled.of C

/-- Construct a bundled `PGrpd` from a `Grpd` and a point -/
def fromGrpd (G : Grpd.{v,u}) (g : G) : PGrpd.{v,u} := by
  have pg : PointedGroupoid (Bundled.α G) := by
    apply PointedGroupoid.of (Bundled.α G) g
  exact PGrpd.of (Bundled.α G)

instance category : LargeCategory.{max v u} PGrpd.{v, u} where
  Hom C D := PointedFunctor C D
  id C := PointedFunctor.id C
  comp f g := PointedFunctor.comp f g
  comp_id f := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.id,PointedFunctor.comp,Functor.comp_id]
  id_comp f := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.id,PointedFunctor.comp,Functor.id_comp]
  assoc f g h := by
    apply PointedFunctor.ext
    simp
    simp [PointedFunctor.comp,Functor.assoc]

/-- The functor that takes PGrpd to Grpd by forgetting the points-/
def forgetPoint : PGrpd ⥤ Grpd where
  obj x := Grpd.of x
  map f := f.toFunctor

/-- This takes PGrpd to PCat-/
def forgetToCat : PGrpd ⥤ PCat where
  obj x := PCat.of x
  map f := f

end PGrpd

end PointedCategories
