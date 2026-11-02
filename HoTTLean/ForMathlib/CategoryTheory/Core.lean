import HoTTLean.ForMathlib.CategoryTheory.Functor.IsPullback
import HoTTLean.ForMathlib.CategoryTheory.Grpd

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

namespace CategoryTheory
namespace Core

@[ext]
theorem obj_ext {C : Type*} {X Y : Core C} (h : X.of = Y.of) :
    X = Y := by
  cases X
  cases h
  rfl

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]

@[simp] theorem eqToHom_iso {X Y : Core C} (h : X = Y) :
    (eqToHom h).iso = eqToIso (by subst h; rfl) := by
  subst h
  rfl

theorem comp_inclusion_injective {l0 l1 : D ⥤ Core C}
    (hl : l0 ⋙ inclusion C = l1 ⋙ inclusion C) : l0 = l1 := by
  fapply Functor.ext
  · intro x
    ext
    exact Functor.congr_obj hl x
  · intro x y f
    apply (inclusion C).map_injective
    simpa [Functor.comp_map, inclusion, eqToHom_iso] using Functor.congr_hom hl f

lemma core_comp_inclusion (F : C ⥤ D) :
    F.core ⋙ inclusion D = inclusion C ⋙ F :=
  rfl

def map : Cat.{v,u} ⥤ Grpd.{v,u} where
  obj C := Grpd.of (Core C)
  map F := Grpd.homOf (F.toFunctor.core)

variable {Γ : Type u} [Groupoid.{v} Γ]

/--  A functor from a groupoid into a category is equivalent
    to a functor from the groupoid into the core -/
@[simps apply]
def functorToCoreEquiv : Γ ⥤ D ≃ Γ ⥤ Core D where
  toFun := functorToCore
  invFun := forgetFunctorToCore.obj
  left_inv _ := rfl
  right_inv _ := by
    apply comp_inclusion_injective
    rfl

variable {C : Type u₁} [Category.{v₁} C]
variable {G : Type u₂} [Groupoid.{v₂} G]
variable {G' : Type u₃} [Groupoid.{v₃} G']
variable {C' : Type u₃} [Category.{v₃} C']

@[simp]
theorem functorToCore_comp_inclusion (H : G ⥤ C) :
    functorToCore H ⋙ inclusion _ = H := rfl

theorem functorToCoreEquiv_symm_apply_comp_left (H : G ⥤ Core C) (F : G' ⥤ G) :
    functorToCoreEquiv.symm (F ⋙ H) = F ⋙ functorToCoreEquiv.symm H :=
  rfl

theorem functorToCoreEquiv_symm_apply_comp_right (H : G ⥤ Core C) (F : C ⥤ C') :
    functorToCoreEquiv.symm (H ⋙ F.core) = functorToCoreEquiv.symm H ⋙ F :=
  rfl

theorem eqToIso_iso_hom {a b : Core C} (h1 : a = b)
    (h2 : (inclusion C).obj a = (inclusion C).obj b) :
    (eqToHom h1).iso.hom = eqToHom h2 := by
  cases h1
  rfl

section Adjunction

def adjunction : Grpd.forgetToCat ⊣ Core.map where
  unit := {
    app G := Grpd.homOf (Core.functorToCore (Functor.id _))
    naturality _ _ F := by
      change F ⋙ functorToCore (𝟭 _) = functorToCore (𝟭 _) ⋙ F.core
      simp [← functorToCore_comp_left,
        ← functorToCore_comp_right,
        Functor.id_comp, Functor.comp_id]}
  counit := {app C := Cat.homOf (Core.inclusion C)}

theorem functorToCore_inclusion_apply {C : Type u} [Category.{v} C] :
    Core.functorToCore (Core.inclusion C) = Functor.id (Core C) :=
  rfl


/-- Mildly evil. -/
instance : IsIso (Grpd.homOf (Core.inclusion G)) where
  out := ⟨ Grpd.homOf (Core.functorToCore (Functor.id G)),
    inclusion_comp_functorToCore, rfl ⟩

/-- Mildly evil. -/
instance {G : Type u} [Groupoid.{v} G] :
  IsIso (Grpd.homOf (Core.functorToCore (Functor.id G))) where
  out := ⟨ Grpd.homOf (Core.inclusion G), rfl,
    inclusion_comp_functorToCore ⟩

end Adjunction

open _root_.CategoryTheory.Functor

instance : IsLeftAdjoint Grpd.forgetToCat :=
  IsLeftAdjoint.mk ⟨ Core.map , ⟨ adjunction ⟩ ⟩

instance : IsRightAdjoint Core.map :=
  IsRightAdjoint.mk ⟨ Grpd.forgetToCat , ⟨ adjunction ⟩ ⟩

/- This whole section is evil. -/
namespace IsPullback

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D) [F.ReflectsIsomorphisms]

variable {E : Type*} [Category E] (En : E ⥤ C) (Ew : E ⥤ Core D)
  (hE : En ⋙ F = Ew ⋙ inclusion D)

-- The equality transports in this dependent construction require reducible type transparency.
set_option backward.isDefEq.respectTransparency.types false in
def lift : E ⥤ Core C where
  obj x := ⟨ En.obj x ⟩
  map {x y} f := ⟨ @asIso _ _ _ _ (En.map f) $ by
    let f' : F.obj (En.obj x) ≅ F.obj (En.obj y) :=
      (eqToIso hE).app x ≪≫ (Ew.map f).iso ≪≫ (eqToIso hE.symm).app y
    have hnat : F.map (En.map f) ≫ _
      = _ ≫ (inclusion D).map (Ew.map f) :=
      (eqToHom hE).naturality f
    have h : F.map (En.map f) = f'.hom := by
      simp only [eqToHom_app, comp_eqToHom_iff] at hnat
      simp [hnat, f', Core.inclusion]
    have : IsIso (F.map (En.map f)) := by rw [h]; exact Iso.isIso_hom f'
    exact Functor.ReflectsIsomorphisms.reflects F (En.map f) ⟩

theorem fac_left : lift F En Ew hE ⋙ inclusion C = En := rfl

theorem fac_right : lift F En Ew hE ⋙ F.core = Ew := by
  apply comp_inclusion_injective
  exact hE

def universal : (lift : E ⥤ Core C) ×' lift ⋙ inclusion C = En ∧ lift ⋙ F.core = Ew ∧
    ∀ {l0 l1 : E ⥤ Core C}, l0 ⋙ inclusion C = l1 ⋙ inclusion C →
      l0 ⋙ F.core = l1 ⋙ F.core → l0 = l1 :=
  ⟨ lift F En Ew hE, fac_left _ _ _ _, fac_right _ _ _ _,
    fun hl _ => comp_inclusion_injective hl ⟩

end IsPullback

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D) [F.ReflectsIsomorphisms]

open _root_.CategoryTheory.Core.IsPullback

/--
  In the category of categories,
  if functor `F : C ⥤ D` reflects isomorphisms
  then taking the `Core` is pullback stable along `F`

  Core C ---- inclusion -----> C
    |                          |
    |                          |
    |                          |
  F.core                       F
    |                          |
    |                          |
    V                          V
  Core D ---- inclusion -----> D
-/
def isPullback_map'_self : Functor.IsPullback (inclusion C) F.core F (inclusion D) :=
  Functor.IsPullback.ofUniversal _ _ _ _ rfl (universal F) (universal F)

end Core

namespace ULift
namespace Core

variable {C : Type u} [Category.{v} C]

-- FIXME could be generalized?
-- def isoCoreULift :
--     Cat.of (ULift.{w} (Core C)) ≅
--       Cat.of (Core (ULift.{w} C)) where
--   hom := Cat.homOf (downFunctor ⋙ upFunctor.core)
--   inv := Cat.homOf (downFunctor.core ⋙ upFunctor)

end Core
end ULift

end CategoryTheory
