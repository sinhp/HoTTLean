import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Category.Cat.Limit

import HoTTLean.Model.Unstructured.UnstructuredUniverse
import HoTTLean.Grothendieck.Groupoidal.IsPullback
import HoTTLean.Groupoids.IsPullback

/-!
Here we construct universes for the groupoid natural model.
-/

set_option backward.isDefEq.respectTransparency false

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory Limits Model UnstructuredUniverse
  Functor.Groupoidal GroupoidModel.Ctx GroupoidModel.U

namespace GroupoidModel

open U

/-- The universe the classifies `v`-large terms and types.
  The π-clan we use is the set of groupoid isofibrations.
-/
@[simps]
def U : UnstructuredUniverse Grpd where
  Ty := Ty.{v}
  Tm := Tm.{v}
  tp := tp
  ext A := ext A
  disp A := disp A
  var A := var A
  disp_pullback A := GroupoidModel.IsPullback.disp_pullback A

namespace U

open MonoidalCategory

def asSmallClosedType : (tensorUnit _ : Ctx) ⟶ Ty.{v+1, max u (v+2)} :=
  toCoreAsSmallEquiv.symm ((Functor.const _).obj
    (Grpd.of (Core (AsSmall.{v+1} Grpd.{v,v}))))

def isoExtAsSmallClosedTypeHom :
    Core (AsSmall.{max u (v+2)} Grpd.{v,v})
    ⥤ ∫(toCoreAsSmallEquiv (asSmallClosedType.{v, max u (v + 2)})) where
  obj X := objMk ⟨⟨⟩⟩ ⟨AsSmall.up.obj (AsSmall.down.obj X.of)⟩
  map {X Y} F := homMk (𝟙 _) ⟨{
    hom := AsSmall.up.map (AsSmall.down.map F.iso.hom)
    inv := AsSmall.up.map (AsSmall.down.map (F.iso.inv))
    hom_inv_id := by
      simp only [← Functor.map_comp, Iso.hom_inv_id]
      rfl
    inv_hom_id := by
      simp only [← Functor.map_comp, Iso.inv_hom_id]
      rfl }⟩

def isoExtAsSmallClosedTypeInv :
    ∫(toCoreAsSmallEquiv (asSmallClosedType.{v, max u (v + 2)})) ⥤
    Core (AsSmall.{max u (v+2)} Grpd.{v,v}) where
  obj X := ⟨AsSmall.up.obj (AsSmall.down.obj X.fiber.of)⟩
  map {X Y} F := ⟨{
    hom := AsSmall.up.map
      (AsSmall.down.map F.fiber.iso.hom)
    inv := AsSmall.up.map
      (AsSmall.down.map F.fiber.iso.inv)
    hom_inv_id := by
      simp only [← Functor.map_comp, Iso.hom_inv_id]
      rfl
    inv_hom_id := by
      simp only [← Functor.map_comp, Iso.inv_hom_id]
      rfl }⟩

def isoExtAsSmallClosedType :
    Ty.{v,max u (v+2)}
    ≅ U.{v+1,max u (v+2)}.ext U.asSmallClosedType.{v, max u (v+2)} where
  hom := (Grpd.homOf isoExtAsSmallClosedTypeHom.{v,u})
  inv := (Grpd.homOf isoExtAsSmallClosedTypeInv.{v,u})
  hom_inv_id := rfl
  inv_hom_id := rfl

end U

def uHomSeqObjs (i : Nat) (h : i < 4) : UnstructuredUniverse Grpd.{4} :=
  match i with
  | 0 => U.{0,4}
  | 1 => U.{1,4}
  | 2 => U.{2,4}
  | 3 => U.{3,4}
  | (n+4) => by omega

open CategoryTheory Opposite

section

variable {Γ : Grpd} {C : Type (v+1)} [Category.{v} C] {Δ : Grpd} (σ : Δ ⟶ Γ)

namespace U

theorem substWk_eq (A : Γ ⟶ U.Ty.{v}) (σA : Δ ⟶ U.Ty.{v}) (eq) :
    U.substWk σ A σA eq =
    map (eqToHom (by subst eq; rfl)) ⋙ pre (toCoreAsSmallEquiv A) σ := by
  subst σA
  apply (U.disp_pullback A).hom_ext
  · rw [substWk_var]
    simp [var, Grpd.comp_eq_comp]
    simp only [map_id_eq]
    change _ = pre (toCoreAsSmallEquiv A) σ ⋙
      toCoreAsSmallEquiv.symm (toPGrpd (toCoreAsSmallEquiv A))
    rw [← toCoreAsSmallEquiv_symm_apply_comp_left, pre_toPGrpd]
    rfl
  · rw [substWk_disp]
    simp [Grpd.comp_eq_comp, Functor.assoc]
    erw [pre_comp_forget, ← Functor.assoc, map_forget]

@[simp] theorem sec_eq {Γ : Ctx} (α : Γ ⟶ U.{v}.Tm) (A : Γ ⟶ U.{v}.Ty) (hα : α ≫ U.tp = A) :
    U.sec _ α hα = sec (toCoreAsSmallEquiv A) (toCoreAsSmallEquiv α)
    (by rw [← hα, Grpd.comp_eq_comp, tp, toCoreAsSmallEquiv_apply_comp_right]) := by
  apply (U.disp_pullback _).hom_ext
  . erw [sec_var, U_var, var, Grpd.comp_eq_comp,
      ← toCoreAsSmallEquiv_symm_apply_comp_left, Equiv.eq_symm_apply, sec_toPGrpd]
    rfl
  . rw [sec_disp]
    rfl

end U

end

end GroupoidModel

end
