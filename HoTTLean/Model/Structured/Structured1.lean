import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import HoTTLean.ForMathlib
import HoTTLean.ForMathlib.Tactic.CategoryTheory.FunctorMap
import HoTTLean.ForMathlib.CategoryTheory.RepPullbackCone
import HoTTLean.ForMathlib.CategoryTheory.WeakPullback
import HoTTLean.ForMathlib.CategoryTheory.Polynomial
import HoTTLean.Model.Unstructured.UnstructuredUniverse
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
universe v u

noncomputable section

open CategoryTheory Limits Opposite Model.UnstructuredUniverse

namespace Model

namespace IdCommon
variable {Ctx : Type u} [Category Ctx] {U0 U1: Model.UnstructuredUniverse Ctx}
{Γ: Ctx} {A: Γ ⟶ U0.Ty} (a: Γ ⟶ U0.Tm)  (a_tp : a ≫ U0.tp = A)

def motiveCtx (IdTy: U0.ext A ⟶ U1.Ty) : Ctx := U1.ext IdTy

def motiveSubst (IdTy: U0.ext A ⟶ U1.Ty) {Δ} (σ : Δ ⟶ Γ)  :
    motiveCtx (substWk U0 σ A ≫ IdTy) ⟶ motiveCtx IdTy := by
  refine substWk _ (substWk _ σ _ _ (by simp)) _ _ ?_
  simp

def reflSubst (IdTy: U0.ext A ⟶ U1.Ty) (reflTm: Γ ⟶ U1.Tm)
              (reflTmTy: reflTm ≫ U1.tp = sec U0 A a (by simp[a_tp]) ≫ IdTy):
                Γ ⟶ motiveCtx IdTy :=
  U1.substCons (sec U0 A a (by simp[a_tp])) IdTy reflTm
  (by simp[reflTmTy])

end IdCommon

namespace UnstructuredId
variable {Ctx : Type u} [Category Ctx] {U0 U1: Model.UnstructuredUniverse Ctx}
{Γ: Ctx} (A: Γ ⟶ U0.Ty) (a: Γ ⟶ U0.Tm)  (a_tp : a ≫ U0.tp = A)
(i : PolymorphicIdIntro U0 U1)

def motiveCtx : Ctx := IdCommon.motiveCtx (i.weakenId a a_tp)

def motiveSubst {Δ} (σ : Δ ⟶ Γ) :
    motiveCtx (σ ≫ A) (σ ≫ a) (by cat_disch) i ⟶ motiveCtx A a a_tp i := by
   convert
    IdCommon.motiveSubst (i.weakenId a a_tp) σ
   simp[motiveCtx];
   congr
   simp[← i.Id_comp]

def reflSubst : Γ ⟶ i.motiveCtx a a_tp :=
 IdCommon.reflSubst a a_tp (i.weakenId a a_tp) (i.refl a a_tp)
 (by simp[← i.Id_comp])

end UnstructuredId


namespace StructuredId
variable {Ctx : Type u} [Category Ctx] {U: Model.UnstructuredUniverse Ctx}
{Γ: Ctx} (A: Γ ⟶ U.Ty) (a: Γ ⟶ U.Tm)  (a_tp : a ≫ U.tp = A)

structure IdIntro (M: Model.UnstructuredUniverse Ctx) where
  Id : M.ext M.tp ⟶ M.Ty
  refl : M.Tm ⟶ M.Tm
  refl_tp : refl ≫ M.tp =
    ((M.disp_pullback M.tp).lift (𝟙 M.Tm) (𝟙 M.Tm) (by simp)) ≫ Id

variable (i: IdIntro U)

def mkId (a0 a1 : Γ ⟶ U.Tm)
    (a0_tp_eq_a1_tp : a0 ≫ U.tp = a1 ≫ U.tp) :
    Γ ⟶ U.Ty :=
  (UnstructuredUniverse.disp_pullback _ U.tp).lift a1 a0 (by rw [a0_tp_eq_a1_tp]) ≫
  i.Id

theorem comp_mkId {Δ : Ctx} (σ : Δ ⟶ Γ)
    (a0 a1 : Γ ⟶ U.Tm) (eq : a0 ≫ U.tp = a1 ≫ U.tp) :
    σ ≫ mkId i a0 a1 eq =
      mkId i (σ ≫ a0) (σ ≫ a1) (by simp [eq]) := by
  simp [mkId]; rw [← Category.assoc]; congr 1
  apply  (UnstructuredUniverse.disp_pullback _ U.tp).hom_ext <;> simp


def mkRefl (a : Γ ⟶ U.Tm) : Γ ⟶ U.Tm :=
  a ≫ i.refl

--previously can write i.mkRefl, why I cannot do it here anymore?
theorem comp_mkRefl {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (a : Γ ⟶ U.Tm) :
    σ ≫ mkRefl i a = mkRefl i (σ ≫ a) := by
  simp [mkRefl]

def motiveCtx : Ctx := IdCommon.motiveCtx (mkId i (U.disp (a ≫ U.tp) ≫ a) (U.var _) (by simp))


abbrev endpts (a0 a1:Γ ⟶ U.Tm) (h: a0 ≫ U.tp = a1 ≫ U.tp): Γ ⟶ U.ext U.tp :=
   (U.disp_pullback U.tp).lift a0 a1 h


abbrev toTmTm : U.ext A ⟶ U.ext U.tp := (endpts (U.var A) (U.disp A ≫ a) (by simp[a_tp]))


def motiveSubst {Δ} (σ : Δ ⟶ Γ)  :
    motiveCtx (σ ≫ a) i ⟶ motiveCtx a i := by
  convert
    IdCommon.motiveSubst (toTmTm A a a_tp ≫ i.Id) σ
  simp[motiveCtx];
  congr 1
  · simp[a_tp]
  · --simp[← i.Id_comp]
    subst a_tp
    rw![Category.assoc]
    simp[heq_eq_eq]
    simp[mkId]
    simp[← Category.assoc]
    congr 1
    apply (U.disp_pullback _).hom_ext
    · simp
    · simp
  · simp[motiveCtx]
    congr 1
    subst a_tp
    simp[heq_eq_eq]
    simp[mkId]


def reflSubst : Γ ⟶ motiveCtx a i := by
  convert
   IdCommon.reflSubst a a_tp (toTmTm A a a_tp ≫ i.Id) (a ≫ i.refl)
    (by simp[i.refl_tp]
        simp[← Category.assoc]
        congr 1
        apply (U.disp_pullback _).hom_ext
        · simp
        simp
      )
  simp[motiveCtx]
  congr 1
  subst a_tp
  simp[mkId]


end StructuredId


end Model
