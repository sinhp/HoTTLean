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

--lemma reflSubst_var

@[reassoc (attr := simp)]
lemma reflSubst_comp_motiveSubst
  (IdTy: U0.ext A ⟶ U1.Ty) (reflTm: Γ ⟶ U1.Tm)
  (reflTmTy: reflTm ≫ U1.tp = sec U0 A a (by simp[a_tp]) ≫ IdTy)
  {Δ} (σ : Δ ⟶ Γ) :
    reflSubst (A:= σ ≫ A) (σ ≫ a) (by simp[a_tp]) (substWk U0 σ A ≫ IdTy) (σ ≫ reflTm)
    (by simp[reflTmTy]
        simp[← Category.assoc,sec_substWk]) ≫
    motiveSubst IdTy σ =
    σ ≫ reflSubst a a_tp IdTy reflTm reflTmTy := by
  apply (disp_pullback ..).hom_ext <;> simp[reflSubst,motiveSubst,sec_substWk]

end IdCommon

namespace UnstructuredId
variable {Ctx : Type u} [Category Ctx] {U0 U1: Model.UnstructuredUniverse Ctx}
{Γ: Ctx} {A: Γ ⟶ U0.Ty} (a: Γ ⟶ U0.Tm)  (a_tp : a ≫ U0.tp = A)
(i : PolymorphicIdIntro U0 U1)

def motiveCtx : Ctx := IdCommon.motiveCtx (i.weakenId a a_tp)

def motiveSubst {Δ} (σ : Δ ⟶ Γ) :
    motiveCtx (A:= σ ≫ A) (σ ≫ a) (by simp[a_tp,Category.assoc]) i ⟶ motiveCtx a a_tp i := by
   convert
    IdCommon.motiveSubst (i.weakenId a a_tp) σ
   simp[motiveCtx];
   congr 1
   simp[← i.Id_comp]


def reflSubst : Γ ⟶ motiveCtx a a_tp i:=
 IdCommon.reflSubst a a_tp (i.weakenId a a_tp) (i.refl a a_tp)
 (by simp[← i.Id_comp])

--abbrev IdTy := (i.weakenId a a_tp)

@[reassoc (attr := simp)]
lemma reflSubst_comp_motiveSubst  {Δ} (σ : Δ ⟶ Γ) :
    reflSubst (A:= σ ≫ A) (σ ≫ a) (by simp[a_tp]) i ≫ motiveSubst a a_tp i σ  =
    σ ≫ reflSubst (A:= A) a a_tp i := by
  simp[reflSubst,motiveSubst]
  have e :=
    IdCommon.reflSubst_comp_motiveSubst a a_tp (i.weakenId a a_tp) (i.refl a a_tp)
    (by simp[← i.Id_comp]) σ
  convert e <;> simp[←i.Id_comp,←i.refl_comp,a_tp,motiveCtx]


structure PolymorphicIdElim (U2 : UnstructuredUniverse Ctx) where
  (j : ∀ {Γ} {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)
    (C : motiveCtx a a_tp i ⟶ U2.Ty) (c : Γ ⟶ U2.Tm),
    (c ≫ U2.tp = (reflSubst a a_tp i) ≫ C) → (motiveCtx a a_tp i ⟶ U2.Tm))
  (comp_j : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm)
    (a_tp : a ≫ U0.tp = A) (C : motiveCtx a a_tp i ⟶ U2.Ty) (c : Γ ⟶ U2.Tm)
    (c_tp : c ≫ U2.tp = (reflSubst a a_tp i) ≫ C),
    j (σ ≫ a) (by cat_disch) (motiveSubst a a_tp i σ ≫ C) (σ ≫ c)
      (by simp[c_tp]) =
    motiveSubst a a_tp i σ ≫ j a a_tp C c c_tp)
  (j_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)
    (C : motiveCtx a a_tp i ⟶ U2.Ty) (c : Γ ⟶ U2.Tm)
    (c_tp : c ≫ U2.tp = (reflSubst a a_tp i) ≫ C),
    j a a_tp C c c_tp ≫ U2.tp = C)
  (reflSubst_j : ∀ {Γ} {A : Γ ⟶ U0.Ty} (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A)
    (C : motiveCtx a a_tp i ⟶ U2.Ty) (c : Γ ⟶ U2.Tm)
    (c_tp : c ≫ U2.tp = (reflSubst a a_tp i) ≫ C),
    reflSubst a a_tp i ≫ j a a_tp C c c_tp = c)


end UnstructuredId


namespace StructuredId
variable {Ctx : Type u} [Category Ctx] {U: Model.UnstructuredUniverse Ctx}
{Γ: Ctx} {A: Γ ⟶ U.Ty} (a: Γ ⟶ U.Tm)  (a_tp : a ≫ U.tp = A)

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

#check substCons
/-def substCons {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty)
    (t : Δ ⟶ M.Tm) (t_tp : t ≫ M.tp = σ ≫ A) :
    Δ ⟶ M.ext A :=
  (M.disp_pullback A).lift t σ t_tp
-/
abbrev toTmTm : U.ext A ⟶ U.ext U.tp :=
 (U.disp_pullback U.tp).lift (U.var A) (U.disp A ≫ a) (by simp[a_tp])
--(endpts (U.var A) (U.disp A ≫ a) (by simp[a_tp]))
--todo: what is it in terms of substCons?

def motiveSubst {Δ} (σ : Δ ⟶ Γ)  :
    motiveCtx (σ ≫ a) i ⟶ motiveCtx a i := by
  convert
    IdCommon.motiveSubst (toTmTm  a a_tp ≫ i.Id) σ
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
   IdCommon.reflSubst a a_tp (toTmTm a a_tp ≫ i.Id) (a ≫ i.refl)
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

-- Q: how to make i the first explicit argument and enable writing i.motiveCtx?
--stupid long proof
@[reassoc (attr := simp)]
lemma reflSubst_comp_motiveSubst  {Δ} (σ : Δ ⟶ Γ) :
    reflSubst (A:= σ ≫ A) (σ ≫ a) (by simp[a_tp]) i ≫ motiveSubst a a_tp i σ  =
    σ ≫ reflSubst (A:= A) a a_tp i := by
  simp[reflSubst,motiveSubst]
  have e :=
    IdCommon.reflSubst_comp_motiveSubst a a_tp (toTmTm a a_tp ≫ i.Id) (a ≫ i.refl)
    (by simp[i.refl_tp]
        simp[← Category.assoc]
        congr 1
        apply (disp_pullback ..).hom_ext <;> simp --toTmTm + endpts not good API, perhaps stick to substCons
        ) σ
  convert e <;> simp[motiveCtx]
  · congr 1
    simp[mkId]
    subst a_tp
    congr 1
    --do not think mkId is good design either, without lemmas
  · subst a_tp
    congr 1
    · simp--this is assoc...
    simp[mkId]
    simp[← Category.assoc]
    congr 1
    · simp
    simp[substWk]
    rw![Category.assoc]
    simp[heq_eq_eq]
    apply (disp_pullback ..).hom_ext <;> simp
  · simp[mkId]
    rw![a_tp]
  · simp[substWk,substCons]
    rw![a_tp]
    congr! 1
    simp[← Category.assoc]
    congr 1
    apply (disp_pullback ..).hom_ext  <;> simp
  · simp[mkId]
    rw![a_tp]


end StructuredId


end Model
