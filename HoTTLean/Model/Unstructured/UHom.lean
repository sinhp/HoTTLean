import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import HoTTLean.ForMathlib
import HoTTLean.Model.Unstructured.UnstructuredUniverse

/-! Morphisms of unstructured models, and Russell-universe embeddings. -/

universe v u

noncomputable section

open CategoryTheory Opposite MonoidalCategory

namespace Model

namespace UnstructuredUniverse

variable {Ctx : Type u} [Category Ctx] (M : UnstructuredUniverse Ctx)

open ChosenTerminal

macro "by>" s:tacticSeq : term => `(by as_aux_lemma => $s)

structure Hom (M N : UnstructuredUniverse Ctx) where
  mapTm : M.Tm ⟶ N.Tm
  mapTy : M.Ty ⟶ N.Ty
  pb : IsPullback mapTm M.tp N.tp mapTy

def Hom.id (M : UnstructuredUniverse Ctx) : Hom M M where
  mapTm := 𝟙 _
  mapTy := 𝟙 _
  pb := IsPullback.of_id_fst

def Hom.comp {M N O : UnstructuredUniverse Ctx} (α : Hom M N) (β : Hom N O) : Hom M O where
  mapTm := α.mapTm ≫ β.mapTm
  mapTy := α.mapTy ≫ β.mapTy
  pb := α.pb.paste_horiz β.pb

def Hom.comp_assoc {M N O P : UnstructuredUniverse Ctx} (α : Hom M N) (β : Hom N O) (γ : Hom O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp]

/-- Morphism into the representable natural transformation `M`
from the pullback of `M` along a type. -/
protected def pullbackHom (M : UnstructuredUniverse Ctx) {Γ : Ctx} (A : (Γ) ⟶ M.Ty) :
    Hom (M.pullback A) M where
  mapTm := M.var A
  mapTy := A
  pb := M.disp_pullback A

/-- Given `M : Universe`, a semantic type `A : (Γ) ⟶ M.Ty`,
and a substitution `σ : Δ ⟶ Γ`, construct a Hom for the substitution `A[σ]`.
-/
def Hom.subst (M : UnstructuredUniverse Ctx)
    {Γ Δ : Ctx} (A : (Γ) ⟶ M.Ty) (σ : Δ ⟶ Γ) :
    Hom (M.pullback ((σ) ≫ A)) (M.pullback A) :=
  let Aσ := (σ) ≫ A
  { mapTm :=
    (M.disp_pullback A).lift (M.var Aσ) (M.disp Aσ ≫ σ) (by aesop_cat)
    mapTy := (σ)
    pb := by
      convert IsPullback.of_right' (M.disp_pullback Aσ) (M.disp_pullback A)}

@[simp] def Hom.extIsoExt {M N : UnstructuredUniverse Ctx} (h : Hom M N)
    {Γ} (A : Γ ⟶ M.Ty) : (N.ext (A ≫ h.mapTy)) ≅ (M.ext A) :=
  IsPullback.isoIsPullback N.Tm Γ (N.disp_pullback (A ≫ h.mapTy))
  (IsPullback.paste_horiz (M.disp_pullback A) h.pb)

variable [ChosenTerminal Ctx]

/-- A Russell universe embedding is a hom of natural models `M ⟶ N`
such that types in `M` correspond to terms of a universe `U` in `N`.

These don't form a category since `UHom.id M` is essentially `Type : Type` in `M`.

Note this doesn't need to extend `Hom` as none of its fields are used;
it's just convenient to pack up the data. -/
structure UHom (M N : UnstructuredUniverse Ctx) extends Hom M N where
  U : terminal ⟶ N.Ty
  asTm : M.Ty ⟶ N.Tm
  U_pb : IsPullback
            /- m.Ty -/           asTm /- N.Tm -/
    (isTerminal.from M.Ty)         N.tp
             /- ⊤ -/               U  /- N.Ty -/

def UHom.ofTyIsoExt
    {M N : UnstructuredUniverse Ctx}
    (H : Hom M N) {U : (𝟭_ Ctx) ⟶ N.Ty} (i : M.Ty ≅ (N.ext U)) :
    UHom M N where
  __ := H
  U := U
  asTm := i.hom ≫ N.var U
  U_pb := by
    convert IsPullback.of_iso_isPullback (N.disp_pullback _) i
    apply isTerminal.hom_ext

def UHom.comp {M N O : UnstructuredUniverse Ctx} (α : UHom M N) (β : UHom N O) : UHom M O where
  __ := Hom.comp α.toHom β.toHom
  U := α.U ≫ β.mapTy
  asTm := α.asTm ≫ β.mapTm
  U_pb := α.U_pb.paste_horiz β.pb

def UHom.comp_assoc {M N O P : UnstructuredUniverse Ctx} (α : UHom M N) (β : UHom N O) (γ : UHom O P) :
    comp (comp α β) γ = comp α (comp β γ) := by
  simp [comp, Hom.comp]

def UHom.wkU {M N : UnstructuredUniverse Ctx} (Γ : Ctx) (α : UHom M N) : (Γ) ⟶ N.Ty :=
  isTerminal.from Γ ≫ α.U

@[reassoc (attr := simp)]
theorem UHom.comp_wkU {M N : UnstructuredUniverse Ctx} {Δ Γ : Ctx} (α : UHom M N) (f : (Δ) ⟶ (Γ)) :
    f ≫ α.wkU Γ = α.wkU Δ := by
  simp [wkU]

/- Sanity check:
construct a `UHom` into a natural model with a Tarski universe. -/
def UHom.ofTarskiU (M : UnstructuredUniverse Ctx) (U : (𝟭_ Ctx) ⟶ M.Ty) (El : (M.ext U) ⟶ M.Ty) :
    UHom (M.pullback El) M where
  __ := M.pullbackHom El
  U
  asTm := M.var U
  U_pb := (M.disp_pullback U).of_iso
      (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
      (Iso.refl _)
      (by simp) (isTerminal.hom_ext ..)
      (by simp) (by simp)

/-! ## Universe embeddings -/

variable (Ctx) in
/-- A sequence of Russell universe embeddings. -/
structure UHomSeq where
  /-- Number of embeddings in the sequence,
  or one less than the number of models in the sequence. -/
  length : Nat
  objs (i : Nat) (h : i < length + 1) : UnstructuredUniverse Ctx
  homSucc' (i : Nat) (h : i < length) : UHom (objs i <| by omega) (objs (i + 1) <| by omega)

namespace UHomSeq

variable (s : UHomSeq Ctx)

instance : GetElem (UHomSeq Ctx) Nat (UnstructuredUniverse Ctx) (fun s i => i < s.length + 1) where
  getElem s i h := s.objs i h

def homSucc (i : Nat) (h : i < s.length := by get_elem_tactic) : UHom s[i] s[i+1] :=
  s.homSucc' i h

/-- Composition of embeddings between `i` and `j` in the chain. -/
def hom (s : UHomSeq Ctx) (i j : Nat) (ij : i < j := by omega)
    (jlen : j < s.length + 1 := by get_elem_tactic) : UHom s[i] s[j] :=
  if h : i + 1 = j then
    h ▸ s.homSucc i
  else
    (s.homSucc i).comp <| s.hom (i+1) j
termination_by s.length - i

theorem hom_comp_trans (s : UHomSeq Ctx) (i j k : Nat) (ij : i < j) (jk : j < k)
    (klen : k < s.length + 1) :
    (s.hom i j ij).comp (s.hom j k jk) = s.hom i k (ij.trans jk) := by
  conv_rhs => unfold hom
  conv in s.hom i j _ => unfold hom
  split_ifs
  all_goals try omega
  . rename_i h _
    cases h
    simp
  . rw [UHom.comp_assoc, hom_comp_trans]
termination_by s.length - i

/- It is useful to be able to talk about the underlying sequence of Homs in a UHomSeq.
  For such a sequence, we can loosen the condition i < j to i <= j
  without creating Type in Type.
  This is helpful for defining `s[i] → s[max i j]` for Pi and Sigma below.
-/
def homOfLe (i j : Nat) (ij : i <= j := by omega)
    (jlen : j < s.length + 1 := by get_elem_tactic) : Hom s[i] s[j] :=
  if h : i = j then h ▸ Hom.id s[i]
  else
    (s.hom i j (by omega) _).toHom

/-- For `i ≤ j` and a term `t` at level `j`,
if the type of `t` is lifted from level `i`,
then `t` is a lift of a term at level `i`. -/
def unlift (i j) (ij : i ≤ j := by omega) (jlen : j < s.length + 1 := by get_elem_tactic)
    {Γ} (A : Γ ⟶ (s[i]'(ij.trans_lt jlen)).Ty) (t : Γ ⟶ s[j].Tm)
    (eq : t ≫ s[j].tp = A ≫ (s.homOfLe i j).mapTy) :
    Γ ⟶ (s[i]'(ij.trans_lt jlen)).Tm :=
  (s.homOfLe i j).pb.lift t A eq

@[simp]
theorem unlift_tp {i j ij jlen Γ A}
    {t : (Γ) ⟶ _} (eq : t ≫ s[j].tp = A ≫ (s.homOfLe i j).mapTy) :
    s.unlift i j ij jlen A t eq ≫ (s[i]'(ij.trans_lt jlen)).tp = A := by
  simp [unlift]

@[simp]
theorem unlift_lift {i j ij jlen Γ A}
    {t : (Γ) ⟶ _} (eq : t ≫ s[j].tp = A ≫ (s.homOfLe i j).mapTy) :
    s.unlift i j ij jlen A t eq ≫ (s.homOfLe i j).mapTm = t := by
  simp [unlift]

def unliftVar (i j) (ij : i ≤ j := by omega) (jlen : j < s.length + 1 := by get_elem_tactic)
    {Γ} (A : (Γ) ⟶ (s[i]'(ij.trans_lt jlen)).Ty)
    {A' : (Γ) ⟶ s[j].Ty} (eq : A ≫ (s.homOfLe i j).mapTy = A') :
    (s[j].ext A') ⟶ (s[i]'(ij.trans_lt jlen)).Tm :=
  s.unlift i j ij jlen ((s[j].disp _) ≫ A) (s[j].var _) (by simp [eq])

@[simp]
theorem unliftVar_tp {i j ij jlen Γ A} {A' : (Γ) ⟶ s[j].Ty}
    (eq : A ≫ (s.homOfLe i j).mapTy = A') :
    s.unliftVar i j ij jlen A eq ≫ (s[i]'(ij.trans_lt jlen)).tp = (s[j].disp _) ≫ A := by
  simp [unliftVar]

theorem substCons_unliftVar {i j ij jlen Γ A} {A' : (Γ) ⟶ s[j].Ty}
    {eq : A ≫ (s.homOfLe i j).mapTy = A'}
    {Δ} {σ : Δ ⟶ Γ} {t : (Δ) ⟶ _}
    (t_tp : t ≫ (s[i]'(ij.trans_lt jlen)).tp = (σ) ≫ A) :
    (s[j].substCons σ A' (t ≫ (s.homOfLe i j ij jlen).mapTm) (by
      simp [*]
      conv_lhs => rhs; apply (s.homOfLe i j).pb.w
      subst A'; rw [← Category.assoc, ← Category.assoc, ← t_tp]))
    ≫ s.unliftVar i j ij jlen A eq = t := by
  simp [unlift, unliftVar]; apply (s.homOfLe i j).pb.hom_ext <;> simp [*]

/--
TODO: Consider generalising to just UHom?
Convert a map into the `i`th type classifier into a a term of the
`i+1`th term classifier, that is a term of the `i`th universe.
It is defined by composition with the first projection of the pullback square
               v
     s[i].Ty ----> s[i+1].Tm
     ^    |          |
  A /     |   p.b.   |
   /      |          |
  /       V          V
(Γ) ---> 1 -----> s[i+1].Ty
              U_i
-/
def code {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : (Γ) ⟶ s[i].Ty) :
    (Γ) ⟶ s[i+1].Tm :=
  A ≫ (s.homSucc i).asTm

@[simp]
theorem code_tp {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : (Γ) ⟶ s[i].Ty) :
    s.code ilen A ≫ s[i+1].tp = (s.homSucc i).wkU Γ := by
  simp [code, (s.homSucc i).U_pb.w, UHom.wkU]

@[reassoc]
theorem comp_code {Δ Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length)
    (σ : (Δ) ⟶ (Γ)) (A : (Γ) ⟶ s[i].Ty) :
    σ ≫ s.code ilen A = s.code ilen (σ ≫ A) := by
  simp [code]

/--
TODO: Consider generalising to just UHom?
Convert a a term of the `i`th universe (it is a `i+1` level term) into
a map into the `i`th type classifier.
It is the unique map into the pullback
             a
(Γ) -----------------¬
‖  -->          v     V
‖    s[i].Ty ----> s[i+1].Tm
‖         |          |
‖         |   p.b.   |
‖         |          |
‖         V          V
(Γ) ---> 1 -----> s[i+1].Ty
              U_i
-/
def el (s : UHomSeq Ctx) {Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (a : (Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    (Γ) ⟶ s[i].Ty :=
  (s.homSucc i).U_pb.lift a (isTerminal.from (Γ)) (by rw [a_tp, UHom.wkU])

@[reassoc]
theorem comp_el (s : UHomSeq Ctx) {Δ Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (σ : (Δ) ⟶ (Γ)) (a : (Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    σ ≫ s.el ilen a a_tp = s.el ilen (σ ≫ a) (by simp [a_tp]) :=
  (s.homSucc i).U_pb.hom_ext (by simp [el]) (by simp)

@[simp]
lemma el_code {Γ : Ctx} {i : Nat} (s : UHomSeq Ctx) (ilen : i < s.length) (A : (Γ) ⟶ s[i].Ty) :
    el s ilen (code s ilen A) (code_tp _ _ _) = A :=
  (s.homSucc i).U_pb.hom_ext (by simp [el, code]) (by simp)

@[simp]
lemma code_el (s : UHomSeq Ctx) {Γ : Ctx} {i : Nat} (ilen : i < s.length)
    (a : (Γ) ⟶ s[i+1].Tm) (a_tp : a ≫ s[i+1].tp = (s.homSucc i).wkU Γ) :
    code s ilen (el s ilen a a_tp) = a := by
  simp [code, el]

-- Sadly, we have to spell out `ilen` and `jlen` due to
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Optional.20implicit.20argument
variable {i j : Nat} (ilen : i < s.length + 1) (jlen : j < s.length + 1)

/-! ## Pi -/

/-- The data of `Pi` and `lam` formers at the `max` of any two universes.
This interprets
```
Γ ⊢ᵢ A type  Γ.A ⊢ⱼ B type
--------------------------
Γ ⊢ₘₐₓ₍ᵢ,ⱼ₎ ΠA. B type
``` -/
class PiSeq (s : UHomSeq Ctx) where
  polyPi (i j : Nat)
    (ilen : i < s.length + 1 := by get_elem_tactic)
    (jlen : j < s.length + 1 := by get_elem_tactic) :
    PolymorphicPi s[i] s[j] s[max i j]

/-! ## Sigma -/

/-- The data of `Sig` and `pair` formers at the `max` of any two universes. -/
class SigSeq (s : UHomSeq Ctx) where
  polySig (i j : Nat)
    (ilen : i < s.length + 1 := by get_elem_tactic)
    (jlen : j < s.length + 1 := by get_elem_tactic) :
    PolymorphicSigma s[i] s[j] s[max i j]

#exit
/-! ## Identity types -/

class IdSeq (s : UHomSeq Ctx) where
  nmII (i : Nat) (ilen : i < s.length + 1 := by get_elem_tactic) : IdIntro s[i]
  nmIEB (i : Nat) (ilen : i < s.length + 1 := by get_elem_tactic) :
    IdElimBase (nmII i ilen)
  nmId (i j : Nat) (ilen : i < s.length + 1 := by get_elem_tactic)
    (jlen : j < s.length + 1 := by get_elem_tactic) : Id (nmIEB i ilen) s[j]

section Id
open IdSeq
variable [s.IdSeq]

/--
```
Γ ⊢ᵢ A  Γ ⊢ᵢ a0, a1 : A
-----------------------
Γ ⊢ᵢ Id(A, a0, a1)
``` -/
def mkId {Γ : Ctx} (A : (Γ) ⟶ s[i].Ty) (a0 a1 : (Γ) ⟶ s[i].Tm)
    (a0_tp : a0 ≫ s[i].tp = A) (a1_tp : a1 ≫ s[i].tp = A) :
    (Γ) ⟶ s[i].Ty :=
  (nmII i).mkId a0 a1 (a1_tp ▸ a0_tp)

theorem comp_mkId {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : (Γ) ⟶ s[i].Ty) (σA) (eq : (σ) ≫ A = σA)
    (a0 a1 : (Γ) ⟶ s[i].Tm)
    (a0_tp : a0 ≫ s[i].tp = A) (a1_tp : a1 ≫ s[i].tp = A) :
    (σ) ≫ s.mkId ilen A a0 a1 a0_tp a1_tp =
      s.mkId ilen σA ((σ) ≫ a0) ((σ) ≫ a1)
        (by simp [eq, a0_tp]) (by simp [eq, a1_tp]) := by
  simp [mkId, IdIntro.mkId]
  rw [← Category.assoc]; congr 1
  apply (nmII i).isKernelPair.hom_ext <;> simp

/--
```
Γ ⊢ᵢ t : A
-----------------------
Γ ⊢ᵢ refl(t) : Id(A, t, t)
``` -/
def mkRefl {Γ : Ctx} (t : (Γ) ⟶ s[i].Tm) : (Γ) ⟶ s[i].Tm :=
  (nmII i).mkRefl t

theorem comp_mkRefl {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (t : (Γ) ⟶ s[i].Tm) :
    (σ) ≫ s.mkRefl ilen t = s.mkRefl ilen ((σ) ≫ t) := by
  simp [mkRefl, IdIntro.mkRefl]

@[simp]
theorem mkRefl_tp {Γ : Ctx} (A : (Γ) ⟶ s[i].Ty)
    (t : (Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A) :
    s.mkRefl ilen t ≫ s[i].tp = s.mkId ilen A t t t_tp t_tp :=
  (nmII i).mkRefl_tp t

/--
```
Γ ⊢ᵢ t : A
-----------------------
Γ ⊢ᵢ idRec(t) : Id(A, t, t)
``` -/
def mkIdRec {Γ : Ctx} (A : (Γ) ⟶ s[i].Ty)
    (t : (Γ) ⟶ s[i].Tm) (t_tp : t ≫ s[i].tp = A)
    (B : (s[i].ext A) ⟶ s[i].Ty)
    (B_eq : s.mkId ilen ((s[i].disp A) ≫ A)
      ((s[i].disp A) ≫ t) (s[i].var A) (by> simp [*]) (var_tp ..) = B)
    (M : (s[i].ext B) ⟶ s[j].Ty)
    (r : (Γ) ⟶ s[j].Tm) (r_tp : r ≫ s[j].tp =
      (substCons _ (s[i].sec A t t_tp) _ (s.mkRefl ilen t)
        (by> simp [comp_mkId, t_tp, ← B_eq])) ≫ M)
    (u : (Γ) ⟶ s[i].Tm) (u_tp : u ≫ s[i].tp = A)
    (h : (Γ) ⟶ s[i].Tm) (h_tp : h ≫ s[i].tp = s.mkId ilen A t u t_tp u_tp) :
    (Γ) ⟶ s[j].Tm := by sorry
  -- refine (nmId i j).toId'.mkJ t
  --   ((substWk _ (substWk _ (𝟙 _) _ _ (by simp [t_tp])) _ _ ?_) ≫ M)
  --   r ?_ u (t_tp ▸ u_tp) h ?_
  -- · simp [← B_eq, comp_mkId, ← mkId.eq_def]; congr 1 <;> simp [t_tp, substWk]
  -- · simp [r_tp]; rw [← Functor.map_comp_assoc]; congr 1
  --   apply (s[i].disp_pullback _).hom_ext <;> simp [IdIntro.reflSubst, mkRefl, substWk, sec]
  -- · simp [h_tp, mkId, IdIntro.mkId]

theorem comp_mkIdRec {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : (Γ) ⟶ s[i].Ty) (σA) (σA_eq : (σ) ≫ A = σA)
    (t t_tp B B_eq σB) (σB_eq : (s[i].substWk σ _ _ σA_eq) ≫ B = σB)
    (M) (r : (Γ) ⟶ (s[j]'jlen).Tm) (r_tp u u_tp h h_tp) :
    (σ) ≫ s.mkIdRec ilen jlen A t t_tp B B_eq M r r_tp u u_tp h h_tp =
    s.mkIdRec ilen jlen σA ((σ) ≫ t) (by> simp [t_tp, ← σA_eq])
      σB (by>
        simp [← σB_eq, ← B_eq]
        rw [comp_mkId]; congr! 1
        · rw [← Category.assoc, ← Category.assoc, substWk_disp]
        · simp
        · rw [← Category.assoc, substWk_disp]; simp [σA_eq])
      ((s[i].substWk (s[i].substWk σ _ _ σA_eq) _ _ σB_eq) ≫ M)
      ((σ) ≫ r) (by>
        -- simp [*]
        -- simp only [← Category.assoc]; congr! 2
        -- simp [comp_substCons, comp_sec, substWk, comp_mkRefl]
        sorry)
      ((σ) ≫ u) (by> simp [*])
      ((σ) ≫ h) (by> simp [*, comp_mkId]) := by sorry
  -- simp [mkIdRec, Id'.mkJ]
  -- change let σ' := _; _ = (σ') ≫ _; intro σ'
  -- refine .trans ?h1 (congr((σ') ≫ $((nmId i j).comp_j σ t ((?v) ≫ M) r ?h2)).trans ?h3)
  -- case v =>
  --   exact s[i].substWk (s[i].substWk (𝟙 _) _ _ (by simp [t_tp])) _ _ (by
  --     simp [← B_eq, comp_mkId, ← mkId.eq_def]
  --     congr! 1 <;>
  --     · subst t_tp; rw [substWk_disp_functor_map_assoc]; simp)
  -- · simp [← Category.assoc]; congr 1
  --   apply (s[i].disp_pullback _).hom_ext <;> simp [IdIntro.motiveSubst]
  --   · dsimp [Id'.endPtSubst, σ']
  --     simp only [substCons_var]
  --   · rw [substWk_disp_functor_map]
  --     apply (s[i].disp_pullback _).hom_ext <;> simp [Id'.endPtSubst, σ', substWk_disp_functor_map]
  -- · simp [r_tp]
  --   simp [← Category.assoc]; congr 1
  --   apply (s[i].disp_pullback _).hom_ext <;> simp [IdIntro.reflSubst]; rfl
  --   rw [substWk_disp_functor_map, substCons_disp_functor_map_assoc]
  --   apply (s[i].disp_pullback _).hom_ext <;> simp
  --   simp [substWk_disp_functor_map]
  -- · congr 2; simp only [← Category.assoc]; congr 1
  --   apply (s[i].disp_pullback _).hom_ext <;> simp [IdIntro.motiveSubst]
  --   apply (s[i].disp_pullback _).hom_ext <;> simp
  --   · simp [substWk_disp_functor_map_assoc]
  --   · simp [substWk_disp_functor_map, substWk_disp_functor_map_assoc]

@[simp]
theorem mkIdRec_tp {Γ : Ctx} (A : (Γ) ⟶ s[i].Ty)
    (t t_tp B B_eq M) (r : (Γ) ⟶ s[j].Tm) (r_tp u u_tp h h_tp) :
    s.mkIdRec ilen jlen A t t_tp B B_eq M r r_tp u u_tp h h_tp ≫ s[j].tp =
      (substCons _ (s[i].sec _ u u_tp) _ h (by> simp [h_tp, comp_mkId, ← B_eq])) ≫ M := by
  -- simp [mkIdRec, Id'.mkJ_tp]; rw [← Category.assoc]; congr 1
  -- apply (s[i].disp_pullback _).hom_ext <;> simp [Id'.endPtSubst, sec, substWk]
  sorry

@[simp]
theorem mkIdRec_mkRefl {Γ : Ctx} (A : (Γ) ⟶ s[i].Ty)
    (t t_tp B B_eq M) (r : (Γ) ⟶ s[j].Tm) (r_tp) :
    s.mkIdRec ilen jlen A t t_tp B B_eq M r r_tp t t_tp
      (s.mkRefl ilen t) (s.mkRefl_tp ilen _ t t_tp) = r := by
  -- simp [mkIdRec, mkRefl, Id'.mkJ_refl]
  sorry

end Id
