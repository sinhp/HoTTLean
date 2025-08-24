import GroupoidModel.Syntax.Inversion
import GroupoidModel.Syntax.UHom

import GroupoidModel.ForMathlib

macro "simp_part" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [
    Part.mem_assert_iff, Part.mem_bind_iff, Part.mem_map_iff,
    Part.pure_eq_some, Part.bind_eq_bind, Part.map_bind,
    Part.map_some, Part.mem_bind_iff, Part.mem_some_iff,
    exists_true_left, exists_const] $(loc)?)

universe v u

open CategoryTheory Limits


noncomputable section

namespace NaturalModel
namespace UHomSeq

variable {𝒞 : Type u} [SmallCategory 𝒞] [CartesianMonoidalCategory 𝒞]

/-! ## Extension sequences -/

/-- `s.ExtSeq Γ Γ'` is a diff from the semantic context `Γ` to `Γ'`,
where `Γ` is a prefix of `Γ'`.
It witnesses a sequence of context extension operations in `s`
that built `Γ'` on top of `Γ`.
We write `Γ ≤ Γ'`. -/
inductive ExtSeq (s : UHomSeq 𝒞) (Γ : 𝒞) : 𝒞 → Type u where
  | nil : s.ExtSeq Γ Γ
  | snoc {Γ'} {l : Nat} (d : s.ExtSeq Γ Γ') (llen : l < s.length + 1) (A : y(Γ') ⟶ s[l].Ty) :
    s.ExtSeq Γ (s[l].ext A)

namespace ExtSeq

-- Q : What would a `Lookup` `Prop` family for `ExtSeq` look like?
-- The purpose of adding it would be to totalize `var`, `tp`, and other functions.

variable {s : UHomSeq 𝒞}

@[simp]
def length {Γ Γ' : 𝒞} : s.ExtSeq Γ Γ' → ℕ
  | nil => 0
  | snoc d _ _ => d.length + 1

@[simp]
def append {Γ₁ Γ₂ Γ₃ : 𝒞} : s.ExtSeq Γ₁ Γ₂ → s.ExtSeq Γ₂ Γ₃ → s.ExtSeq Γ₁ Γ₃
  | d, .nil           => d
  | d, .snoc e llen A => .snoc (d.append e) llen A

theorem append_assoc {Γ₁ Γ₂ Γ₃ Γ₄ : 𝒞}
    (d₁ : s.ExtSeq Γ₁ Γ₂) (d₂ : s.ExtSeq Γ₂ Γ₃) (d₃ : s.ExtSeq Γ₃ Γ₄) :
    d₁.append (d₂.append d₃) = (d₁.append d₂).append d₃ := by
  induction d₃ <;> simp [*]

/-- The composite display map associated to a sequence. -/
@[simp]
def disp {Γ Γ' : 𝒞} : s.ExtSeq Γ Γ' → (Γ' ⟶ Γ)
  | .nil => 𝟙 _
  | snoc (l := l) d _ A =>
    s[l].disp A ≫ d.disp

/-- Weaken a substitution and its domain by an extension sequence.
```
Δ ⊢ σ : Γ  d : Γ ≤ Γ'
-----------------------------
Δ ≤ Δ.d[σ]  Δ.d[σ] ⊢ σ.d : Γ'
```
where
```
Δ ⊢ σ : Γ  d : Γ ≤ Γ.Aₙ.….A₁
-----------------------------
Δ.d[σ] ≡ Δ.Aₙ[σ].….A₁[⋯]
```
-/
@[simp]
def substWk {Δ Γ Γ' : 𝒞} (σ : Δ ⟶ Γ) : s.ExtSeq Γ Γ' → Σ (Δ' : 𝒞), s.ExtSeq Δ Δ' × (Δ' ⟶ Γ')
  | .nil => ⟨Δ, .nil, σ⟩
  | snoc (l := l) d llen A =>
    let ⟨Δ, d, σ⟩ := d.substWk σ
    ⟨s[l].ext (ym(σ) ≫ A), d.snoc llen (ym(σ) ≫ A), s[l].substWk σ A⟩

@[simp]
theorem substWk_length {Δ Γ Γ' : 𝒞} (σ : Δ ⟶ Γ) (d : s.ExtSeq Γ Γ') :
    (d.substWk σ).2.1.length = d.length := by
  induction d <;> simp [substWk, *]

@[functor_map (attr := reassoc)]
theorem substWk_disp {Δ Γ Γ' : 𝒞} (σ : Δ ⟶ Γ) (d : s.ExtSeq Γ Γ') :
    (d.substWk σ).2.2 ≫ d.disp = (d.substWk σ).2.1.disp ≫ σ := by
  induction d generalizing σ <;> simp [substWk, NaturalModel.substWk_disp_assoc, *]

/-- `Γ.Aₖ.….A₀ ⊢ vₙ : Aₙ[↑ⁿ⁺¹]` -/
protected def var {Γ Γ' : 𝒞} {l : Nat} (llen : l < s.length + 1) :
    s.ExtSeq Γ Γ' → ℕ → Part (y(Γ') ⟶ s[l].Tm)
  | .nil, _ => .none
  | snoc (l := l') _ _ A, 0 =>
    Part.assert (l' = l) fun l'l =>
    return l'l ▸ s[l'].var A
  | snoc (l := l') d _ A, n+1 => do
    let v ← d.var llen n
    return ym(s[l'].disp A) ≫ v

/-- `Γ.Aₖ.….A₀ ⊢ Aₙ[↑ⁿ⁺¹]` -/
protected def tp {Γ Γ' : 𝒞} {l : Nat} (llen : l < s.length + 1) :
    s.ExtSeq Γ Γ' → ℕ → Part (y(Γ') ⟶ s[l].Ty)
  | .nil, _ => .none
  | snoc (l := l') _ _ A, 0 =>
    Part.assert (l' = l) fun l'l =>
    return l'l ▸ ym(s[l'].disp A) ≫ A
  | snoc (l := l') d _ A, n+1 => do
    let v ← d.tp llen n
    return ym(s[l'].disp A) ≫ v

theorem var_tp {Γ Γ' : 𝒞} {l : Nat} (d : s.ExtSeq Γ Γ') (llen : l < s.length + 1) (n : ℕ) :
    (d.var llen n).map (· ≫ s[l].tp) = d.tp llen n := by
  induction d generalizing n
  . simp [ExtSeq.var, ExtSeq.tp]
  next l' _ _ _ ih =>
    cases n
    . dsimp [ExtSeq.var, ExtSeq.tp]
      by_cases eq : l' = l
      . cases eq
        simp [Part.assert_pos rfl]
      . simp [Part.assert_neg eq]
    . simp [ExtSeq.var, ExtSeq.tp, ← ih]

theorem var_eq_of_lt_length {l i} {llen : l < s.length + 1} {sΓ sΓ' sΓ'' : 𝒞}
    (d : s.ExtSeq sΓ sΓ') (e : s.ExtSeq sΓ' sΓ'') :
    i < e.length → (d.append e).var llen i = e.var llen i := by
  induction e generalizing i with
  | nil => simp
  | snoc _ _ _ ih =>
    intro h
    cases i
    . simp [ExtSeq.var]
    . simp only [length, Nat.add_lt_add_iff_right] at h
      simp [ExtSeq.var, ih h]

theorem var_append_add_length {l i} {llen : l < s.length + 1} {sΓ sΓ' sΓ'' : 𝒞}
    (d : s.ExtSeq sΓ sΓ') (e : s.ExtSeq sΓ' sΓ'') :
    (d.append e).var llen (i + e.length) = (d.var llen i).map (ym(e.disp) ≫ ·) := by
  induction e <;> (simp [ExtSeq.var, Part.bind_some_eq_map, Part.map_map, *]; rfl)

theorem var_substWk_add_length {l i} {llen : l < s.length + 1} {sΔ sΔ' sΓ sΓ' : 𝒞}
    (d : s.ExtSeq sΔ sΔ') (σ : sΔ' ⟶ sΓ) (e : s.ExtSeq sΓ sΓ') :
    let ⟨_, d', _⟩ := e.substWk σ
    (d.append d').var llen (i + e.length) = (d.var llen i).map (ym(d'.disp) ≫ ·) := by
  rw [← e.substWk_length σ]
  apply var_append_add_length

theorem var_substWk_of_lt_length {l i} {Δ Γ Γ' : 𝒞} (σ : Δ ⟶ Γ) (d : s.ExtSeq Γ Γ')
    (llen : l < s.length + 1) {st} (st_mem : st ∈ d.var llen i) :
    i < d.length → ym((substWk σ d).2.2) ≫ st ∈ (substWk σ d).2.1.var llen i := by
  induction d generalizing i with
  | nil => simp
  | snoc _ _ _ ih =>
    intro h
    cases i
    . clear ih
      dsimp [ExtSeq.var] at st_mem ⊢
      simp_part at st_mem ⊢
      obtain ⟨rfl, rfl⟩ := st_mem
      simp
    . simp only [length, Nat.add_lt_add_iff_right] at h
      dsimp [ExtSeq.var] at st_mem ⊢
      simp_part at st_mem ⊢
      obtain ⟨a, amem, rfl⟩ := st_mem
      refine ⟨_, ih amem h, ?_⟩
      simp only [← Functor.map_comp_assoc]
      simp [NaturalModel.substWk_disp]

end ExtSeq

/-! ## Contextual objects -/

variable [HasTerminal 𝒞] {s : UHomSeq 𝒞}

-- Q: Should we get rid of `CObj` altogether, and generalize interpretation to `ExtSeq`s?
/-- A "contextual" object (as in Cartmell's contextual categories),
i.e., one of the form `1.Aₙ₋₁.….A₀`,
together with the extension sequence `[Aₙ₋₁ :: … :: A₀]`.

This kind of object can be destructured. -/
def CObj (s : UHomSeq 𝒞) : Type u := Σ Γ : 𝒞, s.ExtSeq (⊤_ 𝒞) Γ

def nilCObj (s : UHomSeq 𝒞) : s.CObj :=
  ⟨⊤_ 𝒞, .nil⟩

namespace CObj

@[simps]
def snoc {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty) : s.CObj :=
  ⟨s[l].ext A, Γ.2.snoc llen A⟩

@[simps]
def append {sΓ' : 𝒞} (Γ : s.CObj) (d : s.ExtSeq Γ.1 sΓ') : s.CObj :=
  ⟨sΓ', Γ.2.append d⟩

@[simp]
theorem append_nil (Γ : s.CObj) : Γ.append .nil = Γ := rfl

@[simp]
theorem append_snoc {sΓ' : 𝒞} {l} (Γ : s.CObj) (d : s.ExtSeq Γ.1 sΓ')
    (llen : l < s.length + 1) (A : y(sΓ') ⟶ s[l].Ty) :
    Γ.append (d.snoc llen A) = (Γ.append d).snoc llen A := rfl

def substWk {sΓ sΓ' : 𝒞} (Δ : s.CObj) (σ : Δ.1 ⟶ sΓ) (d : s.ExtSeq sΓ sΓ') :
    Σ (Δ' : s.CObj), Δ'.1 ⟶ sΓ' :=
  let ⟨Δ', d', σ'⟩ := d.substWk σ
  ⟨⟨Δ', Δ.2.append d'⟩, σ'⟩

@[simp]
theorem substWk_nil {sΓ : 𝒞} (Δ : s.CObj) (σ : Δ.1 ⟶ sΓ) :
    Δ.substWk σ .nil = ⟨Δ, σ⟩ := rfl

theorem substWk_snoc {sΓ sΓ' : 𝒞} {l} (Δ : s.CObj) (σ : Δ.1 ⟶ sΓ) (d : s.ExtSeq sΓ sΓ')
    (llen : l < s.length + 1) (A : y(sΓ') ⟶ s[l].Ty) :
    Δ.substWk σ (d.snoc llen A) =
      let ⟨Δ', σ'⟩ := Δ.substWk σ d
     ⟨Δ'.snoc llen (ym(σ') ≫ A), s[l].substWk σ' A⟩ := rfl

protected def var {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (i : ℕ) :
    Part (y(Γ.1) ⟶ s[l].Tm) :=
  Γ.2.var llen i

protected def tp {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (i : ℕ) :
    Part (y(Γ.1) ⟶ s[l].Ty) :=
  Γ.2.tp llen i

@[simp]
theorem mem_var_zero {Γ : s.CObj} {l' l'len A l} {llen : l < s.length + 1} {x} :
    x ∈ (Γ.snoc (l := l') l'len A).var llen 0 ↔
    ∃ l'l : l' = l, x = l'l ▸ s[l'].var A := by
  dsimp only [UHomSeq.CObj.var, UHomSeq.CObj.snoc, UHomSeq.ExtSeq.var]
  simp_part; exact exists_congr fun _ => by subst l'; simp_part

@[simp]
theorem mem_var_succ {Γ : s.CObj} {l' l'len A l i} {llen : l < s.length + 1} {x} :
    x ∈ (Γ.snoc (l := l') l'len A).var llen (i+1) ↔
    ∃ a ∈ Γ.var llen i, x = ym(s[l'].disp A) ≫ a := by
  dsimp only [UHomSeq.CObj.var, UHomSeq.CObj.snoc, UHomSeq.ExtSeq.var]
  simp_part

theorem var_tp {l : Nat} (Γ : s.CObj) (llen : l < s.length + 1) (i : ℕ) :
    (Γ.var llen i).map (· ≫ s[l].tp) = Γ.tp llen i :=
  Γ.2.var_tp llen i

end CObj

variable (slen : univMax ≤ s.length)

section
include slen

omit [HasTerminal 𝒞] in
theorem lt_slen_of_eqTp {Γ A B l} : Γ ⊢[l] A ≡ B → l < s.length + 1 := by
  intro Aeq
  have := Aeq.le_univMax
  omega

omit [HasTerminal 𝒞] in
theorem lt_slen_of_wfTp {Γ A l} (H : Γ ⊢[l] A) : l < s.length + 1 :=
  lt_slen_of_eqTp slen (.refl_tp H)

omit [HasTerminal 𝒞] in
theorem lt_slen_of_wfTm {Γ t A l} (H : Γ ⊢[l] t : A) : l < s.length + 1 :=
  lt_slen_of_wfTp slen H.wf_tp

omit [HasTerminal 𝒞] in
theorem lt_slen_of_eqTm {Γ t u A l} (H : Γ ⊢[l] t ≡ u : A) : l < s.length + 1 :=
  lt_slen_of_wfTp slen H.wf_tp

end

/-! ## Interpretation -/

variable [s.PiSeq] [s.SigSeq]

mutual

/- Recall: cannot have `ofCtx` appearing in the output types
(that would be induction-recursion or something like it),
thus the context must be an *input*. -/
def ofType (Γ : s.CObj) (l : Nat) :
    Expr → (_ : l < s.length + 1 := by get_elem_tactic) → Part (y(Γ.1) ⟶ s[l].Ty)
  | .pi i j A B, _ =>
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let B ← ofType (Γ.snoc ilen A) j B
    return lij ▸ s.mkPi ilen jlen A B
  | .sigma i j A B, _ =>
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let B ← ofType (Γ.snoc ilen A) j B
    return lij ▸ s.mkSig ilen jlen A B
  | .Id _ A a0 a1, llen => do
    let A ← ofType Γ l A
    let a0 ← ofTerm Γ l a0
    let a1 ← ofTerm Γ l a1
    Part.assert (a0 ≫ s[l].tp = A) fun eq0 => do
    Part.assert (a1 ≫ s[l].tp = A) fun eq1 => do
    return s.mkId llen A a0 a1 eq0 eq1
  | .univ i, _ =>
    Part.assert (l = i + 1) fun li => do
    return li ▸ (s.homSucc i).wkU Γ.1
  | .el t, _ => do
    Part.assert (l < s.length) fun llen => do
    let A ← ofTerm Γ (l+1) t
    Part.assert (A ≫ s[l+1].tp = (s.homSucc l).wkU Γ.1) fun A_tp => do
    return s.el llen A A_tp
  | _, _ => .none

def ofTerm (Γ : s.CObj) (l : Nat) :
    Expr → (_ : l < s.length + 1 := by get_elem_tactic) → Part (y(Γ.1) ⟶ s[l].Tm)
  | .bvar i, llen => Γ.var llen i
  | .lam i j A e, _ => do
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let A ← ofType Γ i A
    let e ← ofTerm (Γ.snoc ilen A) j e
    return lij ▸ s.mkLam ilen jlen A e
  | .app i _ B f a, llen => do
    Part.assert (i < s.length + 1) fun ilen => do
    let f ← ofTerm Γ (max i l) f
    let a ← ofTerm Γ i a
    let B ← ofType (Γ.snoc ilen (a ≫ s[i].tp)) l B
    Part.assert (f ≫ s[max i l].tp = s.mkPi ilen llen (a ≫ s[i].tp) B) fun h =>
    return s.mkApp ilen llen _ B f h a rfl
  | .pair i j B t u, _ => do
    Part.assert (l = max i j) fun lij => do
    have ilen : i < s.length + 1 := by omega
    have jlen : j < s.length + 1 := by omega
    let t ← ofTerm Γ i t
    let B ← ofType (Γ.snoc ilen (t ≫ s[i].tp)) j B
    let u ← ofTerm Γ j u
    Part.assert (u ≫ s[j].tp = ym(s[i].sec _ t rfl) ≫ B) fun u_tp =>
    return lij ▸ s.mkPair ilen jlen (t ≫ s[i].tp) B t rfl u u_tp
  | .fst _ j A B p, llen => do
    Part.assert (j < s.length + 1) fun jlen => do
    -- RB was so right
    let A ← ofType Γ l A
    let B ← ofType (Γ.snoc llen A) j B
    let p ← ofTerm Γ (max l j) p
    Part.assert (p ≫ s[max l j].tp = s.mkSig llen jlen A B) fun p_tp =>
    return s.mkFst llen jlen A B p p_tp
  | .snd i _ A B p, llen => do
    Part.assert (i < s.length + 1) fun ilen => do
    let A ← ofType Γ i A
    let B ← ofType (Γ.snoc ilen A) l B
    let p ← ofTerm Γ (max i l) p
    Part.assert (p ≫ s[max i l].tp = s.mkSig ilen llen A B) fun p_tp =>
    return s.mkSnd ilen llen A B p p_tp
  | .refl _ t, llen => do
    let t ← ofTerm Γ l t
    return s.mkRefl llen t
  | .idRec i _ t M r u h, llen => do
    Part.assert (i < s.length + 1) fun ilen => do
    let t ← ofTerm Γ i t
    let A := t ≫ s[i].tp
    let M ← ofType ((Γ.snoc ilen A).snoc ilen _) l M
    let r ← ofTerm Γ l r
    Part.assert _ fun r_tp => do
    let u ← ofTerm Γ i u
    Part.assert (u ≫ s[i].tp = A) fun u_tp => do
    let h ← ofTerm Γ i h
    Part.assert (h ≫ s[i].tp = s.mkId ilen A t u rfl u_tp) fun h_tp => do
    return s.mkIdRec ilen llen A t rfl _ rfl M r r_tp u u_tp h h_tp
  | .code t, _ =>
    Part.assert (0 < l) fun lpos => do
    let A ← ofType Γ (l-1) t
    return cast (by congr 3; omega) <| s.code (by omega) A
  | _, _ => .none

end

variable (s) in
def ofCtx : Ctx → Part s.CObj
  | [] => return s.nilCObj
  | (A,l) :: Γ => do
    Part.assert (l < s.length + 1) fun llen => do
    let sΓ ← ofCtx Γ
    let sA ← ofType (s := s) sΓ l A
    return sΓ.snoc llen sA

@[simp]
theorem mem_ofType_pi {Γ l i j A B} {llen : l < s.length + 1} {x} :
    x ∈ s.ofType Γ l (.pi i j A B) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by> omega
    have jlen : j < s.length + 1 := by> omega
    ∃ (A' : y(Γ.fst) ⟶ s[i].Ty), A' ∈ s.ofType Γ i A ∧
    ∃ (B' : y((Γ.snoc ilen A').fst) ⟶ s[j].Ty), B' ∈ s.ofType (Γ.snoc ilen A') j B ∧
    x = lij ▸ s.mkPi ilen jlen A' B' := by
  dsimp only [ofType]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofType_sigma {Γ l i j A B} {llen : l < s.length + 1} {x} :
    x ∈ s.ofType Γ l (.sigma i j A B) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by> omega
    have jlen : j < s.length + 1 := by> omega
    ∃ (A' : y(Γ.fst) ⟶ s[i].Ty), A' ∈ s.ofType Γ i A ∧
    ∃ (B' : y((Γ.snoc ilen A').fst) ⟶ s[j].Ty), B' ∈ s.ofType (Γ.snoc ilen A') j B ∧
    x = lij ▸ s.mkSig ilen jlen A' B' := by
  dsimp only [ofType]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofType_Id {Γ l i A a b} {llen : l < s.length + 1} {x} :
    x ∈ s.ofType Γ l (.Id i A a b) llen ↔
    ∃ (A' : y(Γ.fst) ⟶ s[l].Ty), A' ∈ s.ofType Γ l A ∧
    ∃ (a' : y(Γ.fst) ⟶ s[l].Tm), a' ∈ s.ofTerm Γ l a ∧
    ∃ (b' : y(Γ.fst) ⟶ s[l].Tm), b' ∈ s.ofTerm Γ l b ∧
    ∃ eq : a' ≫ s[l].tp = A',
    ∃ eq' : b' ≫ s[l].tp = A',
    x = s.mkId llen A' a' b' eq eq' := by
  dsimp only [ofType]; simp_part

@[simp]
theorem mem_ofType_el {Γ l t} {llen : l < s.length + 1} {x} :
    x ∈ s.ofType Γ l (.el t) llen ↔
    ∃ llen : l < s.length,
    ∃ A : y(Γ.1) ⟶ s[l+1].Tm, A ∈ ofTerm Γ (l+1) t ∧
    ∃ A_tp : A ≫ s[l+1].tp = (s.homSucc l).wkU Γ.1,
    x = s.el llen A A_tp := by
  dsimp only [ofType]; simp_part

@[simp]
theorem ofTerm_bvar {Γ l i} {llen : l < s.length + 1} :
    s.ofTerm Γ l (.bvar i) llen = Γ.var llen i := rfl

@[simp]
theorem mem_ofTerm_lam {Γ l i j A e} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.lam i j A e) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by> omega
    have jlen : j < s.length + 1 := by> omega
    ∃ (A' : y(Γ.1) ⟶ s[i].Ty), A' ∈ s.ofType Γ i A ∧
    ∃ (e' : y((Γ.snoc ilen A').1) ⟶ s[j].Tm), e' ∈ s.ofTerm (Γ.snoc ilen A') j e ∧
    x = lij ▸ s.mkLam ilen jlen A' e' := by
  dsimp only [ofTerm]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofTerm_app {Γ l i j B f a} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.app i j B f a) llen ↔
    ∃ ilen : i < s.length + 1,
    ∃ f' : y(Γ.1) ⟶ s[max i l].Tm, f' ∈ ofTerm Γ (max i l) f ∧
    ∃ a' : y(Γ.1) ⟶ s[i].Tm, a' ∈ ofTerm Γ i a ∧
    ∃ A', ∃ eq : a' ≫ s[i].tp = A',
    ∃ B' : y((Γ.snoc ilen A').1) ⟶ s[l].Ty,
      B' ∈ ofType (Γ.snoc ilen A') l B ∧
    ∃ h, x = s.mkApp ilen llen _ B' f' h a' eq := by
  dsimp only [ofTerm]; simp_part; simp only [exists_prop_eq']

@[simp]
theorem mem_ofTerm_pair {Γ l i j B t u} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.pair i j B t u) llen ↔
    ∃ lij : l = max i j,
    have ilen : i < s.length + 1 := by> omega
    have jlen : j < s.length + 1 := by> omega
    ∃ t' : y(Γ.1) ⟶ s[i].Tm, t' ∈ ofTerm Γ i t ∧
    ∃ A', ∃ eq : t' ≫ s[i].tp = A',
    ∃ B' : y((Γ.snoc ilen A').1) ⟶ s[j].Ty,
      B' ∈ ofType (Γ.snoc ilen A') j B ∧
    ∃ u' : y(Γ.1) ⟶ s[j].Tm, u' ∈ ofTerm Γ j u ∧
    ∃ u_tp : u' ≫ s[j].tp = ym(s[i].sec _ t' eq) ≫ B',
    x = lij ▸ s.mkPair ilen jlen A' B' t' eq u' u_tp := by
  dsimp only [ofTerm]; simp only [exists_prop_eq']; simp_part
  exact exists_congr fun _ => by subst l; simp_part

@[simp]
theorem mem_ofTerm_fst {Γ l i j A B p} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.fst i j A B p) llen ↔
    have ilen : l < s.length + 1 := by> omega
    ∃ jlen : j < s.length + 1,
    ∃ (A' : y(Γ.fst) ⟶ s[l].Ty), A' ∈ s.ofType Γ l A ∧
    ∃ B' : y((Γ.snoc llen A').1) ⟶ s[j].Ty,
      B' ∈ ofType (Γ.snoc llen A') j B ∧
    ∃ p' : y(Γ.1) ⟶ s[max l j].Tm, p' ∈ ofTerm Γ (max l j) p ∧
    ∃ p_tp : p' ≫ s[max l j].tp = s.mkSig llen jlen A' B',
    x = s.mkFst llen jlen A' B' p' p_tp := by
  dsimp only [ofTerm]; simp_part

@[simp]
theorem mem_ofTerm_snd {Γ l i j A B p} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.snd i j A B p) llen ↔
    have llen : l < s.length + 1 := by> omega
    ∃ ilen : i < s.length + 1,
    ∃ (A' : y(Γ.fst) ⟶ s[i].Ty), A' ∈ s.ofType Γ i A ∧
    ∃ B' : y((Γ.snoc ilen A').1) ⟶ s[l].Ty,
      B' ∈ ofType (Γ.snoc ilen A') l B ∧
    ∃ p' : y(Γ.1) ⟶ s[max i l].Tm, p' ∈ ofTerm Γ (max i l) p ∧
    ∃ p_tp : p' ≫ s[max i l].tp = s.mkSig ilen llen A' B',
    x = s.mkSnd ilen llen A' B' p' p_tp := by
  dsimp only [ofTerm]; simp_part

@[simp]
theorem mem_ofTerm_refl {Γ l i t} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.refl i t) llen ↔
    ∃ t' ∈ ofTerm Γ l t llen, x = s.mkRefl llen t' := by
  dsimp only [ofTerm]; simp_part

@[simp]
theorem mem_ofTerm_idRec {Γ l i j t M r u h} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.idRec i j t M r u h) llen ↔
    ∃ ilen : i < s.length + 1,
    ∃ t' : y(Γ.1) ⟶ s[i].Tm, t' ∈ ofTerm Γ i t ∧
    ∃ A', ∃ t_tp : t' ≫ s[i].tp = A',
    ∃ B' B_eq,
    ∃ M' : y(((Γ.snoc ilen A').snoc ilen B').1) ⟶ s[l].Ty,
      M' ∈ ofType ((Γ.snoc ilen A').snoc ilen B') l M ∧
    ∃ r' : y(Γ.1) ⟶ s[l].Tm, r' ∈ ofTerm Γ l r ∧
    ∃ r_tp,
    ∃ u' : y(Γ.1) ⟶ s[i].Tm, u' ∈ ofTerm Γ i u ∧
    ∃ u_tp : u' ≫ s[i].tp = A',
    ∃ h' : y(Γ.1) ⟶ s[i].Tm, h' ∈ ofTerm Γ i h ∧
    ∃ h_tp : h' ≫ s[i].tp = s.mkId ilen A' t' u' t_tp u_tp,
    x = s.mkIdRec ilen llen A' t' t_tp B' B_eq M' r' r_tp u' u_tp h' h_tp := by
  dsimp only [ofTerm]; simp_part; simp only [exists_prop_eq']

@[simp]
theorem mem_ofTerm_code {Γ l t} {llen : l < s.length + 1} {x} :
    x ∈ s.ofTerm Γ l (.code t) llen ↔
    ∃ i, ∃ li : l = i + 1,
    ∃ (t' : y(Γ.fst) ⟶ s[i].Ty), t' ∈ s.ofType Γ i t ∧
    x = li ▸ s.code (by> omega) t' := by
  dsimp only [ofTerm]; cases l <;> simp

@[simp]
theorem mem_ofType_univ {Γ l i} {llen : l < s.length + 1} {x} :
    x ∈ s.ofType Γ l (.univ i) llen ↔
    ∃ li : l = i + 1,
    x = li ▸ (s.homSucc i).wkU Γ.1 := by
  dsimp only [ofType]; simp_part; exact exists_congr fun _ => by subst l; simp_part

@[simp] theorem ofCtx_nil : s.ofCtx [] = s.nilCObj := rfl

@[simp]
theorem mem_ofCtx_snoc {Γ A l sΓ'} : sΓ' ∈ s.ofCtx ((A,l) :: Γ) ↔
    ∃ sΓ ∈ s.ofCtx Γ, ∃ llen, ∃ sA ∈ ofType sΓ l A llen, sΓ' = sΓ.snoc llen sA := by
  simp only [ofCtx, Part.pure_eq_some, Part.bind_eq_bind, Part.mem_assert_iff, Part.mem_bind_iff,
    Part.mem_some_iff]
  tauto

/-! ## Admissibility of instantiation -/

variable (slen : univMax ≤ s.length)

/-- An inductive characterization of those semantic substitutions
that appear in syntactic operations.
We use this as an auxiliary device
in the proof of semantic substitution admissibility.

The family with `full = false` characterizes renamings,
whereas `full = true` contains general substitutions
but where composition is limited to renamings on the left. -/
inductive CSb : (Δ Γ : s.CObj) → (Δ.1 ⟶ Γ.1) → (full : Bool := true) → Type _ where
  | id Γ (full : Bool := true) : CSb Γ Γ (𝟙 _) full
  | wk {Γ : s.CObj} {l} (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty)
    (full : Bool := true) : CSb (Γ.snoc llen A) Γ (s[l].disp A) full
  | comp {Θ Δ Γ : s.CObj} {σ τ full} : CSb Θ Δ σ false → CSb Δ Γ τ full → CSb Θ Γ (σ ≫ τ) full
  | snoc' {Δ Γ : s.CObj} {σ full} (_ : CSb Δ Γ σ full) {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e) (hf : ¬full → ∃ i, e = .bvar i)
    {se : y(Δ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = ym(σ) ≫ A)
    (H : se ∈ ofTerm Δ l e) :
    CSb Δ (Γ.snoc llen A) (s[l].substCons σ A se eq) full

def CSb.toSb {Δ Γ σ full} : s.CSb Δ Γ σ full → Nat → Expr
  | .id _ _ => .bvar
  | .wk _ _ _ => Expr.wk
  | .comp σ τ => Expr.comp σ.toSb τ.toSb
  | .snoc' σ _ _ e _ _ _ => Expr.snoc σ.toSb e

theorem CSb.toSb_is_bvar {Δ Γ σ} : ∀ (sσ : s.CSb Δ Γ σ false) i, ∃ j, sσ.toSb i = .bvar j
  | .id _ _, _ => ⟨_, rfl⟩
  | .wk _ _ _, _ => by simp [toSb]
  | .comp σ τ, i => by
    have ⟨j, eq⟩ := toSb_is_bvar τ i
    have ⟨k, eq'⟩ := toSb_is_bvar σ j
    simp [toSb, Expr.comp, eq, Expr.subst, eq']
  | .snoc' σ _ _ e hf _ _, i => by
    cases i <;> simp [toSb, Expr.snoc]
    · apply hf; simp
    · apply toSb_is_bvar

def CSb.snoc {Δ Γ : s.CObj} {σ} (sσ : CSb Δ Γ σ) {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e)
    {se : y(Δ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = ym(σ) ≫ A)
    (H : se ∈ ofTerm Δ l e) :
    CSb Δ (Γ.snoc llen A) (s[l].substCons σ A se eq) :=
  snoc' sσ llen A e (by simp) eq H

@[simp] theorem CSb.snoc_toSb {Δ Γ : s.CObj} {σ} (sσ : CSb Δ Γ σ) {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e)
    {se : y(Δ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = ym(σ) ≫ A)
    (H : se ∈ ofTerm Δ l e) :
    (snoc sσ llen A e eq H).toSb = Expr.snoc sσ.toSb e := rfl

def CSb.sub1 {Γ : s.CObj} {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e)
    {se : y(Γ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = A)
    (H : se ∈ ofTerm Γ l e) :
    CSb Γ (Γ.snoc llen A) (s[l].sec A se eq) :=
  snoc (id Γ) llen A e _ H

@[simp] theorem CSb.sub1_toSb {Γ : s.CObj} {l} (llen : l < s.length + 1)
    (A : y(Γ.1) ⟶ s[l].Ty) (e)
    {se : y(Γ.1) ⟶ s[l].Tm} (eq : se ≫ s[l].tp = A)
    (H : se ∈ ofTerm Γ l e) :
    (sub1 llen A e eq H).toSb = Expr.toSb e := rfl

def CSb.up {Δ Γ σ full} (sσ : s.CSb Δ Γ σ full)
    {l} (llen : l < s.length + 1) (A : y(Γ.1) ⟶ s[l].Ty)
    (A' := ym(σ) ≫ A) (eq : ym(σ) ≫ A = A' := by rfl) :
    CSb (Δ.snoc llen A') (Γ.snoc llen A) (s[l].substWk σ A _ eq) full := by
  refine ((CSb.wk _ _ false).comp sσ).snoc' _ _ (.bvar 0) (by simp) _ ?_
  simp [UHomSeq.CObj.var, UHomSeq.ExtSeq.var]

@[simp] theorem CSb.up_toSb {Δ Γ σ full} (sσ : s.CSb Δ Γ σ full)
     {l} {llen : l < s.length + 1} {A A'} {eq : ym(σ) ≫ A = A'} :
    (up sσ llen A _ eq).toSb = Expr.up sσ.toSb := by
  simp [up, toSb, Expr.up_eq_snoc]

theorem mem_ofType_ofTerm_subst' {full}
    (IH : full = true → ∀ {Δ Γ l} (llen : l < s.length + 1) {sσ} (σ : CSb Δ Γ sσ false) {se e},
      se ∈ ofTerm Γ l e llen → ym(sσ) ≫ se ∈ ofTerm Δ l (Expr.subst σ.toSb e) llen)
    {e l} (llen : l < s.length + 1)
    {Δ Γ : s.CObj} {sσ} (σ : CSb Δ Γ sσ full) {σ'} (eq : σ.toSb = σ') :
    (∀ {sA}, sA ∈ ofType Γ l e llen →
      ym(sσ) ≫ sA ∈ ofType Δ l (Expr.subst σ' e) llen) ∧
    (∀ {se}, se ∈ ofTerm Γ l e llen →
      ym(sσ) ≫ se ∈ ofTerm Δ l (Expr.subst σ' e) llen) := by
  subst σ'
  induction e generalizing Δ Γ l <;>
    (constructor <;> [intro sA H; intro se H] <;> try cases Part.notMem_none _ H)
  case pi.left ihA ihB =>
    obtain ⟨rfl, H⟩ := mem_ofType_pi.1 H; simp at H llen
    obtain ⟨A, hA, B, hB, rfl⟩ := H; clear H
    simp only [Expr.subst, comp_mkPi, mem_ofType_pi, exists_true_left]
    refine ⟨_, (ihA llen.1 σ).1 hA, _, ?_, rfl⟩
    rw [← CSb.up_toSb]; exact (ihB llen.2 (σ.up llen.1 A)).1 hB
  case sigma.left ihA ihB =>
    obtain ⟨rfl, H⟩ := mem_ofType_sigma.1 H; simp at H llen
    obtain ⟨A, hA, B, hB, rfl⟩ := H; clear H
    simp only [Expr.subst, comp_mkSig, mem_ofType_sigma, exists_true_left]
    refine ⟨_, (ihA llen.1 σ).1 hA, _, ?_, rfl⟩
    rw [← CSb.up_toSb]; exact (ihB llen.2 (σ.up llen.1 A)).1 hB
  case Id.left ihA iha ihb =>
    obtain := mem_ofType_Id.1 H; simp at H llen
    obtain ⟨A, hA, a, ha, b, hb, eq, eq', rfl⟩ := H
    simp only [Expr.subst, comp_mkId, mem_ofType_Id]
    refine ⟨_, (ihA llen σ).1 hA, _, (iha llen σ).2 ha, _, (ihb llen σ).2 hb, ?_, ?_, rfl⟩
      <;> simp [eq, eq']
  case el.left ih =>
    obtain ⟨llen', A, hA, tp, rfl⟩ := mem_ofType_el.1 H
    simp only [Expr.subst, mem_ofType_el, UHomSeq.comp_el, exists_true_left, llen']
    exact ⟨_, (ih (by omega) σ).2 hA, by simp [tp], rfl⟩
  case univ.left =>
    obtain ⟨rfl, H⟩ := mem_ofType_univ.1 H; simp at H llen; subst H
    simp only [Expr.subst, mem_ofType_univ, exists_true_left, UHom.comp_wkU]

  case bvar i =>
    simp [ofTerm_bvar] at H
    simp [Expr.subst]
    induction σ generalizing i with simp [CSb.toSb, *]
    | wk => exact CObj.mem_var_succ.2 ⟨_, ‹_›, rfl⟩
    | @comp _ _ _ _ _ full σ τ ih1 ih2 =>
      simp [Expr.comp]
      cases full with
      | false =>
        simp at ih1 ih2; clear IH
        have ⟨j, eq⟩ := CSb.toSb_is_bvar τ i
        simp [eq, Expr.subst]
        refine ih1 _ ?_
        rw [← ofTerm_bvar, ← eq]
        exact ih2 _ H
      | true => exact IH rfl _ _ (ih2 IH _ H)
    | snoc' _ _ _ _ _ _ _ ih1 =>
      induction i with
      | zero =>
        obtain ⟨rfl, H⟩ := CObj.mem_var_zero.1 H
        simp at H; subst H; simpa
      | succ i ih2 =>
        obtain ⟨_, H', rfl⟩ := CObj.mem_var_succ.1 H
        simp [ih1 IH i H']
  case lam ihA ihB =>
    obtain ⟨rfl, H⟩ := mem_ofTerm_lam.1 H; simp at H llen
    obtain ⟨A, hA, B, hB, rfl⟩ := H; clear H
    simp only [Expr.subst, comp_mkLam, mem_ofTerm_lam, exists_true_left]
    refine ⟨_, (ihA llen.1 σ).1 hA, _, ?_, rfl⟩
    rw [← CSb.up_toSb]; exact (ihB llen.2 (σ.up llen.1 A)).2 hB
  case app ihB ihf iha =>
    obtain ⟨llen', f, hf, a, ha, _, rfl, B, hB, eq, rfl⟩ := mem_ofTerm_app.1 H
    simp only [Expr.subst, comp_mkApp, mem_ofTerm_app]
    refine ⟨‹_›, _, (ihf (by simp [*]) σ).2 hf, _, (iha llen' σ).2 ha, _, rfl, _, ?_, ?_, rfl⟩
    · rw [← CSb.up_toSb]; exact (ihB llen (σ.up llen' _ _ (Category.assoc ..).symm)).1 hB
    · simp [*, comp_mkPi]
      congr! 1
  case pair ihB iht ihu =>
    obtain ⟨rfl, H⟩ := mem_ofTerm_pair.1 H; simp at H llen
    obtain ⟨t, ht, B, hB, u, hu, eq, rfl⟩ := H; clear H
    simp only [Expr.subst, comp_mkPair, mem_ofTerm_pair, exists_true_left]
    refine ⟨_, (iht llen.1 σ).2 ht, _, rfl, _, ?_, _, (ihu llen.2 σ).2 hu, ?_, rfl⟩
    · rw [← CSb.up_toSb]; exact (ihB llen.2 (σ.up llen.1 _ _ (Category.assoc ..).symm)).1 hB
    · simp [*]; rw [← Functor.map_comp_assoc, comp_sec, ← Functor.map_comp_assoc]; congr! 0
  case fst ihA ihB ihp =>
    obtain ⟨jlen, A, hA, B, hB, p, hp, eq, rfl⟩ := mem_ofTerm_fst.1 H
    simp only [Expr.subst, comp_mkFst, mem_ofTerm_fst]
    refine ⟨jlen, _, (ihA llen σ).1 hA, _, ?_, _, (ihp (by simp [*]) σ).2 hp, ?_, rfl⟩
    · rw [← CSb.up_toSb]; exact (ihB jlen (σ.up llen _)).1 hB
    · simp [*, comp_mkSig]
  case snd ihA ihB ihp =>
    obtain ⟨ilen, A, hA, B, hB, p, hp, eq, rfl⟩ := mem_ofTerm_snd.1 H
    simp only [Expr.subst, comp_mkSnd, mem_ofTerm_snd]
    refine ⟨ilen, _, (ihA ilen σ).1 hA, _, ?_, _, (ihp (by simp [*]) σ).2 hp, ?_, rfl⟩
    · rw [← CSb.up_toSb]; exact (ihB llen (σ.up ilen _)).1 hB
    · simp [*, comp_mkSig]
  case refl iht =>
    obtain ⟨t, ht, rfl⟩ := mem_ofTerm_refl.1 H
    simp only [Expr.subst, comp_mkRefl, mem_ofTerm_refl]
    exact ⟨_, (iht llen σ).2 ht, rfl⟩
  case idRec iht ihM ihr ihu ihh =>
    obtain ⟨ilen, t, ht, A, Aeq, B, Beq, M, hM, r, hr, rtp, u, hu, utp, h, hh, htp, rfl⟩ :=
      mem_ofTerm_idRec.1 H
    simp only [Expr.subst, mem_ofTerm_idRec]
    refine ⟨ilen, _, (iht ilen σ).2 ht, _, by simp [Aeq], _, ?_, _, ?_,
      _, (ihr llen σ).2 hr, _, _, (ihu ilen σ).2 hu, _, _, (ihh ilen σ).2 hh, _,
      comp_mkIdRec (σA_eq := rfl) (σB_eq := rfl) ..⟩
    · simp [← Beq, comp_mkId (eq := rfl)]
      congr 1 <;> simp only [← Functor.map_comp_assoc, substWk_disp]
    · rw [← CSb.up_toSb, ← CSb.up_toSb]; exact (ihM llen ((σ.up ilen _).up ilen _ _ _)).1 hM
  case code ihA =>
    obtain ⟨l, rfl, H⟩ := mem_ofTerm_code.1 H; simp at H llen
    obtain ⟨A, hA, rfl⟩ := H; clear H
    simp only [Expr.subst, UHomSeq.comp_code, mem_ofTerm_code]
    refine ⟨_, rfl, _, (ihA (by omega) σ).1 hA, ?_⟩; simp

theorem mem_ofType_ofTerm_subst {e l} (llen : l < s.length + 1)
    {Δ Γ : s.CObj} {sσ full} (σ : CSb Δ Γ sσ full) {σ'} (eq : σ.toSb = σ') :
    (∀ {sA}, sA ∈ ofType Γ l e llen →
      ym(sσ) ≫ sA ∈ ofType Δ l (Expr.subst σ' e) llen) ∧
    (∀ {se}, se ∈ ofTerm Γ l e llen →
      ym(sσ) ≫ se ∈ ofTerm Δ l (Expr.subst σ' e) llen) := by
  refine mem_ofType_ofTerm_subst' (fun _ _ _ _ llen sσ σ se i => ?_) llen σ eq
  exact (mem_ofType_ofTerm_subst' (by simp) llen σ rfl).2

theorem mem_ofType_wk {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {X : y(Γ.1) ⟶ s[l'].Ty}
    {se} (H : se ∈ ofType Γ l e hl) :
    ym(s[l'].disp X) ≫ se ∈ ofType (Γ.snoc hl' X) l (Expr.subst Expr.wk e) hl :=
  (mem_ofType_ofTerm_subst hl (.wk hl' X) rfl).1 H

theorem mem_ofTerm_wk {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {X : y(Γ.1) ⟶ s[l'].Ty}
    {se} (H : se ∈ ofTerm Γ l e hl) :
    ym(s[l'].disp X) ≫ se ∈ ofTerm (Γ.snoc hl' X) l (Expr.subst Expr.wk e) hl :=
  (mem_ofType_ofTerm_subst hl (.wk hl' X) rfl).2 H

theorem mem_ofType_toSb {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {A : y(Γ.1) ⟶ s[l'].Ty}
    {a sa} (ha : sa ∈ ofTerm Γ l' a hl') (eq : sa ≫ s[l'].tp = A)
    {se} (H : se ∈ ofType (Γ.snoc hl' A) l e hl) :
    ym(s[l'].sec A sa eq) ≫ se ∈ ofType Γ l (Expr.subst a.toSb e) hl :=
  (mem_ofType_ofTerm_subst hl (.sub1 _ _ _ eq ha) (by simp)).1 H

theorem mem_ofTerm_toSb {e l l' hl} (hl' : l' < s.length + 1)
    {Γ : s.CObj} {A : y(Γ.1) ⟶ s[l'].Ty}
    {a sa} (ha : sa ∈ ofTerm Γ l' a hl') (eq : sa ≫ s[l'].tp = A)
    {se} (H : se ∈ ofTerm (Γ.snoc hl' A) l e hl) :
    ym(s[l'].sec A sa eq) ≫ se ∈ ofTerm Γ l (Expr.subst a.toSb e) hl :=
  (mem_ofType_ofTerm_subst hl (.sub1 _ _ _ eq ha) (by simp)).2 H

/-! ## Soundness of interpretation -/

theorem tp_sound {Γ i A l} (H : Lookup Γ i A l) {sΓ} (hΓ : sΓ ∈ ofCtx s Γ) :
    ∃ llen, ∃ sA ∈ sΓ.tp llen i, sA ∈ ofType sΓ l A llen := by
  induction H generalizing sΓ with (
    obtain ⟨_, hΓ', _, _, hB, rfl⟩ := mem_ofCtx_snoc.1 hΓ
    simp [UHomSeq.CObj.tp, UHomSeq.ExtSeq.tp, *] at *)
  | zero => exact mem_ofType_wk _ hB
  | succ _ _ _ ih =>
    have ⟨_, _, _, _⟩ := ih hΓ'
    exact ⟨‹_›, _, ⟨_, ‹_›, rfl⟩, mem_ofType_wk _ ‹_›⟩

theorem var_sound {Γ i A l} (H : Lookup Γ i A l) {sΓ} (hΓ : sΓ ∈ ofCtx s Γ) :
    ∃ llen, ∃ st ∈ sΓ.var llen i, st ≫ s[l].tp ∈ ofType sΓ l A llen := by
  have ⟨llen, _, h1, h2⟩ := tp_sound H hΓ
  simp [← UHomSeq.CObj.var_tp] at h1
  obtain ⟨_, h1, rfl⟩ := h1
  exact ⟨llen, _, h1, h2⟩

attribute [local irreducible] IsKernelPair.lift IsPullback.isLimit CategoryStruct.comp
  Quiver.Hom yoneda mkId
-- TODO: this proof is boring, repetitive exists-elim/exists-intro: automate!
include slen in
set_option maxHeartbeats 1600000 in
theorem ofType_ofTerm_sound :
    (∀ {Γ}, WfCtx Γ → (ofCtx s Γ).Dom) ∧
    (∀ {Γ l A}, (Awf : Γ ⊢[l] A) → ∃ sΓ ∈ ofCtx s Γ, ∃ llen,
      (ofType sΓ l A llen).Dom) ∧
    (∀ {Γ l A B}, (Aeq : Γ ⊢[l] A ≡ B) → ∃ sΓ ∈ ofCtx s Γ, ∃ llen,
      ∃ sA ∈ ofType sΓ l A llen, sA ∈ ofType sΓ l B llen) ∧
    (∀ {Γ l A t}, (twf : Γ ⊢[l] t : A) → ∃ sΓ ∈ ofCtx s Γ, ∃ llen,
      ∃ sA ∈ ofType sΓ l A llen, ∃ st ∈ ofTerm sΓ l t llen, st ≫ s[l].tp = sA) ∧
    (∀ {Γ l A t u}, (teq : Γ ⊢[l] t ≡ u : A) → ∃ sΓ ∈ ofCtx s Γ, ∃ llen,
      ∃ sA ∈ ofType sΓ l A llen, ∃ st ∈ ofTerm sΓ l t llen,
        st ∈ ofTerm sΓ l u llen ∧ st ≫ s[l].tp = sA) := by
  simp [Part.dom_iff_mem]
  mutual_induction WfCtx

  case nil => as_aux_lemma => simp
  case snoc => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, forall_exists_index, and_imp]
    intros; rename_i hΓ llen _ hA
    exact ⟨_, _, hΓ, llen, _, hA, rfl⟩

  case pi' | sigma' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofType_pi, mem_ofType_sigma,
      sup_lt_iff, exists_true_left, forall_exists_index, and_imp]
    intros; subst_eqs
    exact ⟨_, ‹_›, ⟨‹_›, ‹_›⟩, _, _, ‹_›, _, ‹_›, rfl⟩
  case Id' => as_aux_lemma =>
    simp only [mem_ofType_Id, forall_exists_index, and_imp]
    intros; subst_eqs; rename_i hΓ _ _ hA _ hΓ' _ _ _ _ hΓ₁ _ _ _ hA₁ hA₂
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hΓ hΓ₁
    have := Part.mem_unique hA₁ hA
    have := Part.mem_unique hA₂ hA
    exact ⟨_, ‹_›, ‹_›, _, _, hA, _, ‹_›, _, ‹_›, ‹_›, ‹_›, rfl⟩
  case univ => as_aux_lemma =>
    simp only [mem_ofType_univ, exists_true_left, forall_exists_index]
    intros; rename_i hΓ
    exact ⟨_, hΓ, by omega, _, rfl⟩
  case el => as_aux_lemma =>
    simp only [mem_ofType_univ, mem_ofType_el, forall_exists_index, and_imp]
    intros; subst_eqs
    exact ⟨_, ‹_›, by omega, _, by omega, _, ‹_›, ‹_›, rfl⟩

  case cong_pi' | cong_sigma' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofType_pi, mem_ofType_sigma,
      forall_exists_index, and_imp, exists_true_left, sup_lt_iff]
    intros; subst_eqs; rename_i hΓ _ _ hA _ _ hΓ' _ _ hA' _ _ _ _
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hA hA'
    exact ⟨_, hΓ, ⟨‹_›, ‹_›⟩, _, ⟨_, hA, _, ‹_›, rfl⟩, ⟨_, ‹_›, _, ‹_›, rfl⟩⟩
  case cong_Id => as_aux_lemma =>
    simp only [mem_ofType_Id, forall_exists_index, and_imp]
    intros; subst_eqs; rename_i hΓ _ _ hA hA' _ hΓ' _ _ _ _ _ hΓ₁ _ _ _ _ hA₁ hA₂
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hΓ hΓ₁
    have := Part.mem_unique hA₁ hA
    have := Part.mem_unique hA₂ hA
    exact ⟨_, hΓ, ‹_›, _,
      ⟨_, hA, _, ‹_›, _, ‹_›, ‹_›, ‹_›, rfl⟩, ⟨_, hA', _, ‹_›, _, ‹_›, ‹_›, ‹_›, rfl⟩⟩
  case cong_el => as_aux_lemma =>
    simp only [mem_ofType_univ, mem_ofType_el, forall_exists_index, and_imp]
    intros; subst_eqs
    exact ⟨_, ‹_›, by omega, _, ⟨by omega, _, ‹_›, ‹_›, rfl⟩, ⟨by omega, _, ‹_›, ‹_›, rfl⟩⟩
  case el_code => as_aux_lemma =>
    simp only [mem_ofTerm_code, mem_ofType_el, forall_exists_index, and_imp,
      Nat.add_right_cancel_iff, exists_prop_eq']
    intros
    refine ⟨_, ‹_›, ‹_›, _, ⟨by omega, _, ⟨_, ‹_›, rfl⟩, ?_, rfl⟩, ?_⟩
    · apply s.code_tp
    · rwa [s.el_code]
  case refl_tp | symm_tp => as_aux_lemma => grind
  case trans_tp => as_aux_lemma =>
    simp only [forall_exists_index, and_imp]
    intros; rename_i hΓ _ _ _ hA₁ _ hΓ' _ _ hA₂ _
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hA₁ hA₂
    exact ⟨_, ‹_›, ‹_›, _, ‹_›, ‹_›⟩

  case bvar => as_aux_lemma =>
    simp only [ofTerm_bvar, forall_exists_index]
    intros
    obtain ⟨llen, _, h1, h2⟩ := var_sound ‹_› ‹_›
    exact ⟨_, ‹_›, llen, _, h2, _, h1, rfl⟩
  case lam' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_lam, mem_ofType_pi,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs; rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ _ _
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hA hA'
    refine ⟨_, ‹_›, ⟨‹_›, ‹_›⟩, _, ⟨_, ‹_›, _, ‹_›, rfl⟩, _, ⟨_, ‹_›, _, ‹_›, rfl⟩, ?_⟩
    apply mkLam_tp (t_tp := rfl)
  case app' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_app, mem_ofType_pi,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ hΓ₁ _ _ hA₁ _ _ _ _ _ hΓ₂ _ _ _ _ _ _ hA₂
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₂; clear hA₂
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, rfl, _, ‹_›, ‹_›, rfl⟩, rfl⟩
    rw [mkApp_tp]
    apply mem_ofType_toSb <;> assumption
  case pair' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_pair, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ hΓ₁ _ _ _ _ hΓ₂ _ _ _ _ _ hA₁ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₁; clear hA₁
    refine ⟨_, ‹_›, ⟨‹_›, ‹_›⟩, _, ⟨_, ‹_›, _, ‹_›, ?_⟩, _,
      ⟨_, ‹_›, _, rfl, _, ‹_›, _, ‹_›, ?_, rfl⟩, rfl⟩
    · apply mkPair_tp
    · refine Part.mem_unique ‹_› ?_
      apply mem_ofType_toSb <;> assumption
  case fst' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_fst, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs; rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ hΓ₁ _ _ hA₁ _ hB _ _ _ hB' _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hB hB'; clear hB'
    refine ⟨_, ‹_›, ‹_›, _, ‹_›, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, ?_⟩
    apply mkFst_tp
  case snd' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_snd, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs; rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ hΓ₁ _ _ hA₁ _ hB _ _ _ hB' _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hB hB'; clear hB'
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, rfl⟩
    rw [mkSnd_tp]
    apply mem_ofType_toSb <;> simp only [mem_ofTerm_fst, exists_true_left, *]
    exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩
  case refl' => as_aux_lemma =>
    simp only [mem_ofTerm_refl, mem_ofType_Id, forall_exists_index, and_imp]
    intros; subst_eqs
    refine ⟨_, ‹_›, ‹_›, _, ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl, rfl, rfl⟩, _, ⟨_, ‹_›, rfl⟩, ?_⟩
    apply mkRefl_tp
  case idRec' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_idRec, mem_ofType_Id, ofTerm_bvar,
      forall_exists_index, and_imp]
    intros; subst_eqs
    rename_i t' _ _ _ i _ _ _ _ _ _ _ _
      hΓ ilen A hA _ hΓ' _ t ht _ hΓ₁ _ _ hA₁ _ _ _ hΓ₂ llen r hr _ hΓ₃ _ u hu _ hΓ₄
      _ _ ht₁ _ hu₁ h hh _ _ _ _ hv rtp hA₂ hA₃ utp _ _ _ M hM
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hA hA₁
    cases Part.mem_unique hΓ hΓ₂
    cases Part.mem_unique hΓ hΓ₃
    cases Part.mem_unique hΓ hΓ₄
    cases Part.mem_unique ht ht₁
    cases Part.mem_unique hu hu₁
    cases Part.mem_unique hA₃ hA
    cases Part.mem_unique (mem_ofTerm_wk ilen ht) ‹_›
    simp only [CObj.mem_var_zero, exists_const] at hv; subst hv
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, _, _, by simp,
      M, hM, _, ‹_›, ?_, _, ‹_›, ‹_›, _, ‹_›, ‹_›, rfl⟩, rfl⟩
    · rw [mkIdRec_tp]
      refine (s.mem_ofType_ofTerm_subst llen (.snoc (.sub1 _ _ _ utp hu) _ _ _ ?_ hh) ?_).1 hM
      simp [*]
    · refine Part.mem_unique rtp ?_
      refine (s.mem_ofType_ofTerm_subst llen
        (.snoc (.sub1 _ _ _ rfl ht) _ _ (.refl i t') ?_ ?_) ?_).1 hM
      · exact mem_ofTerm_refl.2 ⟨_, ht, rfl⟩
      · rfl
  case code => as_aux_lemma =>
    simp only [mem_ofTerm_code, mem_ofType_univ,
      Nat.add_right_cancel_iff, exists_prop_eq', exists_eq_left, Nat.add_lt_add_iff_right,
      forall_exists_index, and_imp, exists_true_left]
    intros
    refine ⟨_, ‹_›, by omega, _, ⟨_, ‹_›, rfl⟩, ?_⟩
    apply UHomSeq.code_tp
  case conv => as_aux_lemma =>
    simp only [forall_exists_index, and_imp]
    intros; subst_eqs
    rename_i hΓ _ _ _ _ hΓ' _ _ hA _ hA'
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    exact ⟨_, ‹_›, ‹_›, _, ‹_›, _, ‹_›, rfl⟩

  case cong_lam' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_lam, mem_ofType_pi,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs; rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ hΓ₁ _ _ hA₁ hA'₁ _ hΓ₂ _ _ hA₂ _ _ _ _ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hA' hA'₁; clear hA'₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₂; clear hA₂
    refine ⟨_, ‹_›, ⟨‹_›, ‹_›⟩, _, ⟨_, ‹_›, _, ‹_›, rfl⟩, _,
      ⟨_, ‹_›, _, ‹_›, rfl⟩, ⟨_, ‹_›, _, ‹_›, rfl⟩, ?_⟩
    apply mkLam_tp (t_tp := rfl)
  case cong_app' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_app, mem_ofType_pi,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ hA₂ _ hB _ _ _ _ hΓ₂ _ _ _ _ _ hB₁ _ _ hA₃
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₃; clear hA₃
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, rfl, _, ‹_›, ‹_›, rfl⟩,
      ⟨‹_›, _, ‹_›, _, ‹_›, _, rfl, _, ‹_›, ‹_›, rfl⟩, rfl⟩
    rw [mkApp_tp]
    apply mem_ofType_toSb <;> assumption
  case cong_pair' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_pair, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA' _ _ hΓ₁ _ _ _ _ _ hΓ₂ _ _ _ _ _ _ _ hA₁ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA'; clear hA'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₁; clear hA₁
    refine ⟨_, ‹_›, ⟨‹_›, ‹_›⟩, _, ⟨_, ‹_›, _, ‹_›, ?_⟩, _,
      ⟨_, ‹_›, _, rfl, _, ‹_›, _, ‹_›, ?h2, rfl⟩, ⟨_, ‹_›, _, rfl, _, ‹_›, _, ‹_›, ?h2, rfl⟩, rfl⟩
    · apply mkPair_tp
    · refine Part.mem_unique ‹_› ?_
      apply mem_ofType_toSb <;> assumption
  case cong_fst' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_fst, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ hA₂ _ _ hΓ₂ _ _ hA₃ _ hB _ _ _ _ hB₁ _ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₃; clear hA₃
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ‹_›, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩,
      ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, ?_⟩
    apply mkFst_tp
  case cong_snd' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_snd, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ hA₂ _ _ hΓ₂ _ _ hA₃ _ hB _ _ _ _ hB₁ _ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₃; clear hA₃
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩,
      ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, rfl⟩
    rw [mkSnd_tp]
    apply mem_ofType_toSb <;> simp only [mem_ofTerm_fst, exists_true_left, *]
    exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩
  case cong_refl' => as_aux_lemma =>
    simp only [mem_ofTerm_refl, mem_ofType_Id, forall_exists_index, and_imp]
    intros; subst_eqs
    refine ⟨_, ‹_›, ‹_›, _, ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl, rfl, rfl⟩, _,
      ⟨_, ‹_›, rfl⟩, ⟨_, ‹_›, rfl⟩, ?_⟩
    apply mkRefl_tp
  case cong_idRec' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_idRec, mem_ofType_Id, ofTerm_bvar,
      forall_exists_index, and_imp]
    intros; subst_eqs
    rename_i et _ _ _ _ _ _ _ i _ _ _ _ _ _ _ _ _
      hΓ ilen A hA _ hΓ' _ t ht _ hΓ₁ _ _ ht₁ _ _ hΓ₂ _ _ hA₁ _ llen _ hΓ₃ u _ hr _ _ hΓ₄ _ _
      hu _ _ hΓ₅ _ _ ht₂ _ hu₁ _ hh hh' _ _ _ _ _ hv rtp hA₂ hA₃ utp _ _ _ M hM hM'
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hΓ hΓ₂
    cases Part.mem_unique hA hA₁
    cases Part.mem_unique hΓ hΓ₃
    cases Part.mem_unique hΓ hΓ₄
    cases Part.mem_unique hΓ hΓ₅
    cases Part.mem_unique ht ht₁
    cases Part.mem_unique ht ht₂
    cases Part.mem_unique hu hu₁
    cases Part.mem_unique hA₃ hA
    cases Part.mem_unique (mem_ofTerm_wk ilen ht) ‹_›
    simp only [CObj.mem_var_zero, exists_const] at hv; subst hv
    refine ⟨_, ‹_›, ‹_›, _, ?_, _,
      ⟨‹_›, _, ‹_›, _, rfl, _, by simp, M, hM, _, ‹_›, ?h3, _, ‹_›, ‹_›, _, ‹_›, ‹_›, rfl⟩,
      ⟨‹_›, _, ‹_›, _, rfl, _, by simp, M, hM', _, ‹_›, ?h3, _, ‹_›, ‹_›, _, ‹_›, ‹_›, rfl⟩, rfl⟩
    · rw [mkIdRec_tp]
      refine (s.mem_ofType_ofTerm_subst llen (.snoc (.sub1 _ _ _ utp hu) _ _ _ ?_ hh) ?_).1 hM
      simp [*]
    · refine Part.mem_unique rtp ?_
      refine (s.mem_ofType_ofTerm_subst llen
        (.snoc (.sub1 _ _ _ rfl ht) _ _ (.refl i et) ?_ ?_) ?_).1 hM
      · exact mem_ofTerm_refl.2 ⟨_, ht, rfl⟩
      · rfl
  case cong_code => as_aux_lemma =>
    simp only [mem_ofTerm_code, mem_ofType_univ,
      Nat.add_right_cancel_iff, exists_prop_eq', exists_eq_left, Nat.add_lt_add_iff_right,
      forall_exists_index, and_imp, exists_true_left]
    intros
    refine ⟨_, ‹_›, by omega, _, ⟨_, ‹_›, rfl⟩, ⟨_, ‹_›, rfl⟩, ?_⟩
    apply UHomSeq.code_tp
  case app_lam' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_app, mem_ofTerm_lam,
      forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ hA₂ _ _ hΓ₂ _ _ _ _ hB _ _ hA₃ hB₁
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₃; clear hA₃
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ?_, _,
      ⟨‹_›, _, ⟨_, ‹_›, _, ‹_›, rfl⟩, _, ‹_›, _, rfl, _, ‹_›, ?_, rfl⟩, ?_, rfl⟩
    · rw [mkApp_tp]
      apply mem_ofType_toSb <;> assumption
    · apply mkLam_tp (t_tp := rfl)
    · rw [mkApp_mkLam (t_tp := rfl)]
      apply mem_ofTerm_toSb <;> assumption
  case fst_pair' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_fst, mem_ofTerm_pair,
      forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ _ _ hΓ₂ _ _ _ _ _ hA₂ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₂; clear hA₂
    refine ⟨_, ‹_›, ‹_›, _, ‹_›, _,
      ⟨‹_›, _, ‹_›, _, ‹_›, _, ⟨_, ‹_›, _, rfl, _, ‹_›, _, ‹_›, ?_, rfl⟩, ?_, rfl⟩, ?_, ?_⟩
    · refine Part.mem_unique ‹_› ?_
      apply mem_ofType_toSb <;> assumption
    · apply mkPair_tp
    · rwa [mkFst_mkPair]
    · rw [mkFst_mkPair]
  case snd_pair' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_snd, mem_ofTerm_pair,
      forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i hΓ _ _ hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ _ _ hΓ₂ _ _ _ _ _ hA₂ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hΓ hΓ₂; clear hΓ₂
    cases Part.mem_unique hA hA₂; clear hA₂
    refine ⟨_, ‹_›, ‹_›, _, ?_, _, ⟨‹_›, _, ‹_›, _, ‹_›, _,
      ⟨_, ‹_›, _, rfl, _, ‹_›, _, ‹_›, ?_, rfl⟩, ?_, rfl⟩, ?_, rfl⟩
    · rwa [mkSnd_mkPair]
    · refine Part.mem_unique ‹_› ?_
      apply mem_ofType_toSb <;> assumption
    · apply mkPair_tp
    · rwa [mkSnd_mkPair]
  case idRec_refl' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_idRec, mem_ofTerm_refl, mem_ofType_Id, ofTerm_bvar,
      forall_exists_index, and_imp]
    intros; subst_eqs
    rename_i et _ i _ _ _ _ _ _ hΓ ilen _ hA _ hΓ' _ _ ht _ hΓ₁ _ _ hA₁ _ llen _ hΓ₂
      _ _ hr hA₂ _ _ _ hv rtp _ utp M hM
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hΓ hΓ₁
    cases Part.mem_unique hΓ hΓ₂
    cases Part.mem_unique hA hA₁
    cases Part.mem_unique hA hA₂
    cases Part.mem_unique (mem_ofTerm_wk ilen ht) ‹_›
    simp only [CObj.mem_var_zero, exists_const] at hv; subst hv
    refine ⟨_, ‹_›, ‹_›, _, ‹_›, _,
      ⟨‹_›, _, ‹_›, _, rfl, _, by simp, M, hM, _, ‹_›, ?_,
        _, ‹_›, rfl, _, ⟨_, ‹_›, rfl⟩, by simp⟩, ‹_›, rfl⟩
    refine Part.mem_unique rtp ?_
    refine (s.mem_ofType_ofTerm_subst llen
      (.snoc (.sub1 _ _ _ rfl ht) _ _ (.refl i et) ?_ ?_) ?_).1 hM
    · exact mem_ofTerm_refl.2 ⟨_, ht, rfl⟩
    · rfl
  case lam_app' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_app, mem_ofTerm_lam, mem_ofType_pi, ofTerm_bvar,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i l _ _ _ _ _ hΓ _ A hA _ hΓ' _ _ hA₁ _ _ hΓ₁ _ _ hA₂ _ hB _ _ _ hB₁ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ⟨_, ‹_›, _, ‹_›, ‹_›⟩, _, ‹_›, ⟨_, ‹_›, _,
      ⟨‹_›, _, mem_ofTerm_wk _ ‹_› .., _, (CObj.mem_var_zero (x := s[l].var _)).2 ⟨rfl, rfl⟩, _, _,
        _, (mem_ofType_ofTerm_subst _ (.up (.wk _ _) _ _ _ ?_) (CSb.up_toSb _)).1 ‹_›, ?_, rfl⟩,
      .symm (s.etaExpand_eq (f_tp := ‹_›) ..)⟩, rfl⟩
    · simp
    · simp [*, comp_mkPi, substWk]
  case pair_fst_snd' => as_aux_lemma =>
    simp only [mem_ofCtx_snoc, mem_ofTerm_pair, mem_ofTerm_fst, mem_ofTerm_snd, mem_ofType_sigma,
      sup_lt_iff, forall_exists_index, and_imp, exists_true_left]
    intros; subst_eqs
    rename_i l _ _ _ _ Γ hΓ _ A hA _ hΓ' hl _ hA₁ hl' _ hΓ₁ _ _ hA₂ _ hB _ _ sB hB₁ _
    cases Part.mem_unique hΓ hΓ'; clear hΓ'
    cases Part.mem_unique hΓ hΓ₁; clear hΓ₁
    cases Part.mem_unique hA hA₁; clear hA₁
    cases Part.mem_unique hA hA₂; clear hA₂
    cases Part.mem_unique hB hB₁; clear hB₁
    refine ⟨_, ‹_›, ‹_›, _, ⟨_, ‹_›, _, ‹_›, ‹_›⟩, _, ‹_›,
      ⟨_, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, A, by simp, _, ‹_›,
        _, ⟨‹_›, _, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩, by simp, ?_⟩, rfl⟩
    exact (mkPair_mkFst_mkSnd (p_tp := ‹_›) ..).symm
  case code_el => as_aux_lemma =>
    simp only [mem_ofType_univ, mem_ofTerm_code, mem_ofType_el,
      exists_const, exists_eq_left, Nat.add_lt_add_iff_right,
      Nat.add_right_cancel_iff, exists_prop_eq', forall_exists_index, and_imp]
    intros
    refine ⟨_, ‹_›, ‹_›, _, ‹_›, ⟨_, ⟨_, _, ‹_›, ‹_›, rfl⟩, ?_⟩, ‹_›⟩
    rw [UHomSeq.code_el]
  case conv_eq => as_aux_lemma =>
    rintro _ _ _ _ _ _ _ _ ⟨_, hΓ, _, _, hA, _, _, _, rfl⟩ ⟨_, hΓ', _, _, hA', _⟩
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique hA hA'
    exact ⟨_, ‹_›, ‹_›, _, ‹_›, _, ‹_›, ‹_›, rfl⟩
  case refl_tm => as_aux_lemma =>
    rintro _ _ _ _ _ ⟨_, _, _, _, _, _, _, _⟩
    exact ⟨_, ‹_›, ‹_›, _, ‹_›, _, ‹_›, ‹_›, ‹_›⟩
  case symm_tm' => as_aux_lemma =>
    rintro _ _ _ _ _ _ _ _ ⟨_, _, _, _, _, _, _, _, _⟩
    exact ⟨_, ‹_›, ‹_›, _, ‹_›, _, ‹_›, ‹_›, ‹_›⟩
  case trans_tm' => as_aux_lemma =>
    rintro _ _ _ _ _ _ _ _ _ _ ⟨_, hΓ, _, _, _, _, _, ht₁, _⟩ ⟨_, hΓ', _, _, _, _, ht₂, _, _⟩
    cases Part.mem_unique hΓ hΓ'
    cases Part.mem_unique ht₁ ht₂
    exact ⟨_, ‹_›, ‹_›, _, ‹_›, _, ‹_›, ‹_›, ‹_›⟩

/-- Given `Γ` s.t. `WfCtx Γ`, return `⟦Γ⟧`. -/
def interpCtx {Γ : Ctx} (H : WfCtx Γ) : s.CObj :=
  (s.ofCtx Γ).get <| (ofType_ofTerm_sound slen).1 H

@[simp] theorem interpCtx_mem {Γ : Ctx} (H : WfCtx Γ) : interpCtx slen H ∈ ofCtx s Γ :=
  Part.get_mem ..

/-- Given `Γ, l, A` s.t. `Γ ⊢[l] A`, return `⟦A⟧_⟦Γ⟧`. -/
def interpType
    {Γ : Ctx} {l : Nat} {A : Expr} (H : Γ ⊢[l] A) (lt : l < s.length + 1)
    (sΓ : s.CObj) (sΓ_mem : sΓ ∈ ofCtx s Γ) :
    y(sΓ.1) ⟶ s[l].Ty :=
  (ofType sΓ l A).get <| by
    have ⟨_, h1, _, h2⟩ := (ofType_ofTerm_sound slen).2.1 H
    cases Part.mem_unique sΓ_mem h1
    exact h2

@[simp] theorem interpType_mem {Γ l A} (H : Γ ⊢[l] A) (lt : l < s.length + 1)
    (sΓ : s.CObj) (sΓ_mem : sΓ ∈ ofCtx s Γ) : interpType slen H lt sΓ sΓ_mem ∈ ofType sΓ l A :=
  Part.get_mem ..

theorem interpType_eq {Γ l A B} (H : Γ ⊢[l] A ≡ B) (lt : l < s.length + 1)
    (sΓ : s.CObj) (sΓ_mem : sΓ ∈ ofCtx s Γ) :
    interpType slen H.wf_left lt sΓ sΓ_mem = interpType slen H.wf_right lt sΓ sΓ_mem := by
  have ⟨_, h1, _, _, ⟨_, H⟩, _, rfl⟩ := (ofType_ofTerm_sound slen).2.2.1 H
  cases Part.mem_unique sΓ_mem h1
  exact H

/-- Given `Γ, l, t, A` s.t. `Γ ⊢[l] t : A`, return `⟦t⟧_⟦Γ⟧`. -/
def interpTerm
    {Γ : Ctx} {l : Nat} {t A : Expr} (H : Γ ⊢[l] t : A) (lt : l < s.length + 1)
    (sΓ : s.CObj) (sΓ_mem : sΓ ∈ ofCtx s Γ) :
    y(sΓ.1) ⟶ s[l].Tm :=
  (ofTerm sΓ l t).get <| by
    have ⟨_, h1, _, _, _, _, ⟨h2, rfl⟩, _⟩ := (ofType_ofTerm_sound slen).2.2.2.1 H
    cases Part.mem_unique sΓ_mem h1
    exact h2

@[simp] theorem interpTerm_mem {Γ l t A} (H : Γ ⊢[l] t : A) (lt : l < s.length + 1)
    (sΓ : s.CObj) (sΓ_mem : sΓ ∈ ofCtx s Γ) : interpTerm slen H lt sΓ sΓ_mem ∈ ofTerm sΓ l t :=
  Part.get_mem ..

@[simp] theorem interpTerm_tp {Γ l t A} (H : Γ ⊢[l] t : A) (lt : l < s.length + 1)
    (sΓ : s.CObj) (sΓ_mem : sΓ ∈ ofCtx s Γ) :
    interpTerm slen H lt sΓ sΓ_mem ≫ s[l].tp = interpType slen H.wf_tp lt sΓ sΓ_mem := by
  have ⟨_, h1, _, _, ⟨_, rfl⟩, _, ⟨_, rfl⟩, H⟩ := (ofType_ofTerm_sound slen).2.2.2.1 H
  cases Part.mem_unique sΓ_mem h1
  exact H

theorem interpTerm_eq {Γ l t u A} (H : Γ ⊢[l] t ≡ u : A) (lt : l < s.length + 1)
    (sΓ : s.CObj) (sΓ_mem : sΓ ∈ ofCtx s Γ) :
    interpTerm slen H.wf_left lt sΓ sΓ_mem = interpTerm slen H.wf_right lt sΓ sΓ_mem := by
  have ⟨_, h1, _, _, _, _, ⟨_, H⟩, ⟨_, rfl⟩, _⟩ := (ofType_ofTerm_sound slen).2.2.2.2 H
  cases Part.mem_unique sΓ_mem h1
  exact H

end UHomSeq
end NaturalModel
