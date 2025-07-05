import GroupoidModel.Syntax.Basic

/-! Implementation of simultaneous substitutions
following Schäfer/Tebbi/Smolka in
*Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution*. -/

namespace Expr

/-- Append an element to a substitution or a renaming.
```
Δ ⊢ σ : Γ  Γ ⊢ A  Δ ⊢ t : A[σ]
------------------------------
Δ ⊢ σ.t : Γ.A
``` -/
def snoc.{u} {X : Sort u} (σ : Nat → X) (x : X) : Nat → X
  | 0   => x
  | n+1 => σ n

@[simp]
theorem snoc_zero {X} (σ : Nat → X) (x : X) : snoc σ x 0 = x := rfl

@[simp]
theorem snoc_succ {X} (σ : Nat → X) (x : X) (n) : snoc σ x (n + 1) = σ n := rfl

/-! ## Renaming -/

/-- Lift a renaming under a binder. See `up`. -/
def upr (ξ : Nat → Nat) : Nat → Nat :=
  snoc (fun i => ξ i + 1) 0

@[simp]
theorem upr_id : upr id = id := by
  ext i; cases i <;> dsimp [upr, snoc]

/-- Rename the de Bruijn indices in an expression. -/
def rename (ξ : Nat → Nat) : Expr → Expr
  | .bvar i => .bvar (ξ i)
  | .pi l l' A B => .pi l l' (A.rename ξ) (B.rename (upr ξ))
  | .sigma l l' A B => .sigma l l' (A.rename ξ) (B.rename (upr ξ))
  | .lam l l' A t => .lam l l' (A.rename ξ) (t.rename (upr ξ))
  | .app l l' B fn arg => .app l l' (B.rename (upr ξ)) (fn.rename ξ) (arg.rename ξ)
  | .pair l l' B t u => .pair l l' (B.rename (upr ξ)) (t.rename ξ) (u.rename ξ)
  | .fst l l' A B p => .fst l l' (A.rename ξ) (B.rename (upr ξ)) (p.rename ξ)
  | .snd l l' A B p => .snd l l' (A.rename ξ) (B.rename (upr ξ)) (p.rename ξ)
  | .univ l => .univ l
  | .el a => .el (a.rename ξ)
  | .code A => .code (A.rename ξ)

/-! ## Substitution -/

/-- Lift a substitution under a binder.
```
Δ ⊢ σ : Γ  Γ ⊢ A
------------------------
Δ.A[σ] ⊢ (↑≫σ).v₀ : Γ.A
```

Warning: don't unfold this definition! Use `up_eq_snoc` instead. -/
@[irreducible]
def up (σ : Nat → Expr) : Nat → Expr :=
  snoc (fun i => (σ i).rename Nat.succ) (.bvar 0)

@[simp]
theorem up_bvar : up Expr.bvar = Expr.bvar := by
  ext i; cases i <;> (unfold up; dsimp [snoc, rename])

/-- Apply a substitution to an expression. -/
def subst (σ : Nat → Expr) : Expr → Expr
  | .bvar i => σ i
  | .pi l l' A B => .pi l l' (A.subst σ) (B.subst (up σ))
  | .sigma l l' A B => .sigma l l' (A.subst σ) (B.subst (up σ))
  | .lam l l' A t => .lam l l' (A.subst σ) (t.subst (up σ))
  | .app l l' B fn arg => .app l l' (B.subst (up σ)) (fn.subst σ) (arg.subst σ)
  | .pair l l' B t u => .pair l l' (B.subst (up σ)) (t.subst σ) (u.subst σ)
  | .fst l l' A B p => .fst l l' (A.subst σ) (B.subst (up σ)) (p.subst σ)
  | .snd l l' A B p => .snd l l' (A.subst σ) (B.subst (up σ)) (p.subst σ)
  | .univ l => .univ l
  | .el a => .el (a.subst σ)
  | .code A => .code (A.subst σ)

@[simp]
theorem subst_bvar : subst Expr.bvar = id := by
  ext t; dsimp; induction t <;> grind [subst, up_bvar]

@[simp]
theorem subst_snoc_zero (σ : Nat → Expr) (t : Expr) : subst (snoc σ t) (.bvar 0) = t := by
  dsimp [subst, snoc]

/-- Turn a renaming into a substitution. -/
def ofRen (ξ : Nat → Nat) : Nat → Expr :=
  fun i => Expr.bvar (ξ i)

@[simp]
theorem ofRen_id : ofRen id = Expr.bvar := rfl

theorem ofRen_upr (ξ) : ofRen (upr ξ) = up (ofRen ξ) := by
  ext i; cases i <;> simp [ofRen, upr, up, snoc, rename]

theorem rename_eq_subst_ofRen (ξ : Nat → Nat) : rename ξ = subst (ofRen ξ) := by
  ext t
  induction t generalizing ξ <;> dsimp [rename, subst]
  case bvar => simp [ofRen]
  all_goals grind [ofRen_upr]

/-- Compose two substitutions.
```
Θ ⊢ σ : Δ  Δ ⊢ τ : Γ
--------------------
Θ ⊢ σ≫τ : Γ
``` -/
def comp (σ τ : Nat → Expr) : Nat → Expr :=
  fun i => (τ i).subst σ

@[simp]
theorem bvar_comp (σ) : comp Expr.bvar σ = σ := by
  ext i; simp [comp]

@[simp]
theorem comp_bvar (σ) : comp σ Expr.bvar = σ := by
  ext i; simp [comp, subst]

theorem up_comp_ren_sb (ξ : Nat → Nat) (σ : Nat → Expr) :
    up (fun i => σ (ξ i)) = fun i => up σ (upr ξ i) := by
  ext i; cases i <;> (unfold up; dsimp [snoc, upr])

theorem rename_subst (σ ξ) (t : Expr) : (t.rename ξ).subst σ = t.subst (fun i => σ (ξ i)) := by
  induction t generalizing σ ξ
  all_goals dsimp [rename, subst]
  case pi | sigma | lam | app | pair | fst | snd =>
    conv => rhs; rw [up_comp_ren_sb]
    grind
  all_goals grind

theorem up_comp_sb_ren (σ : Nat → Expr) (ξ : Nat → Nat) :
    up (fun i => (σ i).rename ξ) = fun i => (up σ i).rename (upr ξ) := by
  ext i; cases i <;> (unfold up; dsimp [snoc, rename, upr])
  conv => lhs; rw [rename_eq_subst_ofRen, rename_subst]
  conv => rhs; rw [rename_eq_subst_ofRen, rename_subst]
  rfl

theorem subst_rename (ξ σ) (t : Expr) :
    (t.subst σ).rename ξ = t.subst (fun i => (σ i).rename ξ) := by
  induction t generalizing ξ σ
  all_goals dsimp [subst, rename]
  case pi | sigma | lam | app | pair | fst | snd =>
    conv => rhs; rw [up_comp_sb_ren]
    grind
  all_goals grind

theorem up_comp (σ τ : Nat → Expr) :
    up (comp σ τ) = comp (up σ) (up τ) := by
  ext i; unfold up comp snoc; cases i
  . rfl
  . grind [rename_subst, subst_rename]

theorem subst_subst (σ τ : Nat → Expr) (t : Expr) :
    (t.subst τ).subst σ = t.subst (comp σ τ) := by
  induction t generalizing σ τ
  case bvar => dsimp [subst, comp]
  all_goals grind [subst, up_comp]

theorem comp_assoc (σ τ ρ) : comp σ (comp τ ρ) = comp (comp σ τ) ρ := by
  ext i
  conv => rhs; enter [0]; unfold comp
  rw [← subst_subst]; dsimp [comp]

theorem comp_snoc (σ τ : Nat → Expr) (t : Expr) :
    comp σ (snoc τ t) = snoc (comp σ τ) (t.subst σ) := by
  ext i; cases i <;> dsimp [comp, snoc]

/-- The weakening substitution.
```
Γ ⊢ A
------------
Γ.A ⊢ ↑ : Γ
``` -/
def wk : Nat → Expr :=
  ofRen Nat.succ

@[simp]
theorem ofRen_succ : ofRen Nat.succ = wk := rfl

theorem up_eq_snoc (σ : Nat → Expr) : up σ = snoc (comp wk σ) (.bvar 0) := by
  ext i; unfold up comp; congr 1; ext j
  rw [rename_eq_subst_ofRen]; congr 1

@[simp]
theorem snoc_comp_wk (σ : Nat → Expr) (t) : comp (snoc σ t) wk = σ := by
  ext i; cases i <;> dsimp [comp, snoc, wk, ofRen, subst, -ofRen_succ]

@[simp]
theorem snoc_wk_zero : snoc wk (Expr.bvar 0) = Expr.bvar := by
  ext i; cases i <;> dsimp [snoc, wk, ofRen, -ofRen_succ]

/-- A substitution that instantiates one binder.
```
Γ ⊢ t : A
--------------
Γ ⊢ id.t : Γ.A
``` -/
def toSb (t : Expr) : Nat → Expr :=
  snoc Expr.bvar t

/-! ## Decision procedure -/

theorem snoc_comp_wk_zero_subst (σ) : snoc (comp σ Expr.wk) ((Expr.bvar 0).subst σ) = σ := by
  ext i; cases i <;> dsimp [snoc, comp, subst, wk, ofRen, -ofRen_succ]

-- Rules from Fig. 1 in the paper.
attribute [autosubst low]
  subst
attribute [autosubst]
  subst_snoc_zero
  snoc_zero -- Not in the paper, but seems needed.
  snoc_comp_wk
  snoc_succ -- Same.
  subst_bvar
  snoc_comp_wk_zero_subst
  comp_bvar
  bvar_comp
  comp_assoc
  comp_snoc
  subst_subst
  snoc_wk_zero

-- Rules to unfold abbreviations.
attribute [autosubst high]
  up_eq_snoc
  toSb

-- More rules to deal with renamings. These are ad-hoc, not from paper.
attribute [autosubst low]
  rename
attribute [autosubst]
  rename_eq_subst_ofRen
  ofRen_id
  ofRen_succ
  ofRen_upr

-- Cleanup rules.
attribute [autosubst]
  id_eq

/-- Decides equality of substitutions applied to expressions. -/
macro "autosubst" : tactic => `(tactic| simp only [autosubst])

end Expr
