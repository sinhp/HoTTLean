import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import HoTTLean.ForMathlib
import HoTTLean.ForMathlib.Tactic.CategoryTheory.FunctorMap
import HoTTLean.ForMathlib.CategoryTheory.RepPullbackCone
import HoTTLean.ForMathlib.CategoryTheory.WeakPullback
import HoTTLean.ForMathlib.CategoryTheory.Polynomial

universe u v

noncomputable section

open CategoryTheory Limits Opposite

namespace UnstructuredModel

/-- A natural model with support for dependent types (and nothing more).
The data is a natural transformation with representable fibers,
stored as a choice of representative for each fiber. -/
structure Universe (Ctx : Type u) [Category Ctx] where
  Tm : Ctx
  Ty : Ctx
  tp : Tm ⟶ Ty
  ext {Γ : Ctx} (A : Γ ⟶ Ty) : Ctx
  disp {Γ : Ctx} (A : Γ ⟶ Ty) : ext A ⟶ Γ
  var {Γ : Ctx} (A : Γ ⟶ Ty) : ext A ⟶ Tm
  disp_pullback {Γ : Ctx} (A : Γ ⟶ Ty) :
    IsPullback (var A) (disp A) tp A

namespace Universe

variable {Ctx : Type u} [Category Ctx] (M : Universe Ctx)

/-! ## Pullback of representable natural transformation -/

/-- Pull a natural model back along a type. -/
protected def pullback {Γ : Ctx} (A : Γ ⟶ M.Ty) : Universe Ctx where
  Tm := M.ext A
  Ty := Γ
  tp := M.disp A
  ext := fun B => M.ext (B ≫ A)
  disp := fun B => M.disp (B ≫ A)
  var := fun B => (M.disp_pullback A).lift (M.var (B ≫ A))
    (M.disp (B ≫ A) ≫ B) (by simp [(M.disp_pullback (B ≫ A)).w])
  disp_pullback := fun B =>
    IsPullback.of_right' (M.disp_pullback (B ≫ A)) (M.disp_pullback A)

/--
  Given the pullback square on the right,
  with a natural model structure on `tp : Tm ⟶ Ty`
  giving the outer pullback square.

  Γ.A -.-.- var -.-,-> E ------ toTm ------> Tm
   |                   |                      |
   |                   |                      |
 M.disp                π                     tp
   |                   |                      |
   V                   V                      V
  Γ ------- A -------> U ------ toTy ------> Ty

  construct a natural model structure on `π : E ⟶ U`,
  by pullback pasting.
-/
def ofIsPullback {U E : Ctx} {π : E ⟶ U}
    {toTy : U ⟶ M.Ty} {toTm : E ⟶ M.Tm}
    (pb : IsPullback toTm π M.tp toTy) :
    Universe Ctx where
  Ty := U
  Tm := E
  tp := π
  ext A := M.ext (A ≫ toTy)
  disp A := M.disp (A ≫ toTy)
  var A := pb.lift (M.var (A ≫ toTy)) (M.disp (A ≫ toTy) ≫ A)
    (by simp [(M.disp_pullback (A ≫ toTy)).w])
  disp_pullback A := IsPullback.of_right' (M.disp_pullback (A ≫ toTy)) pb

/-! ## Substitutions -/

/--
```
Δ ⊢ σ : Γ  Γ ⊢ A type  Δ ⊢ t : A[σ]
-----------------------------------
Δ ⊢ σ.t : Γ.A
```
 ------ Δ ------ t --------¬
 |      ↓ substCons         ↓
 |   M.ext A ---var A---> M.Tm
 |      |                  |
 σ      |                  |
 |    disp A              M.tp
 |      |                  |
 |      V                  V
  ---> Γ ------ A -----> M.Ty
-/
def substCons {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty)
    (t : Δ ⟶ M.Tm) (t_tp : t ≫ M.tp = σ ≫ A) :
    Δ ⟶ M.ext A :=
  (M.disp_pullback A).lift t σ t_tp

@[reassoc (attr := simp)]
theorem substCons_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (t : Δ ⟶ M.Tm)
    (tTp : t ≫ M.tp = σ ≫ A) :
    M.substCons σ A t tTp ≫ M.disp A = σ := by
  simp [substCons]

@[reassoc (attr := simp)]
theorem substCons_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (t : Δ ⟶ M.Tm)
    (aTp : t ≫ M.tp = σ ≫ A) :
    M.substCons σ A t aTp ≫ M.var A = t := by
  simp [substCons]

@[simp]
theorem comp_substCons {Θ Δ Γ : Ctx} (τ : Θ ⟶ Δ) (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (t : Δ ⟶ M.Tm)
    (aTp : t ≫ M.tp = σ ≫ A) :
    τ ≫ M.substCons σ A t aTp = M.substCons (τ ≫ σ) A (τ ≫ t) (by simp [*]) := by
  apply (M.disp_pullback A).hom_ext
  · simp
  · simp

/--
```
Δ ⊢ σ : Γ.A
------------
Δ ⊢ ↑∘σ : Γ
```
-/
def substFst {Δ Γ : Ctx} {A : Γ ⟶ M.Ty} (σ : Δ ⟶ M.ext A) : Δ ⟶ Γ :=
  σ ≫ M.disp A

/--
```
Δ ⊢ σ : Γ.A
-------------------
Δ ⊢ v₀[σ] : A[↑∘σ]
```
-/
def substSnd {Δ Γ : Ctx} {A : Γ ⟶ M.Ty} (σ : Δ ⟶ M.ext A) : Δ ⟶ M.Tm :=
  σ ≫ M.var A

theorem substSnd_tp {Δ Γ : Ctx} {A : Γ ⟶ M.Ty} (σ : Δ ⟶ M.ext A) :
    M.substSnd σ ≫ M.tp = (M.substFst σ) ≫ A := by
  simp [substSnd, substFst]; rw [(M.disp_pullback _).w]

@[reassoc (attr := simp)]
theorem var_tp {Γ : Ctx} (A : Γ ⟶ M.Ty) : M.var A ≫ M.tp = (M.disp A) ≫ A := by
  simp [(M.disp_pullback A).w]

/--
Weaken a substitution.
```
Δ ⊢ σ : Γ  Γ ⊢ A type  A' = A[σ]
------------------------------------
Δ.A' ⊢ ↑≫σ : Γ  Δ.A' ⊢ v₀ : A[↑≫σ]
------------------------------------
Δ.A' ⊢ (↑≫σ).v₀ : Γ.A
```
-/
def substWk {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty)
    (A' := σ ≫ A) (eq : σ ≫ A = A' := by rfl) : M.ext A' ⟶ M.ext A :=
  M.substCons (M.disp _ ≫ σ) A (M.var _) (by simp [eq])

@[reassoc]
theorem substWk_disp {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (A' eq) :
    M.substWk σ A A' eq ≫ M.disp A = M.disp A' ≫ σ := by
  simp [substWk]

@[reassoc (attr := simp)]
theorem substWk_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (A' eq) :
    M.substWk σ A A' eq ≫ M.var A = M.var A' := by
  simp [substWk]

/-- `sec` is the section of `disp A` corresponding to `a`.

  ===== Γ ------ a --------¬
 ‖      ↓ sec             V
 ‖   M.ext A -----------> M.Tm
 ‖      |                  |
 ‖      |                  |
 ‖    disp A              M.tp
 ‖      |                  |
 ‖      V                  V
  ===== Γ ------ A -----> M.Ty -/
def sec {Γ : Ctx} (A : Γ ⟶ M.Ty) (a : Γ ⟶ M.Tm) (a_tp : a ≫ M.tp = A) : Γ ⟶ M.ext A :=
  M.substCons (𝟙 Γ) A a (by simp [a_tp])

@[reassoc (attr := simp)]
theorem sec_disp {Γ : Ctx} (A : Γ ⟶ M.Ty) (a : Γ ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    M.sec A a a_tp ≫ M.disp A = 𝟙 _ := by
  simp [sec]

@[reassoc (attr := simp)]
theorem sec_var {Γ : Ctx} (A : Γ ⟶ M.Ty) (a : Γ ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    M.sec A a a_tp ≫ M.var A = a := by
  simp [sec]

@[reassoc]
theorem comp_sec {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (σA) (eq : σ ≫ A = σA)
    (a : Γ ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    σ ≫ M.sec A a a_tp = M.sec σA (σ ≫ a) (by simp [eq, a_tp]) ≫ M.substWk σ A _ eq := by
  apply (M.disp_pullback _).hom_ext <;>
    simp [sec, substWk]

structure PolymorphicSigma (U0 U1 U2 : Universe Ctx) where
    (Sig : ∀ {Γ} {A : Γ ⟶ U0.Ty}, (U0.ext A ⟶ U1.Ty) → (Γ ⟶ U2.Ty))
    (Sig_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (A : Γ ⟶ U0.Ty) {σA} (eq) (B : U0.ext A ⟶ U1.Ty),
      Sig (U0.substWk σ A σA eq ≫ B) = σ ≫ Sig B)
    (pair : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (a : Γ ⟶ U0.Tm)
      (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm) (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B),
      Γ ⟶ U2.Tm)
    (pair_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) (B : U0.ext A ⟶ U1.Ty)
      (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm)
      (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B),
      pair (U0.substWk σ A σA eq ≫ B) (σ ≫ a) (by cat_disch) (σ ≫ b)
        (by simp [b_tp, comp_sec_assoc, eq]) =
        σ ≫ pair B a a_tp b b_tp)
    (pair_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
      (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm)
      (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B),
        pair B a a_tp b b_tp ≫ U2.tp = Sig B)
    (fst : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
      (s_tp : s ≫ U2.tp = Sig B), Γ ⟶ U0.Tm)
    (fst_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) {B : U0.ext A ⟶ U1.Ty}
      (s : Γ ⟶ U2.Tm) (s_tp : s ≫ U2.tp = Sig B),
      fst (U0.substWk σ A σA eq ≫ B) (σ ≫ s) (by cat_disch) = σ ≫ fst B s s_tp)
    (fst_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
      (s_tp : s ≫ U2.tp = Sig B), fst B s s_tp ≫ U0.tp = A)
    (snd : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
      (s_tp : s ≫ U2.tp = Sig B), Γ ⟶ U1.Tm)
    (snd_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) {B : U0.ext A ⟶ U1.Ty}
      (s : Γ ⟶ U2.Tm) (s_tp : s ≫ U2.tp = Sig B),
      snd (U0.substWk σ A σA eq ≫ B) (σ ≫ s) (by cat_disch) = σ ≫ snd B s s_tp)
    (snd_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
      (s_tp : s ≫ U2.tp = Sig B), snd B s s_tp ≫ U1.tp = U0.sec A (fst B s s_tp) (fst_tp ..) ≫ B)
    (fst_pair : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
      (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm)
      (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B), fst B (pair B a a_tp b b_tp) (pair_tp ..) = a)
    (snd_pair : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
      (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm)
      (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B), snd B (pair B a a_tp b b_tp) (pair_tp ..) = b)
    (eta : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
      (s_tp : s ≫ U2.tp = Sig B), pair B (fst B s s_tp) (fst_tp ..) (snd B s s_tp) (snd_tp ..) = s)

-- def Sigma.mk'' {U0 U1 U2 : Universe R}
--     (Sig : ∀ {Γ} {A : Γ ⟶ U0.Ty}, (U0.ext A ⟶ U1.Ty) → (Γ ⟶ U2.Ty))
--     (Sig_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (A : Γ ⟶ U0.Ty) {σA} (eq) (B : U0.ext A ⟶ U1.Ty),
--       Sig (U0.substWk σ A σA eq ≫ B) = σ ≫ Sig B)
--     (pair : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (a : Γ ⟶ U0.Tm)
--       (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm) (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B),
--       Γ ⟶ U2.Tm)
--     (pair_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) (B : U0.ext A ⟶ U1.Ty)
--       (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm)
--       (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B),
--       pair (U0.substWk σ A σA eq ≫ B) (σ ≫ a) (by cat_disch) (σ ≫ b)
--         (by simp [b_tp, comp_sec_assoc, eq]) =
--         σ ≫ pair B a a_tp b b_tp)
--     (pair_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty)
--       (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) (b : Γ ⟶ U1.Tm)
--       (b_tp : b ≫ U1.tp = U0.sec A a a_tp ≫ B),
--         pair B a a_tp b b_tp ≫ U2.tp = Sig B)
--     (fst : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
--       (s_tp : s ≫ U2.tp = Sig B), Γ ⟶ U0.Tm)
--     (fst_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) {B : U0.ext A ⟶ U1.Ty}
--       (s : Γ ⟶ U2.Tm) (s_tp : s ≫ U2.tp = Sig B),
--       fst (U0.substWk σ A σA eq ≫ B) (σ ≫ s) (by cat_disch) = σ ≫ fst B s s_tp)
--     (fst_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
--       (s_tp : s ≫ U2.tp = Sig B), fst B s s_tp ≫ U0.tp = A)
--     (snd : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
--       (s_tp : s ≫ U2.tp = Sig B), Γ ⟶ U1.Tm)
--     (snd_comp : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ U0.Ty} {σA} (eq) {B : U0.ext A ⟶ U1.Ty}
--       (s : Γ ⟶ U2.Tm) (s_tp : s ≫ U2.tp = Sig B),
--       snd (U0.substWk σ A σA eq ≫ B) (σ ≫ s) (by cat_disch) = σ ≫ snd B s s_tp)
--     (snd_tp : ∀ {Γ} {A : Γ ⟶ U0.Ty} (B : U0.ext A ⟶ U1.Ty) (s : Γ ⟶ U2.Tm)
--       (s_tp : s ≫ U2.tp = Sig B), snd B s s_tp ≫ U1.tp = U0.sec A (fst B s s_tp) (fst_tp ..) ≫ B)
--     (fst_pair : sorry)
--     (snd_pair : sorry)
--     (eta : sorry)
--     : PolymorphicSigma U0 U1 U2 :=
--     sorry
