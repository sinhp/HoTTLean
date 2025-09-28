import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
-- import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Presheaf
-- import Poly.UvPoly.UPFan

import HoTTLean.ForMathlib
import HoTTLean.ForMathlib.Tactic.CategoryTheory.FunctorMap
import HoTTLean.ForMathlib.CategoryTheory.Yoneda
import HoTTLean.ForMathlib.CategoryTheory.RepPullbackCone
import HoTTLean.ForMathlib.CategoryTheory.WeakPullback
import HoTTLean.ForMathlib.CategoryTheory.Polynomial

universe v u

noncomputable section

open CategoryTheory Limits Opposite

namespace NaturalModel

/-- A natural model with support for dependent types (and nothing more).
The data is a natural transformation with representable fibers,
stored as a choice of representative for each fiber. -/
structure Universe {Ctx : Type u} [Category Ctx] (R : MorphismProperty Ctx) where
  Tm : Ctx
  Ty : Ctx
  tp : Tm ⟶ Ty
  morphismProperty : R tp
  ext {Γ : Ctx} (A : Γ ⟶ Ty) : Ctx
  disp {Γ : Ctx} (A : Γ ⟶ Ty) : ext A ⟶ Γ
  var {Γ : Ctx} (A : Γ ⟶ Ty) : ext A ⟶ Tm
  disp_pullback {Γ : Ctx} (A : Γ ⟶ Ty) :
    IsPullback (var A) (disp A) tp A

namespace Universe

variable {Ctx : Type u} [Category Ctx] {R : MorphismProperty Ctx} (M : Universe R)
  [R.HasPullbacks] [R.IsStableUnderBaseChange]

instance {Γ : Ctx} (A : Γ ⟶ M.Ty) : HasPullback A M.tp := by
  let tp : M.Tm ⟶(R) M.Ty := ⟨ M.tp, M.morphismProperty ⟩
  convert_to HasPullback A tp.1
  apply MorphismProperty.instHasPullbackFstHomOfHasPullbacks

@[simps! hom inv]
def pullbackIsoExt {Γ : Ctx} (A : Γ ⟶ M.Ty) :
    pullback A M.tp ≅ (M.ext A) :=
  IsPullback.isoPullback (M.disp_pullback A).flip |>.symm

/-! ## Pullback of representable natural transformation -/

/-- Pull a natural model back along a type. -/
protected def pullback {Γ : Ctx} (A : Γ ⟶ M.Ty) : Universe R where
  Tm := M.ext A
  Ty := Γ
  tp := M.disp A
  morphismProperty := R.of_isPullback (disp_pullback ..) M.morphismProperty
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
    Universe R where
  Ty := U
  Tm := E
  tp := π
  morphismProperty := R.of_isPullback pb M.morphismProperty
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
  apply Yoneda.fullyFaithful.map_injective
  simp [substCons]

@[reassoc (attr := simp)]
theorem substCons_var {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (t : Δ ⟶ M.Tm)
    (aTp : t ≫ M.tp = σ ≫ A) :
    (M.substCons σ A t aTp) ≫ M.var A = t := by
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
    (M.substWk σ A A' eq) ≫ M.var A = M.var A' := by
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
    (M.sec A a a_tp) ≫ M.var A = a := by
  simp [sec]

@[reassoc]
theorem comp_sec {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) (σA) (eq : σ ≫ A = σA)
    (a : Γ ⟶ M.Tm) (a_tp : a ≫ M.tp = A) :
    σ ≫ M.sec A a a_tp = M.sec σA (σ ≫ a) (by simp [eq, a_tp]) ≫ M.substWk σ A _ eq := by
  apply (M.disp_pullback _).hom_ext <;>
    simp [sec, substWk]

/-! ## Polynomial functor on `tp`

Specializations of results from the `Poly` package to natural models. -/

abbrev uvPolyTp : UvPoly R M.Tm M.Ty := ⟨M.tp, M.morphismProperty⟩

variable [ChosenTerminal Ctx] [R.HasObjects] [R.IsMultiplicative]
  [R.HasPushforwards R] [R.IsStableUnderPushforward R]

instance : HasTerminal Ctx := IsTerminal.hasTerminal (ChosenTerminal.isTerminal)

def Ptp : Ctx ⥤ Ctx := M.uvPolyTp.functor

namespace PtpEquiv

variable {Γ : Ctx} {X : Ctx}

/--
A map `(AB : Γ ⟶ M.Ptp.obj X)` is equivalent to a pair of maps
`A : Γ ⟶ M.Ty` and `B : (M.ext (fst M AB)) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`.
`PtpEquiv.fst` is the `A` in this pair.
-/
def fst (AB : Γ ⟶ M.Ptp.obj X) : Γ ⟶ M.Ty :=
  UvPoly.Equiv.fst AB

/--
A map `(AB : Γ ⟶ M.Ptp.obj X)` is equivalent to a pair of maps
`A : Γ ⟶ M.Ty` and `B : (M.ext (fst M AB)) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`
`PtpEquiv.snd` is the `B` in this pair.
-/
def snd (AB : Γ ⟶ M.Ptp.obj X) (A := fst M AB) (eq : fst M AB = A := by rfl) : M.ext A ⟶ X :=
  UvPoly.Equiv.snd' AB (by rw [← fst, eq]; exact (M.disp_pullback _).flip)

/--
A map `(AB : Γ ⟶ M.Ptp.obj X)` is equivalent to a pair of maps
`A : Γ ⟶ M.Ty` and `B : (M.ext (fst M AB)) ⟶ X`,
thought of as a dependent pair `A : Type` and `B : A ⟶ Type`
`PtpEquiv.mk` constructs such a map `AB` from such a pair `A` and `B`.
-/
def mk (A : Γ ⟶ M.Ty) (B : M.ext A ⟶ X) : Γ ⟶ M.Ptp.obj X :=
  UvPoly.Equiv.mk' A (M.disp_pullback _).flip B

@[simp]
lemma fst_mk (A : Γ ⟶ M.Ty) (B : M.ext A ⟶ X) :
    fst M (mk M A B) = A := by
  simp [fst, mk]

@[simp]
lemma snd_mk (A : Γ ⟶ M.Ty) (B : M.ext A ⟶ X) :
    snd M (mk M A B) _ (fst_mk ..) = B := by
  dsimp only [snd, mk]
  rw! [UvPoly.Equiv.snd'_mk']

section
variable {Δ : Ctx} {σ : Δ ⟶ Γ} {AB : Γ ⟶ M.Ptp.obj X}

theorem fst_comp_left (σ : Δ ⟶ Γ) : fst M (σ ≫ AB) = σ ≫ fst M AB :=
  UvPoly.Equiv.fst_comp_left ..

@[simp]
theorem fst_comp_right {Y} (σ : X ⟶ Y) : fst M (AB ≫ M.Ptp.map σ) = fst M AB :=
  UvPoly.Equiv.fst_comp_right ..

theorem snd_comp_right {Y} (σ : X ⟶ Y) {A} (eq : fst M AB = A) :
    snd M (AB ≫ M.Ptp.map σ) _ (by simpa) = snd M AB _ eq ≫ σ := by
  simp only [snd, Ptp]
  rw [UvPoly.Equiv.snd'_comp_right]

theorem snd_comp_left {A} (eqA : fst M AB = A) {σA} (eqσ : σ ≫ A = σA) :
    snd M (σ ≫ AB) σA (by simp [fst_comp_left, eqA, eqσ]) =
    (M.substWk σ _ _ eqσ) ≫ snd M AB _ eqA := by
  have H1 : IsPullback (M.disp A) (M.var A) (UvPoly.Equiv.fst AB) M.tp := by
    rw [← fst, eqA]; exact (M.disp_pullback _).flip
  have H2 : IsPullback (M.disp σA) (M.var σA)
    (σ ≫ UvPoly.Equiv.fst AB) M.tp := by
    rw [← fst, eqA, eqσ]; exact (M.disp_pullback _).flip
  convert UvPoly.Equiv.snd'_comp_left AB H1 _ H2
  apply H1.hom_ext <;> simp [substWk]

theorem mk_comp_left {Δ Γ : Ctx} (M : Universe R) (σ : Δ ⟶ Γ)
    {X : Ctx} (A : Γ ⟶ M.Ty) (σA) (eq : σ ≫ A = σA) (B : (M.ext A) ⟶ X) :
    σ ≫ PtpEquiv.mk M A B = PtpEquiv.mk M σA ((M.substWk σ A _ eq) ≫ B) := by
  dsimp [PtpEquiv.mk]
  have h := UvPoly.Equiv.mk'_comp_left (P := M.uvPolyTp) A (f := M.disp A) (g := M.var A)
    (by convert (M.disp_pullback A).flip) B σ σA eq (M.disp_pullback σA).flip
  convert h
  apply (M.disp_pullback _).hom_ext
  · simp
  · simp [substWk_disp]

theorem mk_comp_right {Γ : Ctx} (M : Universe R)
    {X Y : Ctx} (σ : X ⟶ Y) (A : Γ ⟶ M.Ty) (B : (M.ext A) ⟶ X) :
    PtpEquiv.mk M A B ≫ M.Ptp.map σ = PtpEquiv.mk M A (B ≫ σ) :=
  UvPoly.Equiv.mk'_comp_right ..

theorem ext {AB AB' : Γ ⟶ M.Ptp.obj X} (A := fst M AB) (eq : fst M AB = A := by rfl)
    (h1 : fst M AB = fst M AB') (h2 : snd M AB A eq = snd M AB' A (h1 ▸ eq)) :
  AB = AB' := UvPoly.Equiv.ext' _ h1 h2

theorem eta (AB : Γ ⟶ M.Ptp.obj X) : mk M (fst M AB) (snd M AB) = AB :=
  .symm <| ext _ _ rfl (by simp) (by simp)

end

end PtpEquiv

@[reassoc]
theorem PtpEquiv.mk_map {Γ : Ctx} {X Y : Ctx}
    (A : Γ ⟶ M.Ty) (x : (M.ext A) ⟶ X) (α : X ⟶ Y) :
    mk M A x ≫ M.Ptp.map α = mk M A (x ≫ α) := by
  simp [mk, Ptp, UvPoly.Equiv.mk'_comp_right]

/-! ## Polynomial composition `M.tp ▸ N.tp` -/

-- -- `private` lemma for the equivalence below.
-- private lemma lift_ev {Γ : Ctx} {N : Universe Ctx}
--     {AB : Γ ⟶ M.Ptp.obj N.Ty} {α : Γ ⟶ M.Tm}
--     (hA : AB ≫ M.uvPolyTp.fstProj N.Ty = α ≫ M.tp) :
--     pullback.lift AB α hA ≫ (UvPoly.PartialProduct.fan M.uvPolyTp N.Ty).snd =
--       (M.sec (α ≫ M.tp) α rfl) ≫
--         (M.disp_pullback _).lift (M.var _) (M.disp _)
--           (by dsimp; rw [hA, (M.disp_pullback _).w]) ≫
--         (M.Ptp_equiv AB).2 :=
--   sorry

abbrev compDom (M N : Universe R) : Ctx := M.uvPolyTp.compDom N.uvPolyTp

abbrev compP (M N : Universe R) : M.compDom N ⟶ M.uvPolyTp @ N.Ty :=
  (M.uvPolyTp.comp N.uvPolyTp).p

namespace compDomEquiv
open UvPoly

variable {M N : Universe R} {Γ Δ : Ctx} (σ : Δ ⟶ Γ)

/-- Universal property of `compDom`, decomposition (part 1).

A map `ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`. The map `fst : Γ ⟶ M.Tm`
is the `(a : A)` in `(a : A) × (b : B a)`.
-/
abbrev fst (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp) : Γ ⟶ M.Tm :=
  UvPoly.compDomEquiv.fst ab

/-- Computation of `comp` (part 1).

`fst_tp` is (part 1) of the computation that
      (α, B, β, h)
     Γ ⟶ compDom
      \        |
       \       | comp
(α ≫ tp, B)    |
         \     V
           >  P_tp Ty
Namely the first projection `α ≫ tp` agrees.
-/
theorem fst_tp (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp) :
    fst ab ≫ M.tp = PtpEquiv.fst M (ab ≫ M.compP N) :=
  UvPoly.compDomEquiv.fst_comp_p ..

@[reassoc]
theorem fst_comp (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp) (σ : Δ ⟶ Γ) :
    fst (σ ≫ ab) = σ ≫ fst ab :=
  UvPoly.compDomEquiv.fst_comp ..

/-- Universal property of `compDom`, decomposition (part 2).

A map `ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The map `dependent : (M.ext (fst N ab ≫ M.tp)) ⟶ M.Ty`
is the `B : A ⟶ Type` in `(a : A) × (b : B a)`.
Here `A` is implicit, derived by the typing of `fst`, or `(a : A)`.
-/
def dependent (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    (A := fst ab ≫ M.tp) (eq : fst ab ≫ M.tp = A := by rfl) :
    (M.ext A) ⟶ N.Ty :=
  UvPoly.compDomEquiv.dependent ab (M.disp A) (M.var A) <| by
    simpa [eq] using (M.disp_pullback A).flip

lemma dependent_eq (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    (A := fst ab ≫ M.tp) (eq : fst ab ≫ M.tp = A := by rfl) :
    dependent ab A eq = Universe.PtpEquiv.snd M (ab ≫ M.compP N) A (by simp [← eq, fst_tp]) := by
  simp [dependent, UvPoly.compDomEquiv.dependent, PtpEquiv.snd]

theorem comp_dependent (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq1 : fst ab ≫ M.tp = A)
    {σA} (eq2 : σ ≫ A = σA) :
    (substWk M σ _ _ eq2) ≫ dependent ab A eq1 =
    dependent (σ ≫ ab) σA (by simp [fst_comp, eq1, eq2]) := by
  dsimp [dependent]
  rw [UvPoly.compDomEquiv.dependent_comp σ ab (M.disp A) (M.var A)
    (by simpa [eq1] using (M.disp_pullback A).flip)]
  · congr 1
    simp [substWk, substCons]
    apply (M.disp_pullback A).hom_ext <;> simp

/-- Universal property of `compDom`, decomposition (part 3).

A map `ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The map `snd : Γ ⟶ M.Tm`
is the `(b : B a)` in `(a : A) × (b : B a)`.
-/
abbrev snd (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp) : Γ ⟶ N.Tm :=
  UvPoly.compDomEquiv.snd ab

@[reassoc]
theorem snd_comp (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp) (σ : Δ ⟶ Γ) :
    snd (σ ≫ ab) = σ ≫ snd ab :=
  UvPoly.compDomEquiv.snd_comp ..

/-- Universal property of `compDom`, decomposition (part 4).

A map `ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The equation `snd_tp` says that the type of `b : B a` agrees with
the expression for `B a` obtained solely from `dependent`, or `B : A ⟶ Type`.
-/
theorem snd_tp (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq : fst ab ≫ M.tp = A := by rfl) :
    snd ab ≫ N.tp = (M.sec _ (fst ab) eq) ≫ dependent ab A eq := by
  rw [UvPoly.compDomEquiv.snd_comp_p ab (M.disp A) (M.var A) <| by
    simpa [eq] using (M.disp_pullback A).flip]
  congr 1
  apply (disp_pullback ..).hom_ext
  · simp
  · simp

/-- Universal property of `compDom`, constructing a map into `compDom`. -/
def mk (α : Γ ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) (B : M.ext A ⟶ N.Ty) (β : Γ ⟶ N.Tm)
    (h : β ≫ N.tp = M.sec _ α eq ≫ B) : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp :=
  UvPoly.compDomEquiv.mk _ α eq (M.disp A) (M.var A) (M.disp_pullback A).flip B β (by
    convert h
    apply (disp_pullback ..).hom_ext <;> simp)

@[simp]
theorem fst_mk (α : Γ ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) (B : (M.ext A) ⟶ N.Ty) (β : Γ ⟶ N.Tm)
    (h : β ≫ N.tp = (M.sec _ α eq) ≫ B) : fst (mk α eq B β h) = α := by
  simp [mk, fst]

@[simp]
theorem dependent_mk (α : Γ ⟶ M.Tm) {A A'} (eq : α ≫ M.tp = A) (hA' : A' = A)
    (B : M.ext A ⟶ N.Ty) (β : Γ ⟶ N.Tm)
    (h : β ≫ N.tp = (M.sec _ α eq) ≫ B) :
    dependent (mk α eq B β h) A' (by simp [hA', fst_mk, eq]) = eqToHom (by rw [hA']) ≫ B := by
  subst hA'
  simp [mk, dependent]

@[simp]
theorem snd_mk (α : Γ ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) (B : (M.ext A) ⟶ N.Ty) (β : Γ ⟶ N.Tm)
    (h : β ≫ N.tp = (M.sec _ α eq) ≫ B) : snd (mk α eq B β h) = β := by
  simp [mk, snd]

theorem ext {ab₁ ab₂ : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp}
    {A} (eq : fst ab₁ ≫ M.tp = A)
    (h1 : fst ab₁ = fst ab₂)
    (h2 : dependent ab₁ A eq = dependent ab₂ A (h1 ▸ eq))
    (h3 : snd ab₁ = snd ab₂) : ab₁ = ab₂ := by
  apply UvPoly.compDomEquiv.ext ab₁ ab₂ h1 h3 (M.disp _) (M.var _) (M.disp_pullback _).flip
  dsimp only [dependent] at *
  subst eq
  rw! [h2]

theorem comp_mk (α : Γ ⟶ M.Tm) {A} (e1 : α ≫ M.tp = A) (B : (M.ext A) ⟶ N.Ty)
    (β : Γ ⟶ N.Tm) (e2 : β ≫ N.tp = (M.sec A α e1) ≫ B) (σ : Δ ⟶ Γ) {σA} (e3 : σ ≫ A = σA) :
    σ ≫ mk α e1 B β e2 =
    mk (σ ≫ α) (by simp [e1, e3])
      ((M.substWk σ A _ e3) ≫ B) (σ ≫ β)
      (by simp [e2]; rw [← Category.assoc, comp_sec]; simp; congr!) := by
  dsimp only [mk]
  rw [UvPoly.compDomEquiv.comp_mk σ _ α e1 (M.disp _) (M.var _) (M.disp_pullback _).flip
    (M.disp _) (M.var _) (M.disp_pullback _).flip ]
  subst e1 e3
  congr 2
  apply (disp_pullback ..).hom_ext <;> simp [substWk_disp]

@[reassoc]
lemma mk_comp (α : Γ ⟶ M.Tm) {A} (e1 : α ≫ M.tp = A) (B : (M.ext A) ⟶ N.Ty)
    (β : Γ ⟶ N.Tm) (e2 : β ≫ N.tp = (M.sec A α e1) ≫ B) :
    mk α e1 B β e2 ≫ M.compP N = PtpEquiv.mk M A B := by
  erw [PtpEquiv.mk, UvPoly.compDomEquiv.mk_comp]

theorem eta (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq : fst ab ≫ M.tp = A) :
    mk (fst ab) eq (dependent ab A eq) (snd ab) (snd_tp ab eq) = ab := by
  symm; apply ext (eq := eq) <;> simp

end compDomEquiv

/-! ## Pi types -/

/-- The structure on three universes that for
`A : Γ ⟶ U0.Ty` and `B : Γ.A ⟶ U1.Ty` constructs a Π-type `Π_A B : Γ ⟶ U2.Ty`.
-/
structure PolymorphicPi (U0 U1 U2 : Universe R) where
  Pi : U0.Ptp.obj U1.Ty ⟶ U2.Ty
  lam : U0.Ptp.obj U1.Tm ⟶ U2.Tm
  Pi_pullback : IsPullback lam (U0.Ptp.map U1.tp) U2.tp Pi

set_option linter.dupNamespace false in
/-- A universe `M` has Π-type structure. This is the data of a pullback square
```
       lam
Ptp Tm ------> Tm
  |             |
Ptp tp          |tp
  |             |
  V             V
Ptp Ty ------> Ty
        Pi
```
-/
protected abbrev Pi := PolymorphicPi M M M

/-! ## Sigma types -/

/-- The structure on three universes that for
`A : Γ ⟶ U0.Ty` and `B : Γ.A ⟶ U1.Ty` constructs a Π-type `Σ_A B : Γ ⟶ U2.Ty`. -/
structure PolymorphicSigma (U0 U1 U2 : Universe R) where
  Sig : U0.Ptp.obj U1.Ty ⟶ U2.Ty
  pair : U0.compDom U1 ⟶ U2.Tm
  Sig_pullback : IsPullback pair (U0.compP U1) U2.tp Sig

/-- A universe `M` has Σ-type structure. This is the data of a pullback square
```
        Sig
compDom ------> Tm
  |             |
 compP          |tp
  |             |
  V             V
Ptp Ty ------> Ty
        pair
```
-/
protected abbrev Sigma := PolymorphicSigma M M M

namespace PolymorphicSigma

variable {U0 U1 U2 : Universe R} {Γ : Ctx}

section
variable (S : PolymorphicSigma U0 U1 U2)

/--
```
Γ ⊢₀ A  Γ.A ⊢₁ B
-----------------
Γ ⊢₂ ΣA. B
``` -/
def mkSig {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty) :
    Γ ⟶ U2.Ty :=
  PtpEquiv.mk U0 A B ≫ S.Sig

theorem comp_mkSig {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty) :
    σ ≫ S.mkSig A B =
      S.mkSig (σ ≫ A) ((U0.substWk σ A) ≫ B) := by
  simp [mkSig, ← Category.assoc, PtpEquiv.mk_comp_left]

/--
```
Γ ⊢₀ t : A  Γ ⊢₁ u : B[t]
--------------------------
Γ ⊢₂ ⟨t, u⟩ : ΣA. B
``` -/
def mkPair {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (t : Γ ⟶ U0.Tm) (t_tp : t ≫ U0.tp = A)
    (u : Γ ⟶ U1.Tm) (u_tp : u ≫ U1.tp = U0.sec A t t_tp ≫ B) :
    (Γ) ⟶ U2.Tm :=
  compDomEquiv.mk t t_tp B u u_tp ≫ S.pair

theorem comp_mkPair {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (t : Γ ⟶ U0.Tm) (t_tp : t ≫ U0.tp = A)
    (u : Γ ⟶ U1.Tm) (u_tp : u ≫ U1.tp = U0.sec A t t_tp ≫ B) :
    σ ≫ S.mkPair A B t t_tp u u_tp =
      S.mkPair (σ ≫ A) ((U0.substWk σ A) ≫ B)
        (σ ≫ t) (by simp [t_tp])
        (σ ≫ u) (by simp [u_tp, comp_sec_assoc]) := by
  simp only [← Category.assoc, mkPair]; rw [compDomEquiv.comp_mk]

@[simp]
theorem mkPair_tp {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (t : Γ ⟶ U0.Tm) (t_tp : t ≫ U0.tp = A)
    (u : Γ ⟶ U1.Tm) (u_tp : u ≫ U1.tp = U0.sec A t t_tp ≫ B) :
    S.mkPair A B t t_tp u u_tp ≫ U2.tp = S.mkSig A B := by
  simp [mkPair, Category.assoc, S.Sig_pullback.w, mkSig, compDomEquiv.mk_comp_assoc]

def mkFst {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (p : Γ ⟶ U2.Tm) (p_tp : p ≫ U2.tp = S.mkSig A B) :
    Γ ⟶ U0.Tm :=
  compDomEquiv.fst (S.Sig_pullback.lift p (PtpEquiv.mk _ A B) p_tp)

@[simp]
theorem mkFst_tp {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (p : Γ ⟶ U2.Tm) (p_tp : p ≫ U2.tp = S.mkSig A B) :
    S.mkFst A B p p_tp ≫ U0.tp = A := by
  simp [mkFst, compDomEquiv.fst_tp]

@[simp]
theorem mkFst_mkPair {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (t : Γ ⟶ U0.Tm) (t_tp : t ≫ U0.tp = A)
    (u : Γ ⟶ U1.Tm) (u_tp : u ≫ U1.tp = U0.sec A t t_tp ≫ B) :
    S.mkFst A B (S.mkPair A B t t_tp u u_tp) (by simp) = t := by
  simp [mkFst, mkPair]
  convert compDomEquiv.fst_mk t t_tp B u u_tp using 2
  apply (S.Sig_pullback).hom_ext <;> simp [compDomEquiv.mk_comp]

theorem comp_mkFst {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (p : Γ ⟶ U2.Tm) (p_tp : p ≫ U2.tp = S.mkSig A B) :
    (σ) ≫ S.mkFst A B p p_tp =
      S.mkFst (σ ≫ A) (U0.substWk σ A ≫ B) (σ ≫ p)
        (by simp [p_tp, comp_mkSig]) := by
  simp [mkFst]
  rw [← compDomEquiv.fst_comp]; congr 1
  apply S.Sig_pullback.hom_ext <;> simp [PtpEquiv.mk_comp_left]

def mkSnd {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (p : Γ ⟶ U2.Tm) (p_tp : p ≫ U2.tp = S.mkSig A B) :
    Γ ⟶ U1.Tm :=
  compDomEquiv.snd (S.Sig_pullback.lift p (PtpEquiv.mk _ A B) p_tp)

@[simp]
theorem mkSnd_mkPair {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (t : Γ ⟶ U0.Tm) (t_tp : t ≫ U0.tp = A)
    (u : Γ ⟶ U1.Tm) (u_tp : u ≫ U1.tp = U0.sec A t t_tp ≫ B) :
    S.mkSnd A B (S.mkPair A B t t_tp u u_tp) (by simp) = u := by
  simp [mkSnd, mkPair]
  convert compDomEquiv.snd_mk t t_tp B u u_tp using 2
  apply (S.Sig_pullback).hom_ext <;> simp [compDomEquiv.mk_comp]

protected theorem dependent_eq {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (p : Γ ⟶ U2.Tm) (p_tp : p ≫ U2.tp = S.mkSig A B) :
    compDomEquiv.dependent ((S.Sig_pullback).lift p (PtpEquiv.mk U0 A B) p_tp) A
      (by simp [compDomEquiv.fst_tp]) = B := by
  convert PtpEquiv.snd_mk U0 A B using 2
  simp only [compDomEquiv.dependent, UvPoly.compDomEquiv.dependent, PtpEquiv.snd_mk]
  simp [PtpEquiv.mk]

@[simp]
theorem mkSnd_tp {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (p : Γ ⟶ U2.Tm) (p_tp : p ≫ U2.tp = S.mkSig A B) :
    S.mkSnd A B p p_tp ≫ U1.tp =
      (U0.sec A (S.mkFst A B p p_tp) (by simp)) ≫ B := by
  generalize_proofs h
  simp [mkSnd, compDomEquiv.snd_tp (eq := h), S.dependent_eq]; rfl

theorem comp_mkSnd {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (p : Γ ⟶ U2.Tm) (p_tp : p ≫ U2.tp = S.mkSig A B) :
    σ ≫ S.mkSnd A B p p_tp =
      S.mkSnd (σ ≫ A) (U0.substWk σ A ≫ B) (σ ≫ p)
        (by simp [p_tp, comp_mkSig]) := by
  simp [mkSnd, ← compDomEquiv.snd_comp]; congr 1
  apply (S.Sig_pullback).hom_ext <;> simp
  rw [PtpEquiv.mk_comp_left]

@[simp]
theorem mkPair_mkFst_mkSnd {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (p : Γ ⟶ U2.Tm) (p_tp : p ≫ U2.tp = S.mkSig A B) :
    S.mkPair A B
      (S.mkFst A B p p_tp) (by simp)
      (S.mkSnd A B p p_tp) (by simp) = p := by
  simp [mkFst, mkSnd, mkPair]
  have := compDomEquiv.eta ((S.Sig_pullback).lift p (PtpEquiv.mk _ A B) p_tp)
    (eq := by rw [← mkFst.eq_def, mkFst_tp])
  conv at this => enter [1, 3]; apply S.dependent_eq
  simp [this]

end

end PolymorphicSigma

def Sigma.mk'
    (Sig : ∀ {Γ} {A : Γ ⟶ M.Ty}, (M.ext A ⟶ M.Ty) → (Γ ⟶ M.Ty))
    (comp_Sig : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) {σA} (eq) (B : M.ext A ⟶ M.Ty),
      σ ≫ Sig B = Sig (M.substWk σ A σA eq ≫ B))
    (assoc : ∀ {Γ} {A : Γ ⟶ M.Ty} (B : M.ext A ⟶ M.Ty), M.ext B ≅ M.ext (Sig B))
    (comp_assoc : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ M.Ty} {σA} (eq) (B : M.ext A ⟶ M.Ty),
      substWk _ (substWk _ σ _ _ eq) _ ≫ (assoc B).hom =
      (assoc (substWk M σ A σA eq ≫ B)).hom ≫ substWk M σ _ _ (comp_Sig ..))
    (assoc_disp : ∀ {Γ} {A : Γ ⟶ M.Ty} (B : M.ext A ⟶ M.Ty),
      (assoc B).hom ≫ M.disp _ = M.disp _ ≫ M.disp _) :
    M.Sigma := sorry


/--
Universe.IdIntro consists of the following commutative square
       refl
M.Tm ------> M.Tm
 |            |
 |            |
diag         M.tp
 |            |
 |            |
 V            V
 k --------> M.Ty
      Id

where `K` (for "Kernel" of `tp`) is a chosen pullback for the square
       k1
 k ---------> Tm
 |             |
 |             |
 k2            | tp
 |             |
 V             V
Tm ----------> Ty
        tp
and `diag` denotes the diagonal into the pullback `K`.

We require a choice of pullback because,
although all pullbacks exist in presheaf categories,
when constructing a model it is convenient to know
that `k` is some specific construction on-the-nose.
-/
structure IdIntro where
  k : Ctx
  k1 : k ⟶ M.Tm
  k2 : k ⟶ M.Tm
  isKernelPair : IsKernelPair M.tp k1 k2
  Id : k ⟶ M.Ty
  refl : M.Tm ⟶ M.Tm
  refl_tp : refl ≫ M.tp =
    (IsPullback.lift isKernelPair (𝟙 M.Tm) (𝟙 M.Tm) (by simp)) ≫ Id

namespace IdIntro

variable {M} (idIntro : IdIntro M) {Γ : Ctx}

@[simps] def k2UvPoly : UvPoly R idIntro.k M.Tm :=
  ⟨idIntro.k2, R.of_isPullback idIntro.isKernelPair M.morphismProperty⟩

/-- The introduction rule for identity types.
To minimize the number of arguments, we infer the type from the terms. -/
def mkId (a0 a1 : Γ ⟶ M.Tm)
    (a0_tp_eq_a1_tp : a0 ≫ M.tp = a1 ≫ M.tp) :
    Γ ⟶ M.Ty :=
  idIntro.isKernelPair.lift a1 a0 (by rw [a0_tp_eq_a1_tp]) ≫ idIntro.Id

theorem comp_mkId {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (a0 a1 : Γ ⟶ M.Tm) (eq : a0 ≫ M.tp = a1 ≫ M.tp) :
    σ ≫ mkId idIntro a0 a1 eq =
      mkId idIntro (σ ≫ a0) (σ ≫ a1) (by simp [eq]) := by
  simp [mkId]; rw [← Category.assoc]; congr 1
  apply idIntro.isKernelPair.hom_ext <;> simp

def mkRefl (a : Γ ⟶ M.Tm) : Γ ⟶ M.Tm :=
  a ≫ idIntro.refl

theorem comp_mkRefl {Δ Γ : Ctx} (σ : Δ ⟶ Γ) (a : Γ ⟶ M.Tm) :
    σ ≫ idIntro.mkRefl a = idIntro.mkRefl (σ ≫ a) := by
  simp [mkRefl]

@[simp]
theorem mkRefl_tp (a : Γ ⟶ M.Tm) :
    idIntro.mkRefl a ≫ M.tp = idIntro.mkId a a rfl := by
  simp only [mkRefl, Category.assoc, idIntro.refl_tp, mkId]
  rw [← Category.assoc]
  congr 1
  apply idIntro.isKernelPair.hom_ext <;> simp

/-- The context appearing in the motive for identity elimination `J`
  Γ ⊢ A
  Γ ⊢ a : A
  Γ.(x:A).(h:Id(A,a,x)) ⊢ M
  ...
-/
def motiveCtx (a : Γ ⟶ M.Tm) : Ctx :=
  M.ext (idIntro.mkId ((M.disp (a ≫ M.tp)) ≫ a) (M.var _) (by simp))

def motiveSubst {Γ Δ} (σ : Δ ⟶ Γ) (a : Γ ⟶ M.Tm) :
    motiveCtx idIntro (σ ≫ a) ⟶ motiveCtx idIntro a := by
  refine substWk _ (substWk _ σ _ _ (by simp)) _ _ ?_
  simp [comp_mkId]; congr 1; simp only [← Category.assoc, substWk_disp]

/-- The substitution `(a,refl)` appearing in identity elimination `J`
  `(a,refl) : Γ ⟶ (Γ.(x:A).(h:Id(A,a,x)))`
  so that we can write
  `Γ ⊢ r : M(a,refl)`
-/
def reflSubst (a : Γ ⟶ M.Tm) : Γ ⟶ idIntro.motiveCtx a :=
  M.substCons (M.substCons (𝟙 Γ) (a ≫ M.tp) a (by simp)) _ (idIntro.mkRefl a) (by
    simp only [mkRefl_tp, mkId, ← Category.assoc]
    congr 1
    apply idIntro.isKernelPair.hom_ext <;> simp)

@[reassoc]
theorem comp_reflSubst' {Γ Δ} (σ : Δ ⟶ Γ) (a : Γ ⟶ M.Tm) :
    σ ≫ (idIntro.reflSubst a) =
    (idIntro.reflSubst (σ ≫ a)) ≫ (idIntro.motiveSubst σ a) := by
  apply (M.disp_pullback _).hom_ext <;> simp [reflSubst, motiveSubst, mkRefl]
  apply (M.disp_pullback _).hom_ext <;> simp [substWk]

@[simp, reassoc]
lemma comp_reflSubst (a : Γ ⟶ M.Tm) {Δ} (σ : Δ ⟶ Γ) :
    reflSubst idIntro (σ ≫ a) ≫ idIntro.motiveSubst σ a = σ ≫ reflSubst idIntro a := by
  apply Yoneda.fullyFaithful.map_injective
  simp [Functor.map_comp, comp_reflSubst']

def toK (ii : IdIntro M) (a : Γ ⟶ M.Tm) : (M.ext (a ≫ M.tp)) ⟶ ii.k :=
  ii.isKernelPair.lift (M.var _) ((M.disp _) ≫ a) (by simp)

lemma toK_comp_k1 (ii : IdIntro M) (a : Γ ⟶ M.Tm) : ii.toK a ≫ ii.k1 = M.var _ := by
  simp [toK]

lemma ext_a_tp_isPullback (ii : IdIntro M) (a : Γ ⟶ M.Tm) :
    IsPullback (ii.toK a) (M.disp _) ii.k2 a :=
  IsPullback.of_right' (M.disp_pullback _) ii.isKernelPair

end IdIntro

/-- The full structure interpreting the natural model semantics for identity types
requires an `IdIntro` and an elimination rule `j` which satisfies a typing rule `j_tp`
and a β-rule `reflSubst_j`.
There is an equivalent formulation of these extra conditions later in `Id1`
that uses the language of polynomial endofunctors.

Note that the universe/model `N` for the motive `C` is different from the universe `M` that the
identity type lives in.
-/
protected structure Id' (i : IdIntro M) (N : Universe R) where
  j {Γ} (a : Γ ⟶ M.Tm) (C : (IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : Γ ⟶ N.Tm)
    (r_tp : r ≫ N.tp = (i.reflSubst a) ≫ C) :
    (i.motiveCtx a) ⟶ N.Tm
  j_tp {Γ} (a : Γ ⟶ M.Tm) (C : (IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : Γ ⟶ N.Tm)
    (r_tp : r ≫ N.tp = (i.reflSubst a) ≫ C) : j a C r r_tp ≫ N.tp = C
  comp_j {Γ Δ} (σ : Δ ⟶ Γ)
    (a : Γ ⟶ M.Tm) (C : (IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : Γ ⟶ N.Tm)
    (r_tp : r ≫ N.tp = (i.reflSubst a) ≫ C) :
    (i.motiveSubst σ _) ≫ j a C r r_tp =
    j (σ ≫ a) ((i.motiveSubst σ _) ≫ C) (σ ≫ r) (by
      simp [r_tp, IdIntro.comp_reflSubst'_assoc])
  reflSubst_j {Γ} (a : Γ ⟶ M.Tm) (C : (IdIntro.motiveCtx _ a) ⟶ N.Ty) (r : Γ ⟶ N.Tm)
    (r_tp : r ≫ N.tp = (i.reflSubst a) ≫ C) :
    (i.reflSubst a) ≫ j a C r r_tp = r

namespace Id'

variable {M} {N : Universe R} {ii : M.IdIntro} (i : M.Id' ii N) {Γ : Ctx} (a : Γ ⟶ M.Tm)
  (C : (ii.motiveCtx a) ⟶ N.Ty) (r : Γ ⟶ N.Tm)
  (r_tp : r ≫ N.tp = (ii.reflSubst a) ≫ C) (b : Γ ⟶ M.Tm) (b_tp : b ≫ M.tp = a ≫ M.tp)
  (h : Γ ⟶ M.Tm) (h_tp : h ≫ M.tp = ii.isKernelPair.lift b a (by aesop) ≫ ii.Id)

def endPtSubst : Γ ⟶ ii.motiveCtx a :=
  M.substCons (M.substCons (𝟙 _) _ b (by aesop)) _ h (by
    simp only [h_tp, IdIntro.mkId, ← Category.assoc]
    congr 1
    apply ii.isKernelPair.hom_ext
    · simp
    · simp)

/-- The elimination rule for identity types, now with the parameters as explicit terms.
  `Γ ⊢ A` is the type with a term `Γ ⊢ a : A`.
  `Γ (y : A) (p : Id(A,a,y)) ⊢ C` is the motive for the elimination.
  `Γ ⊢ b : A` is a second term in `A` and `Γ ⊢ h : Id(A,a,b)` is a path from `a` to `b`.
  Then `Γ ⊢ mkJ' : C [b/y,h/p]` is a term of the motive with `b` and `h` substituted
-/
def mkJ : Γ ⟶ N.Tm :=
  (endPtSubst a b b_tp h h_tp) ≫ i.j a C r r_tp

/-- Typing for elimination rule `J` -/
lemma mkJ_tp : i.mkJ a C r r_tp b b_tp h h_tp ≫ N.tp = (endPtSubst a b b_tp h h_tp) ≫ C := by
  rw [mkJ, Category.assoc, i.j_tp]

/-- β rule for identity types. Substituting `J` with `refl` gives the user-supplied value `r` -/
lemma mkJ_refl : i.mkJ a C r r_tp a rfl (ii.mkRefl a) (by aesop) = r :=
  calc (endPtSubst a a _ (ii.mkRefl a) _) ≫ i.j a C r r_tp
    _ = (ii.reflSubst a) ≫ i.j a C r r_tp := rfl
    _ = r := by rw [i.reflSubst_j]

end Id'

variable {M}
/--
`UniverseBase.IdElimBase` extends the structure `UniverseBase.IdIntro`
with a chosen pullback of `Id`
       i1
 i --------> M.Tm
 |            |
 |            |
i2           M.tp
 |            |
 V            V
 k --------> M.Ty
      Id

Again, we always have a pullback,
but when we construct a natural model,
this may not be definitionally equal to the pullbacks we construct,
for example using context extension.
-/
structure IdElimBase (ii : IdIntro M) where
  i : Ctx
  i1 : i ⟶ M.Tm
  i2 : i ⟶ ii.k
  i_isPullback : IsPullback i1 i2 M.tp ii.Id

namespace IdElimBase
variable {ii : IdIntro M} (ie : IdElimBase ii)

@[simps] def i2UvPoly : UvPoly R ie.i ii.k :=
  ⟨ie.i2, R.of_isPullback ie.i_isPullback M.morphismProperty⟩

/-- The comparison map `M.tm ⟶ i` induced by the pullback universal property of `i`.

          refl
 M.Tm --------->
           i1
 |   i --------> M.Tm
 |   |            |
diag |            |
 |  i2           M.tp
 |   |            |
 |   V            V
 V   k --------> M.Ty
          Id
-/
def comparison : M.Tm ⟶ ie.i :=
  ie.i_isPullback.lift ii.refl
  (IsPullback.lift ii.isKernelPair (𝟙 M.Tm) (𝟙 M.Tm) (by simp))
  ii.refl_tp

@[simp]
lemma comparison_comp_i1 : ie.comparison ≫ ie.i1 = ii.refl := by
  simp [comparison]

@[simp, reassoc]
lemma comparison_comp_i2_comp_k1 : ie.comparison ≫ ie.i2 ≫ ii.k1 =
    𝟙 _ := by
  simp [comparison]

@[simp, reassoc]
lemma comparison_comp_i2_comp_k2 : ie.comparison ≫ ie.i2 ≫ ii.k2 =
    𝟙 _ := by
  simp [comparison]

/-- `i` over `Tm` can be informally thought of as the context extension
`(A : Ty).(a b : A).(p : Id(a,b)) ->> (A : Ty) (a : A)`
which is defined by the composition of (maps informally thought of as) context extensions
`(A : Ty).(a b : A).(p : Id(a,b)) ->> (A : Ty).(a b : A) ->> (A : Ty).(a : A)`
This is the signature for a polynomial functor `iUvPoly` on the presheaf category `Ctx`.
-/
abbrev iUvPoly : UvPoly R ie.i M.Tm :=
  ie.i2UvPoly.vcomp ii.k2UvPoly

/-- The functor part of the polynomial endofunctor `iOverUvPoly` -/
abbrev iFunctor : Ctx ⥤ Ctx := ie.iUvPoly.functor

/-- Consider the comparison map `comparison : Tm ⟶ i` in the slice over `Tm`.
Then the contravariant action `UVPoly.verticalNatTrans` of taking `UvPoly` on a slice
results in a natural transformation `P_iOver ⟶ P_(𝟙 Tm)`
between the polynomial endofunctors `iUvPoly` and `UvPoly.id M.Tm` respectively.
  comparison
Tm ----> i
 \      /
 𝟙\    /i2 ≫ k2
   \  /
    VV
    Tm
-/
def verticalNatTrans : ie.iFunctor ⟶ (UvPoly.id R M.Tm).functor :=
    UvPoly.verticalNatTrans (UvPoly.id R M.Tm) ie.iUvPoly
  ie.comparison (by simp [iUvPoly])

section reflCase

variable (i : IdIntro M) {N : Universe R}

variable {Γ : Ctx} (a : Γ ⟶ M.Tm) (r : Γ ⟶ N.Tm)

lemma reflCase_aux : IsPullback (𝟙 Γ) a a (UvPoly.id R M.Tm).p :=
  have : IsIso (UvPoly.id R M.Tm).p := by simp; infer_instance
  IsPullback.of_horiz_isIso (by simp)

/-- The variable `r` witnesses the motive for the case `refl`,
This gives a map `(a,r) : Γ ⟶ P_𝟙Tm Tm ≅ Tm × Tm` where
```
    fst ≫ r
N.Tm <--   Γ  --------> Tm
    <      ‖            ‖
     \     ‖   (pb)     ‖ 𝟙_Tm
    r \    ‖            ‖
       \   ‖            ‖
        \  Γ  --------> Tm
                 a
```
-/
def reflCase : Γ ⟶ (UvPoly.id R M.Tm).functor.obj N.Tm :=
  UvPoly.Equiv.mk' a (pb := Γ) (f := 𝟙 _) (g := a) (reflCase_aux a) r
-- TODO: consider generalizing
-- TODO: consider showing UvPoly on identity `(P_𝟙_Y X)` is isomorphic to product `Y × X`

end reflCase

open IdElimBase IdIntro

section Equiv

variable {Γ : Ctx} {X : Ctx}
/-
section
variable (a : Γ ⟶ M.Tm)
/-
In the following lemmas we build the following diagram of pullbacks,
where `pullback` is the pullback of `i₂ ≫ k₂` along `a` given by `HasPullback`.
  X
  Λ
  |
  | x
  |
 (Γ.a≫tp.Id(...)) ------> i ------> Tm
  |                        |         |
  |                        | i₂      V
  |                        |         Ty
  V                        V
 (Γ.a≫tp) ------------>   k ------> Tm
  |                        |    k₁   |
  |                        |k₂       |tp
  |                        |         |
  |                        V         V
  Γ ---------------->   Tm -----> Ty
               a               tp
-/

lemma toK_comp_left {Δ} (σ : Δ ⟶ Γ) : ii.toK (σ ≫ a) =
    (M.substWk σ (a ≫ M.tp)) ≫ ii.toK a := by
  dsimp [toK]
  apply ii.isKernelPair.hom_ext
  -- FIXME: `transparency := .default` is like `erw` and should be avoided
  · rw! (transparency := .default) [Category.assoc]
    simp
  · simp only [IsKernelPair.lift_snd, Category.assoc]
    slice_rhs 1 2 => rw [← Functor.map_comp, substWk_disp]
    -- FIXME: `transparency := .default` is like `erw` and should be avoided
    rw! (transparency := .default) [Category.assoc]
    simp

def toI : (ii.motiveCtx a) ⟶ ie.i :=
  ie.i_isPullback.lift (M.var _) ((M.disp _) ≫ toK ii a)
  (by rw [(M.disp_pullback _).w]; simp [IdIntro.mkId, toK])

lemma toI_comp_i1 : ie.toI a ≫ ie.i1 = M.var _ := by simp [toI]

lemma toI_comp_i2 : ie.toI a ≫ ie.i2 = (M.disp _) ≫ ii.toK a :=
  by simp [toI]

lemma toI_comp_left {Δ} (σ : Δ ⟶ Γ) : toI ie (σ ≫ a) =
    (ii.motiveSubst σ a) ≫ toI ie a := by
  dsimp [toI]
  apply ie.i_isPullback.hom_ext
  · simp [motiveSubst]
  · simp [toK_comp_left, motiveSubst, substWk, substCons]
    rfl

theorem motiveCtx_isPullback :
    IsPullback (ie.toI a) (M.disp _) ie.i2 (toK ii a) :=
  IsPullback.of_right' (M.disp_pullback _) ie.i_isPullback

theorem motiveCtx_isPullback' :
    IsPullback (ie.toI a) ((M.disp (ii.mkId ((M.disp (a ≫ M.tp)) ≫ a)
      (M.var (a ≫ M.tp)) (by simp))) ≫ (M.disp (a ≫ M.tp))) (iUvPoly ie).p a :=
  IsPullback.paste_vert (ie.motiveCtx_isPullback a)
    (ii.ext_a_tp_isPullback a)

def equivMk (x : (ii.motiveCtx a) ⟶ X) : Γ ⟶ ie.iFunctor.obj X :=
  UvPoly.Equiv.mk' ie.iUvPoly X a (ie.motiveCtx_isPullback' a).flip x

def equivFst (pair : Γ ⟶ ie.iFunctor.obj X) :
    Γ ⟶ M.Tm :=
  UvPoly.Equiv.fst ie.iUvPoly X pair

lemma equivFst_comp_left (pair : Γ ⟶ ie.iFunctor.obj X)
    {Δ} (σ : Δ ⟶ Γ) :
    ie.equivFst (σ ≫ pair) = σ ≫ ie.equivFst pair := by
  dsimp [equivFst]
  rw [UvPoly.Equiv.fst_comp_left]

def equivSnd (pair : Γ ⟶ ie.iFunctor.obj X) :
    (ii.motiveCtx (equivFst ie pair)) ⟶ X :=
  UvPoly.Equiv.snd' ie.iUvPoly X pair (ie.motiveCtx_isPullback' _).flip

lemma equivSnd_comp_left (pair : Γ ⟶ ie.iFunctor.obj X)
    {Δ} (σ : Δ ⟶ Γ) :
    ie.equivSnd (σ ≫ pair) =
    (ii.motiveSubst σ _) ≫ ie.equivSnd pair := by
  dsimp only [equivSnd]
  let a := ie.equivFst pair
  have H : IsPullback (ie.toI a)
    ((M.disp (ii.mkId ((M.disp (a ≫ M.tp)) ≫ a) (M.var (a ≫ M.tp)) _)) ≫
    (M.disp (a ≫ M.tp))) ie.iUvPoly.p
    (UvPoly.Equiv.fst ie.iUvPoly X pair) := (motiveCtx_isPullback' _ _)
  have H' : IsPullback ((M.disp
      (ii.mkId ((M.disp (ie.equivFst (σ ≫ pair) ≫ M.tp)) ≫
      ie.equivFst (σ ≫ pair))
      (M.var (ie.equivFst (σ ≫ pair) ≫ M.tp)) _)) ≫
      (M.disp (ie.equivFst (σ ≫ pair) ≫ M.tp)))
      (ie.toI (ie.equivFst (σ ≫ pair)))
      (σ ≫ UvPoly.Equiv.fst ie.iUvPoly X pair)
      ie.iUvPoly.p :=
    (motiveCtx_isPullback' _ _).flip
  rw [UvPoly.Equiv.snd'_comp_left (H := H.flip) (H' := H')]
  · congr 1
    have h : ie.toI (ie.equivFst (σ ≫ pair)) =
        (ii.motiveSubst σ (ie.equivFst pair)) ≫ ie.toI a :=
      ie.toI_comp_left a σ
    apply (IsPullback.flip H).hom_ext
    · simp only [iUvPoly_p, Category.assoc, IsPullback.lift_fst]
      simp [motiveSubst, substWk, substCons, a]; rfl
    · apply ie.i_isPullback.hom_ext
      · simp [IsPullback.lift_snd, h]
      · apply ii.isKernelPair.hom_ext
        · simp [IsPullback.lift_snd, h]
        · simp only [iUvPoly_p, IsPullback.lift_snd, IdElimBase.toI_comp_i2, ← h, toI_comp_i2]

lemma equivFst_verticalNatTrans_app {Γ : Ctx} {X : Ctx}
    (pair : Γ ⟶ ie.iFunctor.obj X) :
    ie.equivFst pair = UvPoly.Equiv.fst (UvPoly.id M.Tm) X
    (pair ≫ ie.verticalNatTrans.app X) := by
  dsimp [equivFst, verticalNatTrans]
  rw [← UvPoly.fst_verticalNatTrans_app]

lemma equivSnd_verticalNatTrans_app {Γ : Ctx} {X : Ctx}
    (pair : Γ ⟶ ie.iFunctor.obj X) :
    UvPoly.Equiv.snd' (UvPoly.id M.Tm) X (pair ≫ ie.verticalNatTrans.app X)
      (R := Γ) (f := 𝟙 _) (g := ie.equivFst pair) (by
        convert reflCase_aux (ie.equivFst pair)
        rw [equivFst_verticalNatTrans_app]) =
      (ii.reflSubst (ie.equivFst pair)) ≫
      ie.equivSnd pair :=
  calc _
  _ = _ ≫ ie.equivSnd pair := by
    dsimp [equivSnd, verticalNatTrans]
    rw [UvPoly.snd'_verticalNatTrans_app (UvPoly.id M.Tm) ie.iUvPoly
      (ie.comparison) _ _ pair _]
    apply reflCase_aux (ie.equivFst pair)
  _ = _ := by
    congr 1
    apply (M.disp_pullback _).hom_ext
    · conv => lhs; rw [← toI_comp_i1 ie]
      simp [reflSubst, comparison, mkRefl]
    · apply (M.disp_pullback _).hom_ext
      · slice_lhs 3 4 => rw [← ii.toK_comp_k1]
        slice_lhs 2 3 => rw [← ie.toI_comp_i2]
        simp [reflSubst]
      · simp [reflSubst]

lemma equivMk_comp_verticalNatTrans_app {Γ : Ctx} {X : Ctx} (a : Γ ⟶ M.Tm)
    (x : (ii.motiveCtx a) ⟶ X) :
    ie.equivMk a x ≫ (ie.verticalNatTrans).app X =
    UvPoly.Equiv.mk' (UvPoly.id M.Tm) X a (R := Γ) (f := 𝟙 _) (g := a)
    (reflCase_aux a) ((ii.reflSubst a) ≫ x) := by
  dsimp only [equivMk, verticalNatTrans]
  rw [UvPoly.mk'_comp_verticalNatTrans_app (R' := Γ) (f' := 𝟙 _) (g' := a)
    (H' := reflCase_aux a)]
  congr 2
  apply (M.disp_pullback _).hom_ext
  · conv => lhs; rw [← toI_comp_i1 ie]
    simp [reflSubst, comparison, mkRefl]
  · apply (M.disp_pullback _).hom_ext
    · slice_lhs 3 4 => rw [← ii.toK_comp_k1]
      slice_lhs 2 3 => rw [← ie.toI_comp_i2]
      simp [reflSubst]
    · simp [reflSubst]

end

-/
end Equiv

end IdElimBase

/-- In the high-tech formulation by Richard Garner and Steve Awodey:
The full structure interpreting the natural model semantics for identity types
requires an `IdIntro`,
(and `IdElimBase` which can be generated by pullback in the presheaf category,)
and that the following commutative square generated by
`IdBaseComparison.verticalNatTrans` is a weak pullback.

```
  verticalNatTrans.app Tm
iFunctor Tm --------> P_𝟙Tm Tm
  |                    |
  |                    |
iFunctor tp           P_𝟙Tm tp
  |                    |
  |                    |
  V                    V
iFunctor Ty --------> P_𝟙Tm Ty
  verticalNatTrans.app Ty
```

This can be thought of as saying the following.
Fix `A : Ty` and `a : A` - we are working in the slice over `M.Tm`.
For any context `Γ`, any map `(a, r) : Γ → P_𝟙Tm Tm`
and `(a, C) : Γ ⟶ iFunctor Ty` such that `r ≫ M.tp = C[x/y, refl_x/p]`,
there is a map `(a,c) : Γ ⟶ iFunctor Tm` such that `c ≫ M.tp = C` and `c[a/y, refl_a/p] = r`.
Here we are thinking
  `Γ (y : A) (p : A) ⊢ C : Ty`
  `Γ ⊢ r : C[a/y, refl_a/p]`
  `Γ (y : A) (p : A) ⊢ c : Ty`
This witnesses the elimination principle for identity types since
we can take `J (y.p.C;x.r) := c`.
-/
structure Id {ii : IdIntro M} (ie : IdElimBase ii) (N : Universe R) where
  weakPullback : WeakPullback
    (ie.verticalNatTrans.app N.Tm)
    (ie.iFunctor.map N.tp)
    ((UvPoly.id R M.Tm).functor.map N.tp)
    (ie.verticalNatTrans.app N.Ty)

namespace Id

variable {N : Universe R} {ii : IdIntro M} {ie : IdElimBase ii} (i : Id ie N)

variable {Γ Δ : Ctx} (σ : Δ ⟶ Γ) (a : Γ ⟶ M.Tm)
  (C : (ii.motiveCtx a) ⟶ N.Ty) (r : Γ ⟶ N.Tm)
  (r_tp : r ≫ N.tp = (ii.reflSubst a) ≫ C)

open IdElimBase IdIntro

#exit
lemma reflCase_aux : IsPullback (𝟙 Γ) a a (UvPoly.id M.Tm).p :=
  have : IsIso (UvPoly.id M.Tm).p := by simp; infer_instance
  IsPullback.of_horiz_isIso (by simp)

/-- The variable `r` witnesses the motive for the case `refl`,
This gives a map `(a,r) : Γ ⟶ P_𝟙Tm Tm ≅ Tm × Tm` where
```
    fst ≫ r
Tm <--   Γ  --------> Tm
  <      ‖            ‖
   \     ‖   (pb)     ‖ 𝟙_Tm
  r \    ‖            ‖
     \   ‖            ‖
      \  Γ  --------> Tm
              a
```
-/
def reflCase : Γ ⟶ (UvPoly.id M.Tm).functor.obj N.Tm :=
  UvPoly.Equiv.mk' (UvPoly.id M.Tm) N.Tm a (R := Γ) (f := 𝟙 _) (g := a)
  (reflCase_aux a) r
-- TODO: consider generalizing
-- TODO: consider showing UvPoly on identity `(P_𝟙_Y X)` is isomorphic to product `Y × X`

variable (ie) in
/-- The variable `C` is the motive for elimination,
This gives a map `(a, C) : Γ ⟶ iFunctor Ty`
```
    C
Ty <-- y(motiveCtx) ----> i
             |            |
             |            | i2 ≫ k2
             |            |
             V            V
             Γ  --------> Tm
                  a
```
-/
abbrev motive : Γ ⟶ ie.iFunctor.obj N.Ty :=
  ie.equivMk a C

lemma motive_comp_left : σ ≫ motive ie a C =
    motive ie (σ ≫ a) ((ii.motiveSubst σ a) ≫ C) := by
  dsimp [motive, equivMk]
  rw [UvPoly.Equiv.mk'_comp_left (iUvPoly ie) _ a
    (ie.motiveCtx_isPullback' a).flip C σ _ rfl (ie.motiveCtx_isPullback' _).flip]
  congr 2
  simp only [Functor.map_comp, iUvPoly_p, Category.assoc, motiveSubst, substWk, substCons,
    Functor.FullyFaithful.map_preimage]
  apply (M.disp_pullback _).hom_ext <;> simp only [IsPullback.lift_fst, IsPullback.lift_snd]
  · simp [← toI_comp_i1 ie]
  · apply (M.disp_pullback _).hom_ext <;> simp
    · slice_lhs 3 4 => rw [← ii.toK_comp_k1]
      slice_rhs 2 3 => rw [← ii.toK_comp_k1]
      slice_lhs 2 3 => rw [← ie.toI_comp_i2]
      slice_rhs 1 2 => rw [← ie.toI_comp_i2]
      simp

def lift : Γ ⟶ ie.iFunctor.obj N.Tm :=
  i.weakPullback.coherentLift (reflCase a r) (motive ie a C) (by
    dsimp only [motive, equivMk, verticalNatTrans, reflCase]
    rw [UvPoly.mk'_comp_verticalNatTrans_app (UvPoly.id M.Tm) ie.iUvPoly ie.comparison
      _ N.Ty a (ie.motiveCtx_isPullback' a).flip C (reflCase_aux a),
      UvPoly.Equiv.mk'_comp_right, r_tp, reflSubst]
    congr
    apply (M.disp_pullback _).hom_ext
    · conv => right; rw [← toI_comp_i1 ie]
      simp [mkRefl, comparison]
    · apply (M.disp_pullback _).hom_ext
      · slice_rhs 3 4 => rw [← ii.toK_comp_k1]
        slice_rhs 2 3 => rw [← ie.toI_comp_i2]
        simp
      · simp)

lemma lift_comp_left {Δ} (σ : Δ ⟶ Γ) : i.lift (σ ≫ a) ((ii.motiveSubst σ a) ≫ C)
    (σ ≫ r) (by simp [r_tp, comp_reflSubst'_assoc]) =
    σ ≫ i.lift a C r r_tp := by
  dsimp [lift]
  rw [WeakPullback.coherentLift_comp_left]
  congr 1
  · dsimp [reflCase]
    rw [UvPoly.Equiv.mk'_comp_left (UvPoly.id M.Tm) N.Tm a (reflCase_aux a) r σ _ rfl
      (reflCase_aux (σ ≫ a))]
    congr 2
    apply (reflCase_aux a).hom_ext
    · simp only [IsPullback.lift_fst]
      simp
    · simp
  · rw [motive_comp_left]

lemma equivFst_lift_eq : ie.equivFst (i.lift a C r r_tp) = a :=
  calc ie.equivFst (i.lift a C r r_tp)
  _ = ie.equivFst (i.lift a C r r_tp ≫ ie.iFunctor.map N.tp) := by
    dsimp [IdElimBase.equivFst]
    rw [UvPoly.Equiv.fst_comp_right]
  _ = _ := by
    dsimp [lift, motive, IdElimBase.equivFst, IdElimBase.equivMk]
    rw [WeakPullback.coherentLift_snd, UvPoly.Equiv.fst_mk']

/-- The elimination rule for identity types.
  `Γ ⊢ A` is the type with a term `Γ ⊢ a : A`.
  `Γ (y : A) (h : Id(A,a,y)) ⊢ C` is the motive for the elimination.
  Then we obtain a section of the motive
  `Γ (y : A) (h : Id(A,a,y)) ⊢ mkJ : A`
-/
def j : y(ii.motiveCtx a) ⟶ N.Tm :=
  eqToHom (by rw [equivFst_lift_eq]) ≫ ie.equivSnd (i.lift a C r r_tp)

/-- Typing for elimination rule `J` -/
lemma j_tp : j i a C r r_tp ≫ N.tp = C := by
  simp only [j, Category.assoc, IdElimBase.equivSnd, ← UvPoly.Equiv.snd'_comp_right]
  -- FIXME: `transparency := .default` is like `erw` and should be avoided
  rw! (transparency := .default) [WeakPullback.coherentLift_snd]
  simp only [IdElimBase.equivMk]
  rw! [equivFst_lift_eq]
  simp

lemma comp_j : ym(ii.motiveSubst σ _) ≫ j i a C r r_tp =
    j i (ym(σ) ≫ a) (ym(ii.motiveSubst σ _) ≫ C) (ym(σ) ≫ r) (by
      simp [r_tp, IdIntro.comp_reflSubst'_assoc]) := by
  simp only [j]
  conv => rhs; rw! [i.lift_comp_left a C r r_tp]
  rw [ie.equivSnd_comp_left]
  simp only [← Category.assoc]
  congr 1
  simp [← heq_eq_eq]
  rw [equivFst_lift_eq]

/-- β rule for identity types. Substituting `J` with `refl` gives the user-supplied value `r` -/
lemma reflSubst_j : ym(ii.reflSubst a) ≫ j i a C r r_tp = r := by
  have h := ie.equivSnd_verticalNatTrans_app (i.lift a C r r_tp)
  -- FIXME: `transparency := .default` is like `erw` and should be avoided
  rw! (transparency := .default) [i.weakPullback.coherentLift_fst] at h
  unfold reflCase at h
  rw [UvPoly.Equiv.snd'_eq_snd', UvPoly.Equiv.snd'_mk', ← Iso.eq_inv_comp] at h
  conv => right; rw [h]
  simp only [j, ← Category.assoc, UvPoly.Equiv.fst_mk', UvPoly.id_p]
  congr 1
  have pb : IsPullback (𝟙 _) a a (𝟙 _) := IsPullback.of_id_fst
  have : (IsPullback.isoIsPullback y(Γ) M.Tm pb pb).inv = 𝟙 _ := by
    apply pb.hom_ext
    · simp only [IsPullback.isoIsPullback_inv_fst]
      simp
    · simp
  simp only [← heq_eq_eq, comp_eqToHom_heq_iff]
  rw! [equivFst_lift_eq]
  simp [this]

variable (b : y(Γ) ⟶ M.Tm) (b_tp : b ≫ M.tp = a ≫ M.tp)
  (h : y(Γ) ⟶ M.Tm) (h_tp : h ≫ M.tp = ii.isKernelPair.lift b a (by aesop) ≫ ii.Id)

def endPtSubst : Γ ⟶ ii.motiveCtx a :=
  M.substCons (M.substCons (𝟙 _) _ b (by aesop)) _ h (by
    simp only [h_tp, IdIntro.mkId, ← Category.assoc]
    congr 1
    apply ii.isKernelPair.hom_ext
    · simp
    · simp)

/-- `Id` is equivalent to `Id` (one half). -/
def toId' : M.Id' ii N where
  j := i.j
  j_tp := i.j_tp
  comp_j := i.comp_j
  reflSubst_j := i.reflSubst_j

end Id

namespace Id'

variable {ii : IdIntro M} {ie : IdElimBase ii} {N : Universe Ctx} (i : M.Id' ii N)

open IdIntro IdElimBase

variable {Γ} (ar : y(Γ) ⟶ (UvPoly.id M.Tm).functor.obj N.Tm)
  (aC : y(Γ) ⟶ ie.iFunctor.obj N.Ty)
  (hrC : ar ≫ (UvPoly.id M.Tm).functor.map N.tp =
    aC ≫ (verticalNatTrans ie).app N.Ty)

include hrC in
lemma fst_eq_fst : UvPoly.Equiv.fst _ _ ar = ie.equivFst aC :=
  calc _
  _ = UvPoly.Equiv.fst _ _ (ar ≫ (UvPoly.id M.Tm).functor.map N.tp) := by
    rw [UvPoly.Equiv.fst_comp_right]
  _ = UvPoly.Equiv.fst _ _  (aC ≫ (IdElimBase.verticalNatTrans ie).app N.Ty) := by
    rw [hrC]
  _ = _ := by
    rw [ie.equivFst_verticalNatTrans_app]

abbrev motive : y(ii.motiveCtx (ie.equivFst aC)) ⟶ N.Ty :=
  ie.equivSnd aC

lemma comp_motive {Δ} (σ : Δ ⟶ Γ) : motive (ym(σ) ≫ aC) =
    ym(ii.motiveSubst σ (ie.equivFst aC)) ≫ motive aC := by
  simp only [motive, equivSnd_comp_left ie aC σ]

abbrev reflCase : y(Γ) ⟶ N.Tm := UvPoly.Equiv.snd' _ _ ar (Id.reflCase_aux _)

lemma comp_reflCase {Δ} (σ : Δ ⟶ Γ) : reflCase (ym(σ) ≫ ar) = ym(σ) ≫ reflCase ar := by
  simp only [reflCase]
  rw [UvPoly.Equiv.snd'_comp_left (UvPoly.id M.Tm) N.Tm ar
    (Id.reflCase_aux (UvPoly.Equiv.fst (UvPoly.id M.Tm) N.Tm ar)) ym(σ)
    (Id.reflCase_aux _)]
  congr 1
  apply (Id.reflCase_aux (UvPoly.Equiv.fst (UvPoly.id M.Tm) N.Tm ar)).hom_ext
  · simp only [IsPullback.lift_fst]
    simp
  · simp

include hrC in
lemma reflCase_comp_tp : reflCase ar ≫ N.tp =
    ym(ii.reflSubst (ie.equivFst aC)) ≫ motive aC := by
  dsimp [reflCase, motive]
  rw! [← UvPoly.Equiv.snd'_comp_right, hrC]
  have H : IsPullback ym(M.disp (ii.mkId
      (ym(M.disp (ie.equivFst aC ≫ M.tp)) ≫ ie.equivFst aC)
      (M.var (ie.equivFst aC ≫ M.tp)) (by simp)) ≫
      M.disp (ie.equivFst aC ≫ M.tp))
    (ie.toI (ie.equivFst aC)) (UvPoly.Equiv.fst ie.iUvPoly N.Ty aC) ie.iUvPoly.p := by
    convert (ie.motiveCtx_isPullback' (ie.equivFst aC)).flip
    simp
  -- FIXME: `transparency := .default` is like `erw` and should be avoided
  rw! (transparency := .default) [UvPoly.snd'_verticalNatTrans_app
    (R := y(ii.motiveCtx (ie.equivFst aC)))
    (H := H)
    (R' := y(Γ)) (f' := 𝟙 _) (g' := UvPoly.Equiv.fst (UvPoly.id M.Tm) N.Tm ar)
    (H' := by
    rw [fst_eq_fst ar aC hrC]
    exact Id.reflCase_aux _)]
  simp only [Functor.map_comp, iUvPoly_p, equivSnd]
  congr 1
  apply (M.disp_pullback _).hom_ext <;>
    simp only [reflSubst, substCons_var, substCons_disp_functor_map, substCons_var]
  · simp [← ie.toI_comp_i1 (ie.equivFst aC), fst_eq_fst ar aC hrC, mkRefl]
  · apply (M.disp_pullback _).hom_ext
    · rw! [fst_eq_fst ar aC hrC]
      slice_lhs 3 4 => rw [← ii.toK_comp_k1]
      slice_lhs 2 3 => rw [← ie.toI_comp_i2]
      simp
    · simp

def lift : y(Γ) ⟶ (IdElimBase.iFunctor ie).obj N.Tm :=
  ie.equivMk (ie.equivFst aC) (i.j (ie.equivFst aC) (motive aC)
   (reflCase ar) (reflCase_comp_tp ar aC hrC))

lemma lift_fst : lift i ar aC hrC ≫ ie.verticalNatTrans.app N.Tm = ar := by
  dsimp only [lift]
  rw [equivMk_comp_verticalNatTrans_app]
  apply UvPoly.Equiv.ext' (UvPoly.id M.Tm) N.Tm (by convert reflCase_aux (ie.equivFst aC); simp)
  · rw! [i.reflSubst_j]
    simp [reflCase, fst_eq_fst ar aC hrC]
  · simp [fst_eq_fst ar aC hrC]

lemma lift_snd : lift i ar aC hrC ≫ ie.iFunctor.map N.tp = aC := by
  dsimp only [lift, equivMk]
  rw [UvPoly.Equiv.mk'_comp_right]
  apply UvPoly.Equiv.ext' ie.iUvPoly N.Ty
  · rw! [i.j_tp]
    rw [UvPoly.Equiv.snd'_mk']
    simp [motive, equivSnd]
  · simp only [UvPoly.Equiv.fst_mk', iUvPoly_p]
    exact (ie.motiveCtx_isPullback' _).flip
  · simp [equivFst]

lemma comp_lift {Δ} (σ : Δ ⟶ Γ) : ym(σ) ≫ lift i ar aC hrC =
    lift i (ym(σ) ≫ ar) (ym(σ) ≫ aC) (by simp [hrC]) := by
  dsimp [lift, equivMk]
  rw [UvPoly.Equiv.mk'_comp_left ie.iUvPoly N.Tm (ie.equivFst aC) _
    (i.j (ie.equivFst aC) (motive aC) (reflCase ar) _) ym(σ) _ rfl
    (by simp only [iUvPoly_p]; exact (ie.motiveCtx_isPullback' _).flip)]
  congr 1
  have h := i.comp_j σ (ie.equivFst aC) _ _ (reflCase_comp_tp ar aC hrC)
  rw! (castMode := .all) [← comp_motive, ← comp_reflCase, ← equivFst_comp_left] at h
  rw [← h]
  congr 1
  simp only [iUvPoly_p, Category.assoc]
  apply (M.disp_pullback _).hom_ext
  · simp [toI_comp_left, ← toI_comp_i1 ie]
  · apply (M.disp_pullback _).hom_ext
    · slice_rhs 3 4 => rw [← toK_comp_k1 ii]
      slice_rhs 2 3 => rw [← toI_comp_i2 ie]
      slice_lhs 3 4 => rw [← toK_comp_k1 ii]
      slice_lhs 2 3 => rw [← toI_comp_i2 ie]
      simp [toI_comp_left]
    · simp [motiveSubst, substWk]

def toId : M.Id ie N where
  __ := ie
  weakPullback := RepPullbackCone.WeakPullback.mk
    ((IdElimBase.verticalNatTrans ie).naturality _).symm
    (fun s => lift i s.fst s.snd s.condition)
    (fun s => lift_fst i s.fst s.snd s.condition)
    (fun s => lift_snd i s.fst s.snd s.condition)
    (fun s _ σ => comp_lift i s.fst s.snd s.condition σ)

end Id'

end Universe

end NaturalModel
