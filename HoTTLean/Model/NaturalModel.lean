import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
-- import Poly.ForMathlib.CategoryTheory.LocallyCartesianClosed.Presheaf
-- import Poly.UvPoly.UPFan

import HoTTLean.ForPoly
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

variable [HasTerminal Ctx] [R.HasObjects] [R.IsMultiplicative]
  [R.HasPushforwards R] [R.IsStableUnderPushforward R]

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

/-
namespace compDomEquiv
open UvPoly

variable {M N : Universe R} {Γ Δ : Ctx} (σ : Δ ⟶ Γ)
/-- Universal property of `compDom`, decomposition (part 1).

A map `ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`. The map `fst : Γ ⟶ M.Tm`
is the `(a : A)` in `(a : A) × (b : B a)`.
-/
def fst (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp) : Γ ⟶ M.Tm :=
  ab ≫ pullback.snd N.tp (UvPoly.PartialProduct.fan M.uvPolyTp N.Ty).snd ≫
    pullback.snd (M.uvPolyTp.fstProj N.Ty) M.uvPolyTp.p

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
    fst ab ≫ M.tp = PtpEquiv.fst M (ab ≫ (M.uvPolyTp.compP _)) := by
  have : pullback.snd (M.uvPolyTp.fstProj N.Ty) M.tp ≫ M.tp =
    pullback.fst (M.uvPolyTp.fstProj N.Ty) M.tp ≫ M.uvPolyTp.fstProj N.Ty :=
      Eq.symm pullback.condition
  simp [PtpEquiv.fst, fst, this]
  rfl

theorem comp_fst (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp) (σ : Δ ⟶ Γ) :
    σ ≫ fst ab = fst (σ ≫ ab) := by simp [fst]

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
  PtpEquiv.snd M (ab ≫ (M.uvPolyTp.compP _)) _ (by rw [← eq, fst_tp])

theorem comp_dependent (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq1 : fst ab ≫ M.tp = A)
    {σA} (eq2 : σ ≫ A = σA) :
    (substWk M σ _ _ eq2) ≫ dependent ab A eq1 =
    dependent (σ ≫ ab) σA (by simp [← comp_fst, eq1, eq2]) := by
  rw [dependent, ← PtpEquiv.snd_comp_left]; rfl

/-- Universal property of `compDom`, decomposition (part 3).

A map `ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The map `snd : Γ ⟶ M.Tm`
is the `(b : B a)` in `(a : A) × (b : B a)`.
-/
def snd (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp) : Γ ⟶ N.Tm :=
  ab ≫ pullback.fst N.tp (PartialProduct.fan M.uvPolyTp N.Ty).snd

theorem comp_snd (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp) (σ : Δ ⟶ Γ) :
    σ ≫ snd ab = snd (σ ≫ ab) := by simp [snd]

/-- Universal property of `compDom`, decomposition (part 4).

A map `ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp` is equivalently three maps
`fst, dependent, snd` such that `fst_tp` and `snd_tp`.
The equation `snd_tp` says that the type of `b : B a` agrees with
the expression for `B a` obtained solely from `dependent`, or `B : A ⟶ Type`.
-/
theorem snd_tp (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq : fst ab ≫ M.tp = A) :
    snd ab ≫ N.tp = (M.sec _ (fst ab) eq) ≫ dependent ab A eq := by
  simp [snd, pullback.condition, dependent, PtpEquiv.snd, Equiv.snd'_eq]
  simp only [← Category.assoc]; congr! 1
  apply pullback.hom_ext <;> simp [fst, UvPoly.compP]

/-- Universal property of `compDom`, constructing a map into `compDom`. -/
def mk (α : Γ ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) (B : (M.ext A) ⟶ N.Ty) (β : Γ ⟶ N.Tm)
    (h : β ≫ N.tp = (M.sec _ α eq) ≫ B) : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp := by
  refine pullback.lift β (pullback.lift (PtpEquiv.mk _ A B) α ?_) ?_
  · simp [← Equiv.fst_eq, ← PtpEquiv.fst.eq_def, eq]
  · simp [h]
    conv_lhs => arg 2; exact
      Equiv.snd'_mk' M.uvPolyTp N.Ty A _ B
        |>.symm.trans <| Equiv.snd'_eq M.uvPolyTp N.Ty (PtpEquiv.mk M A B) _
    simp only [← Category.assoc]; congr! 1
    apply pullback.hom_ext <;> simp

@[simp]
theorem fst_mk (α : Γ ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) (B : (M.ext A) ⟶ N.Ty) (β : Γ ⟶ N.Tm)
    (h : β ≫ N.tp = (M.sec _ α eq) ≫ B) : fst (mk α eq B β h) = α := by
  simp [mk, fst]

@[simp]
theorem dependent_mk (α : Γ ⟶ M.Tm) {A} (eq : α ≫ M.tp = A)
    (B : (M.ext A) ⟶ N.Ty) (β : Γ ⟶ N.Tm)
    (h : β ≫ N.tp = (M.sec _ α eq) ≫ B) :
    dependent (mk α eq B β h) A (by simp [fst_mk, eq]) = B := by
  simp [mk, dependent, UvPoly.compP]
  convert PtpEquiv.snd_mk M A B using 2
  slice_lhs 1 2 => apply pullback.lift_snd
  simp

@[simp]
theorem snd_mk (α : Γ ⟶ M.Tm) {A} (eq : α ≫ M.tp = A) (B : (M.ext A) ⟶ N.Ty) (β : Γ ⟶ N.Tm)
    (h : β ≫ N.tp = (M.sec _ α eq) ≫ B) : snd (mk α eq B β h) = β := by
  simp [mk, snd]

theorem ext {ab₁ ab₂ : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp}
    {A} (eq : fst ab₁ ≫ M.tp = A)
    (h1 : fst ab₁ = fst ab₂)
    (h2 : dependent ab₁ A eq = dependent ab₂ A (h1 ▸ eq))
    (h3 : snd ab₁ = snd ab₂) : ab₁ = ab₂ := by
  refine pullback.hom_ext h3 (pullback.hom_ext ?_ h1)
  simp only [dependent, PtpEquiv.snd] at h2
  generalize_proofs _ _ H at h2
  refine Equiv.ext' M.uvPolyTp N.Ty H ?_ h2
  simp [Equiv.fst, pullback.condition]
  simp only [← Category.assoc]; congr 1

theorem comp_mk
    (α : Γ ⟶ M.Tm) {A} (e1 : α ≫ M.tp = A)
    (B : (M.ext A) ⟶ N.Ty)
    (β : Γ ⟶ N.Tm)
    (e2 : β ≫ N.tp = (M.sec A α e1) ≫ B)
    (σ : Δ ⟶ Γ) {σA} (e3 : σ ≫ A = σA) :
    σ ≫ mk α e1 B β e2 =
    mk (σ ≫ α) (by simp [e1, e3])
      ((M.substWk σ A _ e3) ≫ B) (σ ≫ β)
      (by simp [e2]; rw [← Functor.map_comp_assoc, comp_sec]; simp; congr!) := by
  apply ext (A := σA) (by simp [← comp_fst, e1, e3]) <;> simp [← comp_fst, ← comp_snd]
  rw [← comp_dependent, dependent_mk]

theorem eta (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq : fst ab ≫ M.tp = A) :
    mk (fst ab) eq (dependent ab A eq) (snd ab) (snd_tp ab eq) = ab := by
  symm; apply ext (eq := eq) <;> simp

end compDomEquiv
-/
/-! ## Pi and Sigma types -/

set_option linter.dupNamespace false in
protected structure Pi where
  Pi : M.Ptp.obj M.Ty ⟶ M.Ty
  lam : M.Ptp.obj M.Tm ⟶ M.Tm
  Pi_pullback : IsPullback lam (M.Ptp.map M.tp) M.tp Pi

protected structure Sigma where
  Sig : M.Ptp.obj M.Ty ⟶ M.Ty
  pair : UvPoly.compDom (uvPolyTp M) (uvPolyTp M) ⟶ M.Tm
  -- Sig_pullback : IsPullback pair ((uvPolyTp M).compP (uvPolyTp M)) M.tp Sig

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
    UvPoly.verticalNatTrans (UvPoly.id M.Tm) ie.iUvPoly
  ie.comparison (by simp [iUvPoly])

section reflCase

variable (i : IdIntro M) {N : Universe R}

variable {Γ : Ctx} (a : Γ ⟶ M.Tm) (r : Γ ⟶ N.Tm)

lemma reflCase_aux : IsPullback (𝟙 Γ) a a (UvPoly.id R M.Tm).p :=
  have : IsIso (UvPoly.id M.Tm).p := by simp; infer_instance
  IsPullback.of_horiz_isIso (by simp)

end Id'

end Universe

end NaturalModel
