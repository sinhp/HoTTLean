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

open CategoryTheory Limits Opposite

namespace Model

/-- A natural model with support for dependent types (and nothing more).
The data is a natural transformation with representable fibers,
stored as a choice of representative for each fiber. -/
structure StructuredUniverse {Ctx : Type u} [Category Ctx] (R : MorphismProperty Ctx)
    extends UnstructuredUniverse Ctx where
  morphismProperty : R tp

namespace StructuredUniverse

open Model.UnstructuredUniverse

section

variable {Ctx : Type u} [Category Ctx] {R : MorphismProperty Ctx} (M : StructuredUniverse R)
  [R.HasPullbacks] [R.IsStableUnderBaseChange]

instance {Γ : Ctx} (A : Γ ⟶ M.Ty) : HasPullback A M.tp :=
  have := MorphismProperty.HasPullbacks.hasPullback A M.morphismProperty
  hasPullback_symmetry _ _

lemma disp_mem {Γ : Ctx} (A : Γ ⟶ M.Ty) : R (M.disp A) :=
  R.of_isPullback (M.disp_pullback A) M.morphismProperty

@[simps! hom inv]
def pullbackIsoExt {Γ : Ctx} (A : Γ ⟶ M.Ty) :
    pullback A M.tp ≅ (M.ext A) :=
  IsPullback.isoPullback (M.disp_pullback A).flip |>.symm

/-! ## Pullback of representable natural transformation -/

/-- Pull a natural model back along a type. -/
protected def pullback {Γ : Ctx} (A : Γ ⟶ M.Ty) : StructuredUniverse R where
  __ := UnstructuredUniverse.pullback M.toUnstructuredUniverse A
  morphismProperty := M.disp_mem A

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
    StructuredUniverse R where
  __ := UnstructuredUniverse.ofIsPullback M.toUnstructuredUniverse pb
  morphismProperty := R.of_isPullback pb M.morphismProperty

/-! ## Polynomial functor on `tp`

Specializations of results from the `Poly` package to natural models. -/

abbrev uvPolyTp : UvPoly R M.Tm M.Ty := ⟨M.tp, M.morphismProperty⟩

variable [ChosenTerminal Ctx] [R.HasObjects] [R.IsMultiplicative]
  [R.HasPushforwards R] [R.IsStableUnderPushforwards R]

instance : R.HasPushforwardsAlong M.uvPolyTp.p :=
  MorphismProperty.HasPushforwards.hasPushforwardsAlong M.tp M.morphismProperty

instance : R.IsStableUnderPushforwardsAlong M.uvPolyTp.p :=
  MorphismProperty.IsStableUnderPushforwards.of_isPushforward M.tp M.morphismProperty

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
  rw! [UvPoly.Equiv.snd'_mk' (P := M.uvPolyTp)]

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
  rw [UvPoly.Equiv.snd'_comp_right (P := M.uvPolyTp)]

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

theorem mk_comp_left {Δ Γ : Ctx} (M : StructuredUniverse R) (σ : Δ ⟶ Γ)
    {X : Ctx} (A : Γ ⟶ M.Ty) (σA) (eq : σ ≫ A = σA) (B : (M.ext A) ⟶ X) :
    σ ≫ PtpEquiv.mk M A B = PtpEquiv.mk M σA ((M.substWk σ A _ eq) ≫ B) := by
  dsimp [PtpEquiv.mk]
  have h := UvPoly.Equiv.mk'_comp_left (P := M.uvPolyTp) A (f := M.disp A) (g := M.var A)
    (by convert (M.disp_pullback A).flip) B σ σA eq (M.disp_pullback σA).flip
  convert h
  apply (M.disp_pullback _).hom_ext
  · simp
  · simp [substWk_disp]

theorem mk_comp_right {Γ : Ctx} (M : StructuredUniverse R)
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

abbrev compDom (M N : StructuredUniverse R) : Ctx := M.uvPolyTp.compDom N.uvPolyTp

abbrev compP (M N : StructuredUniverse R) : M.compDom N ⟶ M.uvPolyTp @ N.Ty :=
  (M.uvPolyTp.comp N.uvPolyTp).p

namespace compDomEquiv
open UvPoly

variable {M N : StructuredUniverse R} {Γ Δ : Ctx} (σ : Δ ⟶ Γ)

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
    dependent ab A eq = PtpEquiv.snd M (ab ≫ M.compP N) A (by simp [← eq, fst_tp]) := by
  simp [dependent, UvPoly.compDomEquiv.dependent, PtpEquiv.snd]

theorem comp_dependent (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq1 : fst ab ≫ M.tp = A)
    {σA} (eq2 : σ ≫ A = σA) :
    (M.substWk σ _ _ eq2) ≫ dependent ab A eq1 =
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
theorem fst_mk (α : Γ ⟶ M.Tm) {A} (eq : α ≫ M.tp = A := by rfl) (B : (M.ext A) ⟶ N.Ty)
    (β : Γ ⟶ N.Tm) (h : β ≫ N.tp = (M.sec _ α eq) ≫ B) : fst (mk α eq B β h) = α := by
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
  rw [UvPoly.compDomEquiv.comp_mk (P := M.uvPolyTp) (P' := N.uvPolyTp) σ _ α e1 (M.disp _)
    (M.var _) (M.disp_pullback _).flip (M.disp _) (M.var _) (M.disp_pullback _).flip]
  subst e1 e3
  congr 2
  apply (disp_pullback ..).hom_ext <;> simp [substWk_disp]

@[reassoc]
lemma mk_comp (α : Γ ⟶ M.Tm) {A} (e1 : α ≫ M.tp = A) (B : (M.ext A) ⟶ N.Ty)
    (β : Γ ⟶ N.Tm) (e2 : β ≫ N.tp = (M.sec A α e1) ≫ B) :
    mk α e1 B β e2 ≫ M.compP N = PtpEquiv.mk M A B := by
  erw [PtpEquiv.mk, UvPoly.compDomEquiv.mk_comp (P := M.uvPolyTp) (P' := N.uvPolyTp)]

theorem eta (ab : Γ ⟶ M.uvPolyTp.compDom N.uvPolyTp)
    {A} (eq : fst ab ≫ M.tp = A) :
    mk (fst ab) eq (dependent ab A eq) (snd ab) (snd_tp ab eq) = ab := by
  symm; apply ext (eq := eq) <;> simp

end compDomEquiv

end

variable {Ctx : Type u} [Category Ctx] {R : MorphismProperty Ctx}
  [R.HasPullbacks] [R.IsStableUnderBaseChange]
  [ChosenTerminal Ctx] [R.HasObjects] [R.IsMultiplicative]
  [R.HasPushforwards R] [R.IsStableUnderPushforwards R]

/-! ## Pi types -/

/-- The structure on three universes that for
`A : Γ ⟶ U0.Ty` and `B : Γ.A ⟶ U1.Ty` constructs a Π-type `Π_A B : Γ ⟶ U2.Ty`.
-/
structure PolymorphicPi (U0 U1 U2 : StructuredUniverse R) where
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
protected abbrev Pi (U : StructuredUniverse R) := PolymorphicPi U U U

namespace PolymorphicPi

variable {U0 U1 U2 : StructuredUniverse R} {Γ : Ctx}

section
variable (P : PolymorphicPi U0 U1 U2)

/--
```
Γ ⊢₀ A  Γ.A ⊢₁ B
-----------------
Γ ⊢₂ ΠA. B
``` -/
def mkPi {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty) : Γ ⟶ U2.Ty :=
  PtpEquiv.mk U0 A B ≫ P.Pi

theorem comp_mkPi {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : (Γ) ⟶ U0.Ty) (σA) (eq : (σ) ≫ A = σA)
    (B : (U0.ext A) ⟶ U1.Ty) :
    (σ) ≫ P.mkPi A B = P.mkPi σA ((U0.substWk σ A _ eq) ≫ B) := by
  simp [mkPi, ← Category.assoc, PtpEquiv.mk_comp_left (eq := eq)]

/--
```
Γ ⊢₀ A  Γ.A ⊢₁ t : B
-------------------------
Γ ⊢₂ λA. t : ΠA. B
``` -/
def mkLam {Γ : Ctx} (A : (Γ) ⟶ U0.Ty) (t : (U0.ext A) ⟶ U1.Tm) : (Γ) ⟶ U2.Tm :=
  PtpEquiv.mk U0 A t ≫ P.lam

@[simp]
theorem mkLam_tp {Γ : Ctx} (A : (Γ) ⟶ U0.Ty) (B : (U0.ext A) ⟶ U1.Ty)
    (t : (U0.ext A) ⟶ U1.Tm) (t_tp : t ≫ U1.tp = B) :
    P.mkLam A t ≫ U2.tp = P.mkPi A B := by
  simp [mkLam, mkPi, P.Pi_pullback.w, PtpEquiv.mk_map_assoc, t_tp]

theorem comp_mkLam {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : (Γ) ⟶ U0.Ty) (σA) (eq : (σ) ≫ A = σA) (t : (U0.ext A) ⟶ U1.Tm) :
    (σ) ≫ P.mkLam A t = P.mkLam σA ((U0.substWk σ A _ eq) ≫ t) := by
  simp [mkLam, ← Category.assoc, PtpEquiv.mk_comp_left (eq := eq)]


/--
```
Γ ⊢₀ A  Γ ⊢₂ f : ΠA. B
-----------------------------
Γ.A ⊢₁ unlam f : B
``` -/
def unLam {Γ : Ctx} (A : (Γ) ⟶ U0.Ty) (B : (U0.ext A) ⟶ U1.Ty)
    (f : (Γ) ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.mkPi A B) :
    (U0.ext A) ⟶ U1.Tm := by
  let total : (Γ) ⟶ U0.Ptp.obj U1.Tm :=
    P.Pi_pullback.lift f (PtpEquiv.mk U0 A B) f_tp
  refine PtpEquiv.snd U0 total _ ?_
  have eq : total ≫ U0.Ptp.map U1.tp = PtpEquiv.mk U0 A B :=
    (P.Pi_pullback).lift_snd ..
  apply_fun PtpEquiv.fst U0 at eq
  rw [PtpEquiv.fst_comp_right] at eq
  simpa using eq

@[simp]
theorem unLam_tp {Γ : Ctx} (A : (Γ) ⟶ U0.Ty) (B : (U0.ext A) ⟶ U1.Ty)
    (f : (Γ) ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.mkPi A B) :
    P.unLam A B f f_tp ≫ U1.tp = B := by
  rw [unLam, ← PtpEquiv.snd_comp_right]
  convert PtpEquiv.snd_mk U0 A B using 2; simp

theorem comp_unLam {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : (Γ) ⟶ U0.Ty) (σA) (eq : (σ) ≫ A = σA) (B : (U0.ext A) ⟶ U1.Ty)
    (f : (Γ) ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.mkPi A B) :
    (U0.substWk σ A _ eq) ≫ P.unLam A B f f_tp =
      P.unLam σA ((U0.substWk σ A _ eq) ≫ B)
        ((σ) ≫ f) (by simp [eq, f_tp, comp_mkPi]) := by
  simp [unLam]
  rw [← PtpEquiv.snd_comp_left]
  simp [PtpEquiv.snd, UvPoly.Equiv.snd'_eq]; congr 1
  apply pullback.hom_ext <;> simp; congr 1
  apply (P.Pi_pullback).hom_ext <;> simp
  rw [PtpEquiv.mk_comp_left]

/--
```
Γ ⊢₂ f : ΠA. B  Γ ⊢₀ a : A
---------------------------------
Γ ⊢₁ f a : B[id.a]
``` -/
def mkApp {Γ : Ctx} (A : (Γ) ⟶ U0.Ty) (B : (U0.ext A) ⟶ U1.Ty)
    (f : (Γ) ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.mkPi A B)
    (a : (Γ) ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) : (Γ) ⟶ U1.Tm :=
  (U0.sec A a a_tp) ≫ P.unLam A B f f_tp

@[simp]
theorem mkApp_tp {Γ : Ctx} (A : (Γ) ⟶ U0.Ty) (B : (U0.ext A) ⟶ U1.Ty)
    (f : (Γ) ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.mkPi A B)
    (a : (Γ) ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) :
    P.mkApp A B f f_tp a a_tp ≫ U1.tp = (U0.sec A a a_tp) ≫ B := by
  simp [mkApp]

theorem comp_mkApp {Δ Γ : Ctx} (σ : Δ ⟶ Γ)
    (A : Γ ⟶ U0.Ty) (σA) (eq : σ ≫ A = σA) (B : (U0.ext A) ⟶ U1.Ty)
    (f : Γ ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.mkPi A B)
    (a : Γ ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) :
    σ ≫ P.mkApp A B f f_tp a a_tp =
      P.mkApp σA (U0.substWk σ A _ eq ≫ B)
        (σ ≫ f) (by simp [f_tp, comp_mkPi (eq := eq)])
        (σ ≫ a) (by simp [a_tp, eq]) := by
  unfold mkApp; rw [← Category.assoc,
    comp_sec σ a_tp _ eq, Category.assoc, comp_unLam (eq := eq)]

@[simp]
theorem mkLam_unLam {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : (U0.ext A) ⟶ U1.Ty)
    (f : Γ ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.mkPi A B) :
    P.mkLam A (P.unLam A B f f_tp) = f := by
  let total : Γ ⟶ U0.Ptp.obj U1.Tm :=
    (P.Pi_pullback).lift f (PtpEquiv.mk U0 A B) f_tp
  simp only [mkLam, unLam]
  have : PtpEquiv.fst U0 total = A := by
    simp only [PtpEquiv.fst, UvPoly.Equiv.fst_eq, total]
    rw [← U0.uvPolyTp.map_fstProj U1.tp]
    slice_lhs 1 2 => apply (P.Pi_pullback).lift_snd
    apply PtpEquiv.fst_mk
  slice_lhs 1 1 => equals total =>
    apply PtpEquiv.ext _ (A := A) (by simp) (by simp [this]) (by simp [total])
  apply (P.Pi_pullback).lift_fst

@[simp]
theorem unLam_mkLam {Γ : Ctx} (A : Γ ⟶ U0.Ty) (B : U0.ext A ⟶ U1.Ty)
    (t : U0.ext A ⟶ U1.Tm) (t_tp : t ≫ U1.tp = B)
    (lam_tp : P.mkLam A t ≫ U2.tp = P.mkPi A B) :
    P.unLam A B (P.mkLam A t) lam_tp = t := by
  simp [mkLam, unLam]
  convert PtpEquiv.snd_mk U0 A t using 2
  apply (P.Pi_pullback).hom_ext <;> simp
  rw [PtpEquiv.mk_comp_right, t_tp]

/--
```
Γ ⊢₂ f : ΠA. B
--------------------------------------
Γ ⊢₂ λA. f[↑] v₀ : ΠA. B
```
-/
def etaExpand {Γ : Ctx} (A : (Γ) ⟶ U0.Ty) (B : (U0.ext A) ⟶ U1.Ty)
    (f : Γ ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.mkPi A B) :
    (Γ) ⟶ U2.Tm :=
  P.mkLam A <|
    P.mkApp
      (U0.disp A ≫ A) (U0.substWk .. ≫ B) (U0.disp A ≫ f)
        (by simp [f_tp, comp_mkPi])
      (U0.var A) (U0.var_tp A)

theorem etaExpand_eq {Γ : Ctx} (A : (Γ) ⟶ U0.Ty) (B : (U0.ext A) ⟶ U1.Ty)
    (f : Γ ⟶ U2.Tm) (f_tp : f ≫ U2.tp = P.mkPi A B) :
    P.etaExpand A B f f_tp = f := by
  simp [etaExpand]
  convert P.mkLam_unLam A B f f_tp using 2
  simp [mkApp]; rw [← comp_unLam (f_tp := f_tp), ← Category.assoc]
  conv_rhs => rw [← Category.id_comp (P.unLam ..)]
  congr 2
  apply (U0.disp_pullback A).hom_ext <;> simp

/--
```
Γ ⊢₀ A  Γ.A ⊢₁ t : B  Γ ⊢₀ a : A
--------------------------------
Γ.A ⊢₁ (λA. t) a ≡ t[a] : B[a]
``` -/
@[simp]
theorem mkApp_mkLam {Γ : Ctx} (A : (Γ) ⟶ U0.Ty) (B : (U0.ext A) ⟶ U1.Ty)
    (t : (U0.ext A) ⟶ U1.Tm) (t_tp : t ≫ U1.tp = B)
    (lam_tp : P.mkLam A t ≫ U2.tp = P.mkPi A B)
    (a : (Γ) ⟶ U0.Tm) (a_tp : a ≫ U0.tp = A) :
    P.mkApp A B (P.mkLam A t) lam_tp a a_tp = (U0.sec A a a_tp) ≫ t := by
  rw [mkApp, unLam_mkLam]
  assumption

def toUnstructured :
    UnstructuredUniverse.PolymorphicPi U0.toUnstructuredUniverse
    U1.toUnstructuredUniverse U2.toUnstructuredUniverse where
  Pi := P.mkPi _
  Pi_comp _ _ _ _ _ := (P.comp_mkPi ..).symm
  lam _ b _ := P.mkLam _ b
  lam_comp σ A σA eq _ b _ := (P.comp_mkLam σ A σA eq b).symm
  lam_tp B b b_tp := P.mkLam_tp _ B b b_tp
  unLam := P.unLam _
  unLam_tp B f f_tp := P.unLam_tp _ B f f_tp
  unLam_lam B b b_tp := P.unLam_mkLam _ B b b_tp _
  lam_unLam B := P.mkLam_unLam _ B

end

namespace ofUnstructured

variable {U0 U1 U2 : StructuredUniverse R}
    (P : UnstructuredUniverse.PolymorphicPi U0.toUnstructuredUniverse
    U1.toUnstructuredUniverse U2.toUnstructuredUniverse)

def PiApp (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty) : Γ ⟶ U2.Ty :=
  P.Pi (PtpEquiv.snd U0 AB)

lemma Pi_naturality {Δ Γ} (σ : Δ ⟶ Γ) (AB) :
    PiApp P (σ ≫ AB) = σ ≫ PiApp P AB := by
  simp only [PiApp, PtpEquiv.fst_comp_left, PtpEquiv.snd_comp_left, ← P.Pi_comp]
  rw! [PtpEquiv.fst_comp_left]

def Pi : U0.uvPolyTp @ U1.Ty ⟶ U2.Ty :=
    ofYoneda (PiApp P) (Pi_naturality P)

def lamApp (b : Γ ⟶ U0.uvPolyTp @ U1.Tm) : Γ ⟶ U2.Tm :=
  P.lam _ (PtpEquiv.snd U0 b) rfl

lemma lam_naturality {Δ Γ} (σ : Δ ⟶ Γ) (ab) :
    lamApp P (σ ≫ ab) = σ ≫ lamApp P ab := by
  simp only [lamApp, PtpEquiv.fst_comp_left, PtpEquiv.snd_comp_left, ← P.lam_comp]
  rw! [PtpEquiv.fst_comp_left]
  simp

def lam : U0.uvPolyTp @ U1.Tm ⟶ U2.Tm :=
  ofYoneda (lamApp P) (lam_naturality P)

lemma lamApp_tp (b : Γ ⟶ U0.uvPolyTp @ U1.Tm) :
    lamApp P b ≫ U2.tp = PiApp P (b ≫ U0.Ptp.map U1.tp) := by
  simp only [lamApp, PiApp, PtpEquiv.fst_comp_right, PtpEquiv.snd_comp_right]
  rw! [P.lam_tp, PtpEquiv.fst_comp_right]

def lift (f : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (f_tp : f ≫ U2.tp = PiApp P AB) : Γ ⟶ U0.uvPolyTp @ U1.Tm :=
  PtpEquiv.mk _ (PtpEquiv.fst _ AB) (P.unLam (PtpEquiv.snd _ AB) f f_tp)

lemma lamApp_lift (f : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (f_tp : f ≫ U2.tp = PiApp P AB) :
    lamApp P (lift P f AB f_tp) = f := by
  dsimp only [lamApp, lift]
  rw! (castMode := .all) [PtpEquiv.fst_mk, PtpEquiv.snd_mk, P.unLam_tp, P.lam_unLam]

lemma lift_Ptp_map_tp (f : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (f_tp : f ≫ U2.tp = PiApp P AB) :
    ofUnstructured.lift P f AB f_tp ≫ U0.Ptp.map U1.tp = AB := by
  dsimp [lift]
  rw [PtpEquiv.mk_comp_right, P.unLam_tp, PtpEquiv.eta]

lemma lift_uniq (f : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (f_tp : f ≫ U2.tp = PiApp P AB) (m : Γ ⟶ U0.Ptp.obj U1.Tm)
    (hl : lamApp P m = f) (hr : m ≫ U0.Ptp.map U1.tp = AB) :
    m = lift P f AB f_tp := by
  fapply PtpEquiv.ext _
  · calc PtpEquiv.fst _ m
    _ = PtpEquiv.fst _ (m ≫ U0.Ptp.map U1.tp) := by rw [PtpEquiv.fst_comp_right]
    _ = _ := by simp [hr, lift]
  · subst hl hr
    dsimp only [lift, lamApp]
    rw! [PtpEquiv.fst_comp_right, PtpEquiv.snd_mk, PtpEquiv.snd_comp_right, P.unLam_lam]

end ofUnstructured

def ofUnstructured (P : UnstructuredUniverse.PolymorphicPi U0.toUnstructuredUniverse
    U1.toUnstructuredUniverse U2.toUnstructuredUniverse) : PolymorphicPi U0 U1 U2 where
  Pi := ofUnstructured.Pi P
  lam := ofUnstructured.lam P
  Pi_pullback := ofYoneda_isPullback _ _ _ _ _ _ (ofUnstructured.lamApp_tp P)
    (ofUnstructured.lift P)
    (ofUnstructured.lamApp_lift P)
    (ofUnstructured.lift_Ptp_map_tp P)
    (ofUnstructured.lift_uniq P)

end PolymorphicPi

/-! ## Sigma types -/

/-- The structure on three universes that for
`A : Γ ⟶ U0.Ty` and `B : Γ.A ⟶ U1.Ty` constructs a Π-type `Σ_A B : Γ ⟶ U2.Ty`. -/
structure PolymorphicSigma (U0 U1 U2 : StructuredUniverse R) where
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
protected abbrev Sigma (U : StructuredUniverse R) := PolymorphicSigma U U U

namespace PolymorphicSigma

variable {U0 U1 U2 : StructuredUniverse R} {Γ : Ctx}

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

namespace ofUnstructured

variable {U0 U1 U2 : StructuredUniverse R}
    (S : UnstructuredUniverse.PolymorphicSigma U0.toUnstructuredUniverse
    U1.toUnstructuredUniverse U2.toUnstructuredUniverse)

def SigApp (AB : Γ ⟶ U0.Ptp.obj U1.Ty) : Γ ⟶ U2.Ty :=
  S.Sig (PtpEquiv.snd U0 AB)

lemma Sig_naturality {Δ Γ} (σ : Δ ⟶ Γ) (AB) :
    SigApp S (σ ≫ AB) = σ ≫ SigApp S AB := by
  simp only [SigApp, PtpEquiv.fst_comp_left, PtpEquiv.snd_comp_left, ← S.Sig_comp]
  rw! [PtpEquiv.fst_comp_left]

def Sig : U0.Ptp.obj U1.Ty ⟶ U2.Ty :=
    ofYoneda (SigApp S) (Sig_naturality S)

def pairApp (ab : Γ ⟶ U0.compDom U1) : Γ ⟶ U2.Tm :=
  S.pair (compDomEquiv.dependent ab) (compDomEquiv.fst ab)
    (by rw [compDomEquiv.fst_tp]) (compDomEquiv.snd ab) (by rw [compDomEquiv.snd_tp])

lemma pair_naturality {Δ Γ} (σ : Δ ⟶ Γ) (ab) :
    pairApp S (σ ≫ ab) = σ ≫ pairApp S ab := by
  dsimp [pairApp]
  simp only [← S.pair_comp, compDomEquiv.comp_dependent, compDomEquiv.fst_comp,
      compDomEquiv.snd_comp]
  rw! [compDomEquiv.fst_comp, Category.assoc]

def pair : U0.compDom U1 ⟶ U2.Tm :=
  ofYoneda (pairApp S) (pair_naturality S)

lemma pair_tp (ab : Γ ⟶ U0.compDom U1) :
    pairApp S ab ≫ U2.tp = SigApp S (ab ≫ U0.compP U1) := by
  dsimp [pairApp, SigApp]
  rw! [S.pair_tp, compDomEquiv.dependent_eq, compDomEquiv.fst_tp]

def lift (ab : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (ab_tp : ab ≫ U2.tp = SigApp S AB) :
    Γ ⟶ U0.compDom U1 :=
  let B := PtpEquiv.snd U0 AB
  compDomEquiv.mk (S.fst B ab ab_tp) (S.fst_tp ..) B (S.snd B ab ab_tp) (S.snd_tp ..)

lemma fst_lift (ab : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (ab_tp : ab ≫ U2.tp = SigApp S AB) :
    compDomEquiv.fst (lift S ab AB ab_tp) =
    S.fst (PtpEquiv.snd U0 AB) ab ab_tp := by
  rw [lift, compDomEquiv.fst_mk _ _]

lemma snd_lift (ab : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (ab_tp : ab ≫ U2.tp = SigApp S AB) :
    compDomEquiv.snd (lift S ab AB ab_tp) =
    S.snd (PtpEquiv.snd U0 AB) ab ab_tp := by
  rw [lift, compDomEquiv.snd_mk]

lemma dependent_lift (ab : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (ab_tp : ab ≫ U2.tp = SigApp S AB) :
    compDomEquiv.dependent (lift S ab AB ab_tp) (PtpEquiv.fst U0 AB) (by rw [fst_lift, S.fst_tp]) =
    PtpEquiv.snd U0 AB (PtpEquiv.fst U0 AB) := by
  simp [lift, compDomEquiv.dependent_mk]

lemma pairApp_lift (ab : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (ab_tp : ab ≫ U2.tp = ofUnstructured.SigApp S AB) :
    ofUnstructured.pairApp S (ofUnstructured.lift S ab AB ab_tp) = ab := by
  dsimp [pairApp]
  rw! [fst_lift, S.fst_tp, fst_lift, snd_lift, dependent_lift]
  rw [S.eta]

lemma lift_compP (ab : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (ab_tp : ab ≫ U2.tp = SigApp S AB) :
    lift S ab AB ab_tp ≫ U0.compP U1 = AB := by
  dsimp [lift]
  rw [compDomEquiv.mk_comp, PtpEquiv.eta]

lemma lift_uniq (ab : Γ ⟶ U2.Tm) (AB : Γ ⟶ U0.uvPolyTp @ U1.Ty)
    (ab_tp : ab ≫ U2.tp = SigApp S AB) (m : Γ ⟶ U0.compDom U1)
    (hl : pairApp S m = ab) (hr : m ≫ U0.compP U1 = AB) :
    m = lift S ab AB ab_tp := by
  rw! [← compDomEquiv.eta m]
  fapply compDomEquiv.ext (A := PtpEquiv.fst U0 AB)
  · rw [compDomEquiv.fst_mk, compDomEquiv.fst_tp, hr]
  · rw [fst_lift, compDomEquiv.fst_mk _]
    calc compDomEquiv.fst m
    _ = S.fst (compDomEquiv.dependent m) (pairApp S m) (S.pair_tp ..) := by
      dsimp [pairApp]
      rw [S.fst_pair]
    S.fst (compDomEquiv.dependent m) (pairApp S m) (S.pair_tp ..) =
    S.fst (PtpEquiv.snd U0 AB) ab ab_tp := by
      subst hl hr
      rw! [compDomEquiv.dependent_eq, compDomEquiv.fst_tp]
  · subst hr
    rw [compDomEquiv.dependent_mk, dependent_lift, compDomEquiv.dependent_eq]
    rw! [compDomEquiv.fst_tp, eqToHom_refl, Category.id_comp, compDomEquiv.fst_tp]
  · simp [snd_lift]
    calc compDomEquiv.snd m
    _ = S.snd (compDomEquiv.dependent m) (pairApp S m) (S.pair_tp ..) := by
      dsimp [pairApp]
      rw [S.snd_pair]
    S.snd (compDomEquiv.dependent m) (pairApp S m) (S.pair_tp ..) =
    S.snd (PtpEquiv.snd U0 AB) ab ab_tp := by
      subst hl hr
      rw! [compDomEquiv.dependent_eq, compDomEquiv.fst_tp]

end ofUnstructured

def ofUnstructured {U0 U1 U2 : StructuredUniverse R}
    (S : UnstructuredUniverse.PolymorphicSigma U0.toUnstructuredUniverse
    U1.toUnstructuredUniverse U2.toUnstructuredUniverse) :
    PolymorphicSigma U0 U1 U2 where
  Sig := ofUnstructured.Sig S
  pair := ofUnstructured.pair S
  Sig_pullback := ofYoneda_isPullback _ _ _ _ _ _ (ofUnstructured.pair_tp S)
    (ofUnstructured.lift S)
    (ofUnstructured.pairApp_lift S)
    (ofUnstructured.lift_compP S)
    (ofUnstructured.lift_uniq S)

end PolymorphicSigma

-- def Sigma.mk'
--     (Sig : ∀ {Γ} {A : Γ ⟶ M.Ty}, (M.ext A ⟶ M.Ty) → (Γ ⟶ M.Ty))
--     (comp_Sig : ∀ {Γ Δ} (σ : Δ ⟶ Γ) (A : Γ ⟶ M.Ty) {σA} (eq) (B : M.ext A ⟶ M.Ty),
--       σ ≫ Sig B = Sig (M.substWk σ A σA eq ≫ B))
--     (assoc : ∀ {Γ} {A : Γ ⟶ M.Ty} (B : M.ext A ⟶ M.Ty), M.ext B ≅ M.ext (Sig B))
--     (comp_assoc : ∀ {Γ Δ} (σ : Δ ⟶ Γ) {A : Γ ⟶ M.Ty} {σA} (eq) (B : M.ext A ⟶ M.Ty),
--       substWk _ (substWk _ σ _ _ eq) _ ≫ (assoc B).hom =
--       (assoc (M.substWk σ A σA eq ≫ B)).hom ≫ M.substWk σ _ _ (comp_Sig ..))
--     (assoc_disp : ∀ {Γ} {A : Γ ⟶ M.Ty} (B : M.ext A ⟶ M.Ty),
--       (assoc B).hom ≫ M.disp _ = M.disp _ ≫ M.disp _) :
--     M.Sigma := sorry

section

variable (U0 U1 U2 : StructuredUniverse R)

/--
Used in the definition `IdIntro`,
`diag` is the diagonal substitution into the pullback `U0.ext U0.tp`,
a.k.a the pullback `Tm ×_Ty Tm` or the context `Tm.tp`.
       𝟙 Tm
Tm --------->
 |  ↘diag     var
 |     Tm.tp -----> Tm
 |     |             |
𝟙 Tm   |             |
 |     disp          | tp
 V     |             |
       V             V
      Tm ----------> Ty
              tp
-/
abbrev diag : U0.Tm ⟶ U0.ext U0.tp :=
  (U0.disp_pullback U0.tp).lift (𝟙 U0.Tm) (𝟙 U0.Tm) (by simp)

/-- An auxiliary definition for the structure `StructuredUniverse.Id`.
`Universe.IdIntro` consists of the following commutative square
       refl
Tm --------> Tm
 |            |
 |            |
diag          tp
 |            |
 |            |
 V            V
 Tm.tp -----> Ty
       Id
-/
structure IdIntro where
  Id : U0.ext U0.tp ⟶ U1.Ty
  refl : U0.Tm ⟶ U1.Tm
  refl_tp : refl ≫ U1.tp = U0.diag ≫ Id

variable {U0 U1 U2}

namespace IdIntro

variable (ii : IdIntro U0 U1) {Γ : Ctx}

/-- Used in the definition `StructuredUniverse.Id`,
the comparison map `U0.Tm ⟶ U0.ext ii.Id` induced by the
pullback universal property of `U0.ext ii.Id`.

          refl
 U0.Tm --------->
    ↘comparison   var
 | U1.ext ii.Id ------> U1.Tm
 |   |                   |
diag |                   |
 |  disp              U1.tp
 |   |                   |
 |   V                   V
 V  U0.ext U0.tp ---> U1.Ty
                  Id
-/
def comparison : U0.Tm ⟶ U1.ext ii.Id :=
  (U1.disp_pullback ii.Id).lift ii.refl U0.diag ii.refl_tp

@[simp]
lemma comparison_comp_var : comparison ii ≫ U1.var ii.Id = ii.refl := by
  simp [comparison]

@[simp, reassoc]
lemma comparison_comp_diap_comp_var : comparison ii ≫ U1.disp ii.Id ≫ U0.var U0.tp =
    𝟙 _ := by
  simp [comparison]

@[simp, reassoc]
lemma comparison_comp_disp_comp_disp : ii.comparison ≫ U1.disp ii.Id ≫ U0.disp U0.tp =
    𝟙 _ := by
  simp [comparison]

/-- `dispTpUvPoly` promotes the map `U0.disp U0.tp` to a `UvPoly`,
which we can compose with `dispIdUvPoly` to make `iUvPoly`.
Informally thought of as the context extension
`(A : Ty).(a b : A) ->> (A : Ty) (a : A)`. -/
@[simps] def dispTpUvPoly : UvPoly R (U0.ext U0.tp) U0.Tm :=
  ⟨U0.disp U0.tp, U0.disp_mem _⟩

/-- `dispIdUvPoly` promotes the map `U1.disp ii.Id` to a `UvPoly`,
which we can compose with `dispTpUvPoly` to make `iUvPoly`
Informally thought of as the context extension
`(A : Ty).(a b : A).(p : Id(a,b)) ->> (A : Ty) (a b : A)`. -/
@[simps] def dispIdUvPoly : UvPoly R (U1.ext ii.Id) (U0.ext U0.tp) :=
  ⟨U1.disp ii.Id, U1.disp_mem _⟩

/-- `(U1.ext ii.Id)` over `Tm` can be informally thought of as the context extension
`(A : Ty).(a b : A).(p : Id(a,b)) ->> (A : Ty) (a : A)`.
This is defined by the composition of (maps informally thought of as) context extensions
`(A : Ty).(a b : A).(p : Id(a,b)) ->> (A : Ty).(a b : A) ->> (A : Ty).(a : A)`
This is the signature for a polynomial functor `iUvPoly` on the presheaf category `Ctx`.
-/
abbrev iUvPoly : UvPoly R (U1.ext ii.Id) U0.Tm :=
  (dispIdUvPoly ii).vcomp IdIntro.dispTpUvPoly

instance : R.IsStableUnderPushforwardsAlong ii.iUvPoly.p :=
  UvPoly.isStableUnderPushforwardsAlong_vcomp (U1.disp_mem _) (U0.disp_mem _)

instance :  MorphismProperty.HasPushforwardsAlong R ii.iUvPoly.p :=
  UvPoly.hasPushforwardsAlong_vcomp (U1.disp_mem _) (U0.disp_mem _)

instance : R.HasPushforwardsAlong (UvPoly.id R U0.Tm).p :=
  MorphismProperty.HasPushforwards.hasPushforwardsAlong _ (R.id_mem _)

instance : R.IsStableUnderPushforwardsAlong (UvPoly.id R U0.Tm).p :=
  MorphismProperty.IsStableUnderPushforwards.of_isPushforward _ (R.id_mem _)

/-- Consider the comparison map `comparison : Tm ⟶ i` in the slice over `Tm`.
Then the contravariant action `UVPoly.verticalNatTrans` of taking `UvPoly` on a slice
results in a natural transformation `P_iOver ⟶ P_(𝟙 Tm)`
between the polynomial endofunctors `iUvPoly` and `UvPoly.id U0.Tm` respectively.

  comparison
  Tm ----> i
   \      /
   𝟙\    / `iUvPoly`
     V  V
      Tm
-/
def verticalNatTrans : ii.iUvPoly.functor ⟶ (UvPoly.id R U0.Tm).functor :=
  UvPoly.verticalNatTrans (UvPoly.id R U0.Tm) (iUvPoly ii)
  (comparison ii) (by simp [iUvPoly])

end IdIntro

open IdIntro

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
Fix `A : Ty` and `a : A` - we are working in the slice over `U0.Tm`.
For any context `Γ`, any map `(a, r) : Γ → P_𝟙Tm Tm`
and `(a, C) : Γ ⟶ iFunctor Ty` such that `r ≫ U0.tp = C[x/y, refl_x/p]`,
there is a map `(a,c) : Γ ⟶ iFunctor Tm` such that `c ≫ U0.tp = C` and `c[a/y, refl_a/p] = r`.
Here we are thinking
  `Γ (y : A) (p : A) ⊢ C : Ty`
  `Γ ⊢ r : C[a/y, refl_a/p]`
  `Γ (y : A) (p : A) ⊢ c : Ty`
This witnesses the elimination principle for identity types since
we can take `J (y.p.C;x.r) := c`.
-/
structure Id (ii : IdIntro U0 U1) (U2 : StructuredUniverse R) where
  weakPullback : WeakPullback
    ((verticalNatTrans ii).app U2.Tm)
    (ii.iUvPoly.functor.map U2.tp)
    ((UvPoly.id R U0.Tm).functor.map U2.tp)
    ((verticalNatTrans ii).app U2.Ty)

/-- The additional condition that the weak pullback structure
provided by `Id` is coherent.
We can always replace a weak pullback with a coherent one
(see `coherentId` below),
so this condition is optional, in a sense. -/
class Id.IsCoherent {ii : IdIntro U0 U1} {U2 : StructuredUniverse R}
    (id : Id ii U2) where
  isCoherent : WeakPullback.IsCoherent id.weakPullback

instance {ii : IdIntro U0 U1} {U2 : StructuredUniverse R} :
    HasPullback ((UvPoly.id R U0.Tm).functor.map U2.tp) (ii.verticalNatTrans.app U2.Ty) :=
  sorry

/-- `coherentId` replaces an identity type structure that has possibly
non-coherent/non-substitution-stable elimination with a new identity type
that has coherent/substitution-stable elimination. -/
def coherentId {ii : IdIntro U0 U1} (id : Id ii U2) : Id ii U2 where
  weakPullback := (id.weakPullback.coherent)

/-! ## From structured identity types to unstructured identity types -/

namespace IdIntro

variable (ii : IdIntro U0 U1) {Γ : Ctx}

/-- The substitution `a0.a1 : Γ → Tm.tp`. -/
abbrev endpts (a0 a1 : Γ ⟶ U0.Tm) (h : a0 ≫ U0.tp = a1 ≫ U0.tp) : Γ ⟶ U0.ext U0.tp :=
   (U0.disp_pullback U0.tp).lift a1 a0 h.symm

def toUnstructured :
    U0.toUnstructuredUniverse.PolymorphicIdIntro U1.toUnstructuredUniverse where
  Id a0 a1 a0_tp a1_tp :=
    endpts a0 a1 (by simp[a0_tp,a1_tp]) ≫ ii.Id
  Id_comp  σ A a0 a1 a0_tp a1_tp := by
    simp only [← Category.assoc]
    congr 1
    apply (U0.disp_pullback U0.tp).hom_ext <;> simp
  refl a _ := a ≫ ii.refl
  refl_comp σ A a h := by simp
  refl_tp a a_tp := by
    simp only [Category.assoc, ii.refl_tp]
    simp only [← Category.assoc]
    congr 1
    apply (U0.disp_pullback U0.tp).hom_ext <;> simp

variable {Γ : Ctx} {A : Γ ⟶ U0.Ty} {a : Γ ⟶ U0.Tm} (a_tp : a ≫ U0.tp = A)

end IdIntro

namespace Id

variable (ii : IdIntro U0 U1) (id : Id ii U2)

namespace toUnstructured

variable {Γ : Ctx} {A : Γ ⟶ U0.Ty} {a : Γ ⟶ U0.Tm} (a_tp : a ≫ U0.tp = A)

/- The pullback square
```
   Γ  --------> Tm
   ‖            ‖
   ‖   (pb)     ‖ 𝟙_Tm
   ‖            ‖
   ‖            ‖
   Γ  --------> Tm
          a
```
-/
lemma idPb (U0 : StructuredUniverse R) (a : Γ ⟶ U0.Tm) :
    IsPullback (𝟙 Γ) a a (UvPoly.id R U0.Tm).p :=
  have : IsIso (UvPoly.id R U0.Tm).p := by simp; infer_instance
  IsPullback.of_horiz_isIso (by simp)

/--
`toExtTp` is the substitution,
`toExtId` is the substitution,
`toExtTpPb` is the pullback square,
and `toExtIdPb` is the pullback square in the following
```
      Γ ---------- a --------------> Tm
      |                               |
      |                               |disp
      |                               |
      V                               V
Γ.(x:A).(p:Id(a,x)) --- toExtId ----> U1.ext ii.Id
      |                               |
      |           (toExtIdPb)         |disp
      |                               |
      V                               V
Γ.(x:A) ------------- toExtTp ------> U0.ext U0.tp
      |                               |
      |           (toExtTpPb)         |disp
      |                               |
      V                               V
      Γ ---------- a --------------> Tm
```
The pullback `toExtIdPb'` is the vertical pasting of `toExtIdPb` and `toExtTpPb`
-/
abbrev toExtTp : U0.ext A ⟶ U0.ext U0.tp :=
  endpts (U0.disp A ≫ a) (U0.var A) (by simp[a_tp])

@[inherit_doc toExtTp]
abbrev toExtId : ii.toUnstructured.motiveCtx a a_tp ⟶ U1.ext ii.Id :=
  (U1.disp_pullback ii.Id).lift (U1.var _) (U1.disp _ ≫ toExtTp a_tp)
  (by simp [toUnstructured, toExtTp])

@[inherit_doc toExtTp]
lemma toExtTpPb : IsPullback (toExtTp a_tp) (U0.disp _) (U0.disp _) a :=
  CategoryTheory.IsPullback.of_right (by simpa [a_tp] using U0.disp_pullback _) (by simp)
  (U0.disp_pullback _)

@[inherit_doc toExtTp]
lemma toExtIdPb : IsPullback (toExtId ii a_tp) (U1.disp _) (U1.disp _) (toExtTp a_tp) :=
  CategoryTheory.IsPullback.of_right (by simpa using U1.disp_pullback _)
  (by simp) (U1.disp_pullback ii.Id)

lemma toExtIdPb' : IsPullback (toExtId ii a_tp) (U1.disp _ ≫ U0.disp A)
    (U1.disp _ ≫ U0.disp U0.tp) a :=
  IsPullback.paste_vert (toExtIdPb ii a_tp) (toExtTpPb a_tp)

variable (C : ii.toUnstructured.motiveCtx a a_tp ⟶ U2.Ty) (c : Γ ⟶ U2.Tm)

variable (a) in
/--
For defining `toIUvPolyTm = (a,j)` into the weak pullback,
we define `toUvPolyIdTm = (a,c)`, `toIUvPolyTy = (a,C)` in the following
```
       (a,c)
Γ ------------------------->
 ↘ (a,j)
|         verticalNatTrans.app Tm
|         P_i Tm --------> P_𝟙Tm Tm
|            |                    |
(a,C)        |                    |
|         P_i tp           P_𝟙Tm tp
|            |                    |
|            |                    |
|            V                    V
V         P_i Ty --------> P_𝟙Tm Ty
          verticalNatTrans.app Ty
```
-/
abbrev toUvPolyIdTm : Γ ⟶ (UvPoly.id R U0.Tm).functor.obj U2.Tm :=
  UvPoly.Equiv.mk' a (idPb U0 a) c

@[inherit_doc toUvPolyIdTm]
abbrev toIUvPolyTy : Γ ⟶ ii.iUvPoly.functor.obj U2.Ty :=
  UvPoly.Equiv.mk' a (toExtIdPb' ii a_tp).flip C

variable {ii} {c} (c_tp : c ≫ U2.tp = ii.toUnstructured.reflSubst a a_tp ≫ C)


lemma toIUvPolyTm_aux_fst :
  UvPoly.Equiv.fst (UvPoly.Equiv.mk' a (idPb U0 a) c ≫
  (UvPoly.id R U0.Tm).functor.map U2.tp) = a := by
    simp[UvPoly.Equiv.fst_comp_right]
    --Q: how does it figure out the behavior of id-induced poly? --Ah it does not have to

-- lemma mk'_verticalNatTrans :
--  (UvPoly.Equiv.mk' a ⋯ C ≫ ii.verticalNatTrans.app U2.Ty) =
--   UvPoly.Equiv.mk' a

lemma toIUvPolyTm_aux:
  toUvPolyIdTm a c ≫ (UvPoly.id R U0.Tm).functor.map U2.tp =
  toIUvPolyTy ii a_tp C ≫ ii.verticalNatTrans.app U2.Ty := by
    fapply CategoryTheory.UvPoly.Equiv.ext' (idPb ..)
    · simp[toUvPolyIdTm,] -- why UvPoly.Equiv.fst_mk' not automatic?
      convert_to  a = UvPoly.Equiv.fst (toIUvPolyTy ii a_tp C ≫ ii.verticalNatTrans.app U2.Ty)
      · apply toIUvPolyTm_aux_fst
      simp[toIUvPolyTy,verticalNatTrans]
      simp[UvPoly.fst_verticalNatTrans_app]
      --Q: does verticalNaturalTrans deserve a specific ii-ver?
      -- have e:
      --  UvPoly.Equiv.mk' a (id ..) c ≫ (UvPoly.id R U0.Tm).functor.map U2.tp =
      --  UvPoly.Equiv.mk' a (id ..) C := sorry

    · simp[verticalNatTrans,toIUvPolyTy]
      rw[UvPoly.Equiv.snd'_comp_right
         (H := by
             convert (idPb U0 a) --how do I know it requires indenting like this...?
             · simp[UvPoly.Equiv.fst_comp_right]
             · simp[])]
      -- rw[UvPoly.snd'_verticalNatTrans_app
      --    (P := (UvPoly.id R U0.Tm)) (Q := ii.iUvPoly)
      --    (H' := by
      --         convert (idPb U0 a)
      --         · simp[UvPoly.Equiv.fst_comp_right]
      --         · simp[])
      --    (ρ := ii.comparison)
      --    (h := by simp)
      --    (H := by
      --          convert (toExtIdPb' ii a_tp))

      --  ]
      simp[UvPoly.snd'_verticalNatTrans_app]
      sorry

-- previously called `toWeakpullback`
@[inherit_doc toUvPolyIdTm]
abbrev toIUvPolyTm : Γ ⟶ ii.iUvPoly.functor.obj U2.Tm :=
  id.weakPullback.lift (toUvPolyIdTm a c) (toIUvPolyTy ii a_tp C)
  (by
    have := c_tp -- TODO: remove
    apply toIUvPolyTm_aux)

lemma fst_toIUvPolyTm : UvPoly.Equiv.fst (toIUvPolyTm id a_tp C c_tp) = a :=
  calc
    _ = UvPoly.Equiv.fst (toIUvPolyTm id a_tp C c_tp ≫ ii.iUvPoly.functor.map U2.tp) := by
      rw [UvPoly.Equiv.fst_comp_right]
    _ = _ := by simp

def j : ii.toUnstructured.motiveCtx a a_tp ⟶ U2.Tm :=
  UvPoly.Equiv.snd' (toIUvPolyTm id a_tp C c_tp)
  (by convert (toExtIdPb' ii a_tp).flip; apply fst_toIUvPolyTm)

end toUnstructured

open toUnstructured

def toUnstructured [id.IsCoherent] :
    UnstructuredUniverse.PolymorphicIdElim (ii.toUnstructured)
    U2.toUnstructuredUniverse where
  j a a_tp C c c_tp := j id a_tp C c_tp
  comp_j σ A a a_tp C c c_tp := by
    have e := id.IsCoherent

    sorry -- NOTE: this will need [id.IsCoherent]
  j_tp := by
    intro Γ A a a_tp C c c_tp
    simp[j]
    sorry
  reflSubst_j := sorry

end Id

/-! ## From unstructured identity types to structured identity types -/

namespace IdIntro

variable (ii : PolymorphicIdIntro U0.toUnstructuredUniverse U1.toUnstructuredUniverse)

namespace ofUnstructured

def IdApp {Γ} (α : Γ ⟶ U0.ext U0.tp) : Γ ⟶ U1.Ty :=
  ii.Id (α ≫ U0.disp _) (α ≫ U0.var _) rfl (by simp)

lemma IdApp_comp {Δ Γ} (σ : Δ ⟶ Γ) (α : Γ ⟶ U0.ext U0.tp) :
    IdApp ii (σ ≫ α) = σ ≫ IdApp ii α := by
  simp[IdApp,ii.Id_comp]

def reflApp {Γ} (a : Γ ⟶ U0.Tm) : Γ ⟶ U1.Tm :=
  ii.refl a rfl

lemma reflApp_comp {Δ Γ} (σ : Δ ⟶ Γ) (A : Γ ⟶ U0.Tm) :
    reflApp ii (σ ≫ A) = σ ≫ reflApp ii A := by
  simp[reflApp,← ii.refl_comp]

lemma reflApp_tp {Γ} (ab : Γ ⟶ U0.Tm) : reflApp ii ab ≫ U1.tp = IdApp ii (ab ≫ U0.diag) := by
  simp[reflApp,ii.refl_tp,IdApp]

end ofUnstructured

open ofUnstructured

def ofUnstructured : IdIntro U0 U1 where
  Id := ofYoneda (IdApp ii) (IdApp_comp _)
  refl := ofYoneda (reflApp ii) (reflApp_comp _)
  refl_tp := by apply ofYoneda_comm_sq; simp [reflApp_tp]

end IdIntro

namespace Id

variable {ii : PolymorphicIdIntro U0.toUnstructuredUniverse U1.toUnstructuredUniverse}
  (ie : PolymorphicIdElim ii U2.toUnstructuredUniverse)

namespace ofUnstructured

variable {Γ : Ctx} (toUvPolyIdTm : Γ ⟶ (UvPoly.id R U0.Tm).functor.obj U2.Tm)
  (toIUvPolyTy : Γ ⟶ (IdIntro.ofUnstructured ii).iUvPoly.functor.obj U2.Ty)
  (toUvPolyIdTm_uvPolyIdTp : toUvPolyIdTm ≫ (UvPoly.id R U0.Tm).functor.map U2.tp =
    toIUvPolyTy ≫ (IdIntro.ofUnstructured ii).verticalNatTrans.app U2.Ty)

/--
For defining `lift = (a,j)` into `P_i Tm = (IdIntro.ofUnstructured ii).iUvPoly.functor.obj U2.Tm`,
consider the following diagram
```
       (a,c)
Γ ------------------------->
 ↘ (a,j)
|         verticalNatTrans.app Tm
|         P_i Tm --------> P_𝟙Tm Tm
|            |                    |
(a,C)        |                    |
|         P_i tp           P_𝟙Tm tp
|            |                    |
|            |                    |
|            V                    V
V         P_i Ty --------> P_𝟙Tm Ty
          verticalNatTrans.app Ty
```
In the following lemmas we will have
`toUvPolyIdTm = (a,c)`, `toIUvPolyTy = (a,C)`,
and `endpoint = a : Γ → Tm`. -/
def endpoint : Γ ⟶ U0.Tm := UvPoly.Equiv.fst toIUvPolyTy

/--
`toExtTp` is the substitution,
`toExtId` is the substitution,
`toExtTpPb` is the pullback square,
and `toExtIdPb` is the pullback square in the following
```
      Γ ---------- a --------------> Tm
      |                               |
      |                               |disp
      |                               |
      V                               V
Γ.(x:A).(p:Id(a,x)) --- toExtId ----> U1.ext ii.Id
      |                               |
      |           (toExtIdPb)         |disp
      |                               |
      V                               V
Γ.(x:A) ------------- toExtTp ------> U0.ext U0.tp
      |                               |
      |           (toExtTpPb)         |disp
      |                               |
      V                               V
      Γ ---------- a --------------> Tm
```
The pullback `toExtIdPb'` is the vertical pasting of `toExtIdPb` and `toExtTpPb`
-/
abbrev toExtTp : U0.ext (endpoint toIUvPolyTy ≫ U0.tp) ⟶ U0.ext U0.tp :=
  endpts (U0.disp _ ≫ endpoint toIUvPolyTy) (U0.var _) (by simp)

@[simp]
lemma toExtTp_Id : toExtTp toIUvPolyTy ≫ (ofUnstructured ii).Id =
    ii.Id (U0.disp (endpoint toIUvPolyTy ≫ U0.tp) ≫
    endpoint toIUvPolyTy) (U0.var _) rfl (by simp) := by
  simp [ofUnstructured, ofUnstructured.IdApp]

@[inherit_doc toExtTp]
abbrev toExtId : ii.motiveCtx (endpoint toIUvPolyTy) rfl ⟶ U1.ext (ofUnstructured ii).Id :=
  (U1.disp_pullback _).lift (U1.var _) (U1.disp _ ≫ toExtTp toIUvPolyTy) (by simp)

@[inherit_doc toExtTp]
lemma toExtTpPb : IsPullback (toExtTp toIUvPolyTy) (U0.disp _) (U0.disp _) (endpoint toIUvPolyTy) :=
  CategoryTheory.IsPullback.of_right (by simpa using U0.disp_pullback _) (by simp)
  (U0.disp_pullback _)

@[inherit_doc toExtTp]
lemma toExtIdPb : IsPullback (toExtId toIUvPolyTy) (U1.disp _) (U1.disp _) (toExtTp toIUvPolyTy) :=
  CategoryTheory.IsPullback.of_right (by simpa using U1.disp_pullback _)
  (by simp) (U1.disp_pullback (ofUnstructured ii).Id)

lemma toExtIdPb' : IsPullback (toExtId toIUvPolyTy) (U1.disp _ ≫ U0.disp _)
    (U1.disp _ ≫ U0.disp U0.tp) (endpoint toIUvPolyTy) :=
  IsPullback.paste_vert (toExtIdPb toIUvPolyTy) (toExtTpPb toIUvPolyTy)

-- TODO: maybe move `toUnstructured.toExtIdPb'` out of its current namespace,
-- since it is general enough to used here
def motive : ii.motiveCtx (endpoint toIUvPolyTy) rfl ⟶ U2.Ty :=
  UvPoly.Equiv.snd' toIUvPolyTy (toExtIdPb' toIUvPolyTy).flip

def reflCase : Γ ⟶ U2.Tm :=
  UvPoly.Equiv.snd' toUvPolyIdTm (toUnstructured.idPb U0 (UvPoly.Equiv.fst toUvPolyIdTm))

variable {toIUvPolyTy} {toUvPolyIdTm}

include toUvPolyIdTm_uvPolyIdTp in -- TODO: remove
lemma reflCase_tp : reflCase toUvPolyIdTm ≫ U2.tp =
    ii.reflSubst (endpoint toIUvPolyTy) rfl ≫ motive toIUvPolyTy :=
  have := toUvPolyIdTm_uvPolyIdTp -- TODO: remove
  --also need verticalNatTrans
  sorry

def j : ii.motiveCtx (endpoint toIUvPolyTy) rfl ⟶ U2.Tm :=
  ie.j (endpoint toIUvPolyTy) rfl (motive toIUvPolyTy) (reflCase toUvPolyIdTm)
  (reflCase_tp toUvPolyIdTm_uvPolyIdTp)

@[inherit_doc endpoint]
def lift : Γ ⟶ (IdIntro.ofUnstructured ii).iUvPoly.functor.obj U2.Tm :=
  UvPoly.Equiv.mk' (endpoint toIUvPolyTy)
  (toExtIdPb' toIUvPolyTy).flip (j ie toUvPolyIdTm_uvPolyIdTp)

end ofUnstructured

open ofUnstructured

def ofUnstructured : Id (IdIntro.ofUnstructured ii) U2 where
  weakPullback :=
  { w := by simp only [NatTrans.naturality]
    lift _ _ toUvPolyIdTm_uvPolyIdTp := lift ie toUvPolyIdTm_uvPolyIdTp
    lift_fst' := sorry
    lift_snd' := sorry }

instance : (Id.ofUnstructured ie).IsCoherent := sorry

end Id

end

end StructuredUniverse
