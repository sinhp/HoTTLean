import HoTTLean.Groupoids.IsIsofibration

/-!
Here we construct universes for the groupoid natural model.
-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section
open CategoryTheory Limits Model UnstructuredUniverse StructuredUniverse
  Functor.Groupoidal GroupoidModel.Ctx GroupoidModel.U

namespace GroupoidModel

open U

/-- The universe the classifies `v`-large terms and types.
  The π-clan we use is the set of groupoid isofibrations.
-/
@[simps!]
def StructuredU : StructuredUniverse Grpd.IsIsofibration where
  __ := U
  morphismProperty := sorry

namespace U

open MonoidalCategory

def liftSeqObjs (i : Nat) (h : i < 4) : StructuredUniverse Grpd.IsIsofibration.{5} :=
  match i with
  | 0 => StructuredU.{0,4}
  | 1 => StructuredU.{1,4}
  | 2 => StructuredU.{2,4}
  | 3 => StructuredU.{3,4}
  | (n+4) => by omega

def lift : UHom StructuredU.{v, max u (v+2)} StructuredU.{v+1, max u (v+2)} :=
  sorry
    -- @UHom.ofTyIsoExt _ _ _ _ _ _
    -- { mapTy := U.liftTy.{v,max u (v+2)}
    --   mapTm := U.liftTm
    --   pb := IsPullback.liftTm_isPullback }
    -- asSmallClosedType
    -- isoExtAsSmallClosedType.{v,u}

def liftSeqHomSucc' (i : Nat) (h : i < 3) :
    UHom (liftSeqObjs i (by omega)) (liftSeqObjs (i + 1) (by omega)) :=
  match i with
  | 0 => lift.{0,4}
  | 1 => lift.{1,4}
  | 2 => lift.{2,4}
  | (n+3) => by omega

/--
  The groupoid natural model with three nested representable universes
  within the ambient natural model.
-/
def liftSeq : UHomSeq Grpd.IsIsofibration.{5} where
  length := 3
  objs := liftSeqObjs
  homSucc' := liftSeqHomSucc'

def USig : StructuredUniverse.Sigma StructuredU :=
  PolymorphicSigma.ofUnstructured GroupoidModel.USig

def smallUPi : StructuredUniverse.Pi StructuredU :=
  PolymorphicPi.ofUnstructured GroupoidModel.UPi

#exit
def liftSeqSigs' (i : ℕ) (ilen : i < 4) :
    StructuredUniverse.Sigma (liftSeqObjs i ilen) :=
  match i with
  | 0 => USig.{0, 4}
  | 1 => USig.{1, 4}
  | 2 => USig.{2, 4}
  | 3 => USig.{3, 4}
  | (n+4) => by omega

instance liftSeqSigma : liftSeq.SigSeq where
  nmSig := liftSeqSigs'

def uHomSeqPis' (i : ℕ) (ilen : i < 4) :
    StructuredUniverse.Pi (uHomSeqObjs i ilen) :=
  match i with
  | 0 => smallUPi.{0,4}
  | 1 => smallUPi.{1,4}
  | 2 => smallUPi.{2,4}
  | 3 => smallUPi.{3,4}
  | (n+4) => by omega

instance uHomSeqPi : uHomSeq.PiSeq where
  nmPi := uHomSeqPis'

-- section

-- variable {Γ : Grpd} {C : Type (v+1)} [Category.{v} C] {Δ : Grpd} (σ : Δ ⟶ Γ)

-- namespace PtpEquiv

-- variable (AB : Γ ⟶ StructuredU.{v}.Ptp.obj (Ctx.coreAsSmall C))

-- /--
-- A map `(AB : (Γ) ⟶ U.{v}.Ptp.obj (Ctx.ofCategory C))`
-- is equivalent to a pair of functors `A : Γ ⥤ Grpd` and `B : ∫(fst AB) ⥤ C`,
-- thought of as a dependent pair `A : Type` and `B : A ⟶ Type` when `C = Grpd`.
-- `PtpEquiv.fst` is the `A` in this pair.
-- -/
-- def fst : Γ ⥤ Grpd.{v,v} :=
--   toCoreAsSmallEquiv (StructuredUniverse.PtpEquiv.fst U AB)

-- variable (A := fst AB) (hA : A = fst AB := by rfl)

-- /--
-- A map `(AB : (Γ) ⟶ U.{v}.Ptp.obj (Ctx.ofCategory C))`
-- is equivalent to a pair of functors `A : Γ ⥤ Grpd` and `B : ∫(fst AB) ⥤ C`,
-- thought of as a dependent pair `A : Type` and `B : A ⟶ Type` when `C = Grpd`.
-- `PtpEquiv.snd` is the `B` in this pair.
-- -/
-- def snd : ∫A ⥤ C :=
--   toCoreAsSmallEquiv (StructuredUniverse.PtpEquiv.snd U AB (toCoreAsSmallEquiv.symm A) (by
--     simp [StructuredUniverse.PtpEquiv.fst, hA, fst]))

-- nonrec theorem fst_comp_left : fst (σ ≫ AB) = σ ⋙ fst AB := by
--   dsimp only [fst]
--   rw [PtpEquiv.fst_comp_left, ← toCoreAsSmallEquiv_apply_comp_left, Grpd.comp_eq_comp]

-- theorem fst_comp_right {D : Type (v + 1)} [Category.{v, v + 1} D] (F : C ⥤ D) :
--     fst (AB ≫ U.Ptp.map (Ctx.coreAsSmallFunctor F)) = fst AB := by
--   dsimp only [fst]
--   rw [StructuredUniverse.PtpEquiv.fst_comp_right]

-- nonrec theorem snd_comp_left : snd (σ ≫ AB) (σ ⋙ A) (by rw [hA, fst_comp_left]) =
--     map (eqToHom (by rw [hA])) ⋙ pre _ σ ⋙ snd AB := by
--   dsimp only [snd]
--   erw [PtpEquiv.snd_comp_left _ rfl
--     (by simp [toCoreAsSmallEquiv_symm_apply_comp_left, Grpd.comp_eq_comp, hA, fst]),
--     toCoreAsSmallEquiv_apply_comp_left]
--   subst hA
--   simp [map_id_eq, substWk_eq]; rfl

-- /--
-- A map `(AB : (Γ) ⟶ U.{v}.Ptp.obj (Ctx.ofCategory C))`
-- is equivalent to a pair of functors `A : Γ ⥤ Grpd` and `B : ∫(fst AB) ⥤ C`,
-- thought of as a dependent pair `A : Type` and `B : A ⟶ Type` when `C = Grpd`.
-- `PtpEquiv.mk` constructs such a map `AB` from such a pair `A` and `B`.
-- -/
-- def mk (A : Γ ⥤ Grpd.{v,v}) (B : ∫(A) ⥤ C) :
--     Γ ⟶ U.{v}.Ptp.obj (Ctx.coreAsSmall C) :=
--   StructuredUniverse.PtpEquiv.mk U (toCoreAsSmallEquiv.symm A) (toCoreAsSmallEquiv.symm B)

-- theorem hext (AB1 AB2 : Γ ⟶ U.{v}.Ptp.obj Ty.{v}) (hfst : fst AB1 = fst AB2)
--     (hsnd : HEq (snd AB1) (snd AB2)) : AB1 = AB2 := by
--   have hfst' : StructuredUniverse.PtpEquiv.fst U AB1 = StructuredUniverse.PtpEquiv.fst U AB2 := by
--     dsimp [fst] at hfst
--     aesop
--   apply StructuredUniverse.PtpEquiv.ext U (StructuredUniverse.PtpEquiv.fst U AB1) ?_ hfst' ?_
--   · simp
--   · dsimp only [snd] at hsnd
--     apply toCoreAsSmallEquiv.injective
--     conv => right; rw! (castMode := .all) [hfst']
--     simp [← heq_eq_eq]
--     exact hsnd

-- @[simp]
-- lemma fst_mk (A : Γ ⥤ Grpd.{v,v}) (B : ∫(A) ⥤ C) :
--     fst (mk A B) = A := by
--   simp [fst, mk, StructuredUniverse.PtpEquiv.fst_mk]

-- lemma Grpd.eqToHom_comp_heq {A B : Grpd} {C : Type*} [Category C]
--     (h : A = B) (F : B ⥤ C) : eqToHom h ⋙ F ≍ F := by
--   subst h
--   simp [Grpd.id_eq_id, Functor.id_comp]

-- lemma snd_mk (A A' : Γ ⥤ Grpd.{v,v}) (hA : A = A') (B : ∫(A) ⥤ C) :
--     snd (mk A B) A' (by rw [fst_mk, hA]) = map (eqToHom hA.symm) ⋙ B := by
--   dsimp only [snd, mk]
--   subst hA
--   rw [StructuredUniverse.PtpEquiv.snd_mk U (toCoreAsSmallEquiv.symm A) (toCoreAsSmallEquiv.symm B)]
--   erw [Equiv.apply_symm_apply toCoreAsSmallEquiv B]
--   simp [map_id_eq]

-- lemma snd_mk_heq (A : Γ ⥤ Grpd.{v,v}) (B : ∫(A) ⥤ C) :
--     snd (mk A B) ≍ B := by
--   simp [snd_mk, map_eqToHom_comp_heq]

-- end PtpEquiv

-- def compDom := U.{v}.uvPolyTp.compDom U.{v}.uvPolyTp

-- @[simp]
-- abbrev compP : compDom.{v} ⟶ U.{v}.Ptp.obj Ty.{v} :=
--   StructuredUniverse.compP U U

-- namespace compDom

-- variable (ab : (Γ) ⟶ compDom.{v})

-- /-- Universal property of `compDom`, decomposition (part 1).

-- A map `ab : (Γ) ⟶ compDom` is equivalently three functors
-- `fst, dependent, snd` such that `snd_forgetToGrpd`. The functor `fst : Γ ⥤ PGrpd`
-- is `(a : A)` in `(a : A) × (b : B a)`.
-- -/
-- def fst : Γ ⥤ PGrpd.{v,v} :=
--   toCoreAsSmallEquiv (StructuredUniverse.compDomEquiv.fst ab)

-- /-- Universal property of `compDom`, decomposition (part 2).

-- A map `ab : (Γ) ⟶ compDom` is equivalently three functors
-- `fst, dependent, snd` such that `snd_forgetToGrpd`. The functor `dependent : Γ ⥤ Grpd`
-- is `B : A → Type` in `(a : A) × (b : B a)`.
-- -/
-- def dependent (A := fst ab ⋙ PGrpd.forgetToGrpd) (eq : fst ab ⋙ PGrpd.forgetToGrpd = A := by rfl) :
--     ∫(A) ⥤ Grpd.{v,v} :=
--   toCoreAsSmallEquiv (StructuredUniverse.compDomEquiv.dependent ab (toCoreAsSmallEquiv.symm A) (by
--     simp only [U_Ty, U_Tm, compDomEquiv.fst, U_tp, ← eq]
--     erw [toCoreAsSmallEquiv_symm_apply_comp_right]
--     simp [fst]; rfl))

-- /-- Universal property of `compDom`, decomposition (part 3).

-- A map `ab : (Γ) ⟶ compDom` is equivalently three functors
-- `fst, dependent, snd` such that `snd_forgetToGrpd`. The functor `snd : Γ ⥤ PGrpd`
-- is `(b : B a)` in `(a : A) × (b : B a)`.
-- -/
-- def snd : Γ ⥤ PGrpd.{v,v} :=
--   toCoreAsSmallEquiv (StructuredUniverse.compDomEquiv.snd ab)

-- /-- Universal property of `compDom`, decomposition (part 4).

-- A map `ab : (Γ) ⟶ compDom` is equivalently three functors
-- `fst, dependent, snd` such that `snd_forgetToGrpd`.
-- The equation `snd_forgetToGrpd` says that the type of `b : B a` agrees with
-- the expression for `B a` obtained solely from `dependent`, or `B : A ⟶ Type`.
-- -/
-- theorem snd_forgetToGrpd : snd ab ⋙ PGrpd.forgetToGrpd = sec _ (fst ab) rfl ⋙ (dependent ab) := by
--   erw [← toCoreAsSmallEquiv_apply_comp_right, ← Grpd.comp_eq_comp,
--     StructuredUniverse.compDomEquiv.snd_tp ab, sec_eq]
--   rfl

-- /-- Universal property of `compDom`, constructing a map into `compDom`. -/
-- def mk (α : Γ ⥤ PGrpd.{v,v}) (A := α ⋙ PGrpd.forgetToGrpd)
--     (hA : α ⋙ PGrpd.forgetToGrpd = A := by rfl)
--     (B : ∫(A) ⥤ Grpd.{v,v})
--     (β : Γ ⥤ PGrpd.{v,v}) (h : β ⋙ PGrpd.forgetToGrpd = sec _ α hA ⋙ B) :
--     Γ ⟶ compDom.{v} :=
--   StructuredUniverse.compDomEquiv.mk (toCoreAsSmallEquiv.symm α) (A := toCoreAsSmallEquiv.symm A)
--     (by rw [← hA, toCoreAsSmallEquiv_symm_apply_comp_right]; rfl)
--     (toCoreAsSmallEquiv.symm B) (toCoreAsSmallEquiv.symm β)
--     (by
--       dsimp [U_tp, tp, Grpd.comp_eq_comp]
--       rw [← toCoreAsSmallEquiv_symm_apply_comp_right β PGrpd.forgetToGrpd, h,
--         toCoreAsSmallEquiv_symm_apply_comp_left]
--       congr 1
--       simp only [sec_eq, Equiv.apply_symm_apply]
--       rw! (castMode := .all) [toCoreAsSmallEquiv.apply_symm_apply]
--       )

-- theorem fst_forgetToGrpd : fst ab ⋙ PGrpd.forgetToGrpd =
--     U.PtpEquiv.fst (ab ≫ compP.{v}) := by
--   erw [U.PtpEquiv.fst, ← compDomEquiv.fst_tp ab, ← toCoreAsSmallEquiv_apply_comp_right]
--   rfl

-- theorem dependent_eq (A := fst ab ⋙ PGrpd.forgetToGrpd)
--     (eq : fst ab ⋙ PGrpd.forgetToGrpd = A := by rfl) : dependent ab A eq =
--     map (eqToHom (by rw [← eq, fst_forgetToGrpd])) ⋙ U.PtpEquiv.snd (ab ≫ compP.{v}) := by
--   dsimp only [dependent, PtpEquiv.snd]
--   rw [StructuredUniverse.compDomEquiv.dependent_eq _ _ _, ← toCoreAsSmallEquiv_apply_comp_left]
--   subst eq
--   rw! [← fst_forgetToGrpd]
--   simp [map_id_eq]

-- theorem dependent_heq : HEq (dependent ab) (U.PtpEquiv.snd (ab ≫ compP.{v})) := by
--   rw [dependent_eq]
--   apply Functor.precomp_heq_of_heq_id
--   · rw [fst_forgetToGrpd]
--   · rw [fst_forgetToGrpd]
--   · apply map_eqToHom_heq_id_cod

-- theorem fst_comp : fst (σ ≫ ab) = σ ⋙ fst ab := by
--   dsimp only [fst]
--   rw [StructuredUniverse.compDomEquiv.fst_comp, Grpd.comp_eq_comp,
--     toCoreAsSmallEquiv_apply_comp_left]

-- theorem dependent_comp : dependent (σ ≫ ab) =
--     map (eqToHom (by rw [fst_comp, Functor.assoc]))
--     ⋙ pre _ σ ⋙ dependent ab := by
--   rw [dependent, dependent,
--     ← StructuredUniverse.compDomEquiv.comp_dependent (eq1 := rfl)
--       (eq2 := by erw [← compDomEquiv.fst_comp_assoc, fst, toCoreAsSmallEquiv.eq_symm_apply]; rfl),
--     substWk_eq]
--   rfl

-- theorem snd_comp : snd (σ ≫ ab) = σ ⋙ snd ab := by
--   dsimp only [snd]
--   rw [StructuredUniverse.compDomEquiv.snd_comp, Grpd.comp_eq_comp,
--     toCoreAsSmallEquiv_apply_comp_left]

-- /-- First component of the computation rule for `mk`. -/
-- theorem fst_mk (α : Γ ⥤ PGrpd.{v,v}) (A := α ⋙ PGrpd.forgetToGrpd)
--     (hA : α ⋙ PGrpd.forgetToGrpd = A := by rfl)
--     (B : ∫(A) ⥤ Grpd.{v,v})
--     (β : Γ ⥤ PGrpd.{v,v}) (h : β ⋙ PGrpd.forgetToGrpd = sec _ α hA ⋙ B) :
--     fst (mk α A hA B β h) = α := by
--   simp [fst, mk, StructuredUniverse.compDomEquiv.fst_mk]

-- /-- Second component of the computation rule for `mk`. -/
-- theorem dependent_mk (α : Γ ⥤ PGrpd.{v,v}) (A := α ⋙ PGrpd.forgetToGrpd)
--     (hA : α ⋙ PGrpd.forgetToGrpd = A := by rfl)
--     (B : ∫(A) ⥤ Grpd.{v,v})
--     (β : Γ ⥤ PGrpd.{v,v}) (h : β ⋙ PGrpd.forgetToGrpd = sec _ α hA ⋙ B) :
--     dependent (mk α A hA B β h) = map (eqToHom (by subst hA; rw [fst_mk])) ⋙ B := by
--   dsimp [dependent, mk]
--   rw [Equiv.apply_eq_iff_eq_symm_apply]
--   rw [compDomEquiv.dependent_mk]
--   · rw [toCoreAsSmallEquiv_symm_apply_comp_left]
--     erw [eqToHom_eq_homOf_map]
--     rfl
--   · simp [fst, compDomEquiv.fst_mk, hA]

-- /-- Second component of the computation rule for `mk`. -/
-- theorem snd_mk (α : Γ ⥤ PGrpd.{v,v}) (A := α ⋙ PGrpd.forgetToGrpd)
--     (hA : α ⋙ PGrpd.forgetToGrpd = A := by rfl)
--     (B : ∫(A) ⥤ Grpd.{v,v})
--     (β : Γ ⥤ PGrpd.{v,v}) (h : β ⋙ PGrpd.forgetToGrpd = sec _ α hA ⋙ B) :
--     snd (mk α A hA B β h) = β := by
--   dsimp [snd, mk]
--   rw [StructuredUniverse.compDomEquiv.snd_mk]
--   simp

-- theorem ext (ab1 ab2 : Γ ⟶ U.compDom.{v})
--     (hfst : fst ab1 = fst ab2)
--     (hdependent : dependent ab1 = map (eqToHom (by rw [hfst])) ⋙ dependent ab2)
--     (hsnd : snd ab1 = snd ab2) : ab1 = ab2 := by
--   dsimp only [compDom] at ab1
--   have h1 : compDomEquiv.fst ab1 = compDomEquiv.fst ab2 := by
--     apply toCoreAsSmallEquiv.injective
--     assumption
--   fapply compDomEquiv.ext rfl h1
--   · dsimp [dependent, fst] at hdependent
--     apply toCoreAsSmallEquiv.injective
--     convert hdependent
--     · rw [toCoreAsSmallEquiv_symm_apply_comp_right]
--       simp; rfl
--     rw! (castMode := .all) [toCoreAsSmallEquiv_symm_apply_comp_right,
--       Equiv.symm_apply_apply, h1, hfst]
--     simp [map_id_eq]
--     congr 1
--     simp [← heq_eq_eq]
--     rfl
--   · apply toCoreAsSmallEquiv.injective
--     assumption

-- theorem hext (ab1 ab2 : Γ ⟶ U.compDom.{v})
--     (hfst : fst ab1 = fst ab2) (hdependent : HEq (dependent ab1) (dependent ab2))
--     (hsnd : snd ab1 = snd ab2) : ab1 = ab2 := by
--   apply ext
--   · rw! [hdependent]
--     simp [← heq_eq_eq]
--     conv => right; rw! (castMode := .all) [hfst]
--     simp [map_id_eq]
--   · assumption
--   · assumption

-- end compDom

-- end

end U
end GroupoidModel

end
