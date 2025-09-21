import Mathlib.Tactic.GCongr
import HoTTLean.Syntax.EqCtx
import HoTTLean.Syntax.InversionLemmas

namespace SynthLean

variable {χ : Type*} {E : Axioms χ}

/-! # `gcongr` lemmas

In this module we prove special-case congruence lemmas for use with `gcongr`.
Some of these have fewer premises than general congruences. -/

/- Note: `refl` lemmas are not marked `@[refl]`
because the `rfl` tactic expects unconditional reflexivity
whereas we have `Γ ⊢[l] A → Γ ⊢[l] A ≡ A`. -/

attribute [symm] EqTp.symm_tp
attribute [trans] EqTp.trans_tp

-- https://github.com/leanprover/lean4/issues/9997
-- attribute [symm] EqTm.symm_tm
attribute [trans] EqTm.trans_tm

/-! ## Lemmas for types -/

attribute [gcongr] EqTp.cong_pi

@[gcongr]
theorem EqTp.cong_pi_dom {Γ A A' B l l'} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A, l) :: Γ ⊢[l'] B →
    E ∣ Γ ⊢[max l l'] .pi l l' A B ≡ .pi l l' A' B :=
  fun h h' => EqTp.cong_pi h (EqTp.refl_tp h')

@[gcongr]
theorem EqTp.cong_pi_cod {Γ A B B' l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[max l l'] .pi l l' A B ≡ .pi l l' A B' :=
  fun h => EqTp.cong_pi (EqTp.refl_tp h.wf_binder) h

attribute [gcongr] EqTp.cong_sigma

@[gcongr]
theorem EqTp.cong_sigma_dom {Γ A A' B l l'} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A, l) :: Γ ⊢[l'] B →
    E ∣ Γ ⊢[max l l'] .sigma l l' A B ≡ .sigma l l' A' B :=
  fun h h' => EqTp.cong_sigma h (EqTp.refl_tp h')

@[gcongr]
theorem EqTp.cong_sigma_cod {Γ A B B' l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[max l l'] .sigma l l' A B ≡ .sigma l l' A B' :=
  fun h => EqTp.cong_sigma (EqTp.refl_tp h.wf_binder) h

attribute [gcongr] EqTp.cong_el

@[gcongr]
theorem EqTp.cong_Id_tp {Γ A A' t u l} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ Γ ⊢[l] t : A →
    E ∣ Γ ⊢[l] u : A →
    E ∣ Γ ⊢[l] .Id l A t u ≡ .Id l A' t u :=
  fun A t u => .cong_Id A (.refl_tm t) (.refl_tm u)

@[gcongr]
theorem EqTp.cong_Id_left {Γ A t t' u l} :
    E ∣ Γ ⊢[l] t ≡ t' : A →
    E ∣ Γ ⊢[l] u : A →
    E ∣ Γ ⊢[l] .Id l A t u ≡ .Id l A t' u :=
  fun h h' => .cong_Id (.refl_tp h.wf_tp) h (.refl_tm h')

@[gcongr]
theorem EqTp.cong_Id_right {Γ A t u u' l} :
    E ∣ Γ ⊢[l] t : A →
    E ∣ Γ ⊢[l] u ≡ u' : A →
    E ∣ Γ ⊢[l] .Id l A t u ≡ .Id l A t u' :=
  fun h h' => .cong_Id (.refl_tp h.wf_tp) (.refl_tm h) h'

attribute [gcongr] EqTp.cong_Id

/-! ### Lemmas for terms -/

attribute [gcongr] EqTm.cong_lam

@[gcongr]
theorem EqTm.cong_lam_dom {Γ A A' B t l l'} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ (A, l) :: Γ ⊢[l'] t : B →
    E ∣ Γ ⊢[max l l'] .lam l l' A t ≡ .lam l l' A' t : .pi l l' A B :=
  fun hAA' ht => EqTm.cong_lam hAA' (EqTm.refl_tm ht)

@[gcongr]
theorem EqTm.cong_lam_body {Γ A B t t' l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] t ≡ t' : B →
    E ∣ Γ ⊢[max l l'] .lam l l' A t ≡ .lam l l' A t' : .pi l l' A B :=
  fun htt' => EqTm.cong_lam (EqTp.refl_tp htt'.wf_binder) htt'

attribute [gcongr] EqTm.cong_app

@[gcongr]
theorem EqTm.cong_app_cod {Γ A B B' f a l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[max l l'] f : .pi l l' A B →
    E ∣ Γ ⊢[l] a : A →
    E ∣ Γ ⊢[l'] .app l l' B f a ≡ .app l l' B' f a : B.subst a.toSb :=
  fun hBB' hf ha =>
    EqTm.cong_app hBB' (EqTm.refl_tm hf) (EqTm.refl_tm ha)

@[gcongr]
theorem EqTm.cong_app_fn {Γ A B f f' a l l'} :
    E ∣ Γ ⊢[max l l'] f ≡ f' : .pi l l' A B →
    E ∣ Γ ⊢[l] a : A →
    E ∣ Γ ⊢[l'] .app l l' B f a ≡ .app l l' B f' a : B.subst a.toSb :=
  fun hff' ha =>
    EqTm.cong_app (EqTp.refl_tp hff'.wf_tp.inv_pi.2) hff' (EqTm.refl_tm ha)

@[gcongr]
theorem EqTm.cong_app_arg {Γ A B f a a' l l'} :
    E ∣ Γ ⊢[max l l'] f : .pi l l' A B →
    E ∣ Γ ⊢[l] a ≡ a' : A →
    E ∣ Γ ⊢[l'] .app l l' B f a ≡ .app l l' B f a' : B.subst a.toSb :=
  fun hf haa' =>
    EqTm.cong_app (EqTp.refl_tp hf.wf_tp.inv_pi.2) (EqTm.refl_tm hf) haa'

attribute [gcongr] EqTm.cong_pair

@[gcongr]
theorem EqTm.cong_pair_cod {Γ A B B' t u l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[l] t : A →
    E ∣ Γ ⊢[l'] u : B.subst t.toSb →
    E ∣ Γ ⊢[max l l'] .pair l l' B t u ≡ .pair l l' B' t u : .sigma l l' A B :=
  fun BB' t u => .cong_pair BB' (EqTm.refl_tm t) (EqTm.refl_tm u)

@[gcongr]
theorem EqTm.cong_pair_fst {Γ A B t t' u l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B →
    E ∣ Γ ⊢[l] t ≡ t' : A →
    E ∣ Γ ⊢[l'] u : B.subst t.toSb →
    E ∣ Γ ⊢[max l l'] .pair l l' B t u ≡ .pair l l' B t' u : .sigma l l' A B :=
  fun B tt' u => .cong_pair (EqTp.refl_tp B) tt' (EqTm.refl_tm u)

@[gcongr]
theorem EqTm.cong_pair_snd {Γ A B t u u' l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B →
    E ∣ Γ ⊢[l] t : A →
    E ∣ Γ ⊢[l'] u ≡ u' : B.subst t.toSb →
    E ∣ Γ ⊢[max l l'] .pair l l' B t u ≡ .pair l l' B t u' : .sigma l l' A B :=
  fun B t uu' => .cong_pair (EqTp.refl_tp B) (EqTm.refl_tm t) uu'

attribute [gcongr] EqTm.cong_fst

@[gcongr]
theorem EqTm.cong_fst_dom {Γ A A' B p l l'} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ Γ ⊢[max l l'] p : .sigma l l' A B →
    E ∣ Γ ⊢[l] .fst l l' A B p ≡ .fst l l' A' B p : A :=
  fun AA' p => .cong_fst AA' (EqTp.refl_tp p.wf_tp.inv_sigma.2) (EqTm.refl_tm p)

@[gcongr]
theorem EqTm.cong_fst_cod {Γ A B B' p l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[max l l'] p : .sigma l l' A B →
    E ∣ Γ ⊢[l] .fst l l' A B p ≡ .fst l l' A B' p : A :=
  fun BB' p => .cong_fst (EqTp.refl_tp BB'.wf_binder) BB' (EqTm.refl_tm p)

@[gcongr]
theorem EqTm.cong_fst_pair {Γ A B p p' l l'} :
    E ∣ Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
    E ∣ Γ ⊢[l] .fst l l' A B p ≡ .fst l l' A B p' : A :=
  fun pp' =>
    have ⟨_, B⟩ := pp'.wf_tp.inv_sigma
    .cong_fst (EqTp.refl_tp B.wf_binder) (EqTp.refl_tp B) pp'

attribute [gcongr] EqTm.cong_snd

@[gcongr]
theorem EqTm.cong_snd_dom {Γ A A' B p l l'} :
    E ∣ Γ ⊢[l] A ≡ A' →
    E ∣ Γ ⊢[max l l'] p : .sigma l l' A B →
    E ∣ Γ ⊢[l'] .snd l l' A B p ≡ .snd l l' A' B p : B.subst (Expr.fst l l' A B p).toSb :=
  fun AA' p => .cong_snd AA' (EqTp.refl_tp p.wf_tp.inv_sigma.2) (EqTm.refl_tm p)

@[gcongr]
theorem EqTm.cong_snd_cod {Γ A B B' p l l'} :
    E ∣ (A, l) :: Γ ⊢[l'] B ≡ B' →
    E ∣ Γ ⊢[max l l'] p : .sigma l l' A B →
    E ∣ Γ ⊢[l'] .snd l l' A B p ≡ .snd l l' A B' p : B.subst (Expr.fst l l' A B p).toSb :=
  fun BB' p => .cong_snd (EqTp.refl_tp BB'.wf_binder) BB' (EqTm.refl_tm p)

@[gcongr]
theorem EqTm.cong_snd_pair {Γ A B p p' l l'} :
    E ∣ Γ ⊢[max l l'] p ≡ p' : .sigma l l' A B →
    E ∣ Γ ⊢[l'] .snd l l' A B p ≡ .snd l l' A B p' : B.subst (Expr.fst l l' A B p).toSb :=
  fun pp' =>
    have ⟨_, B⟩ := pp'.wf_tp.inv_sigma
    .cong_snd (EqTp.refl_tp B.wf_binder) (EqTp.refl_tp B) pp'

attribute [gcongr] EqTm.cong_refl
attribute [gcongr] EqTm.cong_idRec

/-! ## Lemmas for substitution -/

attribute [gcongr] WfTp.subst_eq
attribute [gcongr] EqTp.subst_eq
attribute [gcongr] WfTm.subst_eq
attribute [gcongr] EqTm.subst_eq

attribute [gcongr] EqTp.subst
attribute [gcongr] EqTm.subst

end SynthLean
