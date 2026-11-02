import HoTTLean.Frontend.Commands
import HoTTLean.Model.Unstructured.Interpretation
import HoTTLean.Groupoids.UHom
import HoTTLean.Groupoids.Pi
import HoTTLean.Groupoids.Sigma
import HoTTLean.Groupoids.Id

noncomputable section

/-! ## Theory -/

declare_theory unitt

namespace UniTT

unitt axiom funext {α : Type} {β : α → Type} (f g : (a : α) → β a) :
  (∀ a, Identity (f a) (g a)) → Identity f g

unitt axiom Unit : Type
unitt axiom u : Unit
unitt axiom uniq_u (u' : Unit) : Identity u' u

unitt #print u -- Prints `axiom u : Unit`
#print u -- Prints `def u : CheckedAx (Axioms.empty.snoc Unit) := …`

unitt def uniq_fn {A : Type} (f g : A → Unit) : Identity f g := by
  apply funext; intro; exact (uniq_u _).trans₀ (uniq_u _).symm₀

/-! ## Interpretation -/

open SynthLean
open CategoryTheory MonoidalCategory Model.UnstructuredUniverse GroupoidModel ChosenTerminal

theorem slen : univMax ≤ uHomSeq.length := by grind [uHomSeq, univMax]

def Groupoid.asTy (G : Type 0) [Groupoid.{0,0} G] : (𝟭_ Ctx) ⟶ uHomSeq[0].Ty :=
  GroupoidModel.toCoreAsSmallEquiv.symm ((Functor.const _).obj (Grpd.of G))

def sUnit : (𝟭_ Ctx) ⟶ uHomSeq[0].Ty :=
  Groupoid.asTy (Discrete _root_.Unit)

def sUnit' : (𝟭_ Ctx) ⟶ uHomSeq[1].Tm :=
  uHomSeq.code (Nat.zero_lt_succ _) sUnit

@[simp]
theorem sUnit'_tp : sUnit' ≫ uHomSeq[1].tp = (uHomSeq.homSucc 0).wkU _ := by
  exact uHomSeq.code_tp _ _

def I : Interpretation Lean.Name uHomSeq where
  ax := fun
    | ``Unit, 1, _ => some sUnit'
    | _, _, _ => none

theorem I_wf : I.Wf slen Unit.snocAxioms where
  ax := by
    intro _ _ Ec
    unfold CheckedAx.snocAxioms Axioms.snoc at Ec
    split_ifs at Ec <;> cases Ec
    use sUnit'
    subst_vars
    unfold Unit
    simp [I, Interpretation.ofType, UHomSeq.nilCObj]
    -- The axiom lookup proof contains reducible dependent projections.
    set_option backward.isDefEq.respectTransparency false in
      simp [Part.mem_assert_iff]
    exact sUnit'_tp

instance : Fact (I.Wf slen Unit.snocAxioms) := ⟨I_wf⟩

example : I.interpTm Unit.wf_val = sUnit' := by
  unfold Interpretation.interpTm Interpretation.ofTerm CheckedAx.val I Unit
  simp only [Part.pure_eq_some, Part.get_some]
  conv => rhs; rw [← Category.id_comp sUnit']
  congr 1
