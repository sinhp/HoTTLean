-- This module serves as the root of the `GroupoidModelInLean4` library.
-- Import modules here that should be built as part of the library.
import GroupoidModel.Tarski.NaturalModel
import GroupoidModel.Russell_PER_MS.UHom
import GroupoidModel.Russell_PER_MS.Interpretation
import GroupoidModel.Groupoids.TarskiNaturalModel
import GroupoidModel.Groupoids.NaturalModelBase

/- There should be at least three separate files here for three separate developments:
  1. the basic development of the category Grpd of groupoids
  2. the intermediate natural model of HoTT which is constructed out of Gpds
  3. the metaprogram level HoTT 0 for interacting with the model
  -/

/-
# 1. The category Grpd of small groupoids
We will need at least the following:
  - fibrations of groupoids
  - set-valued functors on groupoids (presheaves)
  - the Grothendieck construction relating the previous two
  - Σ- and Π-types for discrete fibrations
  - path groupoids
  - the universe of (small) discrete groupoids
  - polynomial functors of groupoids
  - maybe some W-types
  -/

/-
# 2. The natural model of HoTT to be interpreted in Grpd
We will need at least the following:
  - category Ctx of all small groupoids
  - the presheaf category 𝓔 = Psh(Ctx) in which the model lives
  - the presheaf Type : Ctxᵒᵖ → Set of types in context
  - the presheaf Term : Ctxᵒᵖ → Set of terms in context
  - the typing natural transformation t : Term ⟶ Type
  - the proof that t is (re)presentable
  - the polynomial endofunctor Pₜ : 𝓔 ⥤ 𝓔
  - the type-formers Σ, Π, Id as operations on polynomials
  - the universe Set of (small) discrete groupoids,
      along with its discrete (op-)fibration Set* ⟶ Set
  It might also be useful to have:
  - the proof that presentable natural transformations are tiny maps
  - the proof that Pₜ is therefore cocontinuous, since t is tiny
  -/

  /-
# 3. HoTT in Lean
An interface for the groupoid model in Lean.
It would be nice if the user could:
- interact with types, terms, and type families rather than
    groupoids, homomorphisms, and fibrations
- have the usual Lean rules for the Σ- and Π-types
- have path-induction for the general Id-types
- define the sets as the 0-types
- use Lean's normal infrastructure like rewriting, tactics, mathlib, etc.
  for equality on sets.
-/

/-
# Targets
Here are some things that should be doable in the setting of "HoTT 0",
i.e. HoTT with a univalent universe of 0-types:
- HoTT Book real numbers and cumulative hierarchy,
- univalent set theory,
- Lawvere's objective number theory,
- structure identity principle for general algebraic structures,
- propositional truncation ||A|| ,
- set-truncation ||X||₀ = π₀(X) ,
- groupoid quotients,
- Eilenberg-MacLane spaces K(G,1), and some basic cohomology,
- classifying spaces BG, and the theory of covering spaces,
- calculation of π₁(S¹) = Z using univalence and circle induction,
- Joyal’s combinatorial species,
- Egbert’s univalent combinatorics,
- Rezk completion of a small category,
- univalent category theory: equivalences, etc.
-/
