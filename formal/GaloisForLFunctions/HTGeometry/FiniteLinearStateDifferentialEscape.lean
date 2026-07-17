import GaloisForLFunctions.HTGeometry.FiniteDifferentialSystemAlgebraicity

/-!
# Finite linear differential-state boundary

A finite-dimensional subspace which is preserved by differentiation contains the full differential
jet of each of its elements.  Finite-dimensional linear dependence therefore gives an explicit
nonzero scalar linear differential equation.  In particular, no element hypertranscendental over
the coefficient field can belong to such a state.

This is the exact linear phase boundary required by research programme 5 in
`docs/reports/rh-status-1707.md`.  It is classical differential-module theory, formalized here as
a reusable relative-coefficient interface.
-/

open scoped Differential
open Module

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A submodule of the ambient field which is preserved by its derivation. -/
def DerivationInvariantSubmodule
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (V : Submodule F E) : Prop :=
  ∀ ⦃x : E⦄, x ∈ V → x′ ∈ V

/-- Every differential jet of an element remains in a derivation-invariant submodule. -/
theorem differentialJet_mem_of_mem_derivationInvariantSubmodule
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {V : Submodule F E} (hV : DerivationInvariantSubmodule V)
    {x : E} (hx : x ∈ V) (n : ℕ) :
    differentialJet n x ∈ V := by
  induction n with
  | zero => simpa [differentialJet_zero] using hx
  | succ n ih =>
      rw [differentialJet_succ]
      exact hV ih

/-- In a finite-dimensional derivation-invariant submodule, the first `finrank + 1` jets of an
element satisfy a nonzero linear relation over the coefficient field. -/
theorem exists_nonzero_finite_jet_linearCombination_eq_zero_of_mem_derivationInvariantSubmodule
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (V : Submodule F E) [FiniteDimensional F V]
    {x : E} (hx : x ∈ V) (hV : DerivationInvariantSubmodule V) :
    ∃ c : Fin (finrank F V + 1) →₀ F, c ≠ 0 ∧
      Finsupp.linearCombination E
        (fun r : Fin (finrank F V + 1) => differentialJet r.1 x)
        (Finsupp.mapRange (algebraMap F E) (map_zero (algebraMap F E)) c) = 0 := by
  classical
  let jetsV : Fin (finrank F V + 1) → V := fun r =>
    ⟨differentialJet r.1 x,
      differentialJet_mem_of_mem_derivationInvariantSubmodule hV hx r.1⟩
  have hnot : ¬ LinearIndependent F jetsV := by
    intro hli
    have hbound := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hbound
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
  let c : Fin (finrank F V + 1) →₀ F := Finsupp.equivFunOnFinite.symm g
  have hc : c ≠ 0 := by
    intro hzero
    apply hi
    have hz := congrArg (fun f : Fin (finrank F V + 1) →₀ F => f i) hzero
    simpa [c] using hz
  have hsumE : ∑ r, algebraMap F E (g r) * differentialJet r.1 x = 0 := by
    have hcoe := congrArg V.subtype hg
    rw [map_sum, map_zero] at hcoe
    simp only [map_smul, jetsV] at hcoe
    change (∑ r, g r • differentialJet r.1 x) = 0 at hcoe
    simpa only [Algebra.smul_def] using hcoe
  refine ⟨c, hc, ?_⟩
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simpa only [c, Finsupp.equivFunOnFinite_symm_apply_apply,
    Finsupp.mapRange_apply, smul_eq_mul] using hsumE

/-- Membership in a finite-dimensional derivation-invariant linear state forces differential
algebraicity over the coefficient field.  The preceding theorem records the stronger explicit
linear differential relation. -/
theorem differentialAlgebraicOver_of_mem_derivationInvariantSubmodule
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (V : Submodule F E) [FiniteDimensional F V]
    {x : E} (hx : x ∈ V) (hV : DerivationInvariantSubmodule V) :
    DifferentialAlgebraicOver F x := by
  obtain ⟨c, hc, hrel⟩ :=
    exists_nonzero_finite_jet_linearCombination_eq_zero_of_mem_derivationInvariantSubmodule
      V hx hV
  exact differentialAlgebraicOver_of_finite_jet_linearCombination_eq_zero x c hc hrel

/-- **Linear HT escape law.** A hypertranscendental element cannot lie in any finite-dimensional
linear state which is preserved by differentiation. -/
theorem not_mem_derivationInvariantSubmodule_of_hypertranscendentalOver
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (V : Submodule F E) [FiniteDimensional F V]
    {x : E} (hx : HypertranscendentalOver F x)
    (hV : DerivationInvariantSubmodule V) :
    x ∉ V := by
  intro hxV
  exact hx (differentialAlgebraicOver_of_mem_derivationInvariantSubmodule V hxV hV)

end

end GaloisForLFunctions.HTGeometry
