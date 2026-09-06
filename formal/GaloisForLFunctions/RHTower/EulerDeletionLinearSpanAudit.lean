import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence
import GaloisForLFunctions.RHTower.BaezDuarteGramDiscrete

/-!
# Classical linear span of literal deletion prefixes

This module audits a proposed reformulation. The actual finite deletion prefixes,
after dividing by their nonzero labels, are exactly the fractional-part sequences
in the classical Nyman–Beurling/Báez-Duarte formulation. Their spans are equal.
It does not assert density, prove RH, or identify nonlinear chronological words
with their linear endpoints.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.DeletionLinearSpanAudit

/-- The original finite integer-coefficient prefix, embedded into complex sequences. -/
def prefixVector (q : ℕ) : ℕ → ℂ := fun N => deletionCoeffPartialSum (q+1) N

/-- The published fractional-part sequence, with positive label `q+1`. -/
def fractionVector (q : ℕ) : ℕ → ℂ := fun N =>
  (Int.fract ((N : ℝ) / (q+1 : ℕ)) : ℝ)

theorem prefixVector_eq_mod (q N : ℕ) :
    prefixVector q N = ((N % (q+1) : ℕ) : ℂ) := by
  exact congrArg (fun z : ℤ => (z : ℂ)) (deletionCoeffPartialSum_eq_mod (q+1) N)

/-- The identification uses actual source coefficients, at every cutoff. -/
theorem prefixVector_eq_mul_fraction (q N : ℕ) :
    prefixVector q N = ((q+1 : ℕ) : ℂ) * fractionVector q N := by
  rw [prefixVector_eq_mod, fractionVector, Int.fract_div_natCast_eq_div_natCast_mod]
  push_cast
  field_simp

theorem prefixVector_eq_smul_fraction (q : ℕ) :
    prefixVector q = ((q+1 : ℕ) : ℂ) • fractionVector q := by
  funext N
  exact prefixVector_eq_mul_fraction q N

theorem fractionVector_eq_smul_prefix (q : ℕ) :
    fractionVector q = (((q+1 : ℕ) : ℂ))⁻¹ • prefixVector q := by
  rw [prefixVector_eq_smul_fraction, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero q), one_smul]

/-- Every finite linear operation on the original prefixes has exactly the same
value after the explicit coefficient change in the classical family. -/
theorem finiteCombination_eq {ι : Type*} (s : Finset ι) (q : ι → ℕ) (c : ι → ℂ) :
    (∑ i ∈ s, c i • prefixVector (q i)) =
      ∑ i ∈ s, (c i * ((q i+1 : ℕ) : ℂ)) • fractionVector (q i) := by
  simp_rw [prefixVector_eq_smul_fraction, smul_smul]

/-- Exact equality, not an inclusion or an approximation claim. -/
theorem span_prefixVector_eq_fractionVector :
    Submodule.span ℂ (Set.range prefixVector) =
      Submodule.span ℂ (Set.range fractionVector) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    rw [prefixVector_eq_smul_fraction]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    rw [fractionVector_eq_smul_prefix]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

/-- Any fixed topology on the sequence carrier has equal closures of these
equal spans. This does not choose or prove the RH approximation topology. -/
theorem closure_span_eq [TopologicalSpace (ℕ → ℂ)] :
    closure (Submodule.span ℂ (Set.range prefixVector) : Set (ℕ → ℂ)) =
      closure (Submodule.span ℂ (Set.range fractionVector) : Set (ℕ → ℂ)) := by
  rw [span_prefixVector_eq_fractionVector]

/-- The continuous tail-coordinate generator agrees on every open integer cell.
The finite prefix is retained before the comparison is made. -/
theorem tail_cell_eq_bdGenFun (q N : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioo (N : ℝ) ((N : ℝ)+1)) :
    prefixVector q N / (u : ℂ) =
      ((q+1 : ℕ) : ℂ) * bdGenFun (1 / ((q+1 : ℕ) : ℝ)) u := by
  rw [prefixVector_eq_mod, bdGenFun_eq_ofReal,
    bdGenReal_inv_nat_eq_of_mem_cell (by omega : 1 ≤ q+1) hu]
  push_cast
  field_simp

/-- Closed source/classical dictionary. No density or zero-location premise occurs. -/
theorem literal_prefix_classical_linear_dictionary :
    (∀ q N, prefixVector q N = ((q+1 : ℕ) : ℂ) * fractionVector q N) ∧
      Submodule.span ℂ (Set.range prefixVector) =
        Submodule.span ℂ (Set.range fractionVector) :=
  ⟨prefixVector_eq_mul_fraction, span_prefixVector_eq_fractionVector⟩

end RHTower.DeletionLinearSpanAudit
