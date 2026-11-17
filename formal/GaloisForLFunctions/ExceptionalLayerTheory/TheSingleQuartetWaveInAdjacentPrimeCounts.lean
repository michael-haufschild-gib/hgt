import GaloisForLFunctions.ExceptionalLayerTheory.AdjacentVaughanOctavesRecoverTheOrdinaryPrimeCount
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity

/-!
# The single-quartet waveform in consecutive arithmetic cofactor counts

At cofinally many adjacent first-octave cutoffs their difference, sampled
at multiples of an ordinary prime, recovers the complete Chebyshev error.
The quartet criterion on these counts retains the same multiplicity,
frequency and error bound as the criterion on the original prime count.
-/

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

open ExclusionOfTheCriticalState

/-- Difference of the two ordinary cofactor counts, including the fractional
part of the real cutoff in the integer-density subtraction. -/
def adjacentCountAt (t : ℕ) (x : ℝ) : ℝ :=
  cofactorCountError (t + 1) (2 * (t + 1)) ((2 * t + 1) * ⌊x⌋₊) -
    cofactorCountError t (2 * t) ((2 * t + 1) * ⌊x⌋₊) + (x - ⌊x⌋₊)

/-- A cofinal family of adjacent ordinary cofactor counts characterizes the
single off-line quartet, with a common pair of cutoffs for all strip zeros. -/
theorem cofinal_adjacentCounts_characterize_singleQuartet (B : ℕ) :
    ∃ t > B, (2 * t + 1).Prime ∧ ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 →
      riemannZeta ρ = 0 → (HasSingleOffLineQuartet ρ ↔
        ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
          |adjacentCountAt t x - 2 * (quartetCopyMult ρ : ℝ) * ((x : ℂ) ^ ρ / ρ).re| ≤
            K * Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨t, ht, hp, hcount⟩ := cofinal_adjacent_octaves_recover_prime_error B
  have hreal (x : ℝ) : adjacentCountAt t x = x - Chebyshev.psi x := by
    rw [adjacentCountAt, hcount, ← Chebyshev.psi_eq_psi_coe_floor x]
    ring
  have hsign (a b c : ℝ) : |a - b - c| = |b - a + c| := by
    rw [show a - b - c = -(b - a + c) by ring, abs_neg]
  refine ⟨t, ht, hp, fun ρ hhalf hhi hz => ?_⟩
  simp_rw [hreal, hsign]
  exact hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hhalf
    ⟨hz, by linarith only [hhalf], hhi⟩

#print axioms cofinal_adjacentCounts_characterize_singleQuartet

end GaloisForLFunctions.ExceptionalLayerTheory
