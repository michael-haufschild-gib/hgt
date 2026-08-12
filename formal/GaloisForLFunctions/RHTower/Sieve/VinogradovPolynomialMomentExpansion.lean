import GaloisForLFunctions.RHTower.Sieve.VinogradovBoundedDifference

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovCenteredDifference
    {N b k : ℕ}
    (l : Fin k → Fin (vinogradovDifferenceBoxSize N b k)) (j : Fin k) : ℝ :=
  (l j).val - b * N ^ k

def finiteVinogradovPolynomialPhase
    {N k : ℕ} (α : Fin k → ℝ) (n : Fin N) : ℝ :=
  ∑ j : Fin k, α j * (n.val : ℝ) ^ (j.val + 1)

theorem vinogradovCenteredDifference_signature
    {N b k : ℕ} (hN : N ≠ 0)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) (j : Fin k) :
    vinogradovCenteredDifference
        (vinogradovBoundedDifferenceSignature hN uv) j =
      (∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) -
        ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1) := by
  have hC : (∑ i : Fin b, (uv.2 i).val ^ (j.val + 1)) ≤
      (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + b * N ^ k :=
    (vinogradovPowerSum_le hN uv.2 j).trans
      (Nat.le_add_left (b * N ^ k) _)
  unfold vinogradovCenteredDifference vinogradovBoundedDifferenceSignature
  rw [Nat.cast_sub hC]
  push_cast
  ring

theorem finiteVinogradovPolynomialPhase_tupleDifference
    {N b k : ℕ} (hN : N ≠ 0) (α : Fin k → ℝ)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) :
    (∑ i : Fin b, finiteVinogradovPolynomialPhase α (uv.1 i)) -
        ∑ i : Fin b, finiteVinogradovPolynomialPhase α (uv.2 i) =
      ∑ j : Fin k, α j *
        vinogradovCenteredDifference
          (vinogradovBoundedDifferenceSignature hN uv) j := by
  unfold finiteVinogradovPolynomialPhase
  have hleft :
      (∑ i : Fin b, ∑ j : Fin k,
        α j * ((uv.1 i).val : ℝ) ^ (j.val + 1)) =
      ∑ j : Fin k, ∑ i : Fin b,
        α j * ((uv.1 i).val : ℝ) ^ (j.val + 1) := Finset.sum_comm
  have hright :
      (∑ i : Fin b, ∑ j : Fin k,
        α j * ((uv.2 i).val : ℝ) ^ (j.val + 1)) =
      ∑ j : Fin k, ∑ i : Fin b,
        α j * ((uv.2 i).val : ℝ) ^ (j.val + 1) := Finset.sum_comm
  rw [hleft, hright]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [vinogradovCenteredDifference_signature]
  ring

/-- Exact `2b`-moment expansion of a polynomial exponential sum, indexed by
the bounded power-difference signature consumed by the weighted VMVT
grouping theorem. -/
theorem finiteVinogradovPolynomialPhase_moment_expansion
    {N b k : ℕ} (hN : N ≠ 0) (α : Fin k → ℝ) :
    Complex.normSq (finitePhaseSum (finiteVinogradovPolynomialPhase α : Fin N → ℝ)) ^ b =
      ∑ uv : (Fin b → Fin N) × (Fin b → Fin N),
        Real.cos (2 * Real.pi *
          ∑ j : Fin k, α j *
            vinogradovCenteredDifference
              (vinogradovBoundedDifferenceSignature hN uv) j) := by
  rw [finitePhaseMoment_expansion_real]
  apply Finset.sum_congr rfl
  intro uv _
  rw [finiteVinogradovPolynomialPhase_tupleDifference hN α uv]

end

end RHTower.Sieve
