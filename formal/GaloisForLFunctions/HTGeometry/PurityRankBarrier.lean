import GaloisForLFunctions.HTGeometry.BoundedSumConcentration

/-!
# Purity is bounded below by the reciprocal rank

A probability vector supported on `q` entries has squared mass at least `1/q`, by Cauchy--Schwarz.
For a positive trace-one matrix the eigenvalues form such a vector, so its purity `Tr(M²)` is at
least the reciprocal of its rank, with equality exactly at the uniform distribution.

Subtracting the normalized identity of the symmetric space then leaves an energy of
`Tr(M²) - 1/h`, so a moment of rank below `h` cannot lie close to that identity: the deficit is at
least `1/rank - 1/h`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

section Purity

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **The purity bound.**  A probability vector on `q` entries has squared mass at least `1/q`. -/
theorem inv_card_le_sum_sq (f : ι → ℝ) (hsum : ∑ i, f i = 1) :
    1 / (Fintype.card ι : ℝ) ≤ ∑ i, f i ^ 2 := by
  have hcs := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) f
  have hone : ∑ i : ι, (1 : ℝ) * f i = 1 := by
    simpa using hsum
  rw [hone] at hcs
  have hcard : ∑ _i : ι, (1 : ℝ) ^ 2 = (Fintype.card ι : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    norm_num
  rw [hcard] at hcs
  have hcardpos : (0 : ℝ) < Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    exact_mod_cast this
  rw [div_le_iff₀ hcardpos]
  nlinarith [hcs]

/-- The uniform distribution attains the purity bound. -/
theorem sum_sq_const_eq_inv_card :
    ∑ _i : ι, ((Fintype.card ι : ℝ)⁻¹) ^ 2 = 1 / (Fintype.card ι : ℝ) := by
  have hcardpos : (0 : ℝ) < Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    exact_mod_cast this
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **The deficit.**  A purity above `1/q` and a reference of purity `1/h` are separated by at
least `1/q - 1/h` in squared energy. -/
theorem deficit_ge {P h q : ℝ} (hP : 1 / q ≤ P) :
    1 / q - 1 / h ≤ P - 1 / h := by
  linarith

end Purity

end GaloisForLFunctions.HTGeometry
