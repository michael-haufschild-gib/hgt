/-
# The plain determinant of a finite spectrum is the regularized one times the low traces

For a finite spectrum the order-`p` regularized determinant differs from the honest determinant
`∏(1 − zλ)` by the exponential of the first `p − 1` power traces.  This is the identity the
sufficiency half of the completion law uses: prescribing the low traces of a finite spectrum
prescribes exactly the exponential factor its determinant carries over the regularized one.

Main results:
* `neg_diagonal_pow_trace` — the power traces of the negated diagonal.
* `prod_one_sub_eq_schattenDet_mul_exp` — **`∏(1 − zλ) = det_p(1 − zΛ)·exp(−∑_{k<p} zᵏ tr_k/k)`**.
-/
import GaloisForLFunctions.HTGeometry.SchattenSpectralDeterminant

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

theorem neg_diagonal_pow_trace (mu : Fin N → ℂ) (m : ℕ) :
    (((-(Matrix.diagonal mu)) : Matrix (Fin N) (Fin N) ℂ) ^ m).trace
      = (-1 : ℂ) ^ m * schattenTracePower mu m := by
  have hneg : ((-(Matrix.diagonal mu)) : Matrix (Fin N) (Fin N) ℂ)
      = ((-1 : ℂ)) • Matrix.diagonal mu := by
    rw [neg_smul, one_smul]
  rw [hneg, smul_pow, Matrix.trace_smul, smul_eq_mul, schattenTracePower_diagonal]

theorem det_one_add_smul_neg_diagonal (mu : Fin N → ℂ) (z : ℂ) :
    (1 + z • ((-(Matrix.diagonal mu)) : Matrix (Fin N) (Fin N) ℂ)).det
      = ∏ i, (1 - z * mu i) := by
  have hmat : (1 + z • ((-(Matrix.diagonal mu)) : Matrix (Fin N) (Fin N) ℂ))
      = Matrix.diagonal fun i => 1 - z * mu i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
      ring
    · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
  rw [hmat, Matrix.det_diagonal]

/-- **The plain determinant of a finite spectrum.**  It is the order-`p` regularized determinant
times the exponential of the first `p − 1` power traces. -/
theorem prod_one_sub_eq_schattenDet_mul_exp {p : ℕ} (hp : 0 < p) (mu : Fin N → ℂ) {z : ℂ}
    (hz : ‖z‖ * Real.sqrt (matHSNormSq (Matrix.diagonal mu)) < 1) :
    (∏ i, (1 - z * mu i))
      = schattenDet p mu z * Complex.exp (-∑ j ∈ Finset.range (p - 1),
          z ^ (j + 1) * schattenTracePower mu (j + 1) / ((j + 1 : ℕ) : ℂ)) := by
  rw [schattenDet_eq_finiteDetOrder hp mu hz, finiteDetOrder,
    det_one_add_smul_neg_diagonal]
  rw [mul_assoc, ← Complex.exp_add]
  have hzero : (∑ j ∈ Finset.range (p - 1),
        (-z) ^ (j + 1) * (((-(Matrix.diagonal mu)) : Matrix (Fin N) (Fin N) ℂ) ^ (j + 1)).trace
          / ((j + 1 : ℕ) : ℂ))
      + -∑ j ∈ Finset.range (p - 1),
        z ^ (j + 1) * schattenTracePower mu (j + 1) / ((j + 1 : ℕ) : ℂ) = 0 := by
    rw [← sub_eq_add_neg, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_diagonal_pow_trace, neg_pow]
    have hsq : ((-1 : ℂ) ^ (j + 1)) * ((-1 : ℂ) ^ (j + 1)) = 1 := by
      rw [← mul_pow]
      norm_num
    have hlhs : ((-1 : ℂ) ^ (j + 1) * z ^ (j + 1))
        * ((-1 : ℂ) ^ (j + 1) * schattenTracePower mu (j + 1))
        = z ^ (j + 1) * schattenTracePower mu (j + 1) := by
      calc ((-1 : ℂ) ^ (j + 1) * z ^ (j + 1))
            * ((-1 : ℂ) ^ (j + 1) * schattenTracePower mu (j + 1))
          = ((-1 : ℂ) ^ (j + 1) * (-1 : ℂ) ^ (j + 1))
            * (z ^ (j + 1) * schattenTracePower mu (j + 1)) := by ring
        _ = z ^ (j + 1) * schattenTracePower mu (j + 1) := by rw [hsq, one_mul]
    rw [hlhs]
  rw [hzero, Complex.exp_zero, mul_one]

end

end GaloisForLFunctions.HTGeometry
