import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanCalibration
import GaloisForLFunctions.RHTower.WeilKloostermanBound

/-!
# Hodge index on the Frobenius span is the Riemann hypothesis of the datum

The defect of every span class of a curve datum is nonnegative iff every normalized eigenvalue
lies on the unit circle (`hodgeIndexOnSpan_iff_unitary`). If `|β_i| = 1` the defect is a sum of
squares; conversely the `2 × 2` minors at lags `0, j` bound the power sums by the genus,
`|Σ_i β_i^j| ≤ 2g` for all `j`, which forces `|β_i| ≤ 1` (power-sum elimination), and the
functional equation `β ↦ β⁻¹` forces equality.

So the span carries no information on the sign beyond RH itself: Hodge index on the span of
Frobenius graphs *is* RH for the curve, for every datum, geometric or not. In Weil's proof the
index theorem is supplied by the ambient surface — by Riemann–Roch on all divisors of `C × C` —
and not by the span.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- **Hodge index on the Frobenius span is RH for the datum.** The defect of every span class is
nonnegative iff every normalized eigenvalue lies on the unit circle. -/
theorem hodgeIndexOnSpan_iff_unitary :
    (∀ S d, 0 ≤ D.spanDefect S d) ↔ ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · intro h
    have hT : ∀ S e, 0 ≤ D.toeplitz S e := by
      intro S e
      have := h S (fun k => e k / D.sqrtq ^ k)
      rw [spanDefect_eq_toeplitz] at this
      convert this using 3
      exact (div_mul_cancel₀ _ (pow_ne_zero _ D.sqrtq_pos.ne')).symm
    have hle : ∀ i, ‖D.β i‖ ≤ 1 := by
      intro i
      refine RHTower.WeilKloosterman.norm_le_of_power_sums_bound Finset.univ D.β (C := Fintype.card ι)
        (m0 := 0) zero_le_one (fun j _ => ?_) i (Finset.mem_univ i)
      rw [one_pow, mul_one]
      exact D.norm_powerSum_le hT j
    intro i
    have hfe := congrArg norm (D.β_fePerm i)
    rw [norm_mul, norm_one] at hfe
    have hi := hle i
    have hf := hle (D.fePerm i)
    nlinarith [norm_nonneg (D.β i), norm_nonneg (D.β (D.fePerm i))]
  · intro hU S d
    rw [spanDefect_eq_toeplitz, toeplitz_eq_sum_normSq D hU]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
