import GaloisForLFunctions.RHTower.Sieve.CoeffMajorantMono

/-!
# Scaling the majorant's constants

The price of narrow smoothing enters the majorant through its two constants, as `C·(L+2)²` and
`C'·(L+2)`.  Both are at most a constant times `exp(2v)`, and the majorant is monotone in its
constants, so the price can be pulled out of the majorant entirely:

    coeffMajorant (C·E) (C'·E) M₀ a w  ≤  E · coeffMajorant C C' M₀ a w      for `E ≥ 1`.

The inequality is not an identity — the majorant's constant term `M₀(4+2C)` and the `4` inside its
middle coefficient do not scale — but both discrepancies have the right sign.
-/

namespace RHTower.Sieve

open Real

/-- **The majorant is increasing in its constants.** -/
theorem coeffMajorant_mono_const {C₁ C₂ C₁' C₂' M₀ a t : ℝ} (h : C₁ ≤ C₂) (h' : C₁' ≤ C₂')
    (hM₀ : 0 ≤ M₀) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    coeffMajorant C₁ C₁' M₀ a t ≤ coeffMajorant C₂ C₂' M₀ a t := by
  have hexp : (0 : ℝ) ≤ Real.exp (22 / 4) := (Real.exp_pos _).le
  have hP : (0 : ℝ) ≤ (1 + a * t ^ 9) * (5 / 2 + 2 * t) := by positivity
  rw [coeffMajorant, coeffMajorant]
  gcongr

/-- **The scale factor comes out of the majorant.** -/
theorem coeffMajorant_scale {C C' M₀ a w E : ℝ} (hE : 1 ≤ E)
    (hM₀ : 0 ≤ M₀) (ha : 0 ≤ a) (hw : 0 ≤ w) :
    coeffMajorant (C * E) (C' * E) M₀ a w ≤ E * coeffMajorant C C' M₀ a w := by
  have hexp : (0 : ℝ) < Real.exp (22 / 4) := Real.exp_pos _
  have hP : (0 : ℝ) ≤ (1 + a * w ^ 9) * (5 / 2 + 2 * w) := by positivity
  have hE1 : (0 : ℝ) ≤ E - 1 := by linarith
  rw [coeffMajorant, coeffMajorant]
  nlinarith [mul_nonneg hE1 hP, mul_nonneg hE1 hM₀, hexp.le,
    mul_nonneg (mul_nonneg hE1 hP) hexp.le]

end RHTower.Sieve
