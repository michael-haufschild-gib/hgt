import GaloisForLFunctions.RHTower.XiLogDerivReStripBound
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedOrientationBoundary

/-!
# RH as the sign of the completed logarithmic derivative

The Hedenmalm centre-mixed tangent evaluates to
`ξ'(s) ξ(conj s) + ξ(s) ξ'(conj s)`, which by `ξ(conj s) = conj ξ(s)` is
`2 ‖ξ(s)‖² Re (ξ'/ξ)(s)` — an identity valid even at the zeros, where both sides vanish.
Combining this with the corpus's centre-mixed endpoint and with the line-conjugate pair law gives a
self-contained criterion:

```text
RiemannHypothesis  ↔  ∀ s, 1/2 < Re s → 0 ≤ Re (ξ'/ξ)(s) .
```

The forward direction is the pair law with every zero on the line; the reverse is the centre-mixed
endpoint.  Both directions are unconditional.
-/

open Complex

namespace RHTower

noncomputable section

theorem logDeriv_xi_eq_zero_of_xi_eq_zero {s : ℂ} (h : xi s = 0) : logDeriv xi s = 0 := by
  rw [logDeriv_apply, h, div_zero]

/-- The Hedenmalm tangent pair is `2 ‖ξ(s)‖² Re (ξ'/ξ)(s)`. -/
theorem re_xi_deriv_conj_pair (s : ℂ) :
    (deriv xi s * xi ((starRingEnd ℂ) s) + xi s * deriv xi ((starRingEnd ℂ) s)).re =
      2 * Complex.normSq (xi s) * (logDeriv xi s).re := by
  rw [xi_conj, xi_deriv_conj]
  by_cases h : xi s = 0
  · rw [h, logDeriv_xi_eq_zero_of_xi_eq_zero h]
    simp
  · have hd : deriv xi s = logDeriv xi s * xi s := by
      rw [logDeriv_apply, div_mul_cancel₀ _ h]
    rw [hd]
    have e1 : logDeriv xi s * xi s * (starRingEnd ℂ) (xi s) =
        logDeriv xi s * (Complex.normSq (xi s) : ℂ) := by
      rw [mul_assoc, Complex.mul_conj]
    have e2 : xi s * (starRingEnd ℂ) (logDeriv xi s * xi s) =
        (starRingEnd ℂ) (logDeriv xi s) * (Complex.normSq (xi s) : ℂ) := by
      rw [map_mul, ← Complex.mul_conj]
      ring
    rw [e1, e2, ← add_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
    ring

theorem riemannHypothesis_of_re_logDeriv_xi_nonneg
    (h : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → 0 ≤ (logDeriv xi s).re) :
    RiemannHypothesis := by
  rw [← thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis]
  intro a ha ha0 hahalf b
  rw [fourier_thetaCuspHorizontalAutocorrelationTangent_scaled ha b]
  have harg : (starRingEnd ℂ) ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) =
      (1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I := by
    have hhalf : (starRingEnd ℂ) ((1 : ℂ) / 2) = (1 : ℂ) / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    rw [map_add, map_add, map_mul, hhalf]
    simp
    ring
  rw [← harg, re_xi_deriv_conj_pair]
  have hre : ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I).re = 1 / 2 + a := by simp
  have hlog := h ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) (by rw [hre]; linarith)
    (by rw [hre]; linarith)
  have hns : (0 : ℝ) ≤ Complex.normSq (xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I)) :=
    Complex.normSq_nonneg _
  positivity

/-- **RH is exactly the sign of the completed logarithmic derivative on the right half strip.** -/
theorem riemannHypothesis_iff_re_logDeriv_xi_nonneg :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (logDeriv xi s).re := by
  constructor
  · intro hRH s hs
    by_cases hxi : xi s = 0
    · rw [logDeriv_xi_eq_zero_of_xi_eq_zero hxi]
      simp
    · exact re_logDeriv_xi_nonneg_of_riemannHypothesis hRH hs hxi
  · intro h
    exact riemannHypothesis_of_re_logDeriv_xi_nonneg fun s hs _ => h s hs

end

end RHTower
