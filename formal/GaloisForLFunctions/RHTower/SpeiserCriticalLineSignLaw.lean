import GaloisForLFunctions.RHTower.CompletedSplitRightHalfPlane
import GaloisForLFunctions.RHTower.LevinsonDetectorLine

/-!
# Speiser's sign law on the critical line

The functional equation gives the exact critical-line identity
`2 Re(ζ'/ζ)(1/2+it) = log π − Re ψ(1/4 + it/2)` (`re_logDeriv_riemannZeta_criticalLine`), and the
digamma real part exceeds `log π` from height `20` on (`log_pi_lt_re_digamma_quarter`).  Hence
`Re(ζ'/ζ) < 0` on the critical line above that height wherever `ζ ≠ 0`.  Consequences:

* `deriv_riemannZeta_criticalLine_ne_zero_of_ne_zero` — `ζ'` does not vanish at any non-zero of
  `ζ` on the line above height `20`;
* `riemannZeta_criticalLine_eq_zero_of_deriv_eq_zero` — a critical point of `ζ` on the critical
  line above height `20` is a (multiple) zero of `ζ`.

This is the reflection-odd orientation law that drives Speiser's theorem (`RH ⟺ ζ' has no zeros in
`0 < Re s < 1/2`): on the line the logarithmic derivative points into the left half-plane, so the
argument of `ζ'/ζ` cannot wind along the critical line.  The law is unconditional and contains no
zero of `ζ`; Speiser's equivalence itself is a receiver.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Speiser's sign law.**  Above height `20`, `Re(ζ'/ζ) < 0` on the critical line wherever
`ζ ≠ 0`. -/
theorem re_logDeriv_riemannZeta_criticalLine_neg {τ : ℝ} (hτ : 20 ≤ τ)
    (hz : riemannZeta (1 / 2 + (τ : ℂ) * I) ≠ 0) :
    (logDeriv riemannZeta (1 / 2 + (τ : ℂ) * I)).re < 0 := by
  have hid := re_logDeriv_riemannZeta_criticalLine (t := τ) hz
  have hdig := log_pi_lt_re_digamma_quarter hτ
  have hcast : (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I) = 1 / 4 + (τ : ℂ) * I / 2 := by
    push_cast; ring
  rw [hcast] at hdig
  linarith

/-- On the critical line above height `20`, `ζ'` does not vanish where `ζ` does not. -/
theorem deriv_riemannZeta_criticalLine_ne_zero_of_ne_zero {τ : ℝ} (hτ : 20 ≤ τ)
    (hz : riemannZeta (1 / 2 + (τ : ℂ) * I) ≠ 0) :
    deriv riemannZeta (1 / 2 + (τ : ℂ) * I) ≠ 0 := by
  intro hd
  have h := re_logDeriv_riemannZeta_criticalLine_neg hτ hz
  rw [logDeriv_apply, hd, zero_div] at h
  simp at h

/-- **Critical points on the critical line are multiple zeros.**  Above height `20`, a zero of
`ζ'` on the line is a zero of `ζ`. -/
theorem riemannZeta_criticalLine_eq_zero_of_deriv_eq_zero {τ : ℝ} (hτ : 20 ≤ τ)
    (hd : deriv riemannZeta (1 / 2 + (τ : ℂ) * I) = 0) :
    riemannZeta (1 / 2 + (τ : ℂ) * I) = 0 := by
  by_contra hz
  exact deriv_riemannZeta_criticalLine_ne_zero_of_ne_zero hτ hz hd

end

end RHTower
