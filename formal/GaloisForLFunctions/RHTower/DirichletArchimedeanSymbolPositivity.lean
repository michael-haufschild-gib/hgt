import GaloisForLFunctions.RHTower.WeilPositivityImaginaryQuadraticConductorLaw
import GaloisForLFunctions.RHTower.PoleVanishingWeilTraceCertificate
import GaloisForLFunctions.RHTower.SeamDivisionSourceSplit

/-!
# Without a pole, a large conductor makes the archimedean Weil symbol nonnegative

The explicit formula of a primitive Dirichlet `L(s, χ)` of conductor `q` and parity `a ∈ {0, 1}` has
no pole term. Its archimedean part is the Fourier multiplier

`log(q/π) + Re ψ((½ + a + iτ)/2)`.

In the corpus normalisation (`archimedeanWeilSymbol ξ = Re ψ(¼ + iπξ) − log π`) this is
`archimedeanWeilSymbol (τ/2π) + log q` for even `χ`, and
`archimedeanWeilSymbol (τ/2π) + log q + π/cosh(πτ)` for odd `χ`
(`re_digamma_threeQuarter_sub_quarter`; this is the symbol of
`integral_weilAtomSymbol_dirichlet_odd`).

**Theorems.**
* `oddDirichletArchSymbol_nonneg`: for `q ≥ 4π`, the odd symbol is nonnegative at every `τ`.
* `evenDirichletArchSymbol_nonneg`: for `q ≥ 128π`, the even symbol is nonnegative at every `τ`.
* `integral_oddDirichletArchSymbol_nonneg`, `integral_evenDirichletArchSymbol_nonneg`: the
  zero-weight Weil forms `∫ |f̂|² · symbol` are nonnegative on every test.

Proof. `Re ψ(x + iy) ≥ ψ(x)` for `x > 0` (`digamma_real_le_re_digamma_add_mul_I`). Together with
`ψ(¼) = −γ − 3 log 2 − π/2` and `ψ(¾) = ψ(¼) + π`, the symbol is at least
`ψ(¾) − log π + log q` (odd) or `ψ(¼) − log π + log q` (even), which is positive under the stated
bounds on `q`.

Consequence: for such data the weight `λ = 0` is Weil-positive. So the Weil cone is not a point, and
positivity of the archimedean form on prime-blind tests holds trivially, independently of the
generalized Riemann hypothesis for `χ`. For `ζ` the pole term `ĥ(i/2) + ĥ(−i/2)` and the negative
symbol near `τ = 0` (`ψ(¼) − log π ≈ −5.37`) are what make prime-blind positivity equivalent to RH.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- `ψ(¼) = −γ − 3 log 2 − π/2`, real part. -/
theorem re_digamma_one_quarter :
    (Complex.digamma (1 / 4 : ℂ)).re = -Real.eulerMascheroniConstant - 3 * Real.log 2 - π / 2 := by
  rw [GaloisForLFunctions.SeamSplit.digamma_one_quarter]
  simp [Complex.log_re]

/-- `ψ(¾) = ψ(¼) + π`, real part. -/
theorem re_digamma_three_quarters_eq :
    (Complex.digamma (3 / 4 : ℂ)).re = (Complex.digamma (1 / 4 : ℂ)).re + π := by
  have h := congrArg Complex.re GaloisForLFunctions.SeamSplit.digamma_three_quarters_sub_quarter
  rw [Complex.sub_re, Complex.ofReal_re] at h
  linarith

/-- The archimedean symbol at `τ/2π` is `Re ψ(¼ + iτ/2) − log π`. -/
theorem archimedeanWeilSymbol_div_two_pi (τ : ℝ) :
    archimedeanWeilSymbol (τ / (2 * π)) =
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re - Real.log π := by
  rw [archimedeanWeilSymbol_eq]
  congr 4
  field_simp

/-- The odd symbol is `Re ψ(¾ + iτ/2) − log π`. -/
theorem archimedeanWeilSymbol_add_sech (τ : ℝ) :
    archimedeanWeilSymbol (τ / (2 * π)) + π / Real.cosh (π * τ) =
      (Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re - Real.log π := by
  rw [archimedeanWeilSymbol_div_two_pi, ← re_digamma_threeQuarter_sub_quarter τ]
  have e1 : ((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I = 1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * τ / 2 := by
    push_cast; ring
  have e2 : ((3 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I = 1 / 4 + (1 : ℂ) / 2 + I * τ / 2 := by
    push_cast; ring
  rw [e1, e2]
  ring

/-- **The odd archimedean symbol is nonnegative for `q ≥ 4π`.** -/
theorem oddDirichletArchSymbol_nonneg {q : ℝ} (hq : 4 * π ≤ q) (τ : ℝ) :
    0 ≤ archimedeanWeilSymbol (τ / (2 * π)) + Real.log q + π / Real.cosh (π * τ) := by
  have hmin := digamma_real_le_re_digamma_add_mul_I (a := 3 / 4) (by norm_num) (τ / 2)
  have h34 : (Complex.digamma (((3 / 4 : ℝ) : ℂ))).re =
      -Real.eulerMascheroniConstant - 3 * Real.log 2 + π / 2 := by
    rw [show (((3 / 4 : ℝ) : ℂ)) = (3 / 4 : ℂ) by push_cast; ring, re_digamma_three_quarters_eq,
      re_digamma_one_quarter]
    ring
  have hpi : 0 < π := Real.pi_pos
  have hlogq : Real.log π + 2 * Real.log 2 ≤ Real.log q := by
    have h4 : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
      rw [Real.log_mul (by norm_num) hpi.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have := Real.log_le_log (by positivity) hq
    linarith
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := Real.log_two_lt_d9
  have hπ := Real.pi_gt_d2
  have e := archimedeanWeilSymbol_add_sech τ
  linarith

/-- **The even archimedean symbol is nonnegative for `q ≥ 128π`.** -/
theorem evenDirichletArchSymbol_nonneg {q : ℝ} (hq : 128 * π ≤ q) (τ : ℝ) :
    0 ≤ archimedeanWeilSymbol (τ / (2 * π)) + Real.log q := by
  have hmin := digamma_real_le_re_digamma_add_mul_I (a := 1 / 4) (by norm_num) (τ / 2)
  have h14 : (Complex.digamma (((1 / 4 : ℝ) : ℂ))).re =
      -Real.eulerMascheroniConstant - 3 * Real.log 2 - π / 2 := by
    rw [show (((1 / 4 : ℝ) : ℂ)) = (1 / 4 : ℂ) by push_cast; ring, re_digamma_one_quarter]
  have hpi : 0 < π := Real.pi_pos
  have hlogq : Real.log π + 7 * Real.log 2 ≤ Real.log q := by
    have h128 : Real.log (128 * π) = 7 * Real.log 2 + Real.log π := by
      rw [Real.log_mul (by norm_num) hpi.ne', show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      push_cast; ring
    have := Real.log_le_log (by positivity) hq
    linarith
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := Real.log_two_gt_d9
  have hπ := Real.pi_lt_d2
  have e := archimedeanWeilSymbol_div_two_pi τ
  linarith

/-- **The zero-weight odd Weil form is nonnegative** for `q ≥ 4π`: with no prime weights, the
archimedean part of the explicit formula of an odd `L(s, χ)` is already a nonnegative form. -/
theorem integral_oddDirichletArchSymbol_nonneg {q : ℝ} (hq : 4 * π ≤ q) (f : ℝ → ℂ) :
    0 ≤ ∫ τ : ℝ, ‖Zeta23.paperFT f τ‖ ^ 2 *
      (weilAtomSymbol (fun _ => 0) 0 (τ / (2 * π)) + Real.log q + π / Real.cosh (π * τ)) := by
  refine MeasureTheory.integral_nonneg fun τ => mul_nonneg (by positivity) ?_
  have h := oddDirichletArchSymbol_nonneg hq τ
  simpa [weilAtomSymbol] using h

/-- **The zero-weight even Weil form is nonnegative** for `q ≥ 128π`. -/
theorem integral_evenDirichletArchSymbol_nonneg {q : ℝ} (hq : 128 * π ≤ q) (f : ℝ → ℂ) :
    0 ≤ ∫ τ : ℝ, ‖Zeta23.paperFT f τ‖ ^ 2 *
      (weilAtomSymbol (fun _ => 0) 0 (τ / (2 * π)) + Real.log q) := by
  refine MeasureTheory.integral_nonneg fun τ => mul_nonneg (by positivity) ?_
  have h := evenDirichletArchSymbol_nonneg hq τ
  simpa [weilAtomSymbol] using h

end

end RHTower
