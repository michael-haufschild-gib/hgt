import GaloisForLFunctions.RHTower.DigammaVerticalMinimum
import GaloisForLFunctions.RHTower.DigammaTwoSided
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic

/-!
# An explicit system with positive Weil density for the archimedean datum of `ζ`

For the archimedean datum of `ζ` (symbol `G_∞(s) = ½ψ(s/2) − ½ log π`, pole weight one), a weight
system `λ` on `(1, ∞)` has Weil function `Φ_λ = G_∞ + 1/s + 1/(s−1) − D_λ`. Its Weil measure on the
critical line has density `2 Re Φ_λ(1/2 + it)`.

For `λ₀ = dx` on `(1, ∞)` minus the point mass `e^{1/20000}` at `e^{1/10000}`, we have
`D_{λ₀}(s) = 1/(s−1) − e^{1/20000} e^{−s/10000}`, so
`Φ_{λ₀} = G_∞ + 1/s + e^{1/20000} e^{−s/10000}`. On the critical line this has real part
`θ'(t) + Re(1/(1/2+it)) + cos(t/10⁴)`.

The pole at `0` combines with the symbol into a shifted digamma
(`half_digamma_add_inv_criticalLine`):

`½ψ(s/2) + 1/s = ½ψ(s/2 + 1)`.

The density is then bounded below by `1/200` at every height (`lebesgueAtomWeilDensity_ge`,
`thetaDeriv_add_pole_add_atom_ge`):
- at low height by the vertical minimum of `Re ψ` together with `ψ(5/4) ≥ −3/5` and `log π < 23/20`;
- at large height by `Re ψ(z) ≥ log ‖z‖ − 3/‖z‖`.

The Lebesgue part cancels the growing half of the pole term, and the single negative atom pays for
the negative low-frequency value `½ψ(5/4) − ½ log π ≈ −0.686` of the archimedean density.
-/

open Complex

noncomputable section

namespace RHTower

/-- `log π < 23/20`, from `π < 3.15 < e · (1 + 0.15 + 0.15²/2) ≤ e^{1.15}`. -/
theorem log_pi_lt_twentythree_twentieths : Real.log Real.pi < 23 / 20 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have h1 := Real.exp_one_gt_d9
  have h2 : 1 + (3 / 20 : ℝ) + (3 / 20 : ℝ) ^ 2 / 2 ≤ Real.exp (3 / 20) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hsplit : Real.exp (23 / 20) = Real.exp 1 * Real.exp (3 / 20) := by
    rw [← Real.exp_add]; norm_num
  have h3 : (3.15 : ℝ) < Real.exp 1 * Real.exp (3 / 20) := by
    have hpos : (0 : ℝ) < Real.exp (3 / 20) := Real.exp_pos _
    nlinarith
  rw [hsplit]
  linarith [Real.pi_lt_d2]

/-- `ψ(5/4) ≥ −3/5`, from `log y − 1/y ≤ ψ(y)` and `log(5/4) ≥ 1 − 4/5`. -/
theorem neg_three_fifths_le_re_digamma_five_quarters :
    -(3 / 5 : ℝ) ≤ (Complex.digamma (((5 / 4 : ℝ)) : ℂ)).re := by
  have h := log_sub_inv_le_re_digamma (y := (5 / 4 : ℝ)) (by norm_num)
  have hlog : 1 - (5 / 4 : ℝ)⁻¹ ≤ Real.log (5 / 4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  norm_num at hlog h ⊢
  linarith

/-- `log 2400 ≥ 4`, since `e⁴ < 2.72⁴ < 2400`. -/
theorem four_le_log_twentyfourhundred : (4 : ℝ) ≤ Real.log 2400 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hle : Real.exp 4 ≤ 2400 := by
    rw [h4]
    have : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := by
      apply pow_le_pow_left₀ hpos.le he.le
    linarith [show (2.7182818286 : ℝ) ^ 4 ≤ 2400 by norm_num]
  calc (4 : ℝ) = Real.log (Real.exp 4) := (Real.log_exp 4).symm
    _ ≤ Real.log 2400 := Real.log_le_log (Real.exp_pos 4) hle

/-- **Positive Weil density of the Lebesgue-minus-atom system.**  For every real `t`,
`½ Re ψ(5/4 + it/2) − ½ log π + cos(t/10⁴) ≥ 1/200`.

The left side is the density of the Weil measure, for the archimedean datum of `ζ` with pole weight
one, of the system `dx` on `(1, ∞)` minus the point mass `e^{1/20000}` at `e^{1/10000}`:
`G_∞(s) + 1/s = ½ψ(s/2 + 1) − ½ log π`, and the atom contributes `cos(t/10⁴)` on `Re s = 1/2`.
For `|t| ≤ 4800` the real part of digamma is at least its value at the real point and
`cos(t/10⁴) ≥ 0.8848`; for `|t| > 4800`, `Re ψ(z) ≥ log ‖z‖ − 3/‖z‖` with `‖z‖ ≥ 2400`. -/
theorem lebesgueAtomWeilDensity_ge (t : ℝ) :
    1 / 200 ≤ (1 / 2 : ℝ) * (Complex.digamma (((5 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re
      - (1 / 2 : ℝ) * Real.log Real.pi + Real.cos (t / 10000) := by
  have hpi := log_pi_lt_twentythree_twentieths
  rcases le_or_gt |t| 4800 with ht | ht
  · have hmin := digamma_real_le_re_digamma_add_mul_I (a := (5 / 4 : ℝ)) (by norm_num) (t / 2)
    have hψ := neg_three_fifths_le_re_digamma_five_quarters
    have hcos : 1 - (t / 10000) ^ 2 / 2 ≤ Real.cos (t / 10000) := Real.one_sub_sq_div_two_le_cos
    have hsq : (t / 10000) ^ 2 ≤ (48 / 100 : ℝ) ^ 2 := by
      rw [div_pow]
      have : t ^ 2 ≤ 4800 ^ 2 := by
        have := sq_abs t
        nlinarith [abs_nonneg t]
      nlinarith
    nlinarith
  · set z : ℂ := ((5 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I with hz
    have hre : z.re = 5 / 4 := by simp [hz]
    have him : z.im = t / 2 := by simp [hz]
    have hnorm : 2400 ≤ ‖z‖ := by
      have h1 := Complex.abs_im_le_norm z
      rw [him, abs_div, abs_two] at h1
      linarith
    have hasym := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos
      (z := z) (by rw [hre]; norm_num) (by linarith)
    have hlowre : Real.log ‖z‖ - 3 / ‖z‖ ≤ (Complex.digamma z).re := by
      have h := Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)
      rw [Complex.sub_re, Complex.log_re] at h
      have := abs_le.mp (h.trans hasym)
      linarith [this.1]
    have hlogz : Real.log 2400 ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) hnorm
    have h3 : 3 / ‖z‖ ≤ 3 / 2400 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnorm
    have h4 := four_le_log_twentyfourhundred
    have hcos := Real.neg_one_le_cos (t / 10000)
    nlinarith

/-- On the critical line the archimedean symbol plus the pole at `0` is a shifted digamma:
`½ψ(s/2) + 1/s = ½ψ(s/2 + 1)` at `s = 1/2 + it`. -/
theorem half_digamma_add_inv_criticalLine (t : ℝ) :
    (1 / 2 : ℂ) * Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)
        + 1 / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
      = (1 / 2 : ℂ) * Complex.digamma (((5 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) := by
  set w : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I with hw
  have hwre : w.re = 1 / 4 := by simp [hw]
  have hne : ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    rw [hwre] at this
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hrec := Complex.digamma_apply_add_one w hne
  have hshift : ((5 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I = w + 1 := by
    rw [hw]; push_cast; ring
  have hw0 : w ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hwre] at this; simp at this
  have hs : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I = 2 * w := by
    rw [hw]; push_cast; ring
  rw [hshift, hrec, hs]
  field_simp

/-- **The Weil density of the Lebesgue-minus-atom system in Riemann–Siegel form.**  For every real
`t`, `θ'(t) + Re(1/(1/2+it)) + cos(t/10⁴) ≥ 1/200`, where
`θ'(t) = ½ Re ψ(1/4 + it/2) − ½ log π`. -/
theorem thetaDeriv_add_pole_add_atom_ge (t : ℝ) :
    1 / 200 ≤ (1 / 2 : ℝ) * (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re
      - (1 / 2 : ℝ) * Real.log Real.pi + (1 / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re
      + Real.cos (t / 10000) := by
  have h := lebesgueAtomWeilDensity_ge t
  have hid := congrArg Complex.re (half_digamma_add_inv_criticalLine t)
  simp only [Complex.add_re, Complex.mul_re] at hid
  norm_num at hid h ⊢
  linarith

end RHTower
