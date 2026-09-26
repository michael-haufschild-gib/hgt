import GaloisForLFunctions.RHTower.XiHeatThirdChannelDecomposition

/-!
# An unconditional remainder bound for the third Xi heat-Hankel form

The open critical strip bounds the imaginary square of each squared spectral
coordinate by its norm.  Combining this with the half-heat phase estimate controls
the entire negative square energy by three positive Gaussian norm moments.  All
series converge at every positive heat time; no RH or moment-sign premise is used.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- A squared Xi spectral coordinate has an imaginary square bounded by its norm. -/
theorem xiSpectralSq_im_sq_le_norm (q : XiZeroCopy) :
    (xiSpectralPoint q ^ 2).im ^ 2 ≤ ‖xiSpectralPoint q ^ 2‖ := by
  have hs : (xiSpectralPoint q).im ^ 2 < 1 / 4 := by
    have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
      simp [xiSpectralPoint]
    rw [him, neg_sq]
    exact xi_divisor_support_centered_re_sq_lt_quarter q.1
  rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_im]
  nlinarith [sq_nonneg (xiSpectralPoint q).im,
    mul_nonneg (sq_nonneg (xiSpectralPoint q).re) (sub_nonneg.mpr hs.le)]

/-- Positive reference moments of the actual divisor, including every analytic multiplicity. -/
def xiHeatNormMoment (k : ℕ) (τ : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, ‖xiSpectralPoint q ^ 2‖ ^ k *
    Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re))

theorem summable_xiHeatNormMoment (k : ℕ) (τ : ℝ) :
    Summable (fun q : XiZeroCopy => ‖xiSpectralPoint q ^ 2‖ ^ k *
      Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re))) := by
  have h := (summable_xiGaussianHeatMonomialTerm (Real.exp_pos τ) k).norm
  simpa only [norm_mul, norm_pow, xiGaussianHeatTerm, Complex.norm_exp,
    Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero, neg_mul] using h

theorem xiHeatNormMoment_nonneg (k : ℕ) (τ : ℝ) :
    0 ≤ xiHeatNormMoment k τ :=
  tsum_nonneg fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (Real.exp_pos _).le

def xiHeatThirdDebtBudget (a b c τ : ℝ) : ℝ :=
  (8 * b ^ 2 + 3 * (Real.exp τ) ^ 2 * a ^ 2) * xiHeatNormMoment 1 τ +
    (32 * c ^ 2 + 3 * (Real.exp τ) ^ 2 * b ^ 2) * xiHeatNormMoment 3 τ +
    3 * (Real.exp τ) ^ 2 * c ^ 2 * xiHeatNormMoment 5 τ

/-- The mixed-term bound precedes every diagonal majorization. -/
theorem xiHeatThirdPhaseDebt_atom_bound (a b c τ : ℝ) (q : XiZeroCopy) :
    2 * (xiHeatThirdAmplitude a b c τ q).im ^ 2 ≤
      Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re)) *
        (xiSpectralPoint q ^ 2).im ^ 2 *
        (4 * (b + 2 * c * (xiSpectralPoint q ^ 2).re) ^ 2 +
          (Real.exp τ) ^ 2 * (quadraticHeatValue a b c (xiSpectralPoint q ^ 2)).re ^ 2) := by
  simpa only [xiHeatThirdAmplitude, quadraticHeatValue_re] using
    quadraticHeatPhaseDebt_bound a b c (Real.exp τ) (xiSpectralPoint q ^ 2)

theorem xiHeatThirdPhaseDebt_atom_le_normBudget (a b c τ : ℝ) (q : XiZeroCopy) :
    2 * (xiHeatThirdAmplitude a b c τ q).im ^ 2 ≤
      Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re)) * ‖xiSpectralPoint q ^ 2‖ *
        (8 * b ^ 2 + 32 * c ^ 2 * ‖xiSpectralPoint q ^ 2‖ ^ 2 +
          3 * (Real.exp τ) ^ 2 *
            (a ^ 2 + b ^ 2 * ‖xiSpectralPoint q ^ 2‖ ^ 2 +
              c ^ 2 * ‖xiSpectralPoint q ^ 2‖ ^ 4)) := by
  let z := xiSpectralPoint q ^ 2
  let v := quadraticHeatValue a b c z
  have hv : v.re ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg v.im]
  have hp := quadraticHeatValue_norm_sq_le a b c z
  have hd := quadraticHeatValue_derivative_sq_le b c z
  have hpoly : 4 * (b + 2 * c * z.re) ^ 2 + (Real.exp τ) ^ 2 * v.re ^ 2 ≤
      8 * b ^ 2 + 32 * c ^ 2 * ‖z‖ ^ 2 +
        3 * (Real.exp τ) ^ 2 * (a ^ 2 + b ^ 2 * ‖z‖ ^ 2 + c ^ 2 * ‖z‖ ^ 4) := by
    have hmul := mul_le_mul_of_nonneg_left (hv.trans hp) (sq_nonneg (Real.exp τ))
    nlinarith
  calc
    2 * (xiHeatThirdAmplitude a b c τ q).im ^ 2 ≤
        Real.exp (-(Real.exp τ * z.re)) * z.im ^ 2 *
          (4 * (b + 2 * c * z.re) ^ 2 + (Real.exp τ) ^ 2 * v.re ^ 2) :=
      xiHeatThirdPhaseDebt_atom_bound a b c τ q
    _ ≤ Real.exp (-(Real.exp τ * z.re)) * z.im ^ 2 *
        (8 * b ^ 2 + 32 * c ^ 2 * ‖z‖ ^ 2 +
          3 * (Real.exp τ) ^ 2 * (a ^ 2 + b ^ 2 * ‖z‖ ^ 2 + c ^ 2 * ‖z‖ ^ 4)) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (xiSpectralSq_im_sq_le_norm q) (Real.exp_pos _).le)
      (by positivity)

/-- A bound on the full negative remainder, using only the actual divisor and the critical strip. -/
theorem xiHeatThirdPhaseDebt_le_budget (a b c τ : ℝ) :
    xiHeatThirdPhaseDebt a b c τ ≤ xiHeatThirdDebtBudget a b c τ := by
  let A := 8 * b ^ 2 + 3 * (Real.exp τ) ^ 2 * a ^ 2
  let B := 32 * c ^ 2 + 3 * (Real.exp τ) ^ 2 * b ^ 2
  let C := 3 * (Real.exp τ) ^ 2 * c ^ 2
  let f := fun (k : ℕ) (q : XiZeroCopy) => ‖xiSpectralPoint q ^ 2‖ ^ k *
    Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re))
  have hpoint : ∀ q : XiZeroCopy, 2 * (xiHeatThirdAmplitude a b c τ q).im ^ 2 ≤
      A * f 1 q + B * f 3 q + C * f 5 q := by
    intro q
    refine (xiHeatThirdPhaseDebt_atom_le_normBudget a b c τ q).trans_eq ?_
    dsimp [A, B, C, f]
    ring
  have hs : ∀ k, Summable (f k) := fun k => summable_xiHeatNormMoment k τ
  have h := Summable.tsum_le_tsum hpoint
    ((summable_xiHeatThirdAmplitude_im_sq a b c τ).mul_left 2)
    (((hs 1).mul_left A).add ((hs 3).mul_left B) |>.add ((hs 5).mul_left C))
  rw [Summable.tsum_add (((hs 1).mul_left A).add ((hs 3).mul_left B)) ((hs 5).mul_left C),
    Summable.tsum_add ((hs 1).mul_left A) ((hs 3).mul_left B)] at h
  simp only [tsum_mul_left] at h
  exact h

/-- The actual third Hankel form has an unconditional lower bound by positive energy minus
an explicit three-moment budget. -/
theorem xiHeatThirdQuadratic_lower_bound (a b c τ : ℝ) :
    xiHeatThirdNormEnergy a b c τ - xiHeatThirdDebtBudget a b c τ ≤
      xiHeatThirdQuadratic a b c (Real.exp τ) := by
  rw [xiHeatThirdQuadratic_eq_energy_sub_debt]
  exact sub_le_sub_left (xiHeatThirdPhaseDebt_le_budget a b c τ) _

end
end RHTower
