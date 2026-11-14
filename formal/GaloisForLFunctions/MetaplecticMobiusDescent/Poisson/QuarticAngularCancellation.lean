import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.EisensteinLatticePoisson

/-!
# Quarter-turn cancellation in planar Poisson summation

A radial function multiplied by `(z / ‖z‖)^k` transforms under a quarter turn
by `i^k`. Its planar Fourier transform has the same covariance. The zero
frequency consequently vanishes for weights congruent to one, two, or three
modulo four, without a smoothness assumption on the radial coefficient.
-/

noncomputable section

open Complex MeasureTheory

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson

/-- Angular weight with a radial coefficient; division at the origin is total. -/
def angularRadial (k : ℕ) (W : ℝ → ℂ) (z : ℂ) : ℂ :=
  (z / (‖z‖ : ℂ)) ^ k * W (‖z‖ ^ 2)

/-- Quarter-turn covariance of the angular coefficient. -/
theorem angularRadial_quarter_turn (k : ℕ) (W : ℝ → ℂ) (z : ℂ) :
    angularRadial k W (I * z) = I ^ k * angularRadial k W z := by
  simp only [angularRadial, norm_mul, norm_I, one_mul, mul_div_assoc, mul_pow, mul_assoc]

/-- Angular multiplication does not increase a radial coefficient's magnitude. -/
theorem norm_angularRadial_le (k : ℕ) (W : ℝ → ℂ) (z : ℂ) :
    ‖angularRadial k W z‖ ≤ ‖W (‖z‖ ^ 2)‖ := by
  have hu : ‖z / (‖z‖ : ℂ)‖ ≤ 1 := by
    by_cases hz : z = 0
    · simp [hz]
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
        div_self (norm_ne_zero_iff.mpr hz)]
  rw [angularRadial, norm_mul, norm_pow]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hu (n := k)) (norm_nonneg _)

/-- Schwartz radial coefficients give genuine integrable angular kernels. -/
theorem integrable_angularRadial (k : ℕ) (W : SchwartzMap ℝ ℂ) :
    Integrable (angularRadial k W) := by
  have hm : Measurable (angularRadial k W) := by
    unfold angularRadial
    fun_prop
  apply (radialTest W).integrable.norm.mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  exact norm_angularRadial_le k W z

private theorem paperFourier_const_mul (c : ℂ) (f : ℂ → ℂ) (u : ℂ) :
    paperFourier (fun z => c * f z) u = c * paperFourier f u := by
  unfold paperFourier
  simp_rw [mul_left_comm _ c, integral_const_mul]
  simp only [Algebra.smul_def]
  ring

/-- Fourier covariance survives the radial transform and its lattice normalization. -/
theorem paperFourier_angular_quarter_turn (k : ℕ) (W : ℝ → ℂ) (u : ℂ) :
    paperFourier (angularRadial k W) (u / I) =
      I ^ k * paperFourier (angularRadial k W) u := by
  have h := paperFourier_comp_mul (angularRadial k W) I I_ne_zero u
  simp only [norm_I, one_pow, div_one, one_smul] at h
  rw [show (fun z => angularRadial k W (I * z)) =
    (fun z => I ^ k * angularRadial k W z) from funext (angularRadial_quarter_turn k W),
    paperFourier_const_mul] at h
  exact h.symm

/-- Only angular weights divisible by four can contribute a zero Fourier mode. -/
theorem angular_zero_mode_constraint (k : ℕ) (W : ℝ → ℂ) :
    (I ^ k - 1) * paperFourier (angularRadial k W) 0 = 0 := by
  have h := paperFourier_angular_quarter_turn k W 0
  rw [zero_div] at h
  linear_combination -h

private theorem I_four_mul (n : ℕ) : I ^ (4 * n) = 1 := by
  rw [pow_mul, show I ^ 4 = 1 by norm_num [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq], one_pow]

/-- Angular weights `4n + 1` have no zero frequency. -/
theorem angular_zero_mode_one (n : ℕ) (W : ℝ → ℂ) :
    paperFourier (angularRadial (4 * n + 1) W) 0 = 0 := by
  have h := angular_zero_mode_constraint (4 * n + 1) W
  rw [pow_add, I_four_mul, pow_one, one_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by
    intro hI
    have := congrArg Complex.im hI
    norm_num at this)

/-- Angular weights `4n + 2` have no zero frequency, despite being even. -/
theorem angular_zero_mode_two (n : ℕ) (W : ℝ → ℂ) :
    paperFourier (angularRadial (4 * n + 2) W) 0 = 0 := by
  have h := angular_zero_mode_constraint (4 * n + 2) W
  rw [pow_add, I_four_mul, I_sq, one_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- The cubic angular factor in quartic reflection has no zero frequency. -/
theorem angular_zero_mode_three (n : ℕ) (W : ℝ → ℂ) :
    paperFourier (angularRadial (4 * n + 3) W) 0 = 0 := by
  have h := angular_zero_mode_constraint (4 * n + 3) W
  rw [pow_add, I_four_mul, one_mul, show I ^ 3 = -I by
    rw [pow_succ, I_sq, neg_one_mul]] at h
  exact (mul_eq_zero.mp h).resolve_left (by
    intro hI
    have := congrArg Complex.im hI
    norm_num at this)

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
