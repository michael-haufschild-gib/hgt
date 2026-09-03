import GaloisForLFunctions.RHTower.SemilocalGammaComplexRapidityCharacteristic
import GaloisForLFunctions.RHTower.SemilocalJacobiCoefficientCauchyBound

/-!
# Term-by-term integration of the Meixner–Pollaczek generating function

With the Cauchy bound `|c_m p_m(s)| ≤ C e^{|s|/2} 4^m` the series `Σ_m c_m p_m(s) w^m g(s)` is
dominated, for `‖w‖ < 1/4`, by `C e^{|s|/2} ‖g(s)‖ (4‖w‖)^m`; whenever `e^{|s|/2} ‖g‖` is integrable
against the Gamma measure the sum and the integral may be exchanged:

`Σ_m w^m ∫ c_m p_m(s) g(s) dμ = ∫ G_s(w) g(s) dμ`.

Two instances are recorded: `g = G_s(z) e^{its}` (the boost row generating function in `w`) and
`g = p_m(s) e^{its}` (the expansion of one boost row in `z`).  These are the two one-variable
interchanges of the boost generating function programme (MUST-148).
-/

open Complex MeasureTheory
open scoped BigOperators

namespace RHTower

namespace MeixnerPollaczek

open ComplexRapidity

/-! ## Two integrability facts -/

/-- `e^{κ|s|}` is integrable against the Gamma measure for `|κ| < π/2`. -/
theorem integrable_exp_abs_mul_semilocalArchimedeanGammaMeasure {κ : ℝ} (hκ : |κ| < Real.pi / 2) :
    Integrable (fun s : ℝ => Real.exp (κ * |s|)) semilocalArchimedeanGammaMeasure := by
  have h1 := integrable_exp_mul_semilocalArchimedeanGammaMeasure hκ
  have h2 := integrable_exp_mul_semilocalArchimedeanGammaMeasure (a := -κ) (by rwa [abs_neg])
  refine (h1.add h2).mono' ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hle : Real.exp (κ * |s|) ≤ Real.exp |κ * s| := by
      rw [Real.exp_le_exp, abs_mul]
      exact mul_le_mul_of_nonneg_right (le_abs_self κ) (abs_nonneg s)
    have := Real.exp_abs_le (κ * s)
    simp only [Pi.add_apply]
    rw [show -κ * s = -(κ * s) by ring]
    linarith

/-- A polynomial is bounded by `K e^{|s|/2}`. -/
theorem abs_eval_le_exp_half_abs (p : Polynomial ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ s : ℝ, |p.eval s| ≤ K * Real.exp (|s| / 2) := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * 2 ^ i * i.factorial,
    Finset.sum_nonneg fun i _ => by positivity, fun s => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_pow]
  have hfac := Real.pow_div_factorial_le_exp (|s| / 2) (by positivity) i
  have hpow : |s| ^ i = 2 ^ i * (|s| / 2) ^ i := by
    rw [← mul_pow]; congr 1; ring
  have hfpos : (0 : ℝ) < i.factorial := by exact_mod_cast i.factorial_pos
  have h2 : (|s| / 2) ^ i ≤ i.factorial * Real.exp (|s| / 2) := by
    rw [div_le_iff₀ hfpos] at hfac
    linarith
  calc |p.coeff i| * |s| ^ i = |p.coeff i| * 2 ^ i * (|s| / 2) ^ i := by rw [hpow]; ring
    _ ≤ |p.coeff i| * 2 ^ i * (i.factorial * Real.exp (|s| / 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = |p.coeff i| * 2 ^ i * i.factorial * Real.exp (|s| / 2) := by ring

/-- `e^{|s|/2} |p(s)|` is integrable against the Gamma measure for every real polynomial. -/
theorem integrable_exp_half_abs_mul_abs_eval (p : Polynomial ℝ) :
    Integrable (fun s : ℝ => Real.exp (|s| / 2) * |p.eval s|) semilocalArchimedeanGammaMeasure := by
  obtain ⟨K, hK0, hK⟩ := abs_eval_le_exp_half_abs p
  have hint := (integrable_exp_abs_mul_semilocalArchimedeanGammaMeasure (κ := 1)
    (by rw [abs_one]; linarith [Real.pi_gt_three])).const_mul K
  refine hint.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_abs.div_const 2)).mul
      (continuous_abs.comp (Polynomial.continuous p))).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (|s| / 2) * |p.eval s| ≤ Real.exp (|s| / 2) * (K * Real.exp (|s| / 2)) :=
          mul_le_mul_of_nonneg_left (hK s) (Real.exp_pos _).le
      _ = K * Real.exp (1 * |s|) := by
          rw [show (1 : ℝ) * |s| = |s| / 2 + |s| / 2 by ring, Real.exp_add]; ring

/-! ## The dominated interchange -/

theorem continuous_mpCoefficient (m : ℕ) : Continuous fun s : ℝ => mpCoefficient s m :=
  continuous_const.mul (Polynomial.continuous _)

/-- **Term-by-term integration of the generating function.**  If `e^{|s|/2} ‖g‖` is integrable
and `‖w‖ < 1/4`, then `Σ_m ∫ c_m p_m(s) w^m g(s) dμ = ∫ G_s(w) g(s) dμ`. -/
theorem hasSum_integral_mpCoefficient_mul {g : ℝ → ℂ}
    (hg : Integrable (fun s : ℝ => Real.exp (|s| / 2) * ‖g s‖) semilocalArchimedeanGammaMeasure)
    (hmeas : AEStronglyMeasurable g semilocalArchimedeanGammaMeasure)
    {w : ℂ} (hw : ‖w‖ < 1 / 4) :
    HasSum (fun m : ℕ => ∫ s : ℝ, (mpCoefficient s m : ℂ) * w ^ m * g s
        ∂semilocalArchimedeanGammaMeasure)
      (∫ s : ℝ, mpGeneratingFunction s w * g s ∂semilocalArchimedeanGammaMeasure) := by
  set C : ℝ := (3 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) with hC
  have hC0 : 0 ≤ C := by positivity
  have hr0 : 0 ≤ 4 * ‖w‖ := by positivity
  have hr1 : 4 * ‖w‖ < 1 := by linarith
  refine hasSum_integral_of_dominated_convergence
    (fun m s => C * Real.exp (|s| / 2) * ‖g s‖ * (4 * ‖w‖) ^ m) ?_ ?_ ?_ ?_ ?_
  · intro m
    exact (((Complex.continuous_ofReal.comp (continuous_mpCoefficient m)).mul
      continuous_const).aestronglyMeasurable).mul hmeas
  · intro m
    filter_upwards with s
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    have h := abs_mpCoefficient_le s m
    calc |mpCoefficient s m| * ‖w‖ ^ m * ‖g s‖
        ≤ (C * Real.exp (|s| / 2) * 4 ^ m) * ‖w‖ ^ m * ‖g s‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity))
            (norm_nonneg _)
      _ = C * Real.exp (|s| / 2) * ‖g s‖ * (4 * ‖w‖) ^ m := by rw [mul_pow]; ring
  · filter_upwards with s
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
  · have hfun : (fun s : ℝ => ∑' m : ℕ, C * Real.exp (|s| / 2) * ‖g s‖ * (4 * ‖w‖) ^ m) =
        fun s : ℝ => (C * (1 - 4 * ‖w‖)⁻¹) * (Real.exp (|s| / 2) * ‖g s‖) := by
      funext s
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      ring
    rw [hfun]
    exact hg.const_mul _
  · filter_upwards with s
    exact (hasSum_mpGeneratingFunction s (hw.trans (by norm_num))).mul_right (g s)

/-! ## Instance 1: the boost row generating function in `w` -/

theorem norm_mpGeneratingFunction_ofReal (s z : ℝ) :
    ‖mpGeneratingFunction s z‖ = (1 + z ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (s * Real.arctan z) := by
  rw [mpGeneratingFunction_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem continuous_mpGeneratingFunction_ofReal (z : ℝ) :
    Continuous fun s : ℝ => mpGeneratingFunction s z := by
  have : (fun s : ℝ => mpGeneratingFunction s z) =
      fun s : ℝ => (((1 + z ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (s * Real.arctan z) : ℝ) : ℂ) := by
    funext s; exact mpGeneratingFunction_ofReal s z
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_const.mul
    (Real.continuous_exp.comp (continuous_id.mul continuous_const)))

theorem integrable_exp_half_abs_mul_norm_boostRow {z : ℝ} (hz : |z| < 1) (t : ℝ) :
    Integrable (fun s : ℝ => Real.exp (|s| / 2) *
      ‖mpGeneratingFunction s z * cexp (((t * s : ℝ) : ℂ) * I)‖)
      semilocalArchimedeanGammaMeasure := by
  have hκ : abs (1 / 2 + |Real.arctan z|) < Real.pi / 2 := by
    have := abs_arctan_lt_pi_div_four hz
    rw [abs_of_nonneg (by positivity)]
    linarith [Real.pi_gt_three]
  have hint := (integrable_exp_abs_mul_semilocalArchimedeanGammaMeasure hκ).const_mul
    ((1 + z ^ 2) ^ (-(1 / 4 : ℝ)))
  refine hint.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_abs.div_const 2)).mul
      ((continuous_mpGeneratingFunction_ofReal z).mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
          (continuous_const.mul continuous_id)).mul continuous_const))).norm).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, norm_mpGeneratingFunction_ofReal,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    have h1 : Real.exp (s * Real.arctan z) ≤ Real.exp (|Real.arctan z| * |s|) := by
      rw [Real.exp_le_exp, mul_comm, ← abs_mul]
      exact le_abs_self _
    calc Real.exp (|s| / 2) * ((1 + z ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (s * Real.arctan z))
        ≤ Real.exp (|s| / 2) * ((1 + z ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (|Real.arctan z| * |s|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity))
            (Real.exp_pos _).le
      _ = (1 + z ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp ((1 / 2 + |Real.arctan z|) * |s|) := by
          rw [show (1 / 2 + |Real.arctan z|) * |s| = |s| / 2 + |Real.arctan z| * |s| by ring,
            Real.exp_add]
          ring

/-- **Boost row generating function, integrated term by term in `w`.** -/
theorem hasSum_integral_mpCoefficient_mul_boostRow {z : ℝ} (hz : |z| < 1) (t : ℝ) {w : ℂ}
    (hw : ‖w‖ < 1 / 4) :
    HasSum (fun m : ℕ => ∫ s : ℝ, (mpCoefficient s m : ℂ) * w ^ m *
        (mpGeneratingFunction s z * cexp (((t * s : ℝ) : ℂ) * I)) ∂semilocalArchimedeanGammaMeasure)
      (∫ s : ℝ, mpGeneratingFunction s w *
        (mpGeneratingFunction s z * cexp (((t * s : ℝ) : ℂ) * I)) ∂semilocalArchimedeanGammaMeasure) :=
  hasSum_integral_mpCoefficient_mul (integrable_exp_half_abs_mul_norm_boostRow hz t)
    ((continuous_mpGeneratingFunction_ofReal z).mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id)).mul continuous_const))).aestronglyMeasurable hw

/-! ## Instance 2: one boost row expanded in `z` -/

theorem integrable_exp_half_abs_mul_norm_row (m : ℕ) (t : ℝ) :
    Integrable (fun s : ℝ => Real.exp (|s| / 2) *
      ‖(((semilocalArchimedeanJacobiPolynomial m).eval s : ℝ) : ℂ) * cexp (((t * s : ℝ) : ℂ) * I)‖)
      semilocalArchimedeanGammaMeasure := by
  refine (integrable_exp_half_abs_mul_abs_eval (semilocalArchimedeanJacobiPolynomial m)).congr ?_
  filter_upwards with s
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **One boost row, integrated term by term in `z`.** -/
theorem hasSum_integral_mpCoefficient_mul_row (m : ℕ) (t : ℝ) {z : ℂ} (hz : ‖z‖ < 1 / 4) :
    HasSum (fun n : ℕ => ∫ s : ℝ, (mpCoefficient s n : ℂ) * z ^ n *
        ((((semilocalArchimedeanJacobiPolynomial m).eval s : ℝ) : ℂ) * cexp (((t * s : ℝ) : ℂ) * I))
        ∂semilocalArchimedeanGammaMeasure)
      (∫ s : ℝ, mpGeneratingFunction s z *
        ((((semilocalArchimedeanJacobiPolynomial m).eval s : ℝ) : ℂ) * cexp (((t * s : ℝ) : ℂ) * I))
        ∂semilocalArchimedeanGammaMeasure) :=
  hasSum_integral_mpCoefficient_mul (integrable_exp_half_abs_mul_norm_row m t)
    ((Complex.continuous_ofReal.comp (Polynomial.continuous _)).mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id)).mul continuous_const))).aestronglyMeasurable hz

end MeixnerPollaczek

end RHTower
