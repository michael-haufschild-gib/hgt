import GaloisForLFunctions.RHTower.ThetaHauptmodulLogTranslation

/-!
# The Fourier expansion of the theta-power family

`G(τ) = e^{-πi(a/4)τ} F_a(τ)` is `2`-periodic on `ℍ` (`thetaPowerForm_add_two`) and bounded as
`Im τ → ∞` (`thetaPowerForm_eq_cuspInf`), so its cusp function `g(q)`, `q = e^{πiτ}`, is holomorphic on
the unit disc.  Its Taylor coefficients `b_n` give

  `F_a(τ) = Σ_{n ≥ 0} b_n e^{πi(n + a/4)τ}`   (`Im τ > 0`),

with `Σ |b_n| r^n < ∞` for every `r < 1`.
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

open Bottcher

/-- The `2`-periodic normalization `G = e^{-πi(a/4)τ} F_a` on `ℍ`, extended by `0`. -/
def thetaPowerPeriodic (a : ℝ) (τ : ℂ) : ℂ :=
  if 0 < τ.im then Complex.exp (-(π * I * ((a / 4 : ℝ) : ℂ) * τ)) * thetaPowerForm a τ else 0

theorem thetaPowerPeriodic_of_im_pos (a : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaPowerPeriodic a τ = Complex.exp (-(π * I * ((a / 4 : ℝ) : ℂ) * τ)) * thetaPowerForm a τ := by
  simp [thetaPowerPeriodic, hτ]

theorem periodic_thetaPowerPeriodic (a : ℝ) :
    Function.Periodic (thetaPowerPeriodic a) ((2 : ℝ) : ℂ) := by
  intro τ
  have him : (τ + ((2 : ℝ) : ℂ)).im = τ.im := by simp
  by_cases hτ : 0 < τ.im
  · rw [thetaPowerPeriodic_of_im_pos a (by rw [him]; exact hτ), thetaPowerPeriodic_of_im_pos a hτ]
    rw [show ((2 : ℝ) : ℂ) = 2 by norm_num, thetaPowerForm_add_two a hτ]
    have : -(π * I * ((a / 4 : ℝ) : ℂ) * (τ + 2)) =
        -(π * I * ((a / 4 : ℝ) : ℂ) * τ) + -(π * I * ((a / 2 : ℝ) : ℂ)) := by push_cast; ring
    rw [this, Complex.exp_add]
    have h2 : Complex.exp (-(π * I * ((a / 2 : ℝ) : ℂ))) * Complex.exp (π * I * ((a / 2 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    calc Complex.exp (-(π * I * ((a / 4 : ℝ) : ℂ) * τ)) * Complex.exp (-(π * I * ((a / 2 : ℝ) : ℂ))) *
          (Complex.exp (π * I * ((a / 2 : ℝ) : ℂ)) * thetaPowerForm a τ)
        = Complex.exp (-(π * I * ((a / 4 : ℝ) : ℂ) * τ)) *
            (Complex.exp (-(π * I * ((a / 2 : ℝ) : ℂ))) * Complex.exp (π * I * ((a / 2 : ℝ) : ℂ))) *
              thetaPowerForm a τ := by ring
      _ = _ := by rw [h2, mul_one]
  · have hτ' : ¬ 0 < (τ + ((2 : ℝ) : ℂ)).im := by rw [him]; exact hτ
    simp [thetaPowerPeriodic, hτ]

theorem differentiableAt_thetaPowerPeriodic (a : ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (thetaPowerPeriodic a) τ := by
  have hmem : τ ∈ modUpperSet := hτ
  have hF := (differentiableOn_thetaPowerForm a).differentiableAt (isOpen_modUpperSet.mem_nhds hmem)
  have hd : DifferentiableAt ℂ
      (fun σ => Complex.exp (-(π * I * ((a / 4 : ℝ) : ℂ) * σ)) * thetaPowerForm a σ) τ :=
    (by fun_prop : DifferentiableAt ℂ (fun σ : ℂ => Complex.exp (-(π * I * ((a / 4 : ℝ) : ℂ) * σ))) τ).mul hF
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_modUpperSet.mem_nhds hmem] with σ hσ
  exact thetaPowerPeriodic_of_im_pos a hσ

/-- The bound of `G` near `i∞`. -/
theorem norm_thetaPowerPeriodic_le (ha : 0 ≤ a) {τ : ℂ} (hτ : 6 < τ.im) :
    ‖thetaPowerPeriodic a τ‖ ≤ 2 ^ a * 2 * Real.exp (a / 8) := by
  have hτ0 : 0 < τ.im := by linarith
  rw [thetaPowerPeriodic_of_im_pos a hτ0, thetaPowerForm_eq_cuspInf a hτ]
  have hcancel : Complex.exp (-(π * I * ((a / 4 : ℝ) : ℂ) * τ)) *
      ((2 : ℂ) ^ (a : ℂ) * Complex.exp (π * I * ((a / 4 : ℝ) : ℂ) * τ) *
        (thetaThree τ * Complex.exp (((a / 4 : ℝ) : ℂ) * Complex.log (cuspInfQuot τ)))) =
      (2 : ℂ) ^ (a : ℂ) *
        (thetaThree τ * Complex.exp (((a / 4 : ℝ) : ℂ) * Complex.log (cuspInfQuot τ))) := by
    have : Complex.exp (-(π * I * ((a / 4 : ℝ) : ℂ) * τ)) *
        Complex.exp (π * I * ((a / 4 : ℝ) : ℂ) * τ) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    linear_combination ((2 : ℂ) ^ (a : ℂ) *
        (thetaThree τ * Complex.exp (((a / 4 : ℝ) : ℂ) * Complex.log (cuspInfQuot τ)))) * this
  rw [hcancel, norm_mul, norm_mul]
  have h2 : ‖(2 : ℂ) ^ (a : ℂ)‖ = 2 ^ a := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp
  have h3 : ‖thetaThree τ‖ ≤ 2 := (norm_thetaThree_bounds (by linarith)).2
  have hQ := norm_cuspInfQuot_sub_one_le (le_of_lt hτ)
  have hQn : ‖cuspInfQuot τ‖ ≤ 3 / 2 := by
    calc ‖cuspInfQuot τ‖ = ‖(cuspInfQuot τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖cuspInfQuot τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by rw [norm_one]; linarith
  have hQpos : 0 < ‖cuspInfQuot τ‖ := by
    have := cuspInfQuot_re_pos (le_of_lt hτ)
    exact norm_pos_iff.mpr (fun h => by rw [h] at this; simp at this)
  have he : ‖Complex.exp (((a / 4 : ℝ) : ℂ) * Complex.log (cuspInfQuot τ))‖ ≤ Real.exp (a / 8) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [Complex.re_ofReal_mul, Complex.log_re]
    have hlog : Real.log ‖cuspInfQuot τ‖ ≤ 1 / 2 := by
      have := Real.log_le_sub_one_of_pos hQpos; linarith
    have ha4 : 0 ≤ a / 4 := by positivity
    nlinarith
  rw [h2]
  calc 2 ^ a * (‖thetaThree τ‖ * ‖Complex.exp (((a / 4 : ℝ) : ℂ) * Complex.log (cuspInfQuot τ))‖)
      ≤ 2 ^ a * (2 * Real.exp (a / 8)) := by gcongr
    _ = 2 ^ a * 2 * Real.exp (a / 8) := by ring

/-- The cusp function `g(q)`, `q = e^{πiτ}`. -/
def thetaPowerCusp (a : ℝ) : ℂ → ℂ := Function.Periodic.cuspFunction 2 (thetaPowerPeriodic a)

theorem differentiableOn_thetaPowerCusp (ha : 0 ≤ a) :
    DifferentiableOn ℂ (thetaPowerCusp a) (Metric.ball 0 1) := by
  intro q hq
  have hq1 : ‖q‖ < 1 := by simpa using hq
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases hq0 : q = 0
  · rw [hq0]
    refine Function.Periodic.differentiableAt_cuspFunction_zero (by norm_num)
      (periodic_thetaPowerPeriodic a) ?_ ?_
    · rw [Filter.eventually_comap]
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with y hy τ hτ
      exact differentiableAt_thetaPowerPeriodic a (hτ ▸ hy)
    · rw [Filter.BoundedAtFilter, Asymptotics.isBigO_iff]
      refine ⟨2 ^ a * 2 * Real.exp (a / 8), ?_⟩
      rw [Filter.eventually_comap]
      filter_upwards [Filter.eventually_gt_atTop (6 : ℝ)] with y hy τ hτ
      simp only [Pi.one_apply, norm_one, mul_one]
      exact norm_thetaPowerPeriodic_le ha (hτ ▸ hy)
  · have hz := Function.Periodic.im_invQParam_pos_of_norm_lt_one (h := 2) (by norm_num) hq1 hq0
    have hd := Function.Periodic.differentiableAt_cuspFunction (h := 2) (by norm_num)
      (periodic_thetaPowerPeriodic a) (differentiableAt_thetaPowerPeriodic a hz)
    rwa [Function.Periodic.qParam_right_inv (by norm_num) hq0] at hd

/-- The Fourier coefficients `b_n` of `F_a`. -/
def thetaPowerCoeff (a : ℝ) (n : ℕ) : ℂ :=
  (cauchyPowerSeries (thetaPowerCusp a) 0 (1 / 2 : ℝ)).coeff n

theorem hasFPowerSeriesOnBall_thetaPowerCusp (ha : 0 ≤ a) {R : NNReal} (hR0 : 0 < R) (hR1 : (R : ℝ) < 1) :
    HasFPowerSeriesOnBall (thetaPowerCusp a) (cauchyPowerSeries (thetaPowerCusp a) 0 (1 / 2 : ℝ)) 0 R := by
  have hsub : ∀ {S : NNReal}, (S : ℝ) < 1 → Metric.closedBall (0 : ℂ) S ⊆ Metric.ball 0 1 :=
    fun hS => Metric.closedBall_subset_ball hS
  have hR := (differentiableOn_thetaPowerCusp ha).mono (hsub hR1) |>.hasFPowerSeriesOnBall hR0
  set S : NNReal := ⟨1 / 2, by norm_num⟩ with hS
  have hS0 : 0 < S := by rw [hS]; exact_mod_cast (show (0 : ℝ) < 1 / 2 by norm_num)
  have hS1 : (S : ℝ) < 1 := by show (1 / 2 : ℝ) < 1; norm_num
  have hS' := (differentiableOn_thetaPowerCusp ha).mono (hsub hS1) |>.hasFPowerSeriesOnBall hS0
  have heq := hR.hasFPowerSeriesAt.eq_formalMultilinearSeries hS'.hasFPowerSeriesAt
  have hScoe : ((S : NNReal) : ℝ) = 1 / 2 := by rw [hS]; rfl
  rw [heq, hScoe] at hR
  exact hR

/-- **Power series of the cusp function.** -/
theorem hasSum_thetaPowerCusp (ha : 0 ≤ a) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => thetaPowerCoeff a n * q ^ n) (thetaPowerCusp a q) := by
  set r : ℝ := (‖q‖ + 1) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hqr : ‖q‖ < r := by rw [hr]; linarith
  set R : NNReal := ⟨r, hr0.le⟩
  have hP := hasFPowerSeriesOnBall_thetaPowerCusp ha (R := R) (by exact_mod_cast hr0) hr1
  have hmem : q ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.mem_eball, edist_zero_right]
    exact_mod_cast hqr
  have hs := hP.hasSum hmem
  rw [zero_add] at hs
  refine hs.congr_fun (fun n => ?_)
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  rfl

/-- `Σ ‖b_n‖ r^n < ∞` for `r < 1`. -/
theorem summable_norm_thetaPowerCoeff_mul_pow (ha : 0 ≤ a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n => ‖thetaPowerCoeff a n‖ * r ^ n := by
  set s : ℝ := (r + 1) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s < 1 := by rw [hs]; linarith
  set S : NNReal := ⟨s, hs0.le⟩
  have hP := hasFPowerSeriesOnBall_thetaPowerCusp ha (R := S) (by exact_mod_cast hs0) hs1
  set R : NNReal := ⟨r, hr0⟩
  have hRlt : (R : ENNReal) < (cauchyPowerSeries (thetaPowerCusp a) 0 (1 / 2 : ℝ)).radius := by
    refine lt_of_lt_of_le ?_ hP.r_le
    exact_mod_cast (show r < s by rw [hs]; linarith)
  have h := FormalMultilinearSeries.summable_norm_mul_pow _ hRlt
  refine h.congr (fun n => ?_)
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
  rfl

/-- **Fourier expansion.** `F_a(τ) = Σ b_n e^{πi(n+a/4)τ}` on `ℍ`. -/
theorem hasSum_thetaPowerForm (ha : 0 ≤ a) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => thetaPowerCoeff a n * Complex.exp (π * I * ((n : ℂ) + ((a / 4 : ℝ) : ℂ)) * τ))
      (thetaPowerForm a τ) := by
  set q : ℂ := Function.Periodic.qParam 2 τ with hq
  have hqn : ‖q‖ < 1 := by
    rw [hq, Function.Periodic.norm_qParam]
    rw [Real.exp_lt_one_iff]
    have := Real.pi_pos
    have : 0 < 2 * π * τ.im / 2 := by positivity
    linarith [show -2 * π * τ.im / 2 = -(2 * π * τ.im / 2) by ring]
  have hs := hasSum_thetaPowerCusp ha hqn
  have hcusp : thetaPowerCusp a q = thetaPowerPeriodic a τ := by
    rw [hq]; exact Function.Periodic.eq_cuspFunction (by norm_num) (periodic_thetaPowerPeriodic a) τ
  rw [hcusp, thetaPowerPeriodic_of_im_pos a hτ] at hs
  have hs' := hs.mul_left (Complex.exp (π * I * ((a / 4 : ℝ) : ℂ) * τ))
  have hcancel : Complex.exp (π * I * ((a / 4 : ℝ) : ℂ) * τ) *
      (Complex.exp (-(π * I * ((a / 4 : ℝ) : ℂ) * τ)) * thetaPowerForm a τ) = thetaPowerForm a τ := by
    rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  rw [hcancel] at hs'
  refine hs'.congr_fun (fun n => ?_)
  have hqpow : q ^ n = Complex.exp (π * I * (n : ℂ) * τ) := by
    rw [hq, Function.Periodic.qParam, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hqpow]
  have : π * I * ((n : ℂ) + ((a / 4 : ℝ) : ℂ)) * τ =
      π * I * ((a / 4 : ℝ) : ℂ) * τ + π * I * (n : ℂ) * τ := by ring
  rw [this, Complex.exp_add]; ring

end

end RHTower
