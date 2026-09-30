import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Actual theta-source Borel kernel

The all-order scalar score recurrence provides a compact factorial envelope.
Strict raw moment positivity gives positive Borel coefficients at every degree.
No reciprocal-moment sign or RH hypothesis is used.
-/

open Filter Topology Set
namespace RHTower
noncomputable section

/-- The positive coefficient in the actual raw-source Borel kernel. -/
def liEvenCrossActualClockBorelCoefficient (j : ℕ) : ℝ :=
  thetaCuspNormalizedEvenMoment j / ((2 * j).factorial : ℝ) ^ 2

/-- The actual raw theta-source Borel summand. -/
def liEvenCrossActualClockBorelTerm (t : ℝ) (j : ℕ) : ℝ :=
  thetaCuspNormalizedEvenMoment j * t ^ (2 * j) / ((2 * j).factorial : ℝ) ^ 2

/-- The actual raw-source Borel kernel. -/
def liEvenCrossActualClockBorelKernel (t : ℝ) : ℝ :=
  ∑' j, liEvenCrossActualClockBorelTerm t j

/-- The Borel kernel weighted by its exact even degree. -/
def liEvenCrossActualClockBorelWeighted (t : ℝ) : ℝ :=
  ∑' j : ℕ, (2 * j : ℝ) * liEvenCrossActualClockBorelTerm t j

theorem thetaCuspNormalizedEvenMoment_pos (j : ℕ) :
    0 < thetaCuspNormalizedEvenMoment j :=
  div_pos (thetaCuspRawEvenMoment_pos j) (thetaCuspRawEvenMoment_pos 0)

@[simp] theorem thetaCuspNormalizedEvenMoment_zero :
    thetaCuspNormalizedEvenMoment 0 = 1 := by
  exact div_self (thetaCuspRawEvenMoment_pos 0).ne'

/-- A factorial envelope from the actual all-order scalar score recurrence. -/
theorem thetaCuspNormalizedEvenMoment_le_score_factorial (j : ℕ) :
    thetaCuspNormalizedEvenMoment j ≤ (32 / 303 : ℝ) ^ j * (j.factorial : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hpos := (thetaCuspNormalizedEvenMoment_pos j).le
    have hscore := thetaCuspNormalizedEvenMoment_succ_le_score j
    have hstep : thetaCuspNormalizedEvenMoment (j + 1) ≤
        (32 / 303 : ℝ) * (j + 1 : ℝ) * thetaCuspNormalizedEvenMoment j := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_left ih
      (show 0 ≤ (32 / 303 : ℝ) * (j + 1 : ℝ) by positivity)
    calc
      thetaCuspNormalizedEvenMoment (j + 1) ≤
          (32 / 303 : ℝ) * (j + 1 : ℝ) * thetaCuspNormalizedEvenMoment j := hstep
      _ ≤ (32 / 303 : ℝ) * (j + 1 : ℝ) *
          ((32 / 303 : ℝ) ^ j * (j.factorial : ℝ)) := hm
      _ = (32 / 303 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) := by
        rw [pow_succ, Nat.factorial_succ]
        push_cast
        ring

theorem liEvenCrossActualClockBorelCoefficient_pos (j : ℕ) :
    0 < liEvenCrossActualClockBorelCoefficient j := by
  unfold liEvenCrossActualClockBorelCoefficient
  exact div_pos (thetaCuspNormalizedEvenMoment_pos j) (by positivity)

@[simp] theorem liEvenCrossActualClockBorelCoefficient_zero :
    liEvenCrossActualClockBorelCoefficient 0 = 1 := by
  simp [liEvenCrossActualClockBorelCoefficient]

theorem liEvenCrossActualClockBorelTerm_eq_coefficient_mul (t : ℝ) (j : ℕ) :
    liEvenCrossActualClockBorelTerm t j =
      liEvenCrossActualClockBorelCoefficient j * t ^ (2 * j) := by
  unfold liEvenCrossActualClockBorelTerm liEvenCrossActualClockBorelCoefficient
  ring

theorem liEvenCrossActualClockBorelCoefficient_le (j : ℕ) :
    liEvenCrossActualClockBorelCoefficient j ≤ (32 / 303 : ℝ) ^ j / (j.factorial : ℝ) := by
  have hf : (j.factorial : ℝ) ≤ ((2 * j).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show j ≤ 2 * j by omega)
  have hj : 0 < (j.factorial : ℝ) := by positivity
  have h2 : 0 < ((2 * j).factorial : ℝ) := by positivity
  unfold liEvenCrossActualClockBorelCoefficient
  calc
    thetaCuspNormalizedEvenMoment j / ((2 * j).factorial : ℝ) ^ 2 ≤
        ((32 / 303 : ℝ) ^ j * (j.factorial : ℝ)) / ((2 * j).factorial : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (thetaCuspNormalizedEvenMoment_le_score_factorial j)
        (sq_nonneg _)
    _ ≤ ((32 / 303 : ℝ) ^ j * (j.factorial : ℝ)) / (j.factorial : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hj.le hf 2)
    _ = (32 / 303 : ℝ) ^ j / (j.factorial : ℝ) := by
      field_simp

/-- Compact absolute envelope for the complete actual-source kernel. -/
theorem norm_liEvenCrossActualClockBorelTerm_le {t T : ℝ}
    (ht : |t| ≤ T) (j : ℕ) :
    ‖liEvenCrossActualClockBorelTerm t j‖ ≤
      ((32 / 303 : ℝ) * T ^ 2) ^ j / (j.factorial : ℝ) := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  rw [liEvenCrossActualClockBorelTerm_eq_coefficient_mul, norm_mul,
    Real.norm_eq_abs, abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j),
    norm_pow, Real.norm_eq_abs]
  calc
    liEvenCrossActualClockBorelCoefficient j * |t| ^ (2 * j) ≤
        ((32 / 303 : ℝ) ^ j / (j.factorial : ℝ)) * T ^ (2 * j) :=
      mul_le_mul (liEvenCrossActualClockBorelCoefficient_le j)
        (pow_le_pow_left₀ (abs_nonneg t) ht _)
        (pow_nonneg (abs_nonneg t) _) (by positivity)
    _ = ((32 / 303 : ℝ) * T ^ 2) ^ j / (j.factorial : ℝ) := by
      rw [mul_pow, ← pow_mul]
      ring

theorem summable_liEvenCrossActualClockBorelTerm (t : ℝ) :
    Summable (liEvenCrossActualClockBorelTerm t) := by
  exact (Real.summable_pow_div_factorial ((32 / 303 : ℝ) * |t| ^ 2)).of_norm_bounded
    (fun j => norm_liEvenCrossActualClockBorelTerm_le (le_refl |t|) j)

private theorem summable_degree_pow_div_factorial (r : ℝ) :
    Summable (fun j : ℕ => (2 * j : ℝ) * r ^ j / (j.factorial : ℝ)) := by
  apply (summable_nat_add_iff 1).1
  have h := (Real.summable_pow_div_factorial r).mul_left (2 * r)
  apply h.congr
  intro j
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hj : (j + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem summable_liEvenCrossActualClockBorelWeightedTerm (t : ℝ) :
    Summable (fun j : ℕ => (2 * j : ℝ) * liEvenCrossActualClockBorelTerm t j) := by
  apply (summable_degree_pow_div_factorial ((32 / 303 : ℝ) * |t| ^ 2)).of_norm_bounded
  intro j
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * j)]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
    (norm_liEvenCrossActualClockBorelTerm_le (le_refl |t|) j)
    (show (0 : ℝ) ≤ 2 * j by positivity)

@[simp] theorem liEvenCrossActualClockBorelTerm_zero_degree (t : ℝ) :
    liEvenCrossActualClockBorelTerm t 0 = 1 := by
  simp [liEvenCrossActualClockBorelTerm]

theorem liEvenCrossActualClockBorelTerm_nonneg (t : ℝ) (j : ℕ) :
    0 ≤ liEvenCrossActualClockBorelTerm t j := by
  rw [liEvenCrossActualClockBorelTerm_eq_coefficient_mul, pow_mul]
  exact mul_nonneg (liEvenCrossActualClockBorelCoefficient_pos j).le
    (pow_nonneg (sq_nonneg t) j)

theorem one_le_liEvenCrossActualClockBorelKernel (t : ℝ) :
    1 ≤ liEvenCrossActualClockBorelKernel t := by
  simpa only [liEvenCrossActualClockBorelKernel, liEvenCrossActualClockBorelTerm_zero_degree]
    using (summable_liEvenCrossActualClockBorelTerm t).le_tsum 0
      (fun j _ => liEvenCrossActualClockBorelTerm_nonneg t j)

theorem liEvenCrossActualClockBorelKernel_pos (t : ℝ) :
    0 < liEvenCrossActualClockBorelKernel t :=
  lt_of_lt_of_le zero_lt_one (one_le_liEvenCrossActualClockBorelKernel t)

@[simp] theorem liEvenCrossActualClockBorelKernel_zero :
    liEvenCrossActualClockBorelKernel 0 = 1 := by
  rw [liEvenCrossActualClockBorelKernel, tsum_eq_single 0]
  · simp
  · intro j hj
    have h : 2 * j ≠ 0 := by omega
    simp [liEvenCrossActualClockBorelTerm, h]

theorem liEvenCrossActualClockBorelKernel_mono {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    liEvenCrossActualClockBorelKernel a ≤ liEvenCrossActualClockBorelKernel b := by
  apply Summable.tsum_le_tsum _ (summable_liEvenCrossActualClockBorelTerm a)
    (summable_liEvenCrossActualClockBorelTerm b)
  intro j
  rw [liEvenCrossActualClockBorelTerm_eq_coefficient_mul,
    liEvenCrossActualClockBorelTerm_eq_coefficient_mul]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _)
    (liEvenCrossActualClockBorelCoefficient_pos j).le

theorem continuous_liEvenCrossActualClockBorelTerm (j : ℕ) :
    Continuous (fun t : ℝ => liEvenCrossActualClockBorelTerm t j) := by
  unfold liEvenCrossActualClockBorelTerm
  fun_prop

theorem continuous_liEvenCrossActualClockBorelKernel :
    Continuous liEvenCrossActualClockBorelKernel := by
  rw [continuous_iff_continuousAt]
  intro x
  let T : ℝ := |x| + 1
  have hc : ContinuousOn liEvenCrossActualClockBorelKernel (Metric.ball 0 T) := by
    apply continuousOn_tsum
      (fun j => (continuous_liEvenCrossActualClockBorelTerm j).continuousOn)
      (Real.summable_pow_div_factorial ((32 / 303 : ℝ) * T ^ 2))
    intro j t ht
    apply norm_liEvenCrossActualClockBorelTerm_le
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using ht)
  exact hc.continuousAt (Metric.isOpen_ball.mem_nhds
    (by simp [Metric.mem_ball, T]))


private def liEvenCrossActualClockBorelDerivTerm (t : ℝ) (j : ℕ) : ℝ :=
  liEvenCrossActualClockBorelCoefficient j * (2 * j : ℝ) * t ^ (2 * j - 1)

private theorem norm_borelDerivTerm_le {t T : ℝ} (hT : 1 ≤ T)
    (ht : |t| ≤ T) (j : ℕ) :
    ‖liEvenCrossActualClockBorelDerivTerm t j‖ ≤
      (2 * j : ℝ) * ((32 / 303 : ℝ) * T ^ 2) ^ j / (j.factorial : ℝ) := by
  have hpow : |t| ^ (2 * j - 1) ≤ T ^ (2 * j) :=
    (pow_le_pow_left₀ (abs_nonneg t) ht _).trans
      (pow_le_pow_right₀ hT (Nat.sub_le _ _))
  rw [liEvenCrossActualClockBorelDerivTerm, norm_mul, norm_mul, norm_pow,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * j), Real.norm_eq_abs]
  calc
    liEvenCrossActualClockBorelCoefficient j * (2 * j : ℝ) * |t| ^ (2 * j - 1) ≤
        ((32 / 303 : ℝ) ^ j / (j.factorial : ℝ)) * (2 * j : ℝ) * T ^ (2 * j) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (liEvenCrossActualClockBorelCoefficient_le j)
          (by positivity)
      · exact hpow
      · positivity
      · positivity
    _ = (2 * j : ℝ) * ((32 / 303 : ℝ) * T ^ 2) ^ j / (j.factorial : ℝ) := by
      rw [mul_pow, ← pow_mul]
      ring

/-- The entire Borel kernel can be differentiated termwise at each real argument. -/
theorem hasDerivAt_liEvenCrossActualClockBorelKernel (t : ℝ) :
    HasDerivAt liEvenCrossActualClockBorelKernel
      (∑' j, liEvenCrossActualClockBorelCoefficient j * (2 * j : ℝ) *
        t ^ (2 * j - 1)) t := by
  let T : ℝ := |t| + 1
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hg (j : ℕ) (y : ℝ) (_ : y ∈ Metric.ball 0 T) :
      HasDerivAt (fun z => liEvenCrossActualClockBorelTerm z j)
        (liEvenCrossActualClockBorelDerivTerm y j) y := by
    simpa only [liEvenCrossActualClockBorelTerm_eq_coefficient_mul,
      liEvenCrossActualClockBorelDerivTerm, Pi.pow_apply, id_eq, mul_one, Nat.cast_mul,
      Nat.cast_ofNat, mul_assoc]
      using ((hasDerivAt_id y).pow (2 * j)).const_mul
        (liEvenCrossActualClockBorelCoefficient j)
  exact hasDerivAt_tsum_of_isPreconnected
    (summable_degree_pow_div_factorial ((32 / 303 : ℝ) * T ^ 2))
    Metric.isOpen_ball (convex_ball (0 : ℝ) T).isPreconnected hg
    (fun j y hy => norm_borelDerivTerm_le hT
      (le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hy)) j)
    (by simp [Metric.mem_ball, T]; positivity)
    (summable_liEvenCrossActualClockBorelTerm 0)
    (by simp [Metric.mem_ball, T])

/-- Exact weighted-degree identity, including the origin. -/
theorem liEvenCrossActualClockBorel_mul_deriv (t : ℝ) :
    t * deriv liEvenCrossActualClockBorelKernel t =
      liEvenCrossActualClockBorelWeighted t := by
  rw [(hasDerivAt_liEvenCrossActualClockBorelKernel t).deriv,
    liEvenCrossActualClockBorelWeighted, ← tsum_mul_left]
  apply tsum_congr
  intro j
  by_cases hj : j = 0
  · simp [hj]
  · have hdegree : 1 ≤ 2 * j := by omega
    rw [liEvenCrossActualClockBorelTerm_eq_coefficient_mul]
    have hp : t * t ^ (2 * j - 1) = t ^ (2 * j) := by
      rw [← pow_succ', Nat.sub_add_cancel hdegree]
    calc
      t * (liEvenCrossActualClockBorelCoefficient j * (2 * j : ℝ) *
          t ^ (2 * j - 1)) =
          (2 * j : ℝ) * liEvenCrossActualClockBorelCoefficient j *
            (t * t ^ (2 * j - 1)) := by ring
      _ = (2 * j : ℝ) * (liEvenCrossActualClockBorelCoefficient j *
          t ^ (2 * j)) := by rw [hp]; ring

end
end RHTower
