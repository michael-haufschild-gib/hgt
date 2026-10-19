import GaloisForLFunctions.RHTower.JointAncestryLogBudgetProducer

/-!
# An endpoint arithmetic budget for the native JAS source

The source weights remain `1 / (ρ * (1 - ρ))`. For every sufficiently large budget `B`,
all product tests are nonnegative if their primes exceed a positive `y` and
`16 · 10⁸ · B^(2/3) · (log B)^(8/3) ≤ log y`.

The cutoff `T = exp(2B)` retains the logarithmic correction in the native
Vinogradov–Korobov width. Below `T`, the effective prime budget is at most `1/B`;
above `T`, the weighted error is bounded by a linear polynomial times `exp(-B)`.
Both errors tend to zero. Constant vectors give the existing diagonal Bochner input.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Required logarithmic prime cutoff for an endpoint budget. -/
def jasEndpointPrimeLog (B : ℝ) : ℝ :=
  (16 * 10 ^ 8 : ℝ) * B ^ (2 / 3 : ℝ) * Real.log B ^ (8 / 3 : ℝ)

/-- The exact native VK width at the exponential height cutoff retains its log-log factor. -/
theorem jasEndpoint_width_lower {B : ℝ} (hB : 2 ≤ B) :
    B ^ (-(2 : ℝ) / 3) * Real.log B ^ (-(5 : ℝ) / 3) / (8 * 10 ^ 8) ≤
      vinogradovKorobovGaussianWidth (Real.exp (2 * B)) := by
  have hB0 : 0 < B := by linarith
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  have hlog : Real.log (2 * B) ≤ 2 * Real.log B := by
    rw [Real.log_mul (by norm_num) hB0.ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hB]
  have htwo : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(2 : ℝ) / 3) := by
    calc (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hfour : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-(5 : ℝ) / 3) := by
    calc (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hfirst : B ^ (-(2 : ℝ) / 3) / 2 ≤ (2 * B) ^ (-(2 : ℝ) / 3) := by
    rw [Real.mul_rpow (by norm_num) hB0.le]
    nlinarith [mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hB0.le (-(2 : ℝ) / 3))]
  have hsecond : Real.log B ^ (-(5 : ℝ) / 3) / 4 ≤
      Real.log (2 * B) ^ (-(5 : ℝ) / 3) := by
    calc Real.log B ^ (-(5 : ℝ) / 3) / 4
        ≤ (2 * Real.log B) ^ (-(5 : ℝ) / 3) := by
          rw [Real.mul_rpow (by norm_num) hlB.le]
          nlinarith [mul_le_mul_of_nonneg_right hfour
            (Real.rpow_nonneg hlB.le (-(5 : ℝ) / 3))]
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos
        (Real.log_pos (by linarith)) hlog (by norm_num)
  have hmul := mul_le_mul hfirst hsecond (by positivity)
    (Real.rpow_nonneg (by positivity) (-(2 : ℝ) / 3))
  unfold vinogradovKorobovGaussianWidth
  rw [Real.log_exp]
  linarith

/-- The arithmetic cutoff makes the low-zero prime budget at most `1/B`. -/
theorem jasEndpoint_low_budget {B y : ℝ} (hB : 2 ≤ B)
    (hcut : jasEndpointPrimeLog B ≤ Real.log y) :
    Real.exp (-(vinogradovKorobovGaussianWidth (Real.exp (2 * B)) * Real.log y)) * B ≤
      B⁻¹ := by
  have hB0 : 0 < B := by linarith
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  have hcut0 : 0 ≤ jasEndpointPrimeLog B := by unfold jasEndpointPrimeLog; positivity
  have heq : (B ^ (-(2 : ℝ) / 3) * Real.log B ^ (-(5 : ℝ) / 3) / (8 * 10 ^ 8)) *
      jasEndpointPrimeLog B = 2 * Real.log B := by
    unfold jasEndpointPrimeLog
    calc _ = 2 * (B ^ (-(2 : ℝ) / 3) * B ^ (2 / 3 : ℝ)) *
        (Real.log B ^ (-(5 : ℝ) / 3) * Real.log B ^ (8 / 3 : ℝ)) := by ring
      _ = 2 * Real.log B := by
        rw [← Real.rpow_add hB0, ← Real.rpow_add hlB]
        norm_num
  have hw0 : 0 ≤ vinogradovKorobovGaussianWidth (Real.exp (2 * B)) :=
    le_trans (by positivity) (jasEndpoint_width_lower hB)
  have hwidth : 2 * Real.log B ≤
      vinogradovKorobovGaussianWidth (Real.exp (2 * B)) * Real.log y := by
    rw [← heq]
    exact mul_le_mul (jasEndpoint_width_lower hB) hcut hcut0 hw0
  calc Real.exp (-(vinogradovKorobovGaussianWidth (Real.exp (2 * B)) * Real.log y)) * B
      ≤ Real.exp (-(2 * Real.log B)) * B :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hB0.le
    _ = B⁻¹ := by
      rw [show -(2 * Real.log B) = -Real.log B + -Real.log B by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log hB0]
      field_simp

/-- The two-sided native VK width is valid uniformly up to `exp(2B)` for all large budgets. -/
theorem eventually_jasEndpoint_zero_width :
    ∀ᶠ B : ℝ in atTop, ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ Real.exp (2 * B) →
      vinogradovKorobovGaussianWidth (Real.exp (2 * B)) ≤
        1 / 2 - |(q.1 : ℂ).re - 1 / 2| := by
  obtain ⟨t₀, -, ht₀, hvk⟩ := exists_xiZero_re_le_vinogradovKorobov
  obtain ⟨η₀, hη₀, hlow⟩ := exists_low_zero_width_at t₀
  have hheight : Tendsto (fun B : ℝ => Real.exp (2 * B)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  have hsmall := tendsto_vinogradovKorobovGaussianWidth.comp hheight
  filter_upwards [hsmall.eventually (ge_mem_nhds hη₀)] with B hB q hq
  simp only [Function.comp_apply] at hB
  rcases le_or_gt t₀ |(q.1 : ℂ).im| with ht | ht
  · have hup : (q.1 : ℂ).re ≤ 1 - vinogradovKorobovGaussianWidth |(q.1 : ℂ).im| := hvk q ht
    have hr := hvk (xiZeroCopyReflectEquiv q) (by
      show t₀ ≤ |((xiZeroCopyReflectEquiv q).1 : ℂ).im|
      rw [xiZeroCopy_reflect_val]; simpa [Complex.sub_im] using ht)
    change ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≤
      1 - vinogradovKorobovGaussianWidth |((xiZeroCopyReflectEquiv q).1 : ℂ).im| at hr
    rw [xiZeroCopy_reflect_val] at hr
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub,
      abs_neg] at hr
    have hw := vinogradovKorobovGaussianWidth_anti (ht₀.trans ht) hq
    have hab : |(q.1 : ℂ).re - 1 / 2| ≤
        1 / 2 - vinogradovKorobovGaussianWidth |(q.1 : ℂ).im| := by
      rw [abs_le]; constructor <;> linarith
    linarith
  · linarith [hlow q ht.le]

/-- At the endpoint cutoff, the high-zero error decays exponentially in the prime budget. -/
theorem eventually_jasEndpoint_tail :
    ∀ᶠ B : ℝ in atTop,
      (Real.exp B - 1) * (80 * (xiLineTwoLogDerivConstant +
        Real.log (3 * Real.exp (2 * B) + 4)) / Real.exp (2 * B)) ≤ poleSharpConstant / 2 := by
  have hΦ := poleSharpConstant_pos
  have hdecay : Tendsto (fun B : ℝ =>
      80 * ((|xiLineTwoLogDerivConstant| + Real.log 7) * Real.exp (-B) +
        2 * (B * Real.exp (-B)))) atTop (𝓝 0) := by
    have he : Tendsto (fun B : ℝ => Real.exp (-B)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have hbe : Tendsto (fun B : ℝ => B * Real.exp (-B)) atTop (𝓝 0) := by
      simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 one_pos
    simpa using ((he.const_mul (|xiLineTwoLogDerivConstant| + Real.log 7)).add
      (hbe.const_mul 2)).const_mul 80
  filter_upwards [hdecay.eventually (ge_mem_nhds (by positivity : 0 < poleSharpConstant / 2)),
    eventually_ge_atTop (0 : ℝ)] with B hdec hB
  have hT : 1 ≤ Real.exp (2 * B) := Real.one_le_exp (by positivity)
  have hlog : Real.log (3 * Real.exp (2 * B) + 4) ≤ Real.log 7 + 2 * B := by
    calc _ ≤ Real.log (7 * Real.exp (2 * B)) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hfactor : 80 * (xiLineTwoLogDerivConstant + Real.log (3 * Real.exp (2 * B) + 4)) /
      Real.exp (2 * B) ≤ 80 * (|xiLineTwoLogDerivConstant| + Real.log 7 + 2 * B) /
        Real.exp (2 * B) := by
    apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 80)
    linarith [le_abs_self xiLineTwoLogDerivConstant]
  have hnonneg : 0 ≤ 80 * (|xiLineTwoLogDerivConstant| + Real.log 7 + 2 * B) /
      Real.exp (2 * B) := by positivity
  calc _ ≤ (Real.exp B - 1) * (80 * (|xiLineTwoLogDerivConstant| + Real.log 7 + 2 * B) /
        Real.exp (2 * B)) := mul_le_mul_of_nonneg_left hfactor (by linarith [Real.one_le_exp hB])
    _ ≤ Real.exp B * (80 * (|xiLineTwoLogDerivConstant| + Real.log 7 + 2 * B) /
        Real.exp (2 * B)) := mul_le_mul_of_nonneg_right (by linarith) hnonneg
    _ = 80 * ((|xiLineTwoLogDerivConstant| + Real.log 7) * Real.exp (-B) +
        2 * (B * Real.exp (-B))) := by
      have he : Real.exp B / Real.exp (2 * B) = Real.exp (-B) := by
        rw [← Real.exp_sub]; congr 1; ring
      calc _ = 80 * (|xiLineTwoLogDerivConstant| + Real.log 7 + 2 * B) *
          (Real.exp B / Real.exp (2 * B)) := by ring
        _ = _ := by rw [he]; ring
    _ ≤ _ := hdec

/-- Unconditional endpoint positivity of the native source for arbitrary complex test vectors. -/
theorem eventually_jasProductPositive_endpointBudget :
    ∀ᶠ B : ℝ in atTop, ∀ (σ y : ℝ), 0 < y → jasEndpointPrimeLog B ≤ Real.log y →
      ∀ P : Finset Nat.Primes, (∀ p ∈ P, y < ((p : ℕ) : ℝ)) →
      ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ B →
      ∀ z : Nat.Primes → ℂ, 0 ≤ (∑' q : XiZeroCopy,
        (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
          (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  have hW := lagWeightTotal_pos
  have hΦ := poleSharpConstant_pos
  let t := Real.log (1 + poleSharpConstant / (2 * lagWeightTotal))
  have hquot : 0 < poleSharpConstant / (2 * lagWeightTotal) := by positivity
  have ht : 0 < t := Real.log_pos (by linarith)
  have hexpt : (Real.exp t - 1) * lagWeightTotal = poleSharpConstant / 2 := by
    rw [show Real.exp t = 1 + poleSharpConstant / (2 * lagWeightTotal) from
      Real.exp_log (by positivity)]
    field_simp
    ring
  filter_upwards [eventually_jasEndpoint_zero_width, eventually_jasEndpoint_tail,
    tendsto_inv_atTop_zero.eventually (ge_mem_nhds ht), eventually_ge_atTop (2 : ℝ)]
    with B hwidth htail hsmall hB σ y hy hcut P hP hbudget z
  have hB0 : 0 < B := by linarith
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  exact jasProductAggregate_re_nonneg_of_heightSplit hy
    (Real.one_le_exp (by linarith))
    (le_trans (by positivity) (jasEndpoint_width_lower hB)) P hP hbudget hwidth ht.le hexpt.le
    ((jasEndpoint_low_budget hB hcut).trans hsmall) htail z

/-- The endpoint arithmetic inequality feeds the existing constant-vector receiver unchanged. -/
theorem eventually_jasConstProductPositive_endpointBudget :
    ∀ᶠ B : ℝ in atTop, ∀ (σ y : ℝ), 0 < y → jasEndpointPrimeLog B ≤ Real.log y →
      ∀ P : Finset Nat.Primes, (∀ p ∈ P, y < ((p : ℕ) : ℝ)) →
      ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ B →
      JasConstProductPositiveOn P σ := by
  filter_upwards [eventually_jasProductPositive_endpointBudget] with B hB σ y hy hcut P hP hbudget z
  exact hB σ y hy hcut P hP hbudget (fun _ => z)

/-- The endpoint cutoff grows more slowly than every power with exponent above `2/3`. -/
theorem eventually_jasEndpointPrimeLog_lt_rpow {a : ℝ} (ha : 2 / 3 < a) :
    ∀ᶠ B : ℝ in atTop, jasEndpointPrimeLog B < B ^ a := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := a - 2 / 3) (8 / 3 : ℝ)
    (by linarith)).bound (by norm_num : (0 : ℝ) < 1 / (32 * 10 ^ 8))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with B hbound hB
  have hB0 : 0 < B := by linarith
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlB.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hB0.le _)] at hbound
  calc jasEndpointPrimeLog B
      ≤ (16 * 10 ^ 8 : ℝ) * B ^ (2 / 3 : ℝ) *
          (1 / (32 * 10 ^ 8) * B ^ (a - 2 / 3)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = B ^ a / 2 := by
      calc _ = (B ^ (2 / 3 : ℝ) * B ^ (a - 2 / 3)) / 2 := by ring
        _ = _ := by rw [← Real.rpow_add hB0]; congr 2; ring
    _ < B ^ a := by linarith [Real.rpow_pos_of_pos hB0 a]

/-- At the new cutoff, every previously available fixed log-power budget is strictly smaller. -/
theorem eventually_jasEndpoint_exceeds_logBudget {A : ℝ} (hA0 : 0 ≤ A) (hA : A < 3 / 2) :
    ∀ᶠ B : ℝ in atTop, jasEndpointPrimeLog B ^ A < B := by
  by_cases hzero : A = 0
  · simpa [hzero] using (eventually_gt_atTop (1 : ℝ))
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hzero)
  have ha : 2 / 3 < 1 / A := by rw [lt_div_iff₀ hApos]; linarith
  filter_upwards [eventually_jasEndpointPrimeLog_lt_rpow ha, eventually_ge_atTop (2 : ℝ)]
    with B hbound hB
  have hB0 : 0 < B := by linarith
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  have hcut0 : 0 ≤ jasEndpointPrimeLog B := by unfold jasEndpointPrimeLog; positivity
  calc jasEndpointPrimeLog B ^ A < (B ^ (1 / A)) ^ A :=
      Real.rpow_lt_rpow hcut0 hbound hApos
    _ = B := by rw [← Real.rpow_mul hB0.le, div_mul_cancel₀ _ hzero, Real.rpow_one]

/-- The native receiver is supplied on budgets strictly exceeding every fixed exponent
`A < 3/2`, at the same prime cutoff. -/
theorem eventually_jasConstProductPositive_beyond_logBudget {A : ℝ}
    (hA0 : 0 ≤ A) (hA : A < 3 / 2) :
    ∀ᶠ B : ℝ in atTop,
      Real.log (Real.exp (jasEndpointPrimeLog B)) ^ A < B ∧
      ∀ (σ : ℝ) (P : Finset Nat.Primes),
        (∀ p ∈ P, Real.exp (jasEndpointPrimeLog B) < ((p : ℕ) : ℝ)) →
        ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ B →
        JasConstProductPositiveOn P σ := by
  filter_upwards [eventually_jasEndpoint_exceeds_logBudget hA0 hA,
    eventually_jasConstProductPositive_endpointBudget] with B hstrict hpositive
  refine ⟨by simpa only [Real.log_exp] using hstrict, fun σ P hP hB => ?_⟩
  exact hpositive σ _ (Real.exp_pos _) (by rw [Real.log_exp]) P hP hB

/-- An explicit inverse endpoint budget, as a function of the logarithmic prime cutoff. -/
def jasEndpointBudgetAtLog (L : ℝ) : ℝ :=
  (L / (128 * 10 ^ 8)) ^ (3 / 2 : ℝ) / Real.log L ^ 4

/-- Exact cancellation of the powers in the endpoint budget. -/
theorem jasEndpointBudgetAtLog_cancel {L : ℝ} (hL : 1 < L) :
    jasEndpointBudgetAtLog L ^ (2 / 3 : ℝ) * Real.log L ^ (8 / 3 : ℝ) =
      L / (128 * 10 ^ 8) := by
  have hL0 : 0 < L := by linarith
  have hlL : 0 < Real.log L := Real.log_pos hL
  have hpow : (Real.log L ^ 4) ^ (2 / 3 : ℝ) = Real.log L ^ (8 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlL.le]
    norm_num
  rw [jasEndpointBudgetAtLog, Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num,
    Real.rpow_one, hpow, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hlL _).ne']

/-- The explicit inverse budget satisfies the arithmetic cutoff inequality. -/
theorem jasEndpointPrimeLog_budgetAtLog_le {L : ℝ} (hL : Real.exp 1 ≤ L)
    (hB : 2 ≤ jasEndpointBudgetAtLog L) :
    jasEndpointPrimeLog (jasEndpointBudgetAtLog L) ≤ L := by
  have hL1 : 1 < L := lt_of_lt_of_le (by simp) hL
  have hL0 : 0 < L := by linarith
  have hlL : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hL
  have hB0 : 0 < jasEndpointBudgetAtLog L := by linarith
  have hBsmall : jasEndpointBudgetAtLog L ≤ L ^ (3 / 2 : ℝ) := by
    unfold jasEndpointBudgetAtLog
    calc _ ≤ (L / (128 * 10 ^ 8)) ^ (3 / 2 : ℝ) :=
        div_le_self (by positivity) (one_le_pow₀ hlL)
      _ ≤ _ := Real.rpow_le_rpow (by positivity)
        (div_le_self hL0.le (by norm_num)) (by norm_num)
  have hlog : Real.log (jasEndpointBudgetAtLog L) ≤ 2 * Real.log L := by
    have hB2 : jasEndpointBudgetAtLog L ≤ L ^ (2 : ℝ) := hBsmall.trans
      (Real.rpow_le_rpow_of_exponent_le hL1.le (by norm_num))
    simpa only [Real.log_rpow hL0] using Real.log_le_log hB0 hB2
  have hpower : Real.log (jasEndpointBudgetAtLog L) ^ (8 / 3 : ℝ) ≤
      8 * Real.log L ^ (8 / 3 : ℝ) := by
    calc _ ≤ (2 * Real.log L) ^ (8 / 3 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog (by norm_num)
      _ = (2 : ℝ) ^ (8 / 3 : ℝ) * Real.log L ^ (8 / 3 : ℝ) :=
        Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
          calc (2 : ℝ) ^ (8 / 3 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 8 := by norm_num) (Real.rpow_nonneg (by linarith) _)
  calc jasEndpointPrimeLog (jasEndpointBudgetAtLog L)
      ≤ (16 * 10 ^ 8 : ℝ) * jasEndpointBudgetAtLog L ^ (2 / 3 : ℝ) *
          (8 * Real.log L ^ (8 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = (128 * 10 ^ 8 : ℝ) * (jasEndpointBudgetAtLog L ^ (2 / 3 : ℝ) *
        Real.log L ^ (8 / 3 : ℝ)) := by ring
    _ = L := by rw [jasEndpointBudgetAtLog_cancel hL1]; ring

/-- The explicit endpoint budget tends to infinity, with an eventual lower bound by `L`. -/
theorem eventually_le_jasEndpointBudgetAtLog :
    ∀ᶠ L : ℝ in atTop, L ≤ jasEndpointBudgetAtLog L := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) 4
    (by norm_num)).bound (by positivity : (0 : ℝ) < 1 / (128 * 10 ^ 8 : ℝ) ^ (3 / 2 : ℝ))
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with L hbound hL
  have hL0 : 0 < L := by linarith
  have hlL : 0 < Real.log L := Real.log_pos hL
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlL.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _), show (4 : ℝ) = (4 : ℕ) by norm_num,
    Real.rpow_natCast] at hbound
  unfold jasEndpointBudgetAtLog
  apply (le_div_iff₀ (pow_pos hlL _)).2
  calc L * Real.log L ^ 4 ≤ L * (1 / (128 * 10 ^ 8 : ℝ) ^ (3 / 2 : ℝ) *
      L ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hbound hL0.le
    _ = (L / (128 * 10 ^ 8)) ^ (3 / 2 : ℝ) := by
      rw [Real.div_rpow hL0.le (by norm_num)]
      have he : L ^ (3 / 2 : ℝ) = L ^ (1 / 2 : ℝ) * L := by
        convert Real.rpow_add_one hL0.ne' (1 / 2 : ℝ) using 1
        norm_num
      rw [he]; ring

/-- Native product positivity at the explicit budget
`((log y)/(128·10⁸))^(3/2)/(log log y)^4`, for every phase vector. -/
theorem eventually_jasProductPositive_logLogBudget :
    ∀ᶠ y : ℝ in atTop, ∀ (σ : ℝ) (P : Finset Nat.Primes),
      (∀ p ∈ P, y < ((p : ℕ) : ℝ)) →
      ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤
        jasEndpointBudgetAtLog (Real.log y) →
      ∀ z : Nat.Primes → ℂ, 0 ≤ (∑' q : XiZeroCopy,
        (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
          (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp eventually_jasProductPositive_endpointBudget
  filter_upwards [Real.tendsto_log_atTop.eventually eventually_le_jasEndpointBudgetAtLog,
    Real.tendsto_log_atTop.eventually_ge_atTop B₀,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually_ge_atTop 2, eventually_gt_atTop (0 : ℝ)]
    with y hlarge hB hL hL2 hy σ P hP hbudget z
  exact hB₀ _ (hB.trans hlarge) σ y hy
    (jasEndpointPrimeLog_budgetAtLog_le hL (hL2.trans hlarge)) P hP hbudget z

/-- The explicit log-log budget supplies the native constant-vector receiver. -/
theorem eventually_jasConstProductPositive_logLogBudget :
    ∀ᶠ y : ℝ in atTop, ∀ (σ : ℝ) (P : Finset Nat.Primes),
      (∀ p ∈ P, y < ((p : ℕ) : ℝ)) →
      ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤
        jasEndpointBudgetAtLog (Real.log y) → JasConstProductPositiveOn P σ := by
  filter_upwards [eventually_jasProductPositive_logLogBudget] with y hy σ P hP hbudget z
  exact hy σ P hP hbudget (fun _ => z)

end

end RHTower
