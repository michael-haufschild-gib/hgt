import GaloisForLFunctions.RHTower.LiEvenCrossActualClockCausalHistory
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# Origin normalization of the causal history

With `b = K'(0) = ν₁/2`, `k₁ = ν₂/144` the cubic Taylor coefficient of `K`, `a = 49/21816`,
`A = Σ_q |w_q|²` and `M₀ = ν₁`, `M₁ = ν₁²/2 - ν₂/6` the first normalized prime-arch moments:

* `K'(t) ≥ b` for every `t`;
* `|D(T)| ≤ (A/4) e^{βT} T²` for `T ≥ 0`;
* `0 ≤ K(s) - bs - k₁s³ ≤ b a² s⁵ e^{as²}` for `s ≥ 0`;
* every history row has the leading term `N_n(T) = b^{n+1}T^{2n+2}/((n+1)(2n+2)!) + O(T^{2n+4})`
  on `[0,1]`;
* `N_0(T) - N_1(T) = (M₀/4)T² - (M₁/96)T⁴ + O(T⁶)` on `[0,1]`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "K" => liClockThetaKernel
local notation "K'" => liClockThetaKernelDeriv
local notation "b₀" => liClockThetaKernelDeriv 0
local notation "D" => liEvenCrossActualClockLogHistory
local notation "β" => liEvenCrossActualClockMaxGrowthRate
local notation "W" => liClockHistoryCumulative
local notation "N" => liClockHistoryIntegratedRow
local notation "k" => liClockThetaKernelTaylorCoeff

/-- `K'(t) ≥ K'(0) = b` for every `t`. -/
theorem liClockThetaKernelDeriv_zero_le (t : ℝ) : b₀ ≤ K' t := by
  have hs := (summable_evenFactorialSeries_term (by norm_num)
    geometricCoeffBound_liClockThetaKernelCoeff t).hasSum
  have h := le_hasSum hs 0 fun j _ => by
    have := (liClockThetaGeneratorCoeff_pos (j + 1)).le
    rw [pow_mul]; positivity
  simp only [mul_zero, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one,
    zero_add] at h
  rw [liClockThetaKernelDeriv_zero, ← liClockThetaGeneratorCoeff_one]
  unfold liClockThetaKernelDeriv evenFactorialSeries
  exact h

/-- `|D(T)| ≤ (A/4) e^{βT} T²` for `T ≥ 0`. -/
theorem abs_liEvenCrossActualClockLogHistory_le {T : ℝ} (hT : 0 ≤ T) :
    |D T| ≤ xiShiftAbsoluteMass 0 / 4 * Real.exp (β * T) * T ^ 2 := by
  have hc := continuous_liEvenCrossActualClockLogHistoryDensity
  unfold liEvenCrossActualClockLogHistory
  refine (intervalIntegral.abs_integral_le_integral_abs hT).trans ?_
  refine (intervalIntegral.integral_mono_on hT (hc.abs.intervalIntegrable 0 T)
    ((by fun_prop : Continuous fun t : ℝ =>
      xiShiftAbsoluteMass 0 / 2 * Real.exp (β * T) * t).intervalIntegrable 0 T)
    fun t ht => ?_).trans_eq ?_
  · unfold liEvenCrossActualClockLogHistoryDensity
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0; simp
    · rw [abs_div, abs_of_pos h0, div_le_iff₀ h0]
      have h1 := abs_liEvenCrossActualClockPrimitive_le_sq_of_mem ht
      have e : xiShiftAbsoluteMass 0 / 2 * Real.exp (β * T) * t * t =
          xiShiftAbsoluteMass 0 / 2 * Real.exp (β * T) * t ^ 2 := by ring
      linarith
  · rw [intervalIntegral.integral_const_mul, integral_id]
    ring

/-- `0 ≤ K(s) - bs - k₁s³ ≤ b a² s⁵ e^{as²}` for `s ≥ 0`. -/
theorem liClockThetaKernel_sub_cubic_bounds {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ K s - b₀ * s - k 1 * s ^ 3 ∧
      K s - b₀ * s - k 1 * s ^ 3 ≤ b₀ * (49 / 21816) ^ 2 * s ^ 5 * Real.exp (49 / 21816 * s ^ 2) := by
  have hb := liClockThetaKernelDeriv_zero_pos
  have htail := (hasSum_nat_add_iff' 2).2 (hasSum_liClockThetaKernelTaylorCoeff s)
  have e : K s - ∑ i ∈ Finset.range 2, k i * s ^ (2 * i + 1) = K s - b₀ * s - k 1 * s ^ 3 := by
    simp [Finset.sum_range_succ, liClockThetaKernelTaylorCoeff_zero]
    ring
  rw [e] at htail
  refine ⟨htail.nonneg fun r => mul_nonneg (liClockThetaKernelTaylorCoeff_pos _).le
    (pow_nonneg hs _), ?_⟩
  have hexp : HasSum (fun r : ℕ => b₀ * (49 / 21816) ^ 2 * s ^ 5 *
      ((49 / 21816 * s ^ 2) ^ r / (r.factorial : ℝ)))
      (b₀ * (49 / 21816) ^ 2 * s ^ 5 * Real.exp (49 / 21816 * s ^ 2)) := by
    have h : HasSum (fun r : ℕ => (49 / 21816 * s ^ 2) ^ r / (r.factorial : ℝ))
        (Real.exp (49 / 21816 * s ^ 2)) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
    exact h.mul_left _
  refine hasSum_le (fun r => ?_) htail hexp
  have h1 := mul_le_mul_of_nonneg_right (liClockThetaKernelTaylorCoeff_le (r + 2))
    (pow_nonneg hs (2 * (r + 2) + 1))
  refine h1.trans ?_
  have hfac : (r.factorial : ℝ) ≤ ((r + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hpos : 0 ≤ b₀ * (49 / 21816 : ℝ) ^ (r + 2) * s ^ (2 * (r + 2) + 1) := by positivity
  calc b₀ * (49 / 21816 : ℝ) ^ (r + 2) / ((r + 2).factorial : ℝ) * s ^ (2 * (r + 2) + 1)
      = b₀ * (49 / 21816 : ℝ) ^ (r + 2) * s ^ (2 * (r + 2) + 1) / ((r + 2).factorial : ℝ) := by
        ring
    _ ≤ b₀ * (49 / 21816 : ℝ) ^ (r + 2) * s ^ (2 * (r + 2) + 1) / (r.factorial : ℝ) :=
        div_le_div_of_nonneg_left hpos (by positivity) hfac
    _ = b₀ * (49 / 21816) ^ 2 * s ^ 5 * ((49 / 21816 * s ^ 2) ^ r / (r.factorial : ℝ)) := by
        rw [mul_pow, ← pow_mul]
        ring

private theorem exp_sub_one_le {x : ℝ} : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos x]

/-- **Leading term of every row.**
`0 ≤ N_n(T) - b^{n+1}T^{2n+2}/((n+1)(2n+2)!) ≤ C T^{2n+4}` on `[0,1]`. -/
theorem liClockHistoryIntegratedRow_origin (n : ℕ) :
    ∃ C, ∀ T ∈ Icc (0 : ℝ) 1,
      0 ≤ N n T - b₀ ^ (n + 1) * T ^ (2 * n + 2) / ((n + 1) * ((2 * n + 2).factorial : ℝ)) ∧
      N n T - b₀ ^ (n + 1) * T ^ (2 * n + 2) / ((n + 1) * ((2 * n + 2).factorial : ℝ)) ≤
        C * T ^ (2 * n + 4) := by
  have hb := liClockThetaKernelDeriv_zero_pos
  set a : ℝ := 49 / 21816
  set F : ℝ := (n + 1) * ((2 * n + 2).factorial : ℝ)
  have hF : 0 < F := by positivity
  refine ⟨a * Real.exp a * (b₀ ^ (n + 1) / F), fun T hT => ?_⟩
  have hlow := liClockHistoryCumulative_ge n hT.1
  have hup := liClockHistoryCumulative_le_exp (c := a) (by positivity) hT.1
    (fun s hs => liClockThetaKernel_le_mul_exp hs.1) n
  rw [liClockHistoryIntegratedRow_eq]
  set L := b₀ ^ (n + 1) * T ^ (2 * n + 2) / F
  have eL : b₀ ^ (n + 1) * (T ^ (2 * n + 2) / ((2 * n + 2).factorial : ℝ)) / (n + 1) = L := by
    simp only [L, F]; field_simp
  have hT0 : 0 ≤ T := hT.1
  have hL : 0 ≤ L := by positivity
  have h1 : L ≤ W n T / (n + 1) := by
    rw [← eL]; exact div_le_div_of_nonneg_right hlow (by positivity)
  have h2 : W n T / (n + 1) ≤ Real.exp (a * T ^ 2) * L := by
    rw [← eL, ← mul_div_assoc]; exact div_le_div_of_nonneg_right hup (by positivity)
  refine ⟨by linarith, ?_⟩
  have hT2 : T ^ 2 ≤ 1 := by nlinarith [hT.1, hT.2]
  have hexp : Real.exp (a * T ^ 2) - 1 ≤ a * Real.exp a * T ^ 2 := by
    refine exp_sub_one_le.trans ?_
    have : Real.exp (a * T ^ 2) ≤ Real.exp a :=
      Real.exp_le_exp.2 (by nlinarith [show (0 : ℝ) < a by positivity])
    nlinarith [show (0 : ℝ) ≤ a * T ^ 2 by positivity]
  have hLT : L = b₀ ^ (n + 1) / F * T ^ (2 * n + 2) := by simp only [L]; ring
  calc W n T / (n + 1) - L ≤ (Real.exp (a * T ^ 2) - 1) * L := by linarith
    _ ≤ a * Real.exp a * T ^ 2 * L := mul_le_mul_of_nonneg_right hexp hL
    _ = a * Real.exp a * (b₀ ^ (n + 1) / F) * T ^ (2 * n + 4) := by rw [hLT]; ring

/-- **Two-term origin law.**  `N_0(T) - N_1(T) = (M₀/4)T² - (M₁/96)T⁴ + O(T⁶)` on `[0,1]`. -/
theorem liClockHistoryIntegratedRow_zero_sub_one_origin :
    ∃ C, ∀ T ∈ Icc (0 : ℝ) 1,
      |N 0 T - N 1 T - (normalizedPrimeArchMoment 0 / 4 * T ^ 2 -
        normalizedPrimeArchMoment 1 / 96 * T ^ 4)| ≤ C * T ^ 6 := by
  have hb := liClockThetaKernelDeriv_zero_pos
  have hKc := continuous_liClockThetaKernel
  obtain ⟨C₁, hC₁⟩ := liClockHistoryIntegratedRow_origin 1
  set a : ℝ := 49 / 21816
  set C₀ := b₀ * a ^ 2 * Real.exp a / 6
  refine ⟨C₀ + C₁, fun T hT => ?_⟩

  have hE0 : 0 ≤ N 0 T - (b₀ * (T ^ 2 / 2) + k 1 * (T ^ 4 / 4)) ∧
      N 0 T - (b₀ * (T ^ 2 / 2) + k 1 * (T ^ 4 / 4)) ≤ C₀ * T ^ 6 := by
    have hint : ∫ s in (0 : ℝ)..T, (K s - b₀ * s - k 1 * s ^ 3) =
        N 0 T - (b₀ * (T ^ 2 / 2) + k 1 * (T ^ 4 / 4)) := by
      rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun s => K s - b₀ * s).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun s : ℝ => k 1 * s ^ 3).intervalIntegrable _ _),
        intervalIntegral.integral_sub (hKc.intervalIntegrable _ _)
          ((by fun_prop : Continuous fun s : ℝ => b₀ * s).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
        integral_pow, liClockHistoryIntegratedRow_eq]
      have : W 0 T = ∫ s in (0 : ℝ)..T, K s := rfl
      rw [this]
      push_cast
      ring
    rw [← hint]
    constructor
    · exact intervalIntegral.integral_nonneg hT.1 fun s hs =>
        (liClockThetaKernel_sub_cubic_bounds hs.1).1
    · refine (intervalIntegral.integral_mono_on hT.1
        ((by fun_prop : Continuous fun s => K s - b₀ * s - k 1 * s ^ 3).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun s : ℝ => b₀ * a ^ 2 * Real.exp a * s ^ 5).intervalIntegrable
          _ _) fun s hs => ?_).trans_eq ?_
      · refine (liClockThetaKernel_sub_cubic_bounds hs.1).2.trans ?_
        have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2, hT.2]
        have : Real.exp (a * s ^ 2) ≤ Real.exp a :=
          Real.exp_le_exp.2 (mul_le_of_le_one_right (by positivity) hs2)
        have h5 : 0 ≤ b₀ * a ^ 2 * s ^ 5 := by have := hs.1; positivity
        calc b₀ * a ^ 2 * s ^ 5 * Real.exp (a * s ^ 2) ≤ b₀ * a ^ 2 * s ^ 5 * Real.exp a :=
              mul_le_mul_of_nonneg_left this h5
          _ = b₀ * a ^ 2 * Real.exp a * s ^ 5 := by ring
      · rw [intervalIntegral.integral_const_mul, integral_pow]
        simp only [C₀]
        ring
  obtain ⟨hE1a, hE1b⟩ := hC₁ T hT
  have hb2 : b₀ ^ (1 + 1) * T ^ (2 * 1 + 2) / ((((1 : ℕ) : ℝ) + 1) * ((2 * 1 + 2).factorial : ℝ)) =
      b₀ ^ 2 * T ^ 4 / 48 := by
    norm_num [Nat.factorial]
  have h6 : T ^ (2 * 1 + 4) = T ^ 6 := by norm_num
  rw [hb2] at hE1a hE1b
  rw [h6] at hE1b
  have hM : normalizedPrimeArchMoment 0 / 4 * T ^ 2 - normalizedPrimeArchMoment 1 / 96 * T ^ 4 =
      b₀ * (T ^ 2 / 2) + k 1 * (T ^ 4 / 4) - b₀ ^ 2 * T ^ 4 / 48 := by
    rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
      normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment, liClockThetaKernelDeriv_zero]
    simp only [liClockThetaKernelTaylorCoeff, liClockThetaGeneratorCoeff]
    norm_num [Nat.factorial]
    ring
  rw [hM, abs_le]
  have hT6 : 0 ≤ T ^ 6 := by have := hT.1; positivity
  have hC0 : 0 ≤ C₀ := by positivity
  constructor <;> nlinarith [hE0.1, hE0.2, hE1a, hE1b]

end RHTower
