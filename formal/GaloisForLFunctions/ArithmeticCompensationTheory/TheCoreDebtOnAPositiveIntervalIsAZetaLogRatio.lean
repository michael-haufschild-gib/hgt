import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheCoreDebtIsThePrimeHarmonicSeries
import GaloisForLFunctions.RHTower.LiClockThetaReciprocalEulerCoefficients

/-!
# On a positive damping interval the core debt is a ratio of zeta values

The explicit positive core of the signed damping work integrates, by scales, to
`∫_η^ε core_x(T) dx = Σ_{j ≤ T} (Λ(j)/log j)(j^{−η} − j^{−ε})(1/j − 1/(T+1))`
(`ArithmeticContinuationAndCriticalEnergy.integral_workCore_eq_scaleSum`), and on `[0, ε]` it is
unbounded in the horizon, at the rate of the prime harmonic series
(`exists_horizon_integral_workCore_ge`). That divergence is an endpoint effect. On an interval
`[η, ε]` with `η > 0` every scale term is dominated by the absolutely convergent Euler logarithm,
and the horizon limit is exact:

`lim_{T→∞} ∫_η^ε core_x(T) dx = log ζ(1+η) − log ζ(1+ε)`  (`tendsto_integral_workCore_logZeta`),

with the horizon-free bound `∫_η^ε core_x(T) dx ≤ log ζ(1+η) − log ζ(1+ε)` for every `T` when
`η ≤ ε` (`integral_workCore_le_logZeta`). Admission at a positive damping allows constants that
depend on the damping, so the core debt alone does not obstruct continuation on positive intervals:
it is the deviation of the source and its normalization that remain to be controlled there.
-/

open Filter Topology Finset MeasureTheory RHTower
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-- The scale term `(Λ(j)/log j)(j^{−η} − j^{−ε})(1/j − 1/(T+1))`, extended by `0` beyond `T`. -/
def coreScaleTerm (η ε : ℝ) (T j : ℕ) : ℝ :=
  if j ∈ Icc 1 T then ArithmeticFunction.vonMangoldt j *
    (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) * (1 / (j : ℝ) - 1 / ((T : ℝ) + 1)) else 0

/-- The horizon-free scale term `(Λ(j)/log j)(j^{−1−η} − j^{−1−ε})`. -/
def coreScaleLimit (η ε : ℝ) (j : ℕ) : ℝ :=
  eulerLogCoeffReal j * (((j : ℝ) ^ (1 + η))⁻¹ - ((j : ℝ) ^ (1 + ε))⁻¹)

theorem integral_workCore_eq_tsum (η ε : ℝ) (T : ℕ) :
    (∫ x in η..ε, workCore x T) = ∑' j, coreScaleTerm η ε T j := by
  rw [integral_workCore_eq_scaleSum, tsum_eq_sum (s := Icc 1 T)]
  · exact sum_congr rfl fun j hj => by rw [coreScaleTerm, if_pos hj]
  · intro j hj; rw [coreScaleTerm, if_neg hj]

/-- At a positive scale the limit term is the scale coefficient divided by the scale. -/
theorem coreScaleLimit_eq {η ε : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    coreScaleLimit η ε j = ArithmeticFunction.vonMangoldt j *
      (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) * (1 / (j : ℝ)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hpow : ∀ s : ℝ, ((j : ℝ) ^ (1 + s))⁻¹ = (j : ℝ) ^ (-s) * (1 / (j : ℝ)) := fun s => by
    rw [Real.rpow_add hj0, Real.rpow_one, Real.rpow_neg hj0.le]; field_simp
  rw [coreScaleLimit, eulerLogCoeffReal, hpow, hpow]
  ring

theorem tendsto_coreScaleTerm (η ε : ℝ) (j : ℕ) :
    Tendsto (fun T : ℕ => coreScaleTerm η ε T j) atTop (𝓝 (coreScaleLimit η ε j)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h0 : coreScaleLimit η ε 0 = 0 := by simp [coreScaleLimit, eulerLogCoeffReal]
    rw [h0]
    exact tendsto_const_nhds.congr fun T => by simp [coreScaleTerm]
  · rw [coreScaleLimit_eq hj]
    have hinv : Tendsto (fun T : ℕ => 1 / ((T : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := (tendsto_const_nhds (x := 1 / (j : ℝ))).sub hinv
    rw [sub_zero] at h
    refine (h.const_mul (ArithmeticFunction.vonMangoldt j *
      (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j))).congr' ?_
    filter_upwards [eventually_ge_atTop j] with T hT
    rw [coreScaleTerm, if_pos (mem_Icc.mpr ⟨hj, hT⟩)]

/-- The Euler-logarithm majorant `(Λ(j)/log j)(j^{−1−η} + j^{−1−ε})`. -/
def coreScaleBound (η ε : ℝ) (j : ℕ) : ℝ :=
  eulerLogCoeffReal j * (((j : ℝ) ^ (1 + η))⁻¹ + ((j : ℝ) ^ (1 + ε))⁻¹)

theorem hasSum_eulerLog {s : ℝ} (hs : 0 < s) :
    HasSum (fun j : ℕ => eulerLogCoeffReal j * ((j : ℝ) ^ (1 + s))⁻¹)
      (Real.log (riemannZeta ((1 + s : ℝ) : ℂ)).re) :=
  log_riemannZeta_ofReal_hasSum (by linarith)

theorem abs_coreScaleTerm_le (η ε : ℝ) (T j : ℕ) :
    |coreScaleTerm η ε T j| ≤ coreScaleBound η ε j := by
  have hc0 := eulerLogCoeffReal_nonneg j
  have hB : 0 ≤ coreScaleBound η ε j := mul_nonneg hc0 (by positivity)
  by_cases hj : j ∈ Icc 1 T
  · obtain ⟨hj1, hjT⟩ := mem_Icc.mp hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hfac0 : 0 ≤ 1 / (j : ℝ) - 1 / ((T : ℝ) + 1) := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hj0 (by exact_mod_cast (show j ≤ T + 1 by omega))
    have hfac1 : 1 / (j : ℝ) - 1 / ((T : ℝ) + 1) ≤ 1 / (j : ℝ) := by
      have : 0 ≤ 1 / ((T : ℝ) + 1) := by positivity
      linarith
    rw [coreScaleTerm, if_pos hj, abs_mul, abs_of_nonneg hfac0]
    have hlim : |ArithmeticFunction.vonMangoldt j *
        (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j)| * (1 / (j : ℝ)) =
        |coreScaleLimit η ε j| := by
      rw [coreScaleLimit_eq hj1, abs_mul _ (1 / (j : ℝ)), abs_of_pos (by positivity :
        (0 : ℝ) < 1 / (j : ℝ))]
    calc |ArithmeticFunction.vonMangoldt j * (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j)| *
          (1 / (j : ℝ) - 1 / ((T : ℝ) + 1))
        ≤ |ArithmeticFunction.vonMangoldt j *
            (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j)| * (1 / (j : ℝ)) :=
          mul_le_mul_of_nonneg_left hfac1 (abs_nonneg _)
      _ = |coreScaleLimit η ε j| := hlim
      _ ≤ coreScaleBound η ε j := by
          rw [coreScaleLimit, coreScaleBound, abs_mul, abs_of_nonneg hc0]
          refine mul_le_mul_of_nonneg_left ?_ hc0
          have h1 : 0 ≤ ((j : ℝ) ^ (1 + η))⁻¹ := by positivity
          have h2 : 0 ≤ ((j : ℝ) ^ (1 + ε))⁻¹ := by positivity
          rw [abs_le]; constructor <;> linarith
  · rw [coreScaleTerm, if_neg hj, abs_zero]; exact hB

/-- **The core debt on a positive interval is a zeta-log ratio.** For `η, ε > 0`,
`∫_η^ε core_x(T) dx → log ζ(1+η) − log ζ(1+ε)` as the horizon grows. -/
theorem tendsto_integral_workCore_logZeta {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    Tendsto (fun T : ℕ => ∫ x in η..ε, workCore x T) atTop
      (𝓝 (Real.log (riemannZeta ((1 + η : ℝ) : ℂ)).re -
        Real.log (riemannZeta ((1 + ε : ℝ) : ℂ)).re)) := by
  have hη' := hasSum_eulerLog hη
  have hε' := hasSum_eulerLog hε
  have hsum : HasSum (coreScaleLimit η ε) (Real.log (riemannZeta ((1 + η : ℝ) : ℂ)).re -
      Real.log (riemannZeta ((1 + ε : ℝ) : ℂ)).re) := by
    refine (hη'.sub hε').congr_fun fun j => ?_
    simp only [coreScaleLimit, mul_sub]
  have hbound : Summable (coreScaleBound η ε) := by
    refine (hη'.summable.add hε'.summable).congr fun j => ?_
    simp only [coreScaleBound, mul_add]
  have h := tendsto_tsum_of_dominated_convergence hbound (tendsto_coreScaleTerm η ε)
    (Eventually.of_forall fun T j => by
      rw [Real.norm_eq_abs]; exact abs_coreScaleTerm_le η ε T j)
  rw [hsum.tsum_eq] at h
  exact h.congr fun T => (integral_workCore_eq_tsum η ε T).symm

/-- **A horizon-free bound for the core on a positive interval.** For `0 < η ≤ ε` and every
horizon, `∫_η^ε core_x(T) dx ≤ log ζ(1+η) − log ζ(1+ε)`. -/
theorem integral_workCore_le_logZeta {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (T : ℕ) :
    (∫ x in η..ε, workCore x T) ≤ Real.log (riemannZeta ((1 + η : ℝ) : ℂ)).re -
      Real.log (riemannZeta ((1 + ε : ℝ) : ℂ)).re := by
  have hε : 0 < ε := hη.trans_le hηε
  have hsum : HasSum (coreScaleLimit η ε) (Real.log (riemannZeta ((1 + η : ℝ) : ℂ)).re -
      Real.log (riemannZeta ((1 + ε : ℝ) : ℂ)).re) := by
    refine ((hasSum_eulerLog hη).sub (hasSum_eulerLog hε)).congr_fun fun j => ?_
    simp only [coreScaleLimit, mul_sub]
  rw [integral_workCore_eq_tsum, ← hsum.tsum_eq]
  have hfin : Summable (coreScaleTerm η ε T) :=
    summable_of_ne_finset_zero (s := Icc 1 T) fun j hj => by rw [coreScaleTerm, if_neg hj]
  refine hfin.tsum_le_tsum (fun j => ?_) hsum.summable
  by_cases hj : j ∈ Icc 1 T
  · obtain ⟨hj1, hjT⟩ := mem_Icc.mp hj
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hcoef : 0 ≤ ArithmeticFunction.vonMangoldt j *
        (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) := by
      refine mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (div_nonneg ?_ (Real.log_nonneg hj1'))
      exact sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le hj1' (by linarith))
    rw [coreScaleTerm, if_pos hj, coreScaleLimit_eq hj1]
    refine mul_le_mul_of_nonneg_left ?_ hcoef
    have : 0 ≤ 1 / ((T : ℝ) + 1) := by positivity
    linarith
  · rw [coreScaleTerm, if_neg hj]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [coreScaleLimit, eulerLogCoeffReal]
    · rw [coreScaleLimit]
      refine mul_nonneg (eulerLogCoeffReal_nonneg j) (sub_nonneg.mpr ?_)
      have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj0
      exact inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hj1' (by linarith))

end GaloisForLFunctions.ArithmeticCompensationTheory
