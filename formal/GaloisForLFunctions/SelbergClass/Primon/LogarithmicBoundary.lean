import Mathlib.NumberTheory.SumPrimeReciprocals
import GaloisForLFunctions.RHTower.PrimeZetaLogAsymptotic
import GaloisForLFunctions.SelbergClass.Primon.ThermalLocalFactor

/-!
# The logarithmic boundary of the averaged primon gas

The half-temperature singularity in Hartnoll–Yang, arXiv:2502.02661v2, (96),
follows with an explicit finite part. Subtracting the first prime-power term
leaves a uniformly summable remainder at the boundary. The prime-zeta asymptotic therefore gives the precise
renormalized limit of the logarithmic local averages.
-/

open Filter Topology Set MeasureTheory

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The averaged logarithm at inverse temperature `u/2`. -/
def primeMeanLog (p : Nat.Primes) (u : ℝ) : ℝ :=
  ((p : ℝ) - 1) / 2 * Real.log (1 - (p : ℝ) ^ (-(u + 1)))

/-- The explicit prime summand agrees with the full thermal phase integral. -/
theorem primeMeanLog_eq_thermal_integral (p : Nat.Primes) (β : ℝ) :
    primeMeanLog p (2 * Real.exp β) =
      ∫ t in Set.Ioo (0 : ℝ) 1, kestenMcKayDensity p t * thermalLocalLog p β t := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [primeMeanLog, integral_kesten_thermalLocalLog, Real.rpow_def_of_pos hp,
    mul_comm (Real.log (p : ℝ)) (-(2 * Real.exp β + 1))]

/-- The prime sum of the local logarithmic averages, convergent for `u > 1`. -/
def meanLogPartition (u : ℝ) : ℝ := ∑' p : Nat.Primes, primeMeanLog p u

/-- Removing the first prime-power term leaves a summable boundary remainder. -/
def primeLogRemainder (p : Nat.Primes) (u : ℝ) : ℝ :=
  primeMeanLog p u + (p : ℝ) ^ (-u) / 2

/-- Exact finite part of the logarithmic partition at the boundary. -/
def meanLogBoundaryConstant : ℝ :=
  (∑' p : Nat.Primes, primeLogRemainder p 1) + RHTower.primeLogDefect 1 / 2

private theorem prime_rpow_shift (p : Nat.Primes) (u : ℝ) :
    (p : ℝ) * (p : ℝ) ^ (-(u + 1)) = (p : ℝ) ^ (-u) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  calc (p : ℝ) * (p : ℝ) ^ (-(u + 1)) =
      (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-(u + 1)) := by rw [Real.rpow_one]
    _ = (p : ℝ) ^ ((1 : ℝ) + -(u + 1)) := (Real.rpow_add hp _ _).symm
    _ = (p : ℝ) ^ (-u) := by congr 1; ring

private theorem prime_shift_bounds (p : Nat.Primes) {u : ℝ} (hu : 1 ≤ u) :
    0 < (p : ℝ) ^ (-(u + 1)) ∧
      (p : ℝ) ^ (-(u + 1)) ≤ (p : ℝ)⁻¹ ^ 2 ∧
      (p : ℝ) ^ (-(u + 1)) ≤ (p : ℝ)⁻¹ ∧
      (p : ℝ) ^ (-(u + 1)) ≤ 1 / 2 := by
  have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have ha : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div, inv_le_inv₀ hp0 (by norm_num)]
    exact hp
  have ha0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  have hx : (p : ℝ) ^ (-(u + 1)) ≤ (p : ℝ)⁻¹ ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ (p : ℝ))
      (by linarith : -(u + 1) ≤ -(2 : ℝ))
    simpa only [Real.rpow_neg hp0.le, Real.rpow_two, inv_pow] using h
  have hx' : (p : ℝ) ^ (-(u + 1)) ≤ (p : ℝ)⁻¹ :=
    hx.trans (by nlinarith only [ha, ha0])
  exact ⟨Real.rpow_pos_of_pos hp0 _, hx, hx', hx'.trans ha⟩

private theorem norm_primeLogRemainder_le (p : Nat.Primes) {u : ℝ} (hu : 1 ≤ u) :
    ‖primeLogRemainder p u‖ ≤ 2 * (p : ℝ)⁻¹ ^ 2 := by
  let x := (p : ℝ) ^ (-(u + 1))
  have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hx := prime_shift_bounds p hu
  have hd0 := RHTower.negLog_sub_self_nonneg (lt_of_le_of_lt hx.2.2.2 (by norm_num))
  have hd1 := RHTower.negLog_sub_self_le hx.1.le hx.2.2.2
  have hpx : (p : ℝ) * x ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hx.2.2.1 hp0.le
    simpa only [mul_inv_cancel₀ hp0.ne'] using h
  have hpx2 : (p : ℝ) * x ^ 2 ≤ x := by
    have h := mul_le_mul_of_nonneg_left hpx hx.1.le
    nlinarith only [h]
  have hd : ((p : ℝ) - 1) * (-Real.log (1 - x) - x) ≤ 2 * x := by
    have h := mul_le_mul_of_nonneg_left hd1 (by linarith : 0 ≤ (p : ℝ) - 1)
    nlinarith only [h, hpx2, sq_nonneg x]
  have hdnonneg : 0 ≤ ((p : ℝ) - 1) * (-Real.log (1 - x) - x) :=
    mul_nonneg (by linarith) hd0
  have he : primeLogRemainder p u =
      x / 2 - ((p : ℝ) - 1) / 2 * (-Real.log (1 - x) - x) := by
    rw [primeLogRemainder, primeMeanLog, ← prime_rpow_shift p u]
    dsimp [x]
    ring
  rw [he, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith only [hd, hdnonneg, hx.2.1, hx.1.le, sq_nonneg (p : ℝ)⁻¹]

private theorem summable_remainder {u : ℝ} (hu : 1 ≤ u) :
    Summable (fun p : Nat.Primes => primeLogRemainder p u) :=
  RHTower.summable_primeSquareRecip.of_norm_bounded (fun p => norm_primeLogRemainder_le p hu)

/-- The explicit renormalized prime series converges at every point on or right of its boundary. -/
theorem summable_primeLogRemainder (v : ℝ) :
    Summable (fun p : Nat.Primes => primeLogRemainder p (1 + |v|)) :=
  summable_remainder (by have := abs_nonneg v; linarith)

/-- At inverse temperature `1/2`, the original logarithmic prime series diverges. -/
theorem not_summable_primeMeanLog_boundary :
    ¬ Summable (fun p : Nat.Primes => primeMeanLog p 1) := by
  intro h
  have hs := ((summable_remainder (u := 1) le_rfl).sub h).mul_right 2
  apply Nat.Primes.not_summable_one_div
  refine hs.congr ?_
  intro p
  change (primeLogRemainder p 1 - primeMeanLog p 1) * 2 = 1 / (p : ℝ)
  rw [primeLogRemainder, Real.rpow_neg_one]
  ring

private theorem continuousAt_remainder (p : Nat.Primes) :
    ContinuousAt (primeLogRemainder p) 1 := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hx := prime_shift_bounds p (u := 1) le_rfl
  have hne : 1 - (p : ℝ) ^ (-((1 : ℝ) + 1)) ≠ 0 :=
    (sub_pos.mpr (hx.2.2.2.trans_lt (by norm_num))).ne'
  have hc : Continuous (fun u : ℝ => (p : ℝ) ^ (-(u + 1))) := by
    simp_rw [Real.rpow_def_of_pos hp]
    fun_prop
  have hd : Continuous (fun u : ℝ => (p : ℝ) ^ (-u)) := by
    simp_rw [Real.rpow_def_of_pos hp]
    fun_prop
  exact ((continuousAt_const.mul ((continuousAt_const.sub hc.continuousAt).log hne)).add
    (hd.continuousAt.div_const 2))

private theorem tendsto_remainder :
    Tendsto (fun u : ℝ => ∑' p : Nat.Primes, primeLogRemainder p u)
      (nhdsWithin 1 (Ioi 1)) (𝓝 (∑' p : Nat.Primes, primeLogRemainder p 1)) := by
  refine tendsto_tsum_of_dominated_convergence RHTower.summable_primeSquareRecip
    (fun p => (continuousAt_remainder p).tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with u hu p
  exact norm_primeLogRemainder_le p hu.le

private theorem summable_mean {u : ℝ} (hu : 1 < u) :
    Summable (fun p : Nat.Primes => primeMeanLog p u) := by
  have h : Summable (fun p : Nat.Primes =>
      primeLogRemainder p u - (p : ℝ) ^ (-u) / 2) :=
    (summable_remainder hu.le).sub ((RHTower.summable_primeZetaTerm hu).div_const 2)
  have he : (fun p : Nat.Primes => primeLogRemainder p u - (p : ℝ) ^ (-u) / 2) =
      fun p : Nat.Primes => primeMeanLog p u := by
    funext p
    simp only [primeLogRemainder]
    ring
  rwa [he] at h

/-- The mean logarithm is summable at every strictly supercritical inverse temperature. -/
theorem summable_primeMeanLog (v : ℝ) :
    Summable (fun p : Nat.Primes => primeMeanLog p (1 + Real.exp v)) :=
  summable_mean (by have := Real.exp_pos v; linarith)

private theorem partition_decomposition {u : ℝ} (hu : 1 < u) :
    meanLogPartition u + RHTower.primeZeta u / 2 =
      ∑' p : Nat.Primes, primeLogRemainder p u := by
  change meanLogPartition u + RHTower.primeZeta u / 2 =
    ∑' p : Nat.Primes, (primeMeanLog p u + (p : ℝ) ^ (-u) / 2)
  exact ((summable_mean hu).hasSum.add
    ((RHTower.summable_primeZetaTerm hu).hasSum.div_const 2)).tsum_eq.symm

/-- The full averaged logarithm has a half-logarithmic singularity and an explicit finite part. -/
theorem tendsto_meanLogPartition_sub_half_log :
    Tendsto (fun u : ℝ => meanLogPartition u - Real.log (u - 1) / 2)
      (nhdsWithin 1 (Ioi 1)) (𝓝 meanLogBoundaryConstant) := by
  have h := tendsto_remainder.sub (RHTower.tendsto_primeZeta_add_log_sub.div_const 2)
  have he : (∑' p : Nat.Primes, primeLogRemainder p 1) -
      -RHTower.primeLogDefect 1 / 2 = meanLogBoundaryConstant := by
    unfold meanLogBoundaryConstant
    ring
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [← partition_decomposition hu]
  ring

/-- In the original inverse temperature, the singularity lies exactly at `1/2`. -/
theorem tendsto_meanLogPartition_half_temperature :
    Tendsto (fun β : ℝ => meanLogPartition (2 * β) - Real.log (β - 1 / 2) / 2)
      (nhdsWithin (1 / 2 : ℝ) (Ioi (1 / 2)))
      (𝓝 (meanLogBoundaryConstant + Real.log 2 / 2)) := by
  have hlin : Tendsto (fun β : ℝ => 2 * β)
      (nhdsWithin (1 / 2 : ℝ) (Ioi (1 / 2))) (nhdsWithin 1 (Ioi 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Tendsto (fun β : ℝ => 2 * β) (𝓝 (1 / 2 : ℝ))
          (𝓝 (2 * (1 / 2 : ℝ))) :=
        (by fun_prop : Continuous (fun β : ℝ => 2 * β)).tendsto _
      norm_num at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      change 1 < 2 * β
      have hβ' : (1 / 2 : ℝ) < β := hβ
      linarith
  have h := (tendsto_meanLogPartition_sub_half_log.comp hlin).add_const (Real.log 2 / 2)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hβ' : (1 / 2 : ℝ) < β := hβ
  have he : 2 * β - 1 = 2 * (β - 1 / 2) := by ring
  simp only [Function.comp_apply]
  rw [he, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : β - 1 / 2 ≠ 0)]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon
