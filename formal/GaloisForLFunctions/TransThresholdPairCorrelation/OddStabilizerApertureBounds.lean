import GaloisForLFunctions.TransThresholdPairCorrelation.OddStabilizerExactPoisson
import GaloisForLFunctions.TransThresholdPairCorrelation.OddStabilizerPoissonHorizon
import GaloisForLFunctions.RHTower.GammaInvGrowth
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheConductorEnergyKeepsALogarithmicReserve
import GaloisForLFunctions.RHTower.Sieve.LevinsonGcdFormBound

/-!
# Aperture bounds and fixed-base cancellation for odd stabilizer rows

Fourth-order Fourier decay gives a cubic aperture-tail bound. At a fixed
positive lag, the Ramanujan divisor bound and the summable weight `μ²/φ²`
also bound every row independently of the conductor cutoff. Consequently,
at a fixed base the primitive spatial correction cancels the full leading
logarithmic negative diagonal, unlike the moving support-horizon limit.
-/

noncomputable section
open MeasureTheory Real Filter Topology Finset
open Zeta23
namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem reciprocal_fourth_tail_le {R : ℕ} (hR : 1 ≤ R) :
    ∑' n : ℕ, 1 / (((R + n : ℕ) : ℝ) + 1) ^ 4 ≤ 1 / (R : ℝ) ^ 3 := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hs (k : ℕ) (hk : 1 < k) :
      Summable (fun n : ℕ => 1 / (((R + n : ℕ) : ℝ) + 1) ^ k) := by
    have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ k) :=
      Real.summable_one_div_nat_pow.mpr hk
    simpa [add_comm, add_left_comm, add_assoc] using
      (summable_nat_add_iff (R + 1)).2 hp
  have hpt (n : ℕ) : 1 / (((R + n : ℕ) : ℝ) + 1) ^ 4 ≤
      (1 / (R : ℝ)^2) * (1 / (((R + n : ℕ) : ℝ) + 1)^2) := by
    have hx : (0 : ℝ) < ((R + n : ℕ) : ℝ) + 1 := by positivity
    have hRx : (R : ℝ) ≤ ((R + n : ℕ) : ℝ) + 1 := by push_cast; linarith
    have hi := one_div_le_one_div_of_le (sq_pos_of_pos hR0)
      (pow_le_pow_left₀ hR0.le hRx 2)
    calc
      _ = (1 / (((R + n : ℕ) : ℝ) + 1)^2) *
        (1 / (((R + n : ℕ) : ℝ) + 1)^2) := by
          field_simp [hx.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hi (by positivity)
  calc
    _ ≤ ∑' n : ℕ, (1 / (R : ℝ)^2) *
        (1 / (((R + n : ℕ) : ℝ) + 1)^2) :=
      (hs 4 (by norm_num)).tsum_le_tsum hpt ((hs 2 (by norm_num)).mul_left _)
    _ = (1 / (R : ℝ)^2) * ∑' n : ℕ, 1 / (((R + n : ℕ) : ℝ) + 1)^2 :=
      tsum_mul_left
    _ ≤ (1 / (R : ℝ)^2) * (1 / R) :=
      mul_le_mul_of_nonneg_left (HilbertSchmidt.tsum_reciprocal_square_tail_le hR)
        (by positivity)
    _ = _ := by ring

/-- The uniform Ramanujan bound controls the stabilizer independently of the lag. -/
theorem abs_parityStabilizerWeight_le (Q h : ℕ) :
    |parityStabilizerWeight Q h| ≤
      2 * ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q := by
  let s := (Icc 1 Q).filter (fun q => q % 2 = 1)
  have hq (q : ℕ) (hq : q ∈ s) :
      |(RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
        GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient q h| ≤
      RHTower.Sieve.sqfreeTotientInv q := by
    have hq0 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
    have hg := RHTower.Sieve.sqfreeTotientInv_nonneg q
    rw [abs_mul, abs_of_nonneg (div_nonneg hg hφ.le)]
    calc
      _ ≤ (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) * q.totient :=
        mul_le_mul_of_nonneg_left
          (GaloisForLFunctions.BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q h)
          (div_nonneg hg hφ.le)
      _ = _ := div_mul_cancel₀ _ hφ.ne'
  unfold parityStabilizerWeight
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left
    ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hq)) (by norm_num)


private theorem fourth_decay_truncation {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n : ℕ, |f n| ≤ C / ((n : ℝ) + 1)^4) {R : ℕ} (hR : 1 ≤ R) :
    |(∑ n ∈ range R, f n) - ∑' n : ℕ, f n| ≤ C / (R : ℝ)^3 := by
  have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)^4) := by
    have h := (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (4 : ℕ)))
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hs : Summable f := (hp.mul_left C).of_norm_bounded (by
    intro n
    simpa only [Real.norm_eq_abs, div_eq_mul_inv, one_mul] using hf n)
  have hpt (n : ℕ) : |f (n + R)| ≤ C * (1 / (((R + n : ℕ) : ℝ) + 1)^4) := by
    simpa only [Nat.add_comm n R, div_eq_mul_inv, one_mul] using hf (n + R)
  have htail : Summable (fun n : ℕ => 1 / (((R + n : ℕ) : ℝ) + 1)^4) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
      (summable_nat_add_iff R).2 hp
  have hid := hs.sum_add_tsum_nat_add R
  rw [← hid]
  simp only [sub_add_cancel_left, abs_neg]
  calc
    _ ≤ ∑' n : ℕ, |f (n + R)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (((summable_nat_add_iff R).2 hs).norm)
    _ ≤ ∑' n : ℕ, C * (1 / (((R + n : ℕ) : ℝ) + 1)^4) :=
      ((summable_nat_add_iff R).2 hs).abs.tsum_le_tsum hpt (htail.mul_left C)
    _ = C * ∑' n : ℕ, 1 / (((R + n : ℕ) : ℝ) + 1)^4 := tsum_mul_left
    _ ≤ C * (1 / (R : ℝ)^3) := mul_le_mul_of_nonneg_left (reciprocal_fourth_tail_le hR) hC
    _ = _ := by ring

/-- Fourth-order Fourier decay makes the omitted stabilizer row at most a
cubic inverse power of the aperture length, uniformly in the conductor cutoff. -/
theorem abs_stabilizerLinearRow_truncation_le {Ω : ℝ → ℝ} {a b m : ℝ}
    (Q : ℕ) (hab : a ≤ b) (hm : 0 < m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) {R : ℕ} (hR : 1 ≤ R) :
    |(∑ n ∈ range R, parityStabilizerWeight Q (2 * (n + 1)) *
      cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)) - stabilizerLinearRow Q Ω m| ≤
      2 * (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) *
        (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|) * (m / 2)^4 / (R : ℝ)^3 := by
  let D : ℝ := ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|
  let O : ℝ := ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hO : 0 ≤ O := sum_nonneg (fun q _ => RHTower.Sieve.sqfreeTotientInv_nonneg q)
  apply fourth_decay_truncation (C := 2 * O * D * (m / 2)^4) (by positivity) _ hR
  intro n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hθ : (0 : ℝ) < ((2 * (n + 1) : ℕ) : ℝ) / m := by positivity
  have hc := abs_cosTransform_le hab hΩ hsupp hθ.ne'
  rw [abs_of_pos hθ] at hc
  rw [abs_mul]
  calc
    _ ≤ (2 * O) * (D / (((2 * (n + 1) : ℕ) : ℝ) / m)^4) :=
      mul_le_mul (abs_parityStabilizerWeight_le Q _) hc (abs_nonneg _) (by positivity)
    _ = _ := by
      push_cast
      field_simp [hm.ne', hn.ne']


/-- At a fixed even lag the stabilizer is bounded independently of its
conductor cutoff: the divisor bound is summable against `μ²/φ²`. -/
theorem abs_parityStabilizerWeight_even_le (Q : ℕ) {r : ℕ} (hr : 0 < r) :
    |parityStabilizerWeight Q (2 * r)| ≤ 32 * (r : ℝ)^2 := by
  let s := (Icc 1 Q).filter (fun q => q % 2 = 1)
  let w : ℕ → ℝ := fun q => RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)
  have hw (q : ℕ) : 0 ≤ w q :=
    div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg q) (Nat.cast_nonneg _)
  have hsum : (∑ q ∈ s, w q) ≤ 16 :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => hw q)).trans
      (RHTower.Sieve.sum_sqfreeTotientInv_div_totient_le Q)
  have hpt (q : ℕ) (hq : q ∈ s) :
      |w q * GaloisForLFunctions.BezoutValuationIncidence.ramanujanLagCoefficient q (2 * r)| ≤
        w q * (r : ℝ)^2 := by
    rw [abs_mul, abs_of_nonneg (hw q), ramanujanLagCoefficient_odd_two_mul (mem_filter.mp hq).2]
    exact mul_le_mul_of_nonneg_left
      (GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.abs_ramanujanLagCoefficient_le_lag_sq q hr)
      (hw q)
  unfold parityStabilizerWeight
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ∑ q ∈ s, w q * (r : ℝ)^2 :=
      mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)) (by norm_num)
    _ = 2 * (∑ q ∈ s, w q) * (r : ℝ)^2 := by rw [← sum_mul]; ring
    _ ≤ 2 * 16 * (r : ℝ)^2 := by gcongr
    _ = _ := by ring


private theorem reciprocal_square_sum_le_two :
    ∑' n : ℕ, 1 / ((n : ℝ) + 1)^2 ≤ 2 := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hsplit := hs.sum_add_tsum_nat_add 1
  have ht := HilbertSchmidt.tsum_reciprocal_square_tail_le (m := 1) (by norm_num)
  simp only [Nat.cast_add, Nat.cast_one, add_comm (1 : ℝ)] at ht
  simp only [sum_range_one, Nat.cast_zero, zero_add, one_pow, div_one,
    Nat.cast_add, Nat.cast_one] at hsplit
  linarith

private theorem square_decay_sum_bounds {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n : ℕ, |f n| ≤ C / ((n : ℝ) + 1)^2) :
    |∑' n : ℕ, f n| ≤ 2 * C ∧ ∀ R : ℕ, |∑ n ∈ range R, f n| ≤ 2 * C := by
  have hp : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hs : Summable f := (hp.mul_left C).of_norm_bounded (by
    intro n
    simpa only [Real.norm_eq_abs, div_eq_mul_inv, one_mul] using hf n)
  have hmajor : (∑' n : ℕ, |f n|) ≤ 2 * C := by
    calc
      _ ≤ ∑' n : ℕ, C * (1 / ((n : ℝ) + 1)^2) :=
        hs.abs.tsum_le_tsum (by intro n; simpa only [div_eq_mul_inv, one_mul] using hf n)
          (hp.mul_left C)
      _ = C * ∑' n : ℕ, 1 / ((n : ℝ) + 1)^2 := tsum_mul_left
      _ ≤ C * 2 := mul_le_mul_of_nonneg_left reciprocal_square_sum_le_two hC
      _ = _ := by ring
  constructor
  · have habs : |∑' n : ℕ, f n| ≤ ∑' n : ℕ, |f n| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    exact habs.trans hmajor
  · intro R
    exact ((abs_sum_le_sum_abs _ _).trans
      (hs.abs.sum_le_tsum (range R) (fun n _ => abs_nonneg (f n)))).trans hmajor

private theorem stabilizer_term_le_square_decay {Ω : ℝ → ℝ} {a b m : ℝ}
    (Q : ℕ) (hab : a ≤ b) (hm : 0 < m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (n : ℕ) :
    |parityStabilizerWeight Q (2 * (n + 1)) *
      cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)| ≤
      (2 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|) * m^4) / ((n : ℝ) + 1)^2 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hθ : (0 : ℝ) < ((2 * (n + 1) : ℕ) : ℝ) / m := by positivity
  have hc := abs_cosTransform_le hab hΩ hsupp hθ.ne'
  rw [abs_of_pos hθ] at hc
  rw [abs_mul]
  calc
    _ ≤ (32 * ((n + 1 : ℕ) : ℝ)^2) *
        ((∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|) /
          (((2 * (n + 1) : ℕ) : ℝ) / m)^4) :=
      mul_le_mul (abs_parityStabilizerWeight_even_le Q (by omega)) hc
        (abs_nonneg _) (by positivity)
    _ = _ := by
      push_cast
      field_simp [hm.ne', hn.ne']
      ring

/-- Complete rows of a C⁴ window have a conductor-independent bound. This
controls short rows where the aperture contains only boundedly many lags. -/
theorem abs_stabilizerLinearRow_le {Ω : ℝ → ℝ} {a b m : ℝ}
    (Q : ℕ) (hab : a ≤ b) (hm : 0 < m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) :
    |stabilizerLinearRow Q Ω m| ≤
      4 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|) * m^4 := by
  have hD : 0 ≤ ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t| :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have h := (square_decay_sum_bounds (by positivity)
    (stabilizer_term_le_square_decay Q hab hm hΩ hsupp)).1
  unfold stabilizerLinearRow
  convert h using 1
  ring

/-- The same conductor-independent envelope controls every finite linear row. -/
theorem abs_sum_stabilizerLinearRow_le {Ω : ℝ → ℝ} {a b m : ℝ}
    (Q R : ℕ) (hab : a ≤ b) (hm : 0 < m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) :
    |∑ n ∈ range R, parityStabilizerWeight Q (2 * (n + 1)) *
      cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)| ≤
      4 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|) * m^4 := by
  have hD : 0 ≤ ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t| :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have h := (square_decay_sum_bounds (by positivity)
    (stabilizer_term_le_square_decay Q hab hm hΩ hsupp)).2 R
  convert h using 1
  ring


/-- At a fixed base, the complete row is bounded in the conductor cutoff,
so its logarithmic coefficient vanishes. -/
theorem tendsto_stabilizerLinearRow_fixed_div_log_zero {Ω : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) :
    Tendsto (fun Q : ℕ => stabilizerLinearRow Q Ω m / Real.log Q)
      atTop (𝓝 0) := by
  let C := 4 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|) * m^4
  have hlog : Tendsto (fun Q : ℕ => Real.log Q) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ (hlog.const_div_atTop C)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with Q hQ
  have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (by omega : 1 < Q)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.log_pos hQ1)]
  exact div_le_div_of_nonneg_right (abs_stabilizerLinearRow_le Q hab hm hΩ hsupp)
    (Real.log_pos hQ1).le

/-- At fixed base, primitive spatial samples cancel the full logarithmic
negative diagonal. Their coefficient is the window mass divided by `2πm`. -/
theorem tendsto_stabilizerSpatialDual_fixed_div_log {Ω : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) :
    Tendsto (fun Q : ℕ => stabilizerSpatialDual Q Ω m / Real.log Q)
      atTop (𝓝 (cosTransform Ω 0 / (2 * π * m))) := by
  have hsp : ∀ t, Ω t ≠ 0 → |t| ≤ max |a| |b| := by
    intro t ht
    have hmem : t ∈ Set.Icc a b := by
      by_contra hn
      exact ht (hsupp t hn)
    apply abs_le.mpr
    constructor
    · exact (neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hmem.1)
    · exact hmem.2.trans ((le_abs_self b).trans (le_max_right |a| |b|))
  have hrow := tendsto_stabilizerLinearRow_fixed_div_log_zero hab hm hΩ hsupp
  have hodd := tendsto_sum_odd_sqfreeTotientInv_div_log_half.const_mul (cosTransform Ω 0)
  have h := (hrow.add hodd).div_const (π * m)
  have hv : ((0 : ℝ) + cosTransform Ω 0 * (1 / 2)) / (π * m) =
      cosTransform Ω 0 / (2 * π * m) := by ring
  rw [hv] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with Q hQ
  have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (by omega : 1 < Q)
  rw [stabilizerLinearRow_eq_dual Q hm (hΩ.of_le (by norm_num)) hsp]
  field_simp [Real.pi_ne_zero, hm.ne', (Real.log_pos hQ1).ne']
  ring

end GaloisForLFunctions.TransThresholdPairCorrelation
