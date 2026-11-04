import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeUniformGeometry

/-!
# Vanishing costs for independent cutoff and horizon scales

Reciprocal-prime mass loses one logarithm to the prime charge normalizer.
The centered polar coefficient vanishes independently with the horizon;
neither assertion requires a polynomial relation between the two scales.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

/-- Reciprocal-prime mass is negligible compared with the receiving-charge normalizer. -/
theorem tendsto_primeReciprocal_div_primePoleScale :
    Tendsto (fun Q : ℕ =>
      (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) / primePoleScale Q)
      atTop (𝓝 0) := by
  have h := (tendsto_primeReciprocal_div_log_rpow (q := 1) zero_lt_one).mul
    tendsto_log_div_primePoleScale
  simp only [Real.rpow_one, zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  have hL : 0 < Real.log Q :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  field_simp [hL.ne']

/-- The coherent nonpolar coefficient square vanishes with its prime cutoff. -/
theorem tendsto_primeCharge_reciprocal_mass (t : ℝ) :
    Tendsto (fun Q : ℕ => (t / primePoleScale Q) ^ 2 *
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) atTop (𝓝 0) := by
  have h := (primePoleScale_tendsto_atTop.const_div_atTop (t ^ 2)).mul
    tendsto_primeReciprocal_div_primePoleScale
  simp only [zero_mul] at h
  convert h using 1
  funext Q
  ring

/-- One cutoff logarithm still leaves a vanishing coherent coefficient cost. -/
theorem tendsto_primeCharge_logarithmic_reciprocal_mass (t : ℝ) :
    Tendsto (fun Q : ℕ => (1 + Real.log Q) * (t / primePoleScale Q) ^ 2 *
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_primeCharge_reciprocal_mass t).add
    ((tendsto_primeReciprocal_div_primePoleScale.mul tendsto_log_div_primePoleScale).const_mul
      (t ^ 2))
  simp only [zero_mul, mul_zero, zero_add] at h
  convert h using 1
  funext Q
  ring

/-- The complete nonpolar diagonal has vanishing logarithmic coefficient mass. -/
theorem tendsto_primeCharge_completed_coefficient_mass (t : ℝ) :
    Tendsto (fun Q : ℕ => (t / primePoleScale Q) ^ 2 *
      ((∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) + primePoleScale Q))
      atTop (𝓝 0) := by
  have h := (tendsto_primeCharge_reciprocal_mass t).add
    (primePoleScale_tendsto_atTop.const_div_atTop (t ^ 2))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  field_simp [(primePoleScale_pos hQ).ne']
  <;> ring

/-- The exact polar coefficient bound vanishes for independently growing cutoff and horizon. -/
theorem tendsto_primeCharge_polar_bound {ι : Type*} {l : Filter ι} {Q N : ι → ℕ}
    (hQ : Tendsto Q l atTop) (hN : Tendsto N l atTop) (t : ℝ) :
    Tendsto (fun i => (|t| + 8 * |t| / primePoleScale (Q i)) / Real.log (N i)) l (𝓝 0) := by
  have hB := (primePoleScale_tendsto_atTop.comp hQ).const_div_atTop (8 * |t|)
  have hnum := hB.const_add |t|
  simpa only [Function.comp_def] using hnum.div_atTop
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hN)

/-- Every logarithmic power loses to a positive power of its argument. -/
theorem tendsto_receiving_log_rpow_div_rpow (p : ℝ) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun x : ℝ => Real.log x ^ p / x ^ q) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p q hq).comp
    Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def, Real.rpow_def_of_pos hx,
    div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

/-- Logarithmic powers lose to every positive power of the horizon. -/
theorem tendsto_receiving_log_rpow_div_nat_rpow (p : ℝ) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => Real.log N ^ p / (N : ℝ) ^ q) atTop (𝓝 0) :=
  (tendsto_receiving_log_rpow_div_rpow p hq).comp tendsto_natCast_atTop_atTop

/-- The logarithmic conductor Gram cost vanishes below a power of the horizon logarithm. -/
theorem tendsto_receiving_loglog_square_div_log :
    Tendsto (fun N : ℕ => (1 + Real.log (Real.log N)) ^ 2 / Real.log N)
      atTop (𝓝 0) := by
  have hL := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 := (tendsto_receiving_log_rpow_div_rpow 2 zero_lt_one).comp hL
  have h1 := (tendsto_receiving_log_rpow_div_rpow 1 zero_lt_one).comp hL
  have h0 := hL.const_div_atTop (1 : ℝ)
  have h := (h2.add (h1.const_mul 2)).add h0
  have hp (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast x 2
  simp only [zero_add, mul_zero, Real.rpow_one, hp, Function.comp_def] at h
  convert h using 1
  funext N
  ring

/-- Every power below eight of the critical overlap is smaller than the horizon logarithm. -/
theorem tendsto_primeCharge_critical_power_div_log (K : ℝ) {k : ℕ} (hk : k < 8) :
    Tendsto (fun N : ℕ => (2 * K * Real.log N ^ (1 / 8 : ℝ)) ^ k / Real.log N)
      atTop (𝓝 0) := by
  have hq : 0 < 1 - (1 / 8 : ℝ) * k := by
    have hkR : (k : ℝ) < 8 := by exact_mod_cast hk
    linarith only [hkR]
  have h := ((tendsto_rpow_atTop hq).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_div_atTop ((2 * K) ^ k)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp : (Real.log N ^ (1 / 8 : ℝ)) ^ k =
      Real.log N ^ ((1 / 8 : ℝ) * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  simp only [Function.comp_def]
  rw [Real.rpow_sub hL, Real.rpow_one, mul_pow, hp]
  field_simp [hL.ne', (Real.rpow_pos_of_pos hL ((1 / 8 : ℝ) * k)).ne']

/-- A sublinear power of the horizon logarithm vanishes after physical normalization. -/
theorem tendsto_receiving_log_rpow_div_log {p : ℝ} (hp : p < 1) :
    Tendsto (fun N : ℕ => Real.log N ^ p / Real.log N) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_atTop (sub_pos.mpr hp)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_div_atTop (1 : ℝ)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  simp only [Function.comp_def]
  rw [Real.rpow_sub hL, Real.rpow_one]
  field_simp [hL.ne', (Real.rpow_pos_of_pos hL p).ne']

/-- Logarithmic and overlap powers combine by adding their critical exponents. -/
theorem tendsto_receiving_log_mul_critical_power_div_log (K a : ℝ) (k : ℕ)
    (ha : a + (1 / 8 : ℝ) * k < 1) :
    Tendsto (fun N : ℕ => Real.log N ^ a *
      (2 * K * Real.log N ^ (1 / 8 : ℝ)) ^ k / Real.log N) atTop (𝓝 0) := by
  have h := (tendsto_receiving_log_rpow_div_log ha).const_mul ((2 * K) ^ k)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp : (Real.log N ^ (1 / 8 : ℝ)) ^ k =
      Real.log N ^ ((1 / 8 : ℝ) * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  rw [mul_pow, hp, Real.rpow_add hL]
  ring

/-- Every fixed logarithmic-overlap product loses to a positive power of the horizon. -/
theorem tendsto_receiving_log_mul_critical_power_div_nat_rpow (K a : ℝ) (k : ℕ)
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => Real.log N ^ a *
      (2 * K * Real.log N ^ (1 / 8 : ℝ)) ^ k / (N : ℝ) ^ q) atTop (𝓝 0) := by
  have h := (tendsto_receiving_log_rpow_div_nat_rpow (a + (1 / 8 : ℝ) * k) hq).const_mul
    ((2 * K) ^ k)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp : (Real.log N ^ (1 / 8 : ℝ)) ^ k =
      Real.log N ^ ((1 / 8 : ℝ) * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  rw [mul_pow, hp, Real.rpow_add hL]
  ring

/-- One critical overlap factor still leaves the exact polar coefficient vanishing. -/
theorem tendsto_primeCharge_overlap_polar_bound {ι : Type*} {l : Filter ι} {Q N : ι → ℕ}
    (hQ : Tendsto Q l atTop) (hN : Tendsto N l atTop) (K t : ℝ) :
    Tendsto (fun i => (2 * K * Real.log (N i) ^ (1 / 8 : ℝ)) *
      ((|t| + 8 * |t| / primePoleScale (Q i)) / Real.log (N i))) l (𝓝 0) := by
  have hc := (tendsto_primeCharge_critical_power_div_log K (by omega : 1 < 8)).comp hN
  have hn := ((primePoleScale_tendsto_atTop.comp hQ).const_div_atTop (8 * |t|)).const_add |t|
  have h := hc.mul hn
  simp only [pow_one, zero_mul] at h
  convert h using 1
  funext i
  ring

#print axioms tendsto_primeCharge_logarithmic_reciprocal_mass
#print axioms tendsto_primeCharge_polar_bound
#print axioms tendsto_primeCharge_critical_power_div_log
#print axioms tendsto_receiving_log_mul_critical_power_div_nat_rpow

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
