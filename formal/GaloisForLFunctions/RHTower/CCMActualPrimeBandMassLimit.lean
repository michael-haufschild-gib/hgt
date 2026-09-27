import GaloisForLFunctions.RHTower.CCMActualPrimeBandInterference
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarDLVPRate

/-!
# Actual mass in fixed-width terminal prime bands

The unconditional completed-error estimate determines both band masses
after critical normalization. Their limiting product is strictly positive,
so collective interference need not disappear as the aperture grows.
-/

open Filter Topology Set
open scoped BigOperators
noncomputable section
namespace RHTower

theorem tendsto_exp_neg_half_mul_criticalMellinPrimeMass :
    Tendsto (fun T : ℝ => Real.exp (-T / 2) * criticalMellinPrimeMass T)
      atTop (𝓝 2) := by
  have heq (T : ℝ) : Real.exp (-T / 2) * criticalMellinPrimeMass T =
      2 - 2 * Real.exp (-T) - Real.exp (-T / 2) * criticalMellinCompletedError T := by
    have hcancel : Real.exp (-T / 2) * Real.exp (T / 2) = 1 := by
      rw [← Real.exp_add, show -T / 2 + T / 2 = 0 by ring, Real.exp_zero]
    have hdouble : Real.exp (-T / 2) * Real.exp (-(T / 2)) = Real.exp (-T) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [criticalMellinCompletedError_eq_polar_sub_primeMass, Real.sinh_eq]
    nlinarith only [hcancel, hdouble]
  have h := (tendsto_const_nhds.sub
    (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (2 : ℝ))).sub
      tendsto_exp_neg_half_mul_criticalMellinCompletedError_atTop_zero
  simpa only [mul_zero, sub_zero, ← heq] using h

theorem tendsto_exp_neg_mul_shifted_criticalMellinPrimeMass (c : ℝ) :
    Tendsto (fun a : ℝ => Real.exp (-a) * criticalMellinPrimeMass (2 * a - c))
      atTop (𝓝 (2 * Real.exp (-c / 2))) := by
  have harg : Tendsto (fun a : ℝ => 2 * a - c) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [eventually_ge_atTop c] with a ha
    dsimp only [id_eq]
    linarith
  have h := (tendsto_exp_neg_half_mul_criticalMellinPrimeMass.comp harg).const_mul
    (Real.exp (-c / 2))
  have heq (a : ℝ) : Real.exp (-c / 2) *
      (Real.exp (-(2 * a - c) / 2) * criticalMellinPrimeMass (2 * a - c)) =
        Real.exp (-a) * criticalMellinPrimeMass (2 * a - c) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simpa only [Function.comp_def, heq, mul_comm (Real.exp (-c / 2)) 2] using h

private theorem band_eq_Ioc (a : SuzukiPositiveAperture) (lo hi : ℝ)
    (hhi : 0 ≤ hi) (hlo : 0 < 2 * a.1 - lo) :
    ccmActualPrimeBand a lo hi =
      Finset.Ioc ⌊Real.exp (2 * a.1 - lo)⌋₊ ⌊Real.exp (2 * a.1 - hi)⌋₊ := by
  classical
  ext n
  simp only [ccmActualPrimeBand, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hn, _⟩, hl, hu⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact ⟨(Nat.floor_lt (Real.exp_pos _).le).mpr
      ((Real.lt_log_iff_exp_lt hnpos).mp hl),
      (Nat.le_floor_iff (Real.exp_pos _).le).mpr
        ((Real.log_le_iff_le_exp hnpos).mp hu)⟩
  · rintro ⟨hl, hu⟩
    have hfloor : 1 ≤ ⌊Real.exp (2 * a.1 - lo)⌋₊ :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mpr (by
        simpa only [Nat.cast_one] using (Real.one_le_exp_iff.mpr hlo.le))
    have hn : 2 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hhead : n ≤ ⌊Real.exp (2 * a.1)⌋₊ := hu.trans
      (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith)))
    exact ⟨⟨hn, hhead⟩,
      (Real.lt_log_iff_exp_lt hnpos).mpr ((Nat.floor_lt (Real.exp_pos _).le).mp hl),
      (Real.log_le_iff_le_exp hnpos).mpr ((Nat.le_floor_iff (Real.exp_pos _).le).mp hu)⟩

private theorem band_mass_eq_difference (a : SuzukiPositiveAperture) (lo hi : ℝ)
    (hhi : 0 ≤ hi) (horder : hi ≤ lo) (hlo : 0 < 2 * a.1 - lo) :
    ccmActualPrimeBandMass a lo hi =
      criticalMellinPrimeMass (2 * a.1 - hi) - criticalMellinPrimeMass (2 * a.1 - lo) := by
  have h := sharpMovingPrimeWindowMass_eq_sum_Ioc (L := lo - hi)
    (x := 2 * a.1 - hi) (sub_nonneg.mpr horder)
  unfold sharpMovingPrimeWindowMass at h
  rw [show 2 * a.1 - hi - (lo - hi) = 2 * a.1 - lo by ring] at h
  unfold ccmActualPrimeBandMass
  rw [band_eq_Ioc a lo hi hhi hlo]
  exact h.symm

theorem ccmActualPrimeLowBandMass_eq_difference
    (a : {a : SuzukiPositiveAperture // 4 < a.1}) :
    ccmActualPrimeBandMass a.1 4 3 =
      criticalMellinPrimeMass (2 * a.1.1 - 3) - criticalMellinPrimeMass (2 * a.1.1 - 4) :=
  band_mass_eq_difference a.1 4 3 (by norm_num) (by norm_num) (by linarith [a.2])

theorem ccmActualPrimeHighBandMass_eq_difference
    (a : {a : SuzukiPositiveAperture // 4 < a.1}) :
    ccmActualPrimeBandMass a.1 1 0 =
      criticalMellinPrimeMass (2 * a.1.1) - criticalMellinPrimeMass (2 * a.1.1 - 1) := by
  simpa only [sub_zero] using band_mass_eq_difference a.1 1 0 (by norm_num)
    (by norm_num) (by linarith [a.2])

def ccmPrimeBandsLimitingMassProduct : ℝ :=
  (2 * Real.exp (-(3 : ℝ) / 2) - 2 * Real.exp (-2)) *
    (2 - 2 * Real.exp (-(1 : ℝ) / 2))

theorem ccmPrimeBandsLimitingMassProduct_pos : 0 < ccmPrimeBandsLimitingMassProduct := by
  have hL : Real.exp (-2) < Real.exp (-(3 : ℝ) / 2) := Real.exp_lt_exp.mpr (by norm_num)
  have hH : Real.exp (-(1 : ℝ) / 2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  unfold ccmPrimeBandsLimitingMassProduct
  exact mul_pos (by linarith) (by linarith)

theorem tendsto_ccmActualPrimeBands_scaled_mass_product :
    Tendsto (fun a : ℝ => Real.exp (-2 * a) *
      ((criticalMellinPrimeMass (2 * a - 3) - criticalMellinPrimeMass (2 * a - 4)) *
        (criticalMellinPrimeMass (2 * a) - criticalMellinPrimeMass (2 * a - 1))))
      atTop (𝓝 ccmPrimeBandsLimitingMassProduct) := by
  have h := ((tendsto_exp_neg_mul_shifted_criticalMellinPrimeMass 3).sub
    (tendsto_exp_neg_mul_shifted_criticalMellinPrimeMass 4)).mul
      ((tendsto_exp_neg_mul_shifted_criticalMellinPrimeMass 0).sub
        (tendsto_exp_neg_mul_shifted_criticalMellinPrimeMass 1))
  have heq (a : ℝ) : Real.exp (-2 * a) = Real.exp (-a) * Real.exp (-a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  convert h using 1
  · ext a
    simp only [sub_zero, heq]
    ring
  · norm_num [ccmPrimeBandsLimitingMassProduct]

end RHTower
