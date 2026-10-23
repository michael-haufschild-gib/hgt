import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellGlobalCount

/-!
# Preserved Route-T receiver margin

The optimizer proof spends only half of its available scalar reserve.  This module bounds the
finite-set harmonic factor by one logarithm and absorbs it, together with any fixed logarithmic
receiver loss, into half of the preserved reserve.
-/


noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

theorem sum_range_inv_add_one_eq_harmonic (K : ℕ) :
    ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) = (harmonic K : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      push_cast
      ring

theorem maynardHarmonicFactor_le_hundred_log
    {T delta : ℝ} {K : ℕ} (hT : 1 ≤ T) (hlogT : 1 ≤ Real.log T)
    (hK : (K : ℝ) ≤ T) (hdelta : 1 ≤ delta) :
    maynardHarmonicFactor K delta ≤ 100 * Real.log T := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hKpos : K = 0 ∨ 1 ≤ K := by omega
  have hsum : ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) ≤ 2 * Real.log T := by
    rcases hKpos with rfl | hKone
    · simp
      linarith
    · rw [sum_range_inv_add_one_eq_harmonic]
      have hharm := harmonic_le_one_add_log K
      have hKR : 0 < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hKone)
      have hlogK : Real.log K ≤ Real.log T := Real.log_le_log hKR hK
      linarith
  have hdelta0 : 0 < delta := by linarith
  have hcoeff : 12 * Real.pi / delta ≤ 48 := by
    have hpi := Real.pi_lt_four
    have hinv : delta⁻¹ ≤ 1 := (inv_le_one₀ hdelta0).2 hdelta
    rw [div_eq_mul_inv]
    linarith [mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 12 * Real.pi)]
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by positivity
  dsimp only [maynardHarmonicFactor]
  have hprod := mul_le_mul hcoeff hsum hsum0 (by norm_num : (0 : ℝ) ≤ 48)
  linarith

/-- The harmonic factor and `q` additional receiver logarithms consume only `d/400`. -/
theorem eventually_maynardHarmonicLogCost_absorbed (A : ℝ) (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ K : ℕ, ∀ delta : ℝ,
      (K : ℝ) ≤ T → 1 ≤ delta →
      maynardHarmonicFactor K delta * (Real.log T) ^ q ≤
        T ^ (routeTEndpointGlobalDeficit A T / 400) := by
  filter_upwards [eventually_maynardOptimizerFixedLogCost_absorbed
      A 100 (by norm_num) (q + 1) 400 (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℝ)] with T hcost hlogT hT
  intro K delta hK hdelta
  have hHF := maynardHarmonicFactor_le_hundred_log hT hlogT hK hdelta
  have hlog0 : 0 ≤ Real.log T := le_trans (by norm_num) hlogT
  have hmul := mul_le_mul_of_nonneg_right hHF (pow_nonneg hlog0 q)
  have hcost' := hcost 1 0 (by norm_num) (by exact_mod_cast hT)
    (by omega : 0 ≤ maynardFixedPolylogExponentBound)
  calc
    maynardHarmonicFactor K delta * (Real.log T) ^ q ≤
        (100 * Real.log T) * (Real.log T) ^ q := hmul
    _ = 100 * (Real.log T) ^ (q + 1) := by rw [pow_succ]; ring
    _ ≤ T ^ (routeTEndpointGlobalDeficit A T / 400) := by
      norm_num at hcost' ⊢
      exact hcost'

/-- Half of the preserved endpoint reserve absorbs the harmonic finite-set loss and every fixed
receiver logarithm, while the other half remains as a strict power margin. -/
theorem maynard_count_receiver_margin
    {R T e d H : ℝ} {q : ℕ}
    (hT : 1 ≤ T)
    (hR : R ≤ H * T ^ (e - d / 200))
    (hcost : H * (Real.log T) ^ q ≤ T ^ (d / 400)) :
    R * (Real.log T) ^ q ≤ T ^ (e - d / 400) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hpow0 : 0 ≤ T ^ (e - d / 200) := Real.rpow_nonneg hT0.le _
  calc
    R * (Real.log T) ^ q ≤
        (H * T ^ (e - d / 200)) * (Real.log T) ^ q :=
      mul_le_mul_of_nonneg_right hR (pow_nonneg hlog0 q)
    _ = (H * (Real.log T) ^ q) * T ^ (e - d / 200) := by ring
    _ ≤ T ^ (d / 400) * T ^ (e - d / 200) :=
      mul_le_mul_of_nonneg_right hcost hpow0
    _ = T ^ (e - d / 400) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring

end RHTower.Sieve
