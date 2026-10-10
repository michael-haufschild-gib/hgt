import GaloisForLFunctions.RHTower.WeilLogShiftNodalDistortion
import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalCluster
import GaloisForLFunctions.HTGeometry.LogarithmicSpacing

/-! Log-cluster mass is trapped between explicit distortions of arithmetic-node mass. -/

open scoped BigOperators
noncomputable section
namespace RHTower

def finiteWeilArithmeticNodes (r : ℕ) (i : Fin (r + 2)) : ℝ := (i : ℕ)

theorem finiteWeilArithmeticNodes_injective (r : ℕ) :
    Function.Injective (finiteWeilArithmeticNodes r) := by
  intro i j h
  apply Fin.ext
  dsimp [finiteWeilArithmeticNodes] at h
  exact_mod_cast h

def finiteWeilArithmeticMass (r : ℕ) : ℝ :=
  finiteWeilAbsMass (finiteWeilNormalizedMomentDual (finiteWeilArithmeticNodes r))

theorem finiteWeilArithmeticMass_ge_two (r : ℕ) : 2 ≤ finiteWeilArithmeticMass r := by
  apply finiteWeil_zero_sum_unit_mass _
    (finiteWeilNormalizedMomentDual_norm _ (finiteWeilArithmeticNodes_injective r))
  simpa only [pow_zero, mul_one] using finiteWeilNormalizedMomentDual_moment
    (finiteWeilArithmeticNodes r) (finiteWeilArithmeticNodes_injective r) 0 (by omega)

/-- Existing logarithmic spacing bounds, expressed without denominators on a fixed interval. -/
theorem finiteWeil_log_gap_scaled (A U x y : ℝ) (hA : 0 < A)
    (hAx : A ≤ x) (hAy : A ≤ y) (hxU : x ≤ U) (hyU : y ≤ U) :
    A * |Real.log x - Real.log y| ≤ |x - y| ∧
      |x - y| ≤ U * |Real.log x - Real.log y| := by
  have key (a b : ℝ) (ha : A ≤ a) (hb : A ≤ b) (hbU : b ≤ U) (hab : a ≤ b) :
      A * (Real.log b - Real.log a) ≤ b - a ∧
        b - a ≤ U * (Real.log b - Real.log a) := by
    have ha0 : 0 < a := hA.trans_le ha
    have hb0 : 0 < b := hA.trans_le hb
    have hlog : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha0 hab)
    have hu := (le_div_iff₀ ha0).mp (HTGeometry.log_sub_log_le_sub_div hb0 ha0)
    have hl := (div_le_iff₀ hb0).mp (HTGeometry.sub_div_le_log_sub_log hb0 ha0)
    constructor
    · calc
        _ ≤ a * (Real.log b - Real.log a) := mul_le_mul_of_nonneg_right ha hlog
        _ ≤ b - a := by linarith only [hu]
    · calc
        b - a ≤ b * (Real.log b - Real.log a) := by linarith only [hl]
        _ ≤ _ := mul_le_mul_of_nonneg_right hbU hlog
  rcases le_total x y with hxy | hyx
  · simpa only [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log (hA.trans_le hAx) hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using key x y hAx hAy hyU hxy
  · simpa only [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (hA.trans_le hAy) hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)] using key y x hAy hAx hxU hyx

theorem finiteWeilClusterLogNodes_gap_comparison (r k : ℕ) (i j : Fin (r + 2)) :
    ((k + 2 : ℕ) : ℝ) * |finiteWeilClusterLogNodes r k i - finiteWeilClusterLogNodes r k j| ≤
      |finiteWeilArithmeticNodes r i - finiteWeilArithmeticNodes r j| ∧
    |finiteWeilArithmeticNodes r i - finiteWeilArithmeticNodes r j| ≤
      ((k + r + 3 : ℕ) : ℝ) *
        |finiteWeilClusterLogNodes r k i - finiteWeilClusterLogNodes r k j| := by
  let x : ℝ := ((k + 2 + (i : ℕ) : ℕ) : ℝ)
  let y : ℝ := ((k + 2 + (j : ℕ) : ℕ) : ℝ)
  have hAx : ((k + 2 : ℕ) : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast (show k + 2 ≤ k + 2 + (i : ℕ) by omega)
  have hAy : ((k + 2 : ℕ) : ℝ) ≤ y := by
    dsimp [y]
    exact_mod_cast (show k + 2 ≤ k + 2 + (j : ℕ) by omega)
  have hxU : x ≤ ((k + r + 3 : ℕ) : ℝ) := by
    dsimp [x]
    exact_mod_cast (show k + 2 + (i : ℕ) ≤ k + r + 3 by have := i.isLt; omega)
  have hyU : y ≤ ((k + r + 3 : ℕ) : ℝ) := by
    dsimp [y]
    exact_mod_cast (show k + 2 + (j : ℕ) ≤ k + r + 3 by have := j.isLt; omega)
  have hs := finiteWeil_log_gap_scaled ((k + 2 : ℕ) : ℝ) ((k + r + 3 : ℕ) : ℝ)
    x y (by positivity) hAx hAy hxU hyU
  have hlog : finiteWeilClusterLogNodes r k i - finiteWeilClusterLogNodes r k j =
      Real.log x - Real.log y := by
    rw [finiteWeilClusterLogNodes_apply, finiteWeilClusterLogNodes_apply]
    dsimp [x, y]
    ring
  have hlin : x - y = finiteWeilArithmeticNodes r i - finiteWeilArithmeticNodes r j := by
    dsimp [x, y, finiteWeilArithmeticNodes]
    push_cast
    ring
  rwa [← hlog, hlin] at hs

theorem finiteWeil_log_grid_weights_comparison (r k : ℕ) (i : Fin (r + 2)) :
    ((k + 2 : ℕ) : ℝ) ^ (r + 1) * |finiteWeilMomentWeights (finiteWeilArithmeticNodes r) i| ≤
      |finiteWeilMomentWeights (finiteWeilClusterLogNodes r k) i| ∧
    |finiteWeilMomentWeights (finiteWeilClusterLogNodes r k) i| ≤
      ((k + r + 3 : ℕ) : ℝ) ^ (r + 1) *
        |finiteWeilMomentWeights (finiteWeilArithmeticNodes r) i| := by
  constructor
  · simpa only [one_pow, one_mul] using finiteWeilMomentWeights_scaled_gap_comparison
      (finiteWeilClusterLogNodes r k) (finiteWeilArithmeticNodes r)
      (finiteWeilClusterLogNodes_injective r k) (finiteWeilArithmeticNodes_injective r)
      ((k + 2 : ℕ) : ℝ) 1 (by positivity)
      (fun i j _ => by simpa only [one_mul] using (finiteWeilClusterLogNodes_gap_comparison r k i j).1) i
  · simpa only [one_pow, one_mul] using finiteWeilMomentWeights_scaled_gap_comparison
      (finiteWeilArithmeticNodes r) (finiteWeilClusterLogNodes r k)
      (finiteWeilArithmeticNodes_injective r) (finiteWeilClusterLogNodes_injective r k)
      1 ((k + r + 3 : ℕ) : ℝ) (by norm_num)
      (fun i j _ => by simpa only [one_mul] using (finiteWeilClusterLogNodes_gap_comparison r k i j).2) i

/-- Both directions of mass distortion relative to one position-independent reference. -/
theorem finiteWeilCanonicalCluster_arithmetic_mass_comparison (r k : ℕ) :
    ((k + 2 : ℕ) : ℝ) ^ (r + 1) * finiteWeilArithmeticMass r ≤
      ((k + r + 3 : ℕ) : ℝ) ^ (r + 1) *
        finiteWeilAbsMass (finiteWeilCanonicalCluster r k) ∧
    ((k + 2 : ℕ) : ℝ) ^ (r + 1) * finiteWeilAbsMass (finiteWeilCanonicalCluster r k) ≤
      ((k + r + 3 : ℕ) : ℝ) ^ (r + 1) * finiteWeilArithmeticMass r := by
  simpa only [finiteWeilArithmeticMass, finiteWeilCanonicalCluster] using
    finiteWeilNormalizedMomentDual_mass_comparison
      (finiteWeilArithmeticNodes r) (finiteWeilClusterLogNodes r k)
      (finiteWeilArithmeticNodes_injective r) (finiteWeilClusterLogNodes_injective r k)
      (((k + 2 : ℕ) : ℝ) ^ (r + 1)) (((k + r + 3 : ℕ) : ℝ) ^ (r + 1))
      (by positivity) (by positivity) (finiteWeil_log_grid_weights_comparison r k)

end RHTower
