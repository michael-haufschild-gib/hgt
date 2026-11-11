import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCoupledShiftedSelbergFormHasThePolynomialLimit
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheLinearDetectorHasSmallTaperError

/-!
# The actual twisted-moment gcd sums in profile coordinates

The two gcd kernels have shifts `−2d` and `2d`. The direct kernel also
adds `2d log N` to the coefficient-power parameter. These exact identities
retain the original frozen coefficient weights. The literal linear
Levinson mollifier is the profile `P(x)=x` with parameter `−d log N`.
-/

open Complex
open RHTower RHTower.Sieve RHTower.ZetaGateProductAFE

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Möbius coefficients with an arbitrary logarithmic profile and power shift. -/
def moebiusProfileWeights (P : ℝ → ℝ) (N : ℕ) (v : ℝ) (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) * shiftedProfileWeight P N v n

theorem shiftedSelbergOriginal_eq_gcd_kernel (s : ℝ) {h k : ℕ} (hh : 0 < h) :
    shiftedSelbergOriginal s h k =
      ((ArithmeticFunction.moebius h : ℤ) : ℝ) * ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
        (Nat.gcd h k : ℝ) ^ (1 + s) / ((h : ℝ) * k) := by
  have hg : (0 : ℝ) < Nat.gcd h k := by exact_mod_cast Nat.gcd_pos_of_pos_left k hh
  rw [Real.rpow_add hg, Real.rpow_one]
  unfold shiftedSelbergOriginal selbergOriginalCoeff
  ring

/-- Adding `s log N` to the profile shift multiplies the coefficient by `n^s`. -/
theorem shiftedProfileWeight_add_log {N n : ℕ} (hN : 1 < N) (hn : 0 < n)
    (P : ℝ → ℝ) (v s : ℝ) :
    shiftedProfileWeight P N (v + s * Real.log N) n =
      (n : ℝ) ^ s * shiftedProfileWeight P N v n := by
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (v + s * Real.log N) * Real.log n / Real.log N =
      Real.log n * s + v * Real.log n / Real.log N := by
    field_simp [hL] <;> ring
  unfold shiftedProfileWeight
  rw [he, Real.exp_add, Real.rpow_def_of_pos hnR]
  ring

/-- The reflected main-term gcd sum is exactly the independently shifted profile form. -/
theorem gcdSum₂_moebiusProfileWeights {N : ℕ} (hN : 1 < N)
    (P : ℝ → ℝ) (d v : ℝ) :
    Real.log N * gcdSum₂ d N (moebiusProfileWeights P N v) =
      shiftedSelbergProfileForm P N (2 * d * Real.log N) v := by
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  unfold gcdSum₂ shiftedSelbergProfileForm
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  rw [coeff₂_eq hh0 hk0,
    show 2 * d * Real.log (N : ℝ) / Real.log N = 2 * d by field_simp [hL],
    shiftedSelbergOriginal_eq_gcd_kernel (2 * d) hh0]
  unfold moebiusProfileWeights
  ring

/-- The direct kernel adds twice the displacement to the coefficient power. -/
theorem gcdSum₁_moebiusProfileWeights {N : ℕ} (hN : 1 < N)
    (P : ℝ → ℝ) (d v : ℝ) :
    Real.log N * gcdSum₁ d N (moebiusProfileWeights P N v) =
      shiftedSelbergProfileForm P N (-2 * d * Real.log N) (v + 2 * d * Real.log N) := by
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  unfold gcdSum₁ shiftedSelbergProfileForm
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  rw [coeff₁_eq hh0 hk0,
    show -2 * d * Real.log (N : ℝ) / Real.log N = -2 * d by field_simp [hL],
    shiftedSelbergOriginal_eq_gcd_kernel (-2 * d) hh0,
    shiftedProfileWeight_add_log hN hh0 P v (2 * d),
    shiftedProfileWeight_add_log hN hk0 P v (2 * d)]
  rw [show (1 - 2 * (1 / 2 - d) : ℝ) = 2 * d by ring,
    show (2 * (1 / 2 - d) : ℝ) = 1 + (-2 * d) by ring]
  unfold moebiusProfileWeights
  ring

/-- On its finite support, the actual linear mollifier is precisely the linear profile. -/
theorem linearDetectorWeights_eq_moebiusProfileWeights {N n : ℕ} (hN : 1 < N)
    (hn : n ∈ Finset.Icc 1 N) (d : ℝ) :
    linearDetectorWeights N d n = moebiusProfileWeights (fun x => x) N (-d * Real.log N) n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hp : (n : ℝ) ^ (1 / 2 - d) * (1 / Real.sqrt n) = (n : ℝ) ^ (-d) := by
    rw [Real.sqrt_eq_rpow]
    simp only [one_div]
    rw [← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
    congr 1
    ring
  have hl : Real.log ((N : ℝ) / n) / Real.log N = 1 - Real.log n / Real.log N := by
    rw [Real.log_div hN0.ne' hn0.ne']
    field_simp [hL]
  have he : Real.exp ((-d * Real.log N) * Real.log n / Real.log N) = (n : ℝ) ^ (-d) := by
    rw [Real.rpow_def_of_pos hn0]
    congr 1
    field_simp [hL] <;> ring
  unfold linearDetectorWeights
  rw [levinsonShiftedLinearMollifierCoeff, levinsonLinearMollifierCoeff_eq (Finset.mem_Icc.mp hn).2]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  unfold moebiusProfileWeights shiftedProfileWeight
  rw [he]
  calc
    _ = (((ArithmeticFunction.moebius n : ℤ) : ℝ) *
        (Real.log ((N : ℝ) / n) / Real.log N)) *
          ((n : ℝ) ^ (1 / 2 - d) * (1 / Real.sqrt n)) := by ring
    _ = _ := by rw [hp, hl]; ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
