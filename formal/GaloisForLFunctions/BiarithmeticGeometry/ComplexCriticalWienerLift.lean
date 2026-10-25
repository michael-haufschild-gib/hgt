import GaloisForLFunctions.BiarithmeticGeometry.CriticalWienerLift
import GaloisForLFunctions.BiarithmeticGeometry.GoldenPrimePayment

/-!
# Complex coefficient coordinates on the critical prime-five subalgebra

Real and imaginary coefficient lifts assemble into an actual complex Wiener
kernel. Its coefficients and norm identify the one-prime subalgebra with
complex `ell1`, and golden payment reads its ordinary complex partial sums.
-/

noncomputable section
open Finset
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem summable_abs_re_of_norm (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) : Summable (fun r => |(g r).re|) :=
  hg.of_nonneg_of_le (fun _ => abs_nonneg _) (fun _ => Complex.abs_re_le_norm _)

private theorem summable_abs_im_of_norm (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) : Summable (fun r => |(g r).im|) :=
  hg.of_nonneg_of_le (fun _ => abs_nonneg _) (fun _ => Complex.abs_im_le_norm _)

/-- Complex `ell1` coefficients in the actual critical prime-five Wiener subalgebra. -/
def fiveComplexCriticalWienerLift (g : ℕ → ℂ) (hg : Summable fun r => ‖g r‖) :
    WienerAlgebraAt (1 / 2) :=
  fiveCriticalWienerLift (fun r => (g r).re) (summable_abs_re_of_norm g hg) +
    Complex.I • fiveCriticalWienerLift (fun r => (g r).im) (summable_abs_im_of_norm g hg)

/-- The two real lifts recover the original complex coefficient at each five-power. -/
theorem fiveComplexCriticalWienerLift_pow (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) (r : ℕ) :
    (fiveComplexCriticalWienerLift g hg).toFn (5 ^ r) =
      (Real.sqrt 5 : ℂ) ^ r * g r := by
  change (fiveCriticalWienerLift (fun r => (g r).re) _).toFn (5 ^ r) +
    Complex.I * (fiveCriticalWienerLift (fun r => (g r).im) _).toFn (5 ^ r) = _
  simp only [fiveCriticalWienerLift_toFn, fiveCriticalKernelLift, fiveTowerKernelLift_pow,
    Complex.ofReal_mul, Complex.ofReal_pow]
  calc
    _ = (Real.sqrt 5 : ℂ) ^ r * ((g r).re + (g r).im * Complex.I) := by ring
    _ = _ := by rw [Complex.re_add_im]

/-- The complex lift vanishes off its single-prime support. -/
theorem fiveComplexCriticalWienerLift_off_support (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) (n : ℕ)
    (hn : n ∉ Set.range (fun r : ℕ => 5 ^ r)) :
    (fiveComplexCriticalWienerLift g hg).toFn n = 0 := by
  change (fiveCriticalWienerLift (fun r => (g r).re) _).toFn n +
    Complex.I * (fiveCriticalWienerLift (fun r => (g r).im) _).toFn n = 0
  simp only [fiveCriticalWienerLift_toFn, fiveCriticalKernelLift,
    fiveTowerKernelLift_off_support _ _ hn, Complex.ofReal_zero, mul_zero, add_zero]

private theorem criticalWiener_norm_term (k : WienerAlgebraAt (1 / 2)) (n : ℕ) :
    ‖LSeries.term (⇑k.toFn) ((1 / 2 : ℝ) : ℂ) n‖ =
      ‖k.toFn n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- The complex lift preserves the full coefficient norm exactly. -/
theorem norm_fiveComplexCriticalWienerLift (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) :
    ‖fiveComplexCriticalWienerLift g hg‖ = ∑' r, ‖g r‖ := by
  rw [WienerAlgebraAt.norm_def, wienerNorm]
  simp_rw [criticalWiener_norm_term]
  have hsupp : Function.support
      (fun n : ℕ => ‖(fiveComplexCriticalWienerLift g hg).toFn n‖ *
        (n : ℝ) ^ (-(1 / 2 : ℝ))) ⊆ Set.range (fun r : ℕ => 5 ^ r) := by
    intro n hn
    by_contra hnot
    apply hn
    change ‖(fiveComplexCriticalWienerLift g hg).toFn n‖ *
      (n : ℝ) ^ (-(1 / 2 : ℝ)) = 0
    rw [fiveComplexCriticalWienerLift_off_support g hg n hnot, norm_zero, zero_mul]
  rw [← (Nat.pow_right_injective (by omega : 2 ≤ 5)).tsum_eq hsupp]
  apply tsum_congr
  intro r
  rw [fiveComplexCriticalWienerLift_pow, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ = (Real.sqrt 5 ^ r * ((5 ^ r : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) * ‖g r‖ := by ring
    _ = _ := by rw [fiveCritical_weight_cancel, one_mul]

/-- Lifting is compatible with complex linear combinations. -/
theorem fiveComplexCriticalWienerLift_linear (g h : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) (hh : Summable fun r => ‖h r‖) (z : ℂ)
    (hgh : Summable fun r => ‖g r + z * h r‖) :
    fiveComplexCriticalWienerLift (fun r => g r + z * h r) hgh =
      fiveComplexCriticalWienerLift g hg + z • fiveComplexCriticalWienerLift h hh := by
  apply WienerAlgebraAt.ext
  intro n
  change (fiveComplexCriticalWienerLift (fun r => g r + z * h r) hgh).toFn n =
    (fiveComplexCriticalWienerLift g hg).toFn n + z * (fiveComplexCriticalWienerLift h hh).toFn n
  by_cases hn : n ∈ Set.range (fun r : ℕ => 5 ^ r)
  · obtain ⟨r, rfl⟩ := hn
    simp only [fiveComplexCriticalWienerLift_pow]
    ring
  · rw [fiveComplexCriticalWienerLift_off_support _ _ _ hn,
      fiveComplexCriticalWienerLift_off_support _ _ _ hn,
      fiveComplexCriticalWienerLift_off_support _ _ _ hn, mul_zero, add_zero]

/-- The complex normalized coefficient distance is the actual Wiener distance. -/
theorem norm_fiveComplexCriticalWienerLift_sub (g h : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) (hh : Summable fun r => ‖h r‖) :
    ‖fiveComplexCriticalWienerLift g hg - fiveComplexCriticalWienerLift h hh‖ =
      ∑' r, ‖g r - h r‖ := by
  have hsub : Summable (fun r => ‖g r + (-1 : ℂ) * h r‖) := by
    simp only [neg_one_mul, ← sub_eq_add_neg]
    exact (hg.add hh).of_nonneg_of_le (fun r => norm_nonneg _) (fun r => norm_sub_le _ _)
  have he := fiveComplexCriticalWienerLift_linear g h hg hh (-1) hsub
  simp only [neg_one_mul, neg_one_smul, ← sub_eq_add_neg] at he
  rw [← he, norm_fiveComplexCriticalWienerLift]

/-- Actual critical golden payment is the complex square-partial-sum domain. -/
theorem mem_golden_critical_fiveComplexCriticalWienerLift_iff (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) :
    fiveComplexCriticalWienerLift g hg ∈
      paidIdeal (goldenArithmeticSource goldenCriticalParameter)
        (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
          goldenCriticalParameter_bounds.2.le) ↔
      Summable (fun M : ℕ => ‖∑ r ∈ range (M + 1), g r‖ ^ 2) := by
  rw [mem_paidIdeal_golden_critical_fiveTower_iff _
    (fiveComplexCriticalWienerLift_off_support g hg)]
  have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  simp only [fiveComplexCriticalWienerLift_pow,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hs)]

end GaloisForLFunctions.BiarithmeticGeometry
