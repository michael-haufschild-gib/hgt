import GaloisForLFunctions.BiarithmeticGeometry.PrimeFivePaymentCriterion
import GaloisForLFunctions.BiarithmeticGeometry.GoldenArithmeticSource

/-!
# Complex prime-five payment for the actual golden source

The real packet criterion applies to both components of a complex Wiener
kernel. Their nonnegative square energies add to the complex norm square.
The actual golden paid-ideal identity then transfers the complete one-prime
criterion from its primary geometric tower.
-/

noncomputable section
open Finset RHTower
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem summable_weighted_complex_sq_iff (w : ℕ → ℝ) (hw : ∀ l, 0 ≤ w l)
    (z : ℕ → ℂ) :
    Summable (fun l => w l * ‖z l‖ ^ 2) ↔
      Summable (fun l => w l * (z l).re ^ 2) ∧
        Summable (fun l => w l * (z l).im ^ 2) := by
  have he (l : ℕ) : w l * ‖z l‖ ^ 2 =
      w l * (z l).re ^ 2 + w l * (z l).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  constructor
  · intro h
    constructor
    · refine h.of_nonneg_of_le (fun l => mul_nonneg (hw l) (sq_nonneg _)) fun l => ?_
      rw [he]
      exact le_add_of_nonneg_right (mul_nonneg (hw l) (sq_nonneg _))
    · refine h.of_nonneg_of_le (fun l => mul_nonneg (hw l) (sq_nonneg _)) fun l => ?_
      rw [he]
      exact le_add_of_nonneg_left (mul_nonneg (hw l) (sq_nonneg _))
  · rintro ⟨hr, hi⟩
    exact (hr.add hi).congr fun l => (he l).symm

private theorem partialPoleSum_re (k : WienerAlgebraAt (1 / 2)) (a : ℝ) (l : ℕ) :
    (∑ r ∈ range (l + 1), k.toFn (5 ^ r) / (a : ℂ) ^ r).re =
      ∑ r ∈ range (l + 1), (k.toFn (5 ^ r)).re / a ^ r := by
  simp only [div_eq_mul_inv, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

private theorem partialPoleSum_im (k : WienerAlgebraAt (1 / 2)) (a : ℝ) (l : ℕ) :
    (∑ r ∈ range (l + 1), k.toFn (5 ^ r) / (a : ℂ) ^ r).im =
      ∑ r ∈ range (l + 1), (k.toFn (5 ^ r)).im / a ^ r := by
  simp only [div_eq_mul_inv, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_add]

/-- Complex tower-supported kernels repair exactly when their weighted partial pole sums lie in `ell2`. -/
theorem mem_paidIdeal_fiveTower_iff (a : ℝ) (ha0 : 0 < a) (ha5 : a < 5)
    (k : WienerAlgebraAt (1 / 2))
    (hk : ∀ n, n ∉ Set.range (fun r : ℕ => 5 ^ r) → k.toFn n = 0) :
    k ∈ paidIdeal (localFactorInverse 5 a)
      (summable_abs_fiveTower_div a (by rwa [abs_of_pos ha0])) ↔
      Summable (fun l : ℕ => (a ^ 2 / 5) ^ l *
        ‖∑ r ∈ range (l + 1), k.toFn (5 ^ r) / (a : ℂ) ^ r‖ ^ 2) := by
  have hre : rePart k = fiveTowerKernelLift (fun r => (k.toFn (5 ^ r)).re) := by
    symm
    apply fiveTowerKernelLift_read_of_support (rePart k)
    intro n hn
    simp only [rePart, hk n hn, Complex.zero_re]
  have him : imPart k = fiveTowerKernelLift (fun r => (k.toFn (5 ^ r)).im) := by
    symm
    apply fiveTowerKernelLift_read_of_support (imPart k)
    intro n hn
    simp only [imPart, hk n hn, Complex.zero_im]
  have hfre := criticalWiener_rePart k
  have hfim := criticalWiener_imPart k
  rw [hre, criticalWiener_fiveTowerKernelLift_iff] at hfre
  rw [him, criticalWiener_fiveTowerKernelLift_iff] at hfim
  rw [mem_paidIdeal, hre, him,
    receiverBounded_fiveTowerKernelLift_iff a ha0.ne' (by rwa [abs_of_pos ha0]) _ hfre,
    receiverBounded_fiveTowerKernelLift_iff a ha0.ne' (by rwa [abs_of_pos ha0]) _ hfim,
    summable_weighted_complex_sq_iff _ (fun l => by positivity)]
  simp only [partialPoleSum_re, partialPoleSum_im]

/-- The actual golden source has the same exact complex payment domain on the prime-five subalgebra. -/
theorem mem_paidIdeal_golden_fiveTower_iff (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (k : WienerAlgebraAt (1 / 2))
    (hk : ∀ n, n ∉ Set.range (fun r : ℕ => 5 ^ r) → k.toFn n = 0) :
    k ∈ paidIdeal (goldenArithmeticSource t)
      (summable_abs_goldenArithmeticSource_div t ht0.le ht1) ↔
      Summable (fun l : ℕ => ((goldenPrimaryRoot * t) ^ 2 / 5) ^ l *
        ‖∑ r ∈ range (l + 1), k.toFn (5 ^ r) / ((goldenPrimaryRoot * t : ℝ) : ℂ) ^ r‖ ^ 2) := by
  have ha0 : 0 < goldenPrimaryRoot * t := mul_pos golden_root_bounds.1 ht0
  have ha5 : goldenPrimaryRoot * t < 5 :=
    (mul_le_of_le_one_right golden_root_bounds.1.le ht1).trans_lt golden_root_bounds.2.1
  rw [paidIdeal_goldenArithmeticSource t ht0.le ht1]
  exact mem_paidIdeal_fiveTower_iff _ ha0 ha5 k hk

/-- The parameter at which the actual golden primary tower meets the critical Wiener radius. -/
def goldenCriticalParameter : ℝ := Real.sqrt 5 / goldenPrimaryRoot

theorem goldenCriticalParameter_bounds :
    0 < goldenCriticalParameter ∧ goldenCriticalParameter < 1 := by
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hroot : Real.sqrt 5 < goldenPrimaryRoot := by
    linarith only [golden_roots_sub, golden_root_bounds.2.2.1]
  exact ⟨div_pos hs golden_root_bounds.1, (div_lt_one golden_root_bounds.1).mpr hroot⟩

theorem golden_primary_at_critical :
    goldenPrimaryRoot * goldenCriticalParameter = Real.sqrt 5 := by
  unfold goldenCriticalParameter
  field_simp [golden_root_bounds.1.ne']

/-- At the actual golden critical parameter, the full complex one-prime domain is the square-partial-sum domain. -/
theorem mem_paidIdeal_golden_critical_fiveTower_iff (k : WienerAlgebraAt (1 / 2))
    (hk : ∀ n, n ∉ Set.range (fun r : ℕ => 5 ^ r) → k.toFn n = 0) :
    k ∈ paidIdeal (goldenArithmeticSource goldenCriticalParameter)
      (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
        goldenCriticalParameter_bounds.2.le) ↔
      Summable (fun l : ℕ =>
        ‖∑ r ∈ range (l + 1), k.toFn (5 ^ r) / (Real.sqrt 5 : ℂ) ^ r‖ ^ 2) := by
  rw [mem_paidIdeal_golden_fiveTower_iff _ goldenCriticalParameter_bounds.1
    goldenCriticalParameter_bounds.2.le k hk]
  simp only [golden_primary_at_critical, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
    div_self (by norm_num : (5 : ℝ) ≠ 0), one_pow, one_mul]

/-- The zero parameter has the unit source and is repaired by every critical Wiener kernel. -/
theorem mem_paidIdeal_golden_zero (k : WienerAlgebraAt (1 / 2)) :
    k ∈ paidIdeal (goldenArithmeticSource 0)
      (summable_abs_goldenArithmeticSource_div 0 (by norm_num) (by norm_num)) := by
  have he : goldenArithmeticSource 0 = unitKernel := by
    funext n
    rw [goldenArithmeticSource_eq_towers]
    simp only [mul_zero]
    ring
  have hc : CriticalWiener (goldenArithmeticSource 0) := by
    rw [he]
    exact criticalWiener_unitKernel
  exact mem_paidIdeal_of_receiverBounded _ _ (receiverBounded_of_criticalWiener _ hc) k

end GaloisForLFunctions.BiarithmeticGeometry
