import GaloisForLFunctions.RHTower.DeBruijnNewmanHalfBound
import GaloisForLFunctions.RHTower.XiGlobalKummerAugmentation

/-!
# Separation of signed Xi source divisors

The exact positive Riemann-kernel representation bounds Xi on the imaginary
axis by Xi(0)=1/2. Equal-radius exponential translates with coefficient norm
greater than 1/2 therefore have disjoint zeros unless their labels coincide.
This separates every positive and negative integer-labelled source factor.
-/

open Complex MeasureTheory
namespace RHTower.XiGlobalKummer
open DeBruijn

/-- The established Riemann transform, with the spectral variable eliminated. -/
theorem xi_eq_positive_bilateral_integral (s : ℂ) :
    xi s = ∫ x : ℝ, (riemannKernelReal x : ℂ) * Complex.exp ((s - 1 / 2) * x) := by
  have ht := cosTransform_riemannKernel (-I * (s - 1 / 2))
  have ha : (1 / 2 : ℂ) + I * (-I * (s - 1 / 2)) = s := by
    ring_nf
    rw [I_sq]
    ring
  rw [ha] at ht
  rw [← ht]
  unfold cosTransform
  congr 1
  funext x
  congr 1
  congr 1
  ring_nf
  rw [I_sq]
  ring

/-- Taking absolute values in the exact positive-kernel representation. -/
theorem norm_xi_le_real_axis (s : ℂ) : ‖xi s‖ ≤ (xi (s.re : ℂ)).re := by
  have hnorm (x : ℝ) :
      ‖(riemannKernelReal x : ℂ) * Complex.exp ((s - 1 / 2) * x)‖ =
        riemannKernelReal x * Real.exp ((s.re - 1 / 2) * x) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (riemannKernelReal_pos x), Complex.norm_exp]
    congr 2
    norm_num [Complex.mul_re, Complex.sub_re]
  have hreal : xi (s.re : ℂ) =
      ((∫ x : ℝ, riemannKernelReal x * Real.exp ((s.re - 1 / 2) * x) : ℝ) : ℂ) := by
    rw [xi_eq_positive_bilateral_integral, ← integral_complex_ofReal]
    congr 1
    funext x
    push_cast
    rfl
  rw [xi_eq_positive_bilateral_integral, hreal, Complex.ofReal_re]
  have hb := norm_integral_le_integral_norm (μ := volume)
    (fun x : ℝ => (riemannKernelReal x : ℂ) * Complex.exp ((s - 1 / 2) * x))
  simpa only [hnorm] using hb

theorem norm_xi_le_half_of_re_zero {s : ℂ} (hs : s.re = 0) : ‖xi s‖ ≤ 1 / 2 := by
  have h := norm_xi_le_real_axis s
  simpa [hs, xi_zero] using h


/-- Equal-radius exponential perturbations have disjoint zero sets unless
both their real rates and complex coefficients agree. -/
theorem exponential_translate_label_injective_at_zero
    {h k : ℝ} {c d s : ℂ} (hc : 1 / 2 < ‖c‖) (hcd : ‖c‖ = ‖d‖)
    (hz : xi s + c * Complex.exp ((h : ℂ) * s) = 0)
    (hw : xi s + d * Complex.exp ((k : ℂ) * s) = 0) : h = k ∧ c = d := by
  have he : c * Complex.exp ((h : ℂ) * s) = d * Complex.exp ((k : ℂ) * s) := by
    linear_combination hz - hw
  have hn := congrArg norm he
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hn
  rw [← hcd] at hn
  have hc0 : ‖c‖ ≠ 0 := by linarith
  have hr : h * s.re = k * s.re := Real.exp_injective (mul_left_cancel₀ hc0 hn)
  have hrate : h = k := by
    by_contra hne
    have hre : s.re = 0 := by
      have hp : (h - k) * s.re = 0 := by nlinarith
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hne)
    have hnorm : ‖xi s‖ = ‖c‖ := by
      have hx : xi s = -(c * Complex.exp ((h : ℂ) * s)) := by linear_combination hz
      rw [hx, norm_neg, norm_mul, Complex.norm_exp]
      simp [Complex.mul_re, hre]
    have hb := norm_xi_le_half_of_re_zero hre
    linarith
  refine ⟨hrate, ?_⟩
  rw [hrate] at he
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) he

private theorem exp_neg_log_mul_exp_log (n : ℕ) (s : ℂ) :
    Complex.exp (-s * (Real.log n : ℂ)) * Complex.exp ((Real.log n : ℂ) * s) = 1 := by
  rw [← Complex.exp_add, show -s * (Real.log n : ℂ) + (Real.log n : ℂ) * s = 0 by ring,
    Complex.exp_zero]

theorem augmentationFactor_mul_exp (n : ℕ) (s : ℂ) :
    augmentationFactor n s * Complex.exp ((Real.log n : ℂ) * s) =
      xi s + Complex.exp ((Real.log n : ℂ) * s) := by
  dsimp [augmentationFactor, deletionFactor]
  linear_combination (xi s) * exp_neg_log_mul_exp_log n s

theorem deletionFactor_mul_exp (n : ℕ) (s : ℂ) :
    deletionFactor n s * Complex.exp ((Real.log n : ℂ) * s) =
      Complex.exp ((Real.log n : ℂ) * s) - xi s := by
  dsimp [deletionFactor]
  linear_combination -(xi s) * exp_neg_log_mul_exp_log n s

theorem xi_ne_zero_of_augmentationFactor_zero {n : ℕ} {s : ℂ}
    (hz : augmentationFactor n s = 0) : xi s ≠ 0 := by
  intro hx
  norm_num [augmentationFactor, deletionFactor, hx] at hz

/-- Positive companions of different integer labels have disjoint divisors. -/
theorem augmentationFactor_label_injective_at_zero {n m : ℕ} {s : ℂ}
    (hn : 0 < n) (hm : 0 < m)
    (hz : augmentationFactor n s = 0) (hw : augmentationFactor m s = 0) : n = m := by
  have hz' : xi s + (1 : ℂ) * Complex.exp ((Real.log n : ℂ) * s) = 0 := by
    simpa [hz] using (augmentationFactor_mul_exp n s).symm
  have hw' : xi s + (1 : ℂ) * Complex.exp ((Real.log m : ℂ) * s) = 0 := by
    simpa [hw] using (augmentationFactor_mul_exp m s).symm
  have he := congrArg Real.exp (exponential_translate_label_injective_at_zero
    (by norm_num) rfl hz' hw').1
  rw [Real.exp_log (by exact_mod_cast hn), Real.exp_log (by exact_mod_cast hm)] at he
  exact_mod_cast he

/-- A positive and a negative companion never have a common zero, even at equal labels. -/
theorem deletionFactor_ne_zero_of_augmentationFactor_zero {n m : ℕ} {s : ℂ}
    (hz : augmentationFactor n s = 0) : deletionFactor m s ≠ 0 := by
  intro hw
  have hz' : xi s + (1 : ℂ) * Complex.exp ((Real.log n : ℂ) * s) = 0 := by
    simpa [hz] using (augmentationFactor_mul_exp n s).symm
  have hw' : xi s + (-1 : ℂ) * Complex.exp ((Real.log m : ℂ) * s) = 0 := by
    have h := deletionFactor_mul_exp m s
    rw [hw, zero_mul] at h
    linear_combination h
  have he := (exponential_translate_label_injective_at_zero
    (by norm_num) (by norm_num) hz' hw').2
  norm_num at he

/-- Negative companions of different positive integer labels have disjoint divisors. -/
theorem deletionFactor_label_injective_at_zero {n m : ℕ} {s : ℂ}
    (hn : 0 < n) (hm : 0 < m)
    (hz : deletionFactor n s = 0) (hw : deletionFactor m s = 0) : n = m := by
  have hz' : xi s + (-1 : ℂ) * Complex.exp ((Real.log n : ℂ) * s) = 0 := by
    have h := deletionFactor_mul_exp n s
    rw [hz, zero_mul] at h
    linear_combination h
  have hw' : xi s + (-1 : ℂ) * Complex.exp ((Real.log m : ℂ) * s) = 0 := by
    have h := deletionFactor_mul_exp m s
    rw [hw, zero_mul] at h
    linear_combination h
  have he := congrArg Real.exp (exponential_translate_label_injective_at_zero
    (by norm_num) rfl hz' hw').1
  rw [Real.exp_log (by exact_mod_cast hn), Real.exp_log (by exact_mod_cast hm)] at he
  exact_mod_cast he

end RHTower.XiGlobalKummer
