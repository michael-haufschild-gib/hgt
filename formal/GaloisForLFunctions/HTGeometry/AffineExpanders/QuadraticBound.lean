import GaloisForLFunctions.HTGeometry.AffineExpanders.FrequencyWeights
import GaloisForLFunctions.HTGeometry.FiniteCyclicAffineCorrelations

/-!
# The affine expander quadratic bound

Fourier duality converts the four affine correlations to weighted shear correlations.
The reciprocal row estimate and Parseval bound the zero-sum quadratic form by
`5√2/8` times its energy.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix
namespace GaloisForLFunctions.HTGeometry
variable {n : ℕ} [NeZero n]

private theorem abs_re_phase_correlation_le (z w : ℂ) (a : ZMod n) :
    |(conj z * ((1 + ZMod.stdAddChar a) * w)).re| ≤
      2 * (mggCosineWeight a * ‖z‖ * ‖w‖) := by
  calc
    _ ≤ ‖conj z * ((1 + ZMod.stdAddChar a) * w)‖ := Complex.abs_re_le_norm _
    _ = _ := by rw [norm_mul, norm_mul, Complex.norm_conj, norm_one_add_stdAddChar];
                unfold mggCosineWeight; ring

/-- On zero-sum functions, the MGG quadratic form is bounded by `5√2/8` times energy.
The Fourier transform removes the zero mode; reciprocal shear weights bound the others. -/
theorem mggAffineMatrix_quadratic_le (hn : 3 ≤ n) (f : ZMod n × ZMod n → ℝ)
    (hf : ∑ a, f a = 0) :
    |∑ a, f a * (mggAffineMatrix n *ᵥ f) a| ≤
      5 * Real.sqrt 2 / 8 * ∑ a, f a ^ 2 := by
  let F := cyclicPairFourier (fun a => (f a : ℂ))
  have hF : F 0 = 0 := by
    change cyclicPairFourier (fun a => (f a : ℂ)) (0, 0) = 0
    rw [cyclicPairFourier_zero, ← Complex.ofReal_sum, hf, Complex.ofReal_zero]
  have hspatial : 4 * (∑ a, f a * (mggAffineMatrix n *ᵥ f) a) =
      (∑ a, f a * (f (a.1 + 2 * a.2, a.2) + f (a.1 + 2 * a.2 + 1, a.2))) +
      (∑ a, f a * (f (a.1, a.2 + 2 * a.1) + f (a.1, a.2 + 2 * a.1 + 1))) := by
    rw [mggAffineMatrix_quadratic, Fin.sum_univ_four]
    change 4 * (((∑ a, f a * f (a.1 + 2 * a.2 + 0, a.2)) +
      (∑ a, f a * f (a.1, a.2 + 2 * a.1 + 0)) +
      (∑ a, f a * f (a.1 + 2 * a.2 + 1, a.2)) +
      (∑ a, f a * f (a.1, a.2 + 2 * a.1 + 1))) / 4) = _
    simp only [add_zero, mul_add, Finset.sum_add_distrib]
    ring
  have hx := cyclicPairFourier_correlationX (fun a => (f a : ℂ)) 2
  have hy := cyclicPairFourier_correlationY (fun a => (f a : ℂ)) 2
  simp only [Complex.conj_ofReal, ← Complex.ofReal_add, ← Complex.ofReal_mul,
    Complex.ofReal_re] at hx hy
  have hfourier : (n : ℝ) ^ 2 * (4 * (∑ a, f a * (mggAffineMatrix n *ᵥ f) a)) =
      (∑ a, (conj (F a) * ((1 + ZMod.stdAddChar a.1) * F (a.1, a.2 - 2 * a.1))).re) +
      (∑ a, (conj (F a) * ((1 + ZMod.stdAddChar a.2) * F (a.1 - 2 * a.2, a.2))).re) := by
    rw [hspatial, mul_add, hx, hy]
  have habs : (n : ℝ) ^ 2 * |4 * (∑ a, f a * (mggAffineMatrix n *ᵥ f) a)| ≤
      2 * ((∑ a, mggCosineWeight a.1 * ‖F a‖ * ‖F (a.1, a.2 - 2 * a.1)‖) +
        (∑ a, mggCosineWeight a.2 * ‖F a‖ * ‖F (a.1 - 2 * a.2, a.2)‖)) := by
    rw [← abs_of_nonneg (sq_nonneg (n : ℝ)), ← abs_mul, hfourier]
    calc
      _ ≤ (∑ a, |(conj (F a) * ((1 + ZMod.stdAddChar a.1) * F (a.1, a.2 - 2 * a.1))).re|) +
          (∑ a, |(conj (F a) * ((1 + ZMod.stdAddChar a.2) * F (a.1 - 2 * a.2, a.2))).re|) :=
        (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ _ := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        exact add_le_add
          (Finset.sum_le_sum fun a _ => abs_re_phase_correlation_le _ _ _)
          (Finset.sum_le_sum fun a _ => abs_re_phase_correlation_le _ _ _)
  have hweight := mgg_frequency_correlation_le hn (fun a => ‖F a‖) (by rw [hF, norm_zero])
  have hparseval := cyclicPairFourier_parseval (fun a => (f a : ℂ))
  have henergy : (∑ a, ‖F a‖ ^ 2) = (n : ℝ) ^ 2 * ∑ a, f a ^ 2 := by
    simpa only [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      sq_abs] using hparseval
  have hcombined : (n : ℝ) ^ 2 * |4 * (∑ a, f a * (mggAffineMatrix n *ᵥ f) a)| ≤
      2 * (5 * Real.sqrt 2 / 4 * ((n : ℝ) ^ 2 * ∑ a, f a ^ 2)) :=
    habs.trans (mul_le_mul_of_nonneg_left (henergy ▸ hweight) (by norm_num))
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hcombined
  have hnpos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr (NeZero.pos n))
  have hcancel : (n : ℝ) ^ 2 *
      (4 * |∑ a, f a * (mggAffineMatrix n *ᵥ f) a|) ≤
      (n : ℝ) ^ 2 * (4 * (5 * Real.sqrt 2 / 8 * ∑ a, f a ^ 2)) := by
    convert hcombined using 1; ring
  have h := (mul_le_mul_iff_right₀ hnpos).mp hcancel
  linarith only [h]

end GaloisForLFunctions.HTGeometry
