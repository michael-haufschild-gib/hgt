import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheInterpolationWeightsAdmitNearbyLogarithms
import GaloisForLFunctions.HTGeometry.LagrangeNodeBounds
import GaloisForLFunctions.HTGeometry.PolynomialExtrapolationRemez
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds

/-!
# Exponential interpolation with controlled remainder

Lagrange weights cancel every nonconstant monomial below the node count.
The exponential Taylor remainder therefore controls the whole block.
Index separation retains the factorial denominator in the total weight.
-/

open Complex Finset Polynomial

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Interpolation weights reproduce the moments of evaluation at zero. -/
theorem sum_zeroInterpolationWeight_mul_pow {N k : ℕ} {z : Fin N → ℂ}
    (hz : Function.Injective z) (hk : k < N) :
    ∑ j, zeroInterpolationWeight z j * z j ^ k = (0 : ℂ) ^ k := by
  have hdeg : ((X : Polynomial ℂ) ^ k).degree < (N : ℕ) := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast hk
  have hh := HTGeometry.eval_eq_sum_lagrange z hz ((X : Polynomial ℂ) ^ k) hdeg 0
  simp only [Polynomial.eval_pow, Polynomial.eval_X, zero_sub] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  congr 1
  unfold zeroInterpolationWeight
  apply Finset.prod_congr rfl
  intro k _
  rw [div_eq_mul_inv, mul_comm]

private theorem sum_weighted_exp_section {N : ℕ} (hN : 0 < N) {z : Fin N → ℂ}
    (hz : Function.Injective z) (v : ℂ) :
    ∑ j, zeroInterpolationWeight z j *
      (∑ k ∈ Finset.range N, (v * z j) ^ k / (k.factorial : ℂ)) = 1 := by
  calc
    _ = ∑ k ∈ Finset.range N, (v ^ k / (k.factorial : ℂ)) *
        (∑ j, zeroInterpolationWeight z j * z j ^ k) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow]
      ring
    _ = ∑ k ∈ Finset.range N, (v ^ k / (k.factorial : ℂ)) * (0 : ℂ) ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [sum_zeroInterpolationWeight_mul_pow hz (Finset.mem_range.mp hk)]
    _ = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        simp only [zero_pow hk0, mul_zero]
      · intro h
        exact False.elim (h (Finset.mem_range.mpr hN))

/-- The exponential interpolation error is bounded by the Taylor tail times total weight. -/
theorem norm_weighted_exponential_sum_sub_one_le {N : ℕ} (hN : 0 < N)
    {z : Fin N → ℂ} (hz : Function.Injective z) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ j, ‖z j‖ ≤ B) (v : ℂ) :
    ‖(∑ j, zeroInterpolationWeight z j * Complex.exp (v * z j)) - 1‖ ≤
      (∑ j, ‖zeroInterpolationWeight z j‖) *
        (((‖v‖ * B) ^ N / (N.factorial : ℝ)) * Real.exp (‖v‖ * B)) := by
  rw [← sum_weighted_exp_section hN hz v, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖zeroInterpolationWeight z j * Complex.exp (v * z j) -
        zeroInterpolationWeight z j * (∑ k ∈ Finset.range N, (v * z j) ^ k / (k.factorial : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, ‖zeroInterpolationWeight z j‖ *
        (((‖v‖ * B) ^ N / (N.factorial : ℝ)) * Real.exp (‖v‖ * B)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      refine (RHTower.norm_complex_exp_sub_sum_le_factorial_tail (v * z j) N).trans ?_
      have hn : ‖v * z j‖ ≤ ‖v‖ * B := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound j) (norm_nonneg _)
      gcongr
    _ = _ := by rw [Finset.sum_mul]

/-- Index separation bounds one complex interpolation weight with the full factorial denominator. -/
theorem norm_zeroInterpolationWeight_le_index_separation {k : ℕ} (z : Fin (k + 1) → ℂ)
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hb : ∀ i, ‖z i‖ ≤ B)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ ‖z i - z j‖)
    (i : Fin (k + 1)) :
    ‖zeroInterpolationWeight z i‖ ≤
      (B / δ) ^ k * (∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ := by
  have hcard : (univ.erase i).card = k := by simp
  unfold zeroInterpolationWeight
  rw [norm_prod]
  calc
    _ ≤ ∏ j ∈ univ.erase i, (B / δ) * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|⁻¹ := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro j hj
      have hij : 0 < |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
        rw [abs_pos, sub_ne_zero]
        intro he
        have he' : (i : ℕ) = (j : ℕ) := by exact_mod_cast he
        exact (Finset.mem_erase.mp hj).1 (Fin.ext he').symm
      rw [norm_div, norm_neg]
      have hid : (B / δ) * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|⁻¹ =
          B / (|((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ) := by ring
      rw [hid]
      exact div_le_div₀ hB (hb j) (mul_pos hij hδ) (hsep i j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, Finset.prod_inv_distrib]

/-- The total complex interpolation weight has only exponential loss at a regular node spacing. -/
theorem sum_norm_zeroInterpolationWeight_le {k : ℕ} (z : Fin (k + 1) → ℂ)
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hb : ∀ i, ‖z i‖ ≤ B)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ ‖z i - z j‖) :
    ∑ i, ‖zeroInterpolationWeight z i‖ ≤ (2 * B / δ) ^ k / (k.factorial : ℝ) := by
  calc
    _ ≤ ∑ i : Fin (k + 1), (B / δ) ^ k *
        (∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ :=
      Finset.sum_le_sum (fun i _ => norm_zeroInterpolationWeight_le_index_separation z hδ hB hb hsep i)
    _ = (B / δ) ^ k * (2 ^ k / (k.factorial : ℝ)) := by
      rw [← Finset.mul_sum, HTGeometry.sum_inv_prod_erase_abs_sub_fin]
    _ = _ := by rw [← mul_div_assoc, ← mul_pow]; congr 1 <;> ring

/-- Exact coefficient calibration turns the interpolation estimate into a literal exponential block. -/
theorem norm_calibrated_exponential_block_sub_one_le {k : ℕ} {z : Fin (k + 1) → ℂ}
    (hz : Function.Injective z) {T δ B R : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hb : ∀ i, ‖z i‖ ≤ B)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ ‖z i - z j‖)
    (hcal : ∀ i, Complex.exp ((T : ℂ) * z i) = zeroInterpolationWeight z i)
    {v : ℝ} (hv : |v| ≤ R) :
    ‖(∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)) - 1‖ ≤
      ((2 * B / δ) ^ k / (k.factorial : ℝ)) *
        (((R * B) ^ (k + 1) / ((k + 1).factorial : ℝ)) * Real.exp (R * B)) := by
  have hid : (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)) =
      ∑ i, zeroInterpolationWeight z i * Complex.exp ((v : ℂ) * z i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, hcal i]
  rw [hid]
  refine (norm_weighted_exponential_sum_sub_one_le (by omega) hz hB hb (v : ℂ)).trans ?_
  have hm := sum_norm_zeroInterpolationWeight_le z hδ hB hb hsep
  simp only [Complex.norm_real, Real.norm_eq_abs]
  gcongr

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
