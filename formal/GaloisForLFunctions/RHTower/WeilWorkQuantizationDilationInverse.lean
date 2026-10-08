import GaloisForLFunctions.RHTower.WeilWorkQuantizationDirichletInverse

/-!
# Absolute dilation inversion

Summable inverse Dirichlet coefficients invert the complete dilation sum of
every bounded function. The proof keeps every resonance and justifies the
double sum before regrouping it by the product of the two integer indices.
-/

open Complex Set
noncomputable section
namespace RHTower.WeilSpectral
open GaloisForLFunctions.HTGeometry IntegerMassRigidity AbelianTwist

theorem quantization_dilation_inverse {a b : ℕ → ℂ}
    (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (hinv : ∀ n, LSeries.convolution b a n = if n = 1 then 1 else 0)
    {f : ℝ → ℂ} {K : ℝ} (hbound : ∀ x, ‖f x‖ ≤ K) (x : ℝ) :
    (∑' n : ℕ, b n * ∑' m : ℕ, a m * f ((x / n) / m)) = f x := by
  classical
  let H : ℕ × ℕ → ℂ := fun q => b q.1 * a q.2 * f (x / (q.1 * q.2 : ℕ))
  have hsum : Summable H := by
    apply ((hb.mul_norm ha).mul_right K).of_norm_bounded
    intro q
    dsimp only [H]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
  have hgroup (n : ℕ) :
      (∑' q : (fun q : ℕ × ℕ => q.1 * q.2) ⁻¹' {n}, H q) =
        LSeries.convolution b a n * f (x / n) := by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.convolution_map_zero, zero_mul]
      have hz : ∀ q : (fun q : ℕ × ℕ => q.1 * q.2) ⁻¹' {0}, H q = 0 := by
        rintro ⟨⟨i,j⟩, hij⟩
        have he : i * j = 0 := hij
        rcases Nat.mul_eq_zero.mp he with hi | hj
        · simp [H, hi, hb0]
        · simp [H, hj, ha0]
      simp only [hz, tsum_zero]
    · rw [show (fun q : ℕ × ℕ => q.1 * q.2) ⁻¹' {n} = n.divisorsAntidiagonal from
        Set.ext fun q => by simp [hn]]
      rw [Finset.tsum_subtype', LSeries.convolution_def, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [H, (Nat.mem_divisorsAntidiagonal.mp hq).1]
  have he := (hsum.hasSum.tsum_fiberwise (fun q : ℕ × ℕ => q.1 * q.2)).tsum_eq
  have hcollapse : (∑' q, H q) = f x := by
    rw [← he]
    simp_rw [hgroup, hinv]
    simp
  rw [← hcollapse, hsum.tsum_prod]
  apply tsum_congr
  intro n
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  simp only [H, Nat.cast_mul, div_div, mul_assoc]

/-- The original source supplies every coefficient and summability bound in
the inverse action; only the bounded function being acted on is arbitrary. -/
theorem quantization_actual_dilation_inverse {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {f : ℝ → ℂ} {K : ℝ} (hbound : ∀ x, ‖f x‖ ≤ K) (x : ℝ) :
    (∑' n : ℕ, LSeries.term (quantizationInverseCoeff lam) (((3 / 2 : ℝ) : ℂ)) n *
      ∑' m : ℕ, LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) m *
        f ((x / n) / m)) = f x := by
  apply quantization_dilation_inverse (summable_quantization_forward_terms hW)
    (summable_quantization_inverse_terms hW) (by simp) (by simp) ?_ hbound
  intro n
  rw [LSeries.convolution_def]
  dsimp only
  rw [← LSeries.term_convolution]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, quantization_inverse_convolution hW]
  by_cases hn1 : n = 1
  · simp [hn1]
  · simp [hn1]

end RHTower.WeilSpectral
