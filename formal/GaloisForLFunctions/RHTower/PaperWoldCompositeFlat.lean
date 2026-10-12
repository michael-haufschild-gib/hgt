import GaloisForLFunctions.RHTower.PaperWoldFullMeans

/-! # Weakly null probes on the literal even-composite coordinates

The probes have norm one and retain exactly their original arithmetic matrix
entries. Every compact operator sends them to zero in norm and quadratic form.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal InnerProductSpace

def paperWoldCompositeFlat (N : ℕ) : PaperWoldHistory :=
  ∑ k ∈ Finset.range (N + 1), lp.single 2 (2 * k + 2) (paperWoldFlatAmplitude N : ℂ)

private theorem compositeIndex_injective : Function.Injective (fun k : ℕ => 2 * k + 2) := by
  intro a b h
  change 2 * a + 2 = 2 * b + 2 at h
  omega

theorem paperWoldCompositeFlat_eq_image (N : ℕ) :
    paperWoldCompositeFlat N = ∑ n ∈ (Finset.range (N + 1)).image (fun k => 2 * k + 2),
      lp.single 2 n (paperWoldFlatAmplitude N : ℂ) := by
  symm
  exact Finset.sum_image compositeIndex_injective.injOn

theorem paperWoldCompositeFlat_norm (N : ℕ) : ‖paperWoldCompositeFlat N‖ = 1 := by
  have h := lp.norm_sum_single (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (fun _ : ℕ => (paperWoldFlatAmplitude N : ℂ))
    ((Finset.range (N + 1)).image (fun k => 2 * k + 2))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperWoldFlatAmplitude_nonneg N), Finset.sum_const,
    Finset.card_image_of_injective _ compositeIndex_injective, Finset.card_range,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, paperWoldFlatAmplitude_sq] at h
  rw [mul_inv_cancel₀ (by positivity : (N : ℝ) + 1 ≠ 0), ← paperWoldCompositeFlat_eq_image] at h
  nlinarith [norm_nonneg (paperWoldCompositeFlat N)]

theorem paperWoldCompositeFlat_coordinate_bound (N n : ℕ) :
    ‖paperWoldCompositeFlat N n‖ ≤ paperWoldFlatAmplitude N := by
  rw [paperWoldCompositeFlat_eq_image]
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single]
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (paperWoldFlatAmplitude_nonneg N)]
  · simpa only [norm_zero] using paperWoldFlatAmplitude_nonneg N

theorem paperWoldCompositeFlat_coordinate_tendsto (n : ℕ) :
    Tendsto (fun N => paperWoldCompositeFlat N n) atTop (𝓝 0) :=
  squeeze_zero_norm (fun N => paperWoldCompositeFlat_coordinate_bound N n)
    paperWoldFlatAmplitude_tendsto

theorem paperWoldCompositeFlat_weak_tendsto (x : PaperWoldHistory) :
    Tendsto (fun N => inner ℂ x (paperWoldCompositeFlat N)) atTop (𝓝 0) :=
  tendsto_inner_lp_of_coord paperWoldCompositeFlat zero_le_one
    (fun N => (paperWoldCompositeFlat_norm N).le) paperWoldCompositeFlat_coordinate_tendsto x

theorem paperWoldCompositeFlat_compact_tendsto (K : compactOperatorStarAlgebra PaperWoldHistory) :
    Tendsto (fun N => K.1 (paperWoldCompositeFlat N)) atTop (𝓝 0) :=
  tendsto_norm_compact_of_weaklyNull K.1 K.2 paperWoldCompositeFlat
    (fun N => (paperWoldCompositeFlat_norm N).le) paperWoldCompositeFlat_weak_tendsto

theorem paperWoldCompositeFlat_compact_form_tendsto
    (K : compactOperatorStarAlgebra PaperWoldHistory) :
    Tendsto (fun N => inner ℂ (paperWoldCompositeFlat N) (K.1 (paperWoldCompositeFlat N)))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _)
    (fun N => (norm_inner_le_norm _ _).trans_eq (by rw [paperWoldCompositeFlat_norm, one_mul]))
  exact tendsto_zero_iff_norm_tendsto_zero.mp (paperWoldCompositeFlat_compact_tendsto K)

theorem paperWoldCompositeFlat_eq_smul_sum (N : ℕ) :
    paperWoldCompositeFlat N = (paperWoldFlatAmplitude N : ℂ) •
      ∑ k ∈ Finset.range (N + 1), lp.single 2 (2 * k + 2) (1 : ℂ) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← lp.single_smul]
  simp only [smul_eq_mul, mul_one]

theorem paperWoldCompositeFlat_quadratic (T : PaperWoldHistory →L[ℂ] PaperWoldHistory) (N : ℕ) :
    inner ℂ (paperWoldCompositeFlat N) (T (paperWoldCompositeFlat N)) =
      Complex.ofReal (((N : ℝ) + 1)⁻¹) * ∑ n ∈ Finset.range (N + 1),
        ∑ j ∈ Finset.range (N + 1), T (lp.single 2 (2 * j + 2) (1 : ℂ)) (2 * n + 2) := by
  have h : inner ℂ (∑ n ∈ Finset.range (N + 1), lp.single 2 (2 * n + 2) (1 : ℂ))
      (T (∑ j ∈ Finset.range (N + 1), lp.single 2 (2 * j + 2) (1 : ℂ))) =
      ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        T (lp.single 2 (2 * j + 2) (1 : ℂ)) (2 * n + 2) := by
    simp only [map_sum, sum_inner, inner_sum, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    exact Finset.sum_comm
  simp only [paperWoldCompositeFlat_eq_smul_sum, map_smul, inner_smul_left, inner_smul_right]
  rw [h, Complex.conj_ofReal, ← mul_assoc, ← pow_two, ← Complex.ofReal_pow, paperWoldFlatAmplitude_sq]

end
end RHTower
