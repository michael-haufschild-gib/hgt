import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedFrequencyMeans

/-! Squared separation from actual Hardy L2 derivative coordinates.
Only the coordinate space carries the Hilbert inner product. The chain space retains
its genuine supremum norm throughout the argument. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalCoordinateSquareLowerComplete : CompleteSpace (hardyL2ᗮ) :=
  hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalCoordinateSquareChainNormedGroup : NormedAddCommGroup causalBoundedChain :=
  causalBoundedChain.normedAddCommGroup
local instance causalCoordinateSquareChainNormedSpace : NormedSpace ℂ causalBoundedChain :=
  causalBoundedChain.normedSpace

private theorem unit_coordinate (b ω : ℝ) (j : ℕ) :
    causalBoundedChainCoordinate j (causalBoundedUnitEigenchain b ω) =
      (causalUnitBoundaryRate b ω).val^j • (causalUnitBoundaryEigenvector b ω).val := rfl

private theorem unit_rate_conj (b ω : ℝ) :
    (starRingEnd ℂ) (causalUnitBoundaryRate b ω).val = ((causalUnitBoundaryRate b ω).val)⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, norm_causalUnitBoundaryRate,
    one_pow, inv_one, Complex.ofReal_one, mul_one]

private theorem unit_hilbert_difference (x y : hardyL2ᗮ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖^2 = 2 - 2 * (inner ℂ x y).re := by
  rw [norm_sub_sq (𝕜 := ℂ), hx, hy]
  change (1 : ℝ)^2 - 2 * (inner ℂ x y).re + 1^2 = _
  ring

private theorem tendsto_real_part {f : ℕ → ℂ} {z : ℂ}
    (h : Tendsto f atTop (𝓝 z)) : Tendsto (fun N => (f N).re) atTop (𝓝 z.re) := by
  change Tendsto (Complex.re ∘ f) atTop (𝓝 (Complex.re z))
  exact (Complex.continuous_re.tendsto z).comp h

private theorem coordinate_square_identity (b ω η : ℝ) (j : ℕ) :
    ‖causalBoundedChainCoordinate j
      (causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η)‖^2 =
      2 - 2 * (((((causalUnitBoundaryRate b ω).val)⁻¹ *
        (causalUnitBoundaryRate b η).val)^j) *
          inner ℂ (causalUnitBoundaryEigenvector b ω).val
            (causalUnitBoundaryEigenvector b η).val).re := by
  have hi : inner ℂ
      (causalBoundedChainCoordinate j (causalBoundedUnitEigenchain b ω))
      (causalBoundedChainCoordinate j (causalBoundedUnitEigenchain b η)) =
      ((((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val)^j) *
        inner ℂ (causalUnitBoundaryEigenvector b ω).val
          (causalUnitBoundaryEigenvector b η).val := by
    rw [unit_coordinate, unit_coordinate, inner_smul_left, inner_smul_right,
      map_pow, unit_rate_conj, mul_pow]
    ring
  have hd := congrArg (fun v : hardyL2ᗮ => ‖v‖^2)
    ((causalBoundedChainCoordinate j).map_sub
      (causalBoundedUnitEigenchain b ω) (causalBoundedUnitEigenchain b η))
  exact hd.trans ((unit_hilbert_difference
    (causalBoundedChainCoordinate j (causalBoundedUnitEigenchain b ω))
    (causalBoundedChainCoordinate j (causalBoundedUnitEigenchain b η))
    (causalBoundedUnitEigenchain_coordinate_norm b ω j)
    (causalBoundedUnitEigenchain_coordinate_norm b η j)).trans
      (congrArg (fun z : ℂ => 2 - 2 * z.re) hi))

/-- Cesàro mean of the squared differences of genuine derivative coordinates. -/
def causalBoundedCoordinateSquareMean (b ω η : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
    ‖causalBoundedChainCoordinate j
      (causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η)‖^2

/-- Every finite coordinate square mean is bounded by the genuine squared chain distance. -/
theorem causalBoundedCoordinateSquareMean_le (b ω η : ℝ) (N : ℕ) :
    causalBoundedCoordinateSquareMean b ω η N ≤
      ‖causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η‖^2 := by
  have hs (j : ℕ) :
      ‖causalBoundedChainCoordinate j
        (causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η)‖^2 ≤
        ‖causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η‖^2 := by
    have h := causalBoundedChainCoordinate_norm_le j
      (causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η)
    nlinarith [norm_nonneg (causalBoundedChainCoordinate j
      (causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η)),
      norm_nonneg (causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ _j ∈ Finset.range N,
        ‖causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η‖^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hs j))
        (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ ≤ _ := by
      by_cases hN : N = 0
      · simp [hN]
      · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN : (N : ℝ) ≠ 0), one_mul]
        exact le_rfl

private theorem real_cesaro_character (q c : ℂ) (N : ℕ) :
    ((((N : ℝ)⁻¹ : ℂ) * (∑ j ∈ Finset.range N, q^j)) * c).re =
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, (q^j * c).re := by
  rw [mul_assoc, Finset.sum_mul, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]

private theorem square_mean_character (b ω η : ℝ) (N : ℕ) :
    causalBoundedCoordinateSquareMean b ω η N =
      2 * ((N : ℝ)⁻¹ * (N : ℝ)) - 2 *
        ((((N : ℝ)⁻¹ : ℂ) * (∑ j ∈ Finset.range N,
          (((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val)^j)) *
            inner ℂ (causalUnitBoundaryEigenvector b ω).val
              (causalUnitBoundaryEigenvector b η).val).re := by
  rw [causalBoundedCoordinateSquareMean, real_cesaro_character]
  have hs : (∑ j ∈ Finset.range N,
      ‖causalBoundedChainCoordinate j
        (causalBoundedUnitEigenchain b ω - causalBoundedUnitEigenchain b η)‖^2) =
      (N : ℝ) * 2 - 2 * ∑ j ∈ Finset.range N,
        (((((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val)^j) *
          inner ℂ (causalUnitBoundaryEigenvector b ω).val
            (causalUnitBoundaryEigenvector b η).val).re := by
    simp only [coordinate_square_identity, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  rw [hs]
  ring

/-- Distinct actual unit frequencies have coordinate square mean exactly two in the limit. -/
theorem causalBoundedCoordinateSquareMean_tendsto (b ω η : ℝ) :
    Tendsto (causalBoundedCoordinateSquareMean b ω η) atTop (𝓝 (if ω = η then 0 else 2)) := by
  split_ifs with h
  · subst η
    have hz : causalBoundedCoordinateSquareMean b ω ω = (fun _ : ℕ => (0 : ℝ)) := by
      funext N
      simp [causalBoundedCoordinateSquareMean]
    rw [hz]
    exact tendsto_const_nhds
  · let q : ℂ := ((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val
    let c : ℂ := inner ℂ (causalUnitBoundaryEigenvector b ω).val
      (causalUnitBoundaryEigenvector b η).val
    have hn : (causalUnitBoundaryRate b ω).val ≠ 0 := by
      intro hz
      have hh := norm_causalUnitBoundaryRate b ω
      rw [hz, norm_zero] at hh
      norm_num at hh
    have hq : q ≠ 1 := by
      intro he
      have he' := congrArg (fun z : ℂ => (causalUnitBoundaryRate b ω).val * z) he
      change (causalUnitBoundaryRate b ω).val *
        (((causalUnitBoundaryRate b ω).val)⁻¹ * (causalUnitBoundaryRate b η).val) =
          (causalUnitBoundaryRate b ω).val * 1 at he'
      simp only [← mul_assoc, mul_inv_cancel₀ hn, one_mul, mul_one] at he'
      exact h ((causalUnitBoundaryRate_injective b he').symm)
    have hqn : ‖q‖ ≤ 1 := by
      dsimp [q]
      rw [norm_mul, norm_inv, norm_causalUnitBoundaryRate, norm_causalUnitBoundaryRate]
      norm_num
    have hgeom : Tendsto (fun N : ℕ =>
        ((((N : ℝ)⁻¹ : ℂ) * (∑ j ∈ Finset.range N, q^j)) * c).re) atTop (𝓝 0) := by
      have ht := tendsto_real_part
        ((tendsto_geomSum_cesaro_of_norm_le_one hqn hq).mul_const c)
      simpa only [Function.comp_apply, zero_mul, Complex.zero_re] using ht
    have hone : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (N : ℝ)) atTop (𝓝 1) := by
      have ht := tendsto_real_part tendsto_geomSum_cesaro_one
      simpa only [Function.comp_apply, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Complex.one_re, Complex.natCast_re,
        Complex.natCast_im] using ht
    have ht := (hone.const_mul (2 : ℝ)).sub (hgeom.const_mul (2 : ℝ))
    have he : causalBoundedCoordinateSquareMean b ω η = (fun N : ℕ =>
        2 * ((N : ℝ)⁻¹ * (N : ℝ)) -
          2 * ((((N : ℝ)⁻¹ : ℂ) * (∑ j ∈ Finset.range N, q^j)) * c).re) :=
      funext (square_mean_character b ω η)
    rw [he]
    simpa only [mul_one, mul_zero, sub_zero] using ht

/-- Genuine unit-frequency chains are separated by at least the square root of two in chain norm. -/
theorem causalBoundedUnitEigenchain_pairwise_square_separated (b : ℝ) :
    Pairwise (fun ω η : ℝ => 2 ≤
      (dist (causalBoundedUnitEigenchain b ω) (causalBoundedUnitEigenchain b η))^2) := by
  intro ω η h
  have ht := causalBoundedCoordinateSquareMean_tendsto b ω η
  rw [if_neg h] at ht
  have hb := le_of_tendsto ht (Filter.Eventually.of_forall
    (fun N => causalBoundedCoordinateSquareMean_le b ω η N))
  simpa only [dist_eq_norm] using hb

end
end RHTower.FokasLenells
