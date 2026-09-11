import GaloisForLFunctions.RHTower.FokasLenellsCausalIntrinsicFrequency
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare
import Mathlib.Analysis.InnerProductSpace.Basic
open Complex Set Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section FiniteHilbertMeans
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def vectorPencil (s : Finset I) (c z : I → ℂ) (h : I → H) (n : ℕ) : H :=
  ∑ i ∈ s, (c i * z i ^ n) • h i

private theorem unit_cross_phase (z : I → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) (i j : I) :
    star (z i) * z j = 1 ↔ i = j := by
  have hui : z i * star (z i) = 1 := by
    simpa [hz i] using Complex.mul_conj' (z i)
  have hsi : star (z i) * z i = 1 := by
    simpa [hz i] using Complex.conj_mul' (z i)
  constructor
  · intro h
    apply hinj
    symm
    calc
      z j = 1 * z j := (one_mul _).symm
      _ = (z i * star (z i)) * z j := by rw [hui]
      _ = z i * (star (z i) * z j) := by rw [mul_assoc]
      _ = z i := by rw [h, mul_one]
  · rintro rfl
    exact hsi

private theorem vectorPencil_inner_mean [DecidableEq I] (s : Finset I)
    (c z : I → ℂ) (h : I → H) (hz : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective z) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
      inner ℂ (vectorPencil s c z h n) (vectorPencil s c z h n)) atTop
      (𝓝 (∑ i ∈ s, star (c i) * c i * inner ℂ (h i) (h i))) := by
  let pairs : Finset (I × I) := s ×ˢ s
  let C : I × I → ℂ := fun p => star (c p.1) * c p.2 * inner ℂ (h p.1) (h p.2)
  let W : I × I → ℂ := fun p => star (z p.1) * z p.2
  have hW : ∀ p ∈ pairs, ‖W p‖ = 1 := by
    intro p hp
    simp only [W, norm_mul, norm_star, hz, one_mul]
  have hl := RHTower.tendsto_finset_complex_geometric_cesaro pairs C W hW
  convert hl using 1
  · funext N
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    unfold vectorPencil
    rw [sum_inner]
    simp_rw [inner_sum]
    simp only [inner_smul_left, inner_smul_right, map_mul, map_pow]
    simp only [pairs, C, W, mul_pow, starRingEnd_apply]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · apply congrArg 𝓝
    symm
    dsimp only [pairs, C, W]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [if_pos ((unit_cross_phase z hz hinj i i).mpr rfl)]
    · intro j hj hji
      rw [if_neg]
      exact fun hp => hji ((unit_cross_phase z hz hinj i j).mp hp).symm
    · intro hi'
      exact (hi' hi).elim

private theorem hilbert_self_square (x : H) :
    inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
  change inner ℂ x x = (‖x‖ : ℂ) ^ 2 at h
  exact h.trans (Complex.ofReal_pow ‖x‖ 2).symm

private theorem real_mean_inner (x : ℕ → H) (N : ℕ) :
    (((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, inner ℂ (x n) (x n)).re =
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖x n‖ ^ 2 := by
  have he : ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, inner ℂ (x n) (x n) =
      (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖x n‖ ^ 2 : ℝ) : ℂ) := by
    simp only [hilbert_self_square, ← Complex.ofReal_sum]
    rw [Complex.ofReal_mul, Complex.ofReal_inv]
  rw [he, Complex.ofReal_re]

private theorem complex_star_square (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  change (starRingEnd ℂ) z * z = _
  rw [Complex.conj_mul', Complex.ofReal_pow]

private theorem diagonal_real (s : Finset I) (c : I → ℂ) (h : I → H) :
    (∑ i ∈ s, star (c i) * c i * inner ℂ (h i) (h i)).re =
      ∑ i ∈ s, ‖c i‖ ^ 2 * ‖h i‖ ^ 2 := by
  have he : (∑ i ∈ s, star (c i) * c i * inner ℂ (h i) (h i)) =
      ((∑ i ∈ s, ‖c i‖ ^ 2 * ‖h i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [complex_star_square, hilbert_self_square, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [he, Complex.ofReal_re]

private theorem vectorPencil_square_mean [DecidableEq I] (s : Finset I)
    (c z : I → ℂ) (h : I → H) (hz : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective z) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖vectorPencil s c z h n‖ ^ 2) atTop (𝓝 (∑ i ∈ s, ‖c i‖ ^ 2 * ‖h i‖ ^ 2)) := by
  have hc := vectorPencil_inner_mean s c z h hz hinj
  have hr := (Complex.continuous_re.tendsto _).comp hc
  simpa only [Function.comp_def, real_mean_inner, diagonal_real] using! hr
end FiniteHilbertMeans
section CoordinatePackets
variable {E H I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem coordinate_vectorPencil (q : ℕ → E →L[ℂ] H) (v : I → E)
    (h : I → H) (z : I → ℂ)
    (hq : ∀ n i, q n (v i) = z i ^ n • h i)
    (s : Finset I) (c : I → ℂ) (n : ℕ) :
    q n (∑ i ∈ s, c i • v i) = vectorPencil s c z h n := by
  simp only [vectorPencil, map_sum, map_smul, hq, smul_smul]

private theorem nonnegative_cesaro_le (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, f n ≤ C) (N : ℕ) :
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f n ≤ C := by
  by_cases hN : N = 0
  · subst N
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero] using hC
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hi : 0 ≤ (N : ℝ)⁻¹ := by positivity
  calc
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f n ≤
        (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n hn => hf n)) hi
    _ = C := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hn, one_mul]

private theorem coordinate_packet_square_mean [DecidableEq I]
    (q : ℕ → E →L[ℂ] H) (v : I → E) (h : I → H) (z : I → ℂ)
    (hq : ∀ n i, q n (v i) = z i ^ n • h i)
    (hh : ∀ i, ‖h i‖ = 1) (hz : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z)
    (s : Finset I) (c : I → ℂ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖q n (∑ i ∈ s, c i • v i)‖ ^ 2) atTop (𝓝 (∑ i ∈ s, ‖c i‖ ^ 2)) := by
  have hm := vectorPencil_square_mean s c z h hz hinj
  simpa only [coordinate_vectorPencil q v h z hq, hh, one_pow, mul_one] using! hm

private theorem coordinate_packet_lower_bound [DecidableEq I]
    (q : ℕ → E →L[ℂ] H) (v : I → E) (h : I → H) (z : I → ℂ)
    (hq : ∀ n i, q n (v i) = z i ^ n • h i)
    (hb : ∀ n u, ‖q n u‖ ≤ ‖u‖)
    (hh : ∀ i, ‖h i‖ = 1) (hz : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z)
    (s : Finset I) (c : I → ℂ) :
    ∑ i ∈ s, ‖c i‖ ^ 2 ≤ ‖∑ i ∈ s, c i • v i‖ ^ 2 := by
  have hm := coordinate_packet_square_mean q v h z hq hh hz hinj s c
  apply le_of_tendsto hm
  apply Filter.Eventually.of_forall
  intro N
  apply nonnegative_cesaro_le _ _ (sq_nonneg _) _ N
  intro n
  have hb' := hb n (∑ i ∈ s, c i • v i)
  nlinarith [norm_nonneg (q n (∑ i ∈ s, c i • v i)), norm_nonneg (∑ i ∈ s, c i • v i)]
end CoordinatePackets
private theorem packet_rate_injective (b : ℝ) :
    Function.Injective (fun ω : ℝ => (causalUnitBoundaryRate b ω).val) := by
  intro ω η h
  have hr : causalUnitFrequencyRate b ω = causalUnitFrequencyRate b η := Subtype.ext h
  calc
    ω = causalUnitFrequencyCoordinate b (causalUnitFrequencyRate b ω) :=
      (causalUnitFrequencyCoordinate_rate b ω).symm
    _ = causalUnitFrequencyCoordinate b (causalUnitFrequencyRate b η) :=
      congrArg (causalUnitFrequencyCoordinate b) hr
    _ = η := causalUnitFrequencyCoordinate_rate b η

private theorem packet_coordinate (b : ℝ) (n : ℕ) (ω : ℝ) :
    causalBoundedChainCoordinate n (causalBoundedUnitEigenchain b ω) =
      (causalUnitBoundaryRate b ω).val ^ n • (causalUnitBoundaryEigenvector b ω).val := rfl

/-- The exact mean square of all genuine derivative coordinates of any finite
frequency packet equals the sum of its squared scalar amplitudes. Distinctness
comes from the actual rate chart; no orthogonality premise is imposed on the
underlying rational Hilbert data. -/
theorem causalFrequencyPacket_coordinate_square_mean (b : ℝ) (s : Finset ℝ) (c : ℝ → ℂ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖causalBoundedChainCoordinate n (∑ ω ∈ s, c ω • causalBoundedUnitEigenchain b ω)‖ ^ 2)
      atTop (𝓝 (∑ ω ∈ s, ‖c ω‖ ^ 2)) :=
  coordinate_packet_square_mean causalBoundedChainCoordinate (causalBoundedUnitEigenchain b)
    (fun ω => (causalUnitBoundaryEigenvector b ω).val) (fun ω => (causalUnitBoundaryRate b ω).val)
    (packet_coordinate b) (norm_causalUnitBoundaryEigenvector b) (norm_causalUnitBoundaryRate b)
    (packet_rate_injective b) s c

/-- Every actual finite frequency packet has squared bounded-chain norm at least
the sum of its squared amplitudes, regardless of phase cancellation in individual
Hilbert coordinates. -/
theorem causalFrequencyPacket_norm_sq_lower_bound (b : ℝ) (s : Finset ℝ) (c : ℝ → ℂ) :
    ∑ ω ∈ s, ‖c ω‖ ^ 2 ≤ ‖∑ ω ∈ s, c ω • causalBoundedUnitEigenchain b ω‖ ^ 2 :=
  coordinate_packet_lower_bound causalBoundedChainCoordinate (causalBoundedUnitEigenchain b)
    (fun ω => (causalUnitBoundaryEigenvector b ω).val) (fun ω => (causalUnitBoundaryRate b ω).val)
    (packet_coordinate b) causalBoundedChainCoordinate_norm_le
    (norm_causalUnitBoundaryEigenvector b) (norm_causalUnitBoundaryRate b)
    (packet_rate_injective b) s c

end RHTower.FokasLenells
