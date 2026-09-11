import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyHilbertMean
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section CoherentPackets
variable {H I : Type*} [NormedAddCommGroup H]
private theorem infinite_small_cluster [Uncountable I]
    [TopologicalSpace.SeparableSpace H] (v : I → H) :
    ∃ i₀, {i | ‖v i₀ - v i‖ < (1 / 2 : ℝ)}.Infinite := by
  classical
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  let F : ℕ → Set I := fun n => {i | dist (v i) (d n) < (1 / 4 : ℝ)}
  have hcover : (⋃ n, F n) = Set.univ := by
    ext i
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact (Metric.denseRange_iff.mp hd) (v i) (1 / 4) (by norm_num)
  have hex : ∃ n, (F n).Infinite := by
    by_contra h
    have hf : ∀ n, (F n).Finite := by
      intro n
      by_contra hn
      exact h ⟨n, hn⟩
    apply Set.not_countable_univ (α := I)
    rw [← hcover]
    exact Set.countable_iUnion (fun n => (hf n).countable)
  obtain ⟨n, hn⟩ := hex
  obtain ⟨i₀, hi₀⟩ := hn.nonempty
  refine ⟨i₀, ?_⟩
  intro hfinite
  apply hn
  apply hfinite.subset
  intro i hi
  change ‖v i₀ - v i‖ < (1 / 2 : ℝ)
  have h₀ : dist (v i₀) (d n) < (1 / 4 : ℝ) := hi₀
  have h₁ : dist (v i) (d n) < (1 / 4 : ℝ) := hi
  have ht := dist_triangle (v i₀) (d n) (v i)
  rw [dist_comm (d n) (v i), dist_eq_norm (v i₀) (v i)] at ht
  linarith

private theorem coherent_packet_norm_lower [NormedSpace ℂ H]
    (v : I → H) (hv : ∀ i, ‖v i‖ = 1) (s : Finset I) (i₀ : I)
    (hc : ∀ i ∈ s, ‖v i₀ - v i‖ ≤ (1 / 2 : ℝ)) :
    (s.card : ℝ) / 2 ≤ ‖∑ i ∈ s, v i‖ := by
  have hconst : ‖∑ _i ∈ s, v i₀‖ = (s.card : ℝ) := by
    simp only [Finset.sum_const, RCLike.norm_nsmul ℂ, hv, nsmul_eq_mul, mul_one]
  have hdiff : ‖(∑ _i ∈ s, v i₀) - ∑ i ∈ s, v i‖ ≤ (s.card : ℝ) / 2 := by
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ i ∈ s, (v i₀ - v i)‖ ≤ ∑ i ∈ s, ‖v i₀ - v i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, (1 / 2 : ℝ) := Finset.sum_le_sum hc
      _ = (s.card : ℝ) / 2 := by simp [div_eq_mul_inv]
  have ht := norm_add_le ((∑ _i ∈ s, v i₀) - ∑ i ∈ s, v i) (∑ i ∈ s, v i)
  rw [sub_add_cancel, hconst] at ht
  linarith


end CoherentPackets
section HilbertLowerBounds
variable {E H I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem mean_lower_from_isometry (T : E ≃ₗᵢ[ℂ] E) (J : E →L[ℂ] H)
    (D : ℝ) (hD : 0 ≤ D) (hb : ∀ u, ‖u‖ ≤ D * ‖J u‖)
    (u : E) (L : ℝ)
    (hm : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖J ((T ^ n) u)‖ ^ 2) atTop (𝓝 L)) : ‖u‖ ^ 2 ≤ D ^ 2 * L := by
  apply ge_of_tendsto (hm.const_mul (D ^ 2))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ht (n : ℕ) : ‖u‖ ^ 2 ≤ D ^ 2 * ‖J ((T ^ n) u)‖ ^ 2 := by
    have h := hb ((T ^ n) u)
    rw [(T ^ n).norm_map] at h
    have hh := (sq_le_sq₀ (norm_nonneg u)
      (mul_nonneg hD (norm_nonneg (J ((T ^ n) u))))).2 h
    simpa only [mul_pow] using hh
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => ht n)
  have hscaled := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ (N : ℝ)⁻¹)
  calc
    ‖u‖ ^ 2 = (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, ‖u‖ ^ 2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hn, one_mul]
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, D ^ 2 * ‖J ((T ^ n) u)‖ ^ 2 := hscaled
    _ = D ^ 2 * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖J ((T ^ n) u)‖ ^ 2) := by rw [← Finset.mul_sum]; ring

private theorem observed_packet_lower_from_mean
    (T : E ≃ₗᵢ[ℂ] E) (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (J : E →L[ℂ] H)
    (hm : ∀ (s : Finset I) (c : I → ℂ),
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖J ((T ^ n) (∑ i ∈ s, c i • v i))‖ ^ 2) atTop
        (𝓝 (∑ i ∈ s, ‖c i‖ ^ 2 * ‖J (v i)‖ ^ 2)))
    (D : ℝ) (hD : 0 ≤ D) (hb : ∀ u, ‖u‖ ≤ D * ‖J u‖)
    (s : Finset I) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ D ^ 2 * ‖J‖ ^ 2 * s.card := by
  have hmean : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖J ((T ^ n) (∑ i ∈ s, v i))‖ ^ 2) atTop
      (𝓝 (∑ i ∈ s, ‖J (v i)‖ ^ 2)) := by
    simpa only [one_smul, norm_one, one_pow, one_mul] using hm s (fun _ => 1)
  have hl := mean_lower_from_isometry T J D hD hb _ _ hmean
  have hJ (i : I) : ‖J (v i)‖ ^ 2 ≤ ‖J‖ ^ 2 := by
    have h := J.le_opNorm (v i)
    rw [hv, mul_one] at h
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg J)).2 h
  calc
    _ ≤ D ^ 2 * ∑ i ∈ s, ‖J (v i)‖ ^ 2 := hl
    _ ≤ D ^ 2 * ∑ _i ∈ s, ‖J‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hJ i) (sq_nonneg D)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

private theorem hilbert_observer_inverse_unbounded
    {H₀ : Type*} [NormedAddCommGroup H₀] [NormedSpace ℂ H₀]
    [TopologicalSpace.SeparableSpace H₀] [Uncountable I]
    (T : E ≃ₗᵢ[ℂ] E) (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (q : E →L[ℂ] H₀) (hq : ∀ u, ‖q u‖ ≤ ‖u‖)
    (hqv : ∀ i, ‖q (v i)‖ = 1) (J : E →L[ℂ] H)
    (hm : ∀ (s : Finset I) (c : I → ℂ),
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖J ((T ^ n) (∑ i ∈ s, c i • v i))‖ ^ 2) atTop
        (𝓝 (∑ i ∈ s, ‖c i‖ ^ 2 * ‖J (v i)‖ ^ 2))) (C : ℝ) :
    ∃ u : E, C * ‖J u‖ < ‖u‖ := by
  classical
  by_contra h
  push Not at h
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hb (u : E) : ‖u‖ ≤ D * ‖J u‖ :=
    (h u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨i₀, hi₀⟩ := infinite_small_cluster (fun i => q (v i))
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * D ^ 2 * ‖J‖ ^ 2 + 1)
  obtain ⟨s, hs, hcard⟩ := hi₀.exists_subset_card_eq N
  have hlo : (N : ℝ) / 2 ≤ ‖∑ i ∈ s, v i‖ := by
    have hl := coherent_packet_norm_lower (fun i => q (v i)) hqv s i₀
      (fun i hi => (hs hi).le)
    rw [hcard] at hl
    have he : q (∑ i ∈ s, v i) = ∑ i ∈ s, q (v i) := map_sum q _ s
    exact hl.trans (he ▸ hq (∑ i ∈ s, v i))
  have hup := observed_packet_lower_from_mean T v hv J hm D hD hb s
  rw [hcard] at hup
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (N : ℝ) / 2)
    (norm_nonneg (∑ i ∈ s, v i))).2 hlo
  have hNp : (0 : ℝ) < N := by
    nlinarith [mul_nonneg (sq_nonneg D) (sq_nonneg ‖J‖)]
  have hlarge : 4 * D ^ 2 * ‖J‖ ^ 2 < (N : ℝ) := by linarith
  have hstrict := mul_lt_mul_of_pos_right hlarge hNp
  nlinarith
end HilbertLowerBounds


/-- Every bounded linear observation in a complex inner-product space loses
uniform control of the actual frequency norm. The statement quantifies over
all observations and imposes no injectivity or lower-bound premise. -/
theorem causalFrequencySpace_hilbert_inverse_unbounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b C : ℝ) (J : causalFrequencySpace b →L[ℂ] H) :
    ∃ u : causalFrequencySpace b, C * ‖J u‖ < ‖u‖ := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact hilbert_observer_inverse_unbounded (causalFrequencyShift b)
    (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b)
    ((causalBoundedChainCoordinate 0).comp (causalFrequencySpace b).subtypeL)
    (fun u => causalBoundedChainCoordinate_norm_le 0 u.val)
    (fun ω => causalBoundedUnitEigenchain_coordinate_norm b ω 0) J
    (causalFrequencyShift_hilbert_square_mean b J) C

end RHTower.FokasLenells
