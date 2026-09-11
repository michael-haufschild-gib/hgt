import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAmplitudeMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
open Complex Set Filter
noncomputable section
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

private theorem coherent_lp2_inverse_unbounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℂ H] [TopologicalSpace.SeparableSpace H]
    [Uncountable I] [DecidableEq I]
    (q : E →L[ℂ] H) (hq : ∀ u, ‖q u‖ ≤ ‖u‖)
    (v : I → E) (hv : ∀ i, ‖q (v i)‖ = 1)
    (A : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hA : ∀ i, A (v i) = lp.single 2 i 1) (C : ℝ) :
    ∃ u : E, C * ‖A u‖ < ‖u‖ := by
  classical
  obtain ⟨i₀, hi₀⟩ := infinite_small_cluster (fun i => q (v i))
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * C ^ 2 + 1)
  obtain ⟨s, hs, hcard⟩ := hi₀.exists_subset_card_eq N
  let u : E := ∑ i ∈ s, v i
  have hlo : (N : ℝ) / 2 ≤ ‖u‖ := by
    have hl := coherent_packet_norm_lower (fun i => q (v i)) hv s i₀
      (fun i hi => (hs hi).le)
    rw [hcard] at hl
    have he : q u = ∑ i ∈ s, q (v i) := map_sum q _ s
    exact hl.trans (he ▸ hq u)
  have hAu : A u = ∑ i ∈ s, lp.single 2 i 1 := by
    simp only [u, map_sum, hA]
  have ha : ‖A u‖ ^ 2 = (N : ℝ) := by
    rw [hAu]
    simpa [hcard] using (lp.norm_sum_single (E := fun _ : I => ℂ)
      (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (fun _ : I => (1 : ℂ)) s)
  refine ⟨u, ?_⟩
  by_contra h
  have hu : ‖u‖ ≤ C * ‖A u‖ := le_of_not_gt h
  have hup : ‖u‖ ^ 2 ≤ (C * ‖A u‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg u) ((norm_nonneg u).trans hu)).mpr hu
  rw [mul_pow, ha] at hup
  have hNp : (0 : ℝ) < N := by nlinarith [sq_nonneg C]
  have hlow : ((N : ℝ) / 2) ^ 2 ≤ ‖u‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg u)).mpr hlo
  have hlarge : 4 * C ^ 2 < (N : ℝ) := by linarith
  have hprod := mul_lt_mul_of_pos_right hlarge hNp
  nlinarith
end CoherentPackets

private theorem unbounded_inverse_not_closed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) (hi : Function.Injective A)
    (hu : ∀ C : ℝ, ∃ u : E, C * ‖A u‖ < ‖u‖) :
    ¬ IsClosed (Set.range A) := by
  intro hclosed
  obtain ⟨K, hK⟩ := A.antilipschitz_of_injective_of_isClosed_range hi hclosed
  obtain ⟨u, hlarge⟩ := hu (K : ℝ)
  have hd := hK.le_mul_dist u 0
  have hle : ‖u‖ ≤ (K : ℝ) * ‖A u‖ := by
    simpa only [map_zero, dist_zero_right] using hd
  exact not_lt_of_ge hle hlarge

private theorem not_closed_not_surjective
    {E F : Type*} [TopologicalSpace F] (A : E → F)
    (h : ¬ IsClosed (Set.range A)) : ¬ Function.Surjective A := by
  intro hs
  apply h
  rw [Set.range_eq_univ.mpr hs]
  exact isClosed_univ

/-- No constant controls the actual reconstruction norm by the lp2 amplitude norm. -/
theorem causalFrequencyAmplitudeMap_inverse_unbounded (b C : ℝ) :
    ∃ u : causalFrequencySpace b, C * ‖causalFrequencyAmplitudeMap b u‖ < ‖u‖ := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact coherent_lp2_inverse_unbounded
    ((causalBoundedChainCoordinate 0).comp (causalFrequencySpace b).subtypeL)
    (fun u => causalBoundedChainCoordinate_norm_le 0 u.val)
    (causalFrequencyMode b)
    (fun ω => causalBoundedUnitEigenchain_coordinate_norm b ω 0)
    (causalFrequencyAmplitudeMap b) (causalFrequencyAmplitudeMap_mode b) C

/-- The actual amplitude image is not closed in the lp2 norm. -/
theorem causalFrequencyAmplitudeMap_not_isClosed_range (b : ℝ) :
    ¬ IsClosed (Set.range (causalFrequencyAmplitudeMap b)) := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  exact unbounded_inverse_not_closed (causalFrequencyAmplitudeMap b)
    (causalFrequencyAmplitudeMap_injective b) (causalFrequencyAmplitudeMap_inverse_unbounded b)

/-- Some square-summable amplitude families do not come from any actual bounded
frequency chain, although finite realizable families are dense in lp2. -/
theorem causalFrequencyAmplitudeMap_not_surjective (b : ℝ) :
    ¬ Function.Surjective (causalFrequencyAmplitudeMap b) :=
  not_closed_not_surjective (causalFrequencyAmplitudeMap b)
    (causalFrequencyAmplitudeMap_not_isClosed_range b)

end RHTower.FokasLenells
