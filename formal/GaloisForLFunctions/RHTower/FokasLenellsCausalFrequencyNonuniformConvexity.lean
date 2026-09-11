import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAmplitudeInstability
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyStrictConvexity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Data.Set.Finite.Basic
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
open Complex Set Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false

private theorem close_pair_of_uncountable
    {H I : Type*} [NormedAddCommGroup H] [TopologicalSpace.SeparableSpace H] [Uncountable I]
    (v : I → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ i j, i ≠ j ∧ ‖v i - v j‖ < ε := by
  classical
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  let F : ℕ → Set I := fun n => {i | dist (v i) (d n) < ε / 2}
  have hcover : (⋃ n, F n) = Set.univ := by
    ext i
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact (Metric.denseRange_iff.mp hd) (v i) (ε / 2) (half_pos hε)
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
  obtain ⟨i, hi⟩ := hn.nonempty
  have hj : ∃ j ∈ F n, j ≠ i := by
    by_contra h
    apply hn
    apply (Set.finite_singleton i).subset
    intro j hj
    simp only [Set.mem_singleton_iff]
    by_contra hji
    exact h ⟨j, hj, hji⟩
  obtain ⟨j, hj, hji⟩ := hj
  refine ⟨i, j, Ne.symm hji, ?_⟩
  have hi' : dist (v i) (d n) < ε / 2 := hi
  have hj' : dist (v j) (d n) < ε / 2 := hj
  have ht := dist_triangle (v i) (d n) (v j)
  rw [dist_comm (d n) (v j), dist_eq_norm (v i) (v j)] at ht
  linarith

private theorem bessel_biorthogonal_pair_separation
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [DecidableEq I]
    (v : I → E) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (hb : ∀ u s, ∑ i ∈ s, ‖a i u‖ ^ 2 ≤ ‖u‖ ^ 2)
    (i j : I) (hij : i ≠ j) : 2 ≤ ‖v i - v j‖ ^ 2 := by
  have h := hb (v i - v j) {i, j}
  norm_num [Finset.sum_pair hij, map_sub, hd, hij, Ne.symm hij] at h
  exact h

private theorem separated_near_extremal_pair
    {E H I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [TopologicalSpace.SeparableSpace H] [Uncountable I]
    (v : I → E) (q : E →L[ℂ] H) (hq : ∀ u, ‖q u‖ ≤ ‖u‖)
    (hvq : ∀ i, ‖q (v i)‖ = 1) (hs : ∀ i j, i ≠ j → 2 ≤ ‖v i - v j‖ ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ i j, i ≠ j ∧ 2 ≤ ‖v i - v j‖ ^ 2 ∧ 2 - ε < ‖v i + v j‖ := by
  obtain ⟨i, j, hij, hc⟩ := close_pair_of_uncountable (fun i => q (v i)) ε hε
  refine ⟨i, j, hij, hs i j hij, ?_⟩
  have hn : ‖q (v i) + q (v i)‖ = 2 := by
    simpa [two_nsmul, hvq] using RCLike.norm_nsmul ℂ 2 (q (v i))
  have he : q (v i) + q (v i) = q (v i + v j) + (q (v i) - q (v j)) := by
    rw [map_add]
    abel
  have ht := norm_add_le (q (v i + v j)) (q (v i) - q (v j))
  rw [← he, hn] at ht
  have hbound := hq (v i + v j)
  linarith

private theorem near_extremal_pairs_not_uniformConvex
    {E I : Type*} [NormedAddCommGroup E] (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (hp : ∀ ε : ℝ, 0 < ε → ∃ i j, i ≠ j ∧
      2 ≤ ‖v i - v j‖ ^ 2 ∧ 2 - ε < ‖v i + v j‖) :
    ¬UniformConvexSpace E := by
  intro h
  letI : UniformConvexSpace E := h
  obtain ⟨δ, hδ, hmod⟩ := exists_forall_sphere_dist_add_le_two_sub E (by norm_num : 0 < (1 : ℝ))
  obtain ⟨i, j, _, hs, hn⟩ := hp δ hδ
  have hd : 1 ≤ ‖v i - v j‖ := by nlinarith [norm_nonneg (v i - v j)]
  exact hn.not_ge (hmod (hv i) (hv j) hd)


private theorem actual_separated_near_extremal_pair (b ε : ℝ) (hε : 0 < ε) :
    ∃ ω η, ω ≠ η ∧ 2 ≤ ‖causalFrequencyMode b ω - causalFrequencyMode b η‖ ^ 2 ∧
      2 - ε < ‖causalFrequencyMode b ω + causalFrequencyMode b η‖ := by
  classical
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact separated_near_extremal_pair (causalFrequencyMode b)
    ((causalBoundedChainCoordinate 0).comp (causalFrequencySpace b).subtypeL)
    (fun u => causalBoundedChainCoordinate_norm_le 0 u.val)
    (fun ω => causalBoundedUnitEigenchain_coordinate_norm b ω 0)
    (fun ω η h => bessel_biorthogonal_pair_separation (causalFrequencyMode b)
      (causalFrequencyCoefficient b) (causalFrequencyCoefficient_mode b)
      (causalFrequencyCoefficient_bessel b) ω η h) ε hε

/-- Actual unit modes stay uniformly separated while their sums approach the
extremal norm two at every prescribed natural precision. -/
theorem causalFrequencyMode_separated_near_extremal (b : ℝ) (n : ℕ) :
    ∃ ω η, ω ≠ η ∧ 2 ≤ ‖causalFrequencyMode b ω - causalFrequencyMode b η‖ ^ 2 ∧
      2 - 1 / ((n : ℝ) + 1) < ‖causalFrequencyMode b ω + causalFrequencyMode b η‖ :=
  actual_separated_near_extremal_pair b (1 / ((n : ℝ) + 1)) (by positivity)

/-- The completed actual frequency norm is not uniformly convex. Its proved
strict convexity therefore has no uniform positive midpoint gap. -/
theorem causalFrequencySpace_not_uniformConvex (b : ℝ) :
    ¬UniformConvexSpace (causalFrequencySpace b) :=
  near_extremal_pairs_not_uniformConvex (causalFrequencyMode b)
    (norm_causalBoundedUnitEigenchain b) (actual_separated_near_extremal_pair b)

end RHTower.FokasLenells
