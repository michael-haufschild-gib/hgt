import GaloisForLFunctions.RHTower.FokasLenellsCausalUnitBoundaryWeakLimit
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyChart
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyMeanSquare
import GaloisForLFunctions.RHTower.Sieve.AlmostOrthogonality
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Order.Filter.Finite

open Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false

section Selection
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem weak_unit_finite_selection (v : I → H) (f : Filter I) [NeBot f]
    (hv : ∀ i, ‖v i‖ = 1)
    (hw : ∀ y, Tendsto (fun i => inner ℂ y (v i)) f (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ s : Finset I, s.card = N ∧
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖inner ℂ (v i) (v j)‖ < ε := by
  classical
  induction N with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨s, hs, hp⟩ := ih
    have he : 0 < min ε (1 / 2 : ℝ) := lt_min hε (by norm_num)
    have hevent : ∀ᶠ j in f, ∀ i ∈ s,
        ‖inner ℂ (v i) (v j)‖ < min ε (1 / 2 : ℝ) := by
      apply (eventually_all_finset s).2
      intro i _
      simpa only [dist_zero_right] using
        (Metric.tendsto_nhds.1 (hw (v i))) _ he
    obtain ⟨j, hj⟩ := hevent.exists
    have hjs : j ∉ s := by
      intro h
      have hself := hj j h
      rw [inner_self_eq_norm_sq_to_K, hv] at hself
      norm_num at hself
    refine ⟨insert j s, by simp [hjs, hs], ?_⟩
    intro a ha b hb hab
    rcases Finset.mem_insert.1 ha with haj | has
    · subst a
      rcases Finset.mem_insert.1 hb with hbj | hbs
      · exact (hab hbj.symm).elim
      · rw [RHTower.Sieve.norm_inner_symm]
        exact (hj b hbs).trans_le (min_le_left _ _)
    · rcases Finset.mem_insert.1 hb with hbj | hbs
      · subst b
        exact (hj a has).trans_le (min_le_left _ _)
      · exact hp a has b hbs hab

private theorem unit_gram_row_le (v : I → H) (s : Finset I)
    (hv : ∀ i, ‖v i‖ = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖inner ℂ (v i) (v j)‖ < ε)
    (i : I) (hi : i ∈ s) :
    ∑ j ∈ s, ‖inner ℂ (v i) (v j)‖ ≤ 1 + s.card * ε := by
  classical
  calc
    _ ≤ ∑ j ∈ s, ((if i = j then (1 : ℝ) else 0) + ε) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · subst j
        simpa [inner_self_eq_norm_sq_to_K, hv] using
          (le_add_of_nonneg_right hε : (1 : ℝ) ≤ 1 + ε)
      · simpa [hij] using (hp i hi j hj hij).le
    _ = _ := by simp [Finset.sum_add_distrib, hi]

private theorem unimodular_gram_norm (v w : H) (z t : ℂ)
    (hz : ‖z‖ = 1) (ht : ‖t‖ = 1) (n : ℕ) :
    ‖inner ℂ (z ^ n • v) (t ^ n • w)‖ = ‖inner ℂ v w‖ := by
  simp [inner_smul_left, inner_smul_right, norm_pow, hz, ht]
end Selection

section CoordinateEstimate
variable {I E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem coordinate_gram_packet_bound
    (q : ℕ → E →L[ℂ] H) (v : I → E) (h : I → H) (z : I → ℂ)
    (hq : ∀ n i, q n (v i) = z i ^ n • h i)
    (hz : ∀ i, ‖z i‖ = 1)
    (hnorm : ∀ u C, 0 ≤ C → (∀ n, ‖q n u‖ ≤ C) → ‖u‖ ≤ C)
    (s : Finset I) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, ‖inner ℂ (h i) (h j)‖ ≤ Δ)
    (c : I → ℂ) :
    ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ Δ * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have hG : 0 ≤ Δ * ∑ i ∈ s, ‖c i‖ ^ 2 :=
    mul_nonneg hΔ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hcoord : ∀ n, ‖q n (∑ i ∈ s, c i • v i)‖ ^ 2 ≤
      Δ * ∑ i ∈ s, ‖c i‖ ^ 2 := by
    intro n
    simp only [map_sum, map_smul]
    apply RHTower.Sieve.norm_sum_smul_sq_le_of_schur
    intro i hi
    calc
      _ = ∑ j ∈ s, ‖inner ℂ (h i) (h j)‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hq, hq, unimodular_gram_norm _ _ _ _ (hz i) (hz j)]
      _ ≤ Δ := hrow i hi
  have hb := hnorm (∑ i ∈ s, c i • v i)
    (Real.sqrt (Δ * ∑ i ∈ s, ‖c i‖ ^ 2)) (Real.sqrt_nonneg _)
    (fun n => Real.le_sqrt_of_sq_le (hcoord n))
  nlinarith [Real.sq_sqrt hG, norm_nonneg (∑ i ∈ s, c i • v i)]
end CoordinateEstimate

private theorem fixed_chart_weak_null (b : ℝ) (y : hardyL2ᗮ) :
    Tendsto (fun ω : ℝ => inner ℂ y (causalUnitBoundaryEigenvector b ω).val)
      (Filter.map (fun n : ℕ => Real.exp (b + (n : ℝ))) atTop) (𝓝 0) := by
  apply tendsto_map'_iff.2
  have hn : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have he (n : ℕ) :
      (causalUnitBoundaryEigenvector b (Real.exp (b + (n : ℝ)))).val =
        (causalUnitBoundaryEigenvector (-(n : ℝ)) 1).val := by
    simpa only [sub_neg_eq_add, mul_one] using
      congrArg Subtype.val (causalUnitBoundaryEigenvector_rescale (-(n : ℝ)) b 1)
  simpa only [Function.comp_def, he] using
    (causalUnitBoundaryEigenvector_weak_tendsto_pos y).comp hn

private theorem bounded_chain_norm_from_coordinates (u : causalBoundedChain) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ n, ‖causalBoundedChainCoordinate n u‖ ≤ C) : ‖u‖ ≤ C := by
  change ‖u.val‖ ≤ C
  exact lp.norm_le_of_forall_le hC hc

private theorem actual_finite_packet_upper (b : ℝ) (s : Finset ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ‖inner ℂ (causalUnitBoundaryEigenvector b i).val
        (causalUnitBoundaryEigenvector b j).val‖ < ε)
    (c : ℝ → ℂ) :
    ‖∑ i ∈ s, c i • causalBoundedUnitEigenchain b i‖ ^ 2 ≤
      (1 + s.card * ε) * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  apply coordinate_gram_packet_bound causalBoundedChainCoordinate
    (causalBoundedUnitEigenchain b)
    (fun ω => (causalUnitBoundaryEigenvector b ω).val)
    (fun ω => (causalUnitBoundaryRate b ω).val)
    (fun _ _ => rfl) (norm_causalUnitBoundaryRate b)
    bounded_chain_norm_from_coordinates s (1 + s.card * ε) (by positivity)
  exact unit_gram_row_le _ s (norm_causalUnitBoundaryEigenvector b) ε hε hp

/-- Arbitrarily large actual mode packets have almost Euclidean chain norms,
uniformly for every complex amplitude family. The precision is prescribed by
`k`; the finite set is selected from actual normalized boundary data. -/
theorem causalFrequencyPacket_almost_euclidean (b : ℝ) (N k : ℕ) :
    ∃ s : Finset ℝ, s.card = N ∧ ∀ c : ℝ → ℂ,
      (∑ ω ∈ s, ‖c ω‖ ^ 2 ≤
        ‖∑ ω ∈ s, c ω • causalBoundedUnitEigenchain b ω‖ ^ 2) ∧
      (‖∑ ω ∈ s, c ω • causalBoundedUnitEigenchain b ω‖ ^ 2 ≤
        (1 + 1 / ((k : ℝ) + 1)) * ∑ ω ∈ s, ‖c ω‖ ^ 2) := by
  let ε : ℝ := ((N : ℝ) + 1)⁻¹ * ((k : ℝ) + 1)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨s, hs, hp⟩ := weak_unit_finite_selection
    (fun ω => (causalUnitBoundaryEigenvector b ω).val)
    (Filter.map (fun n : ℕ => Real.exp (b + (n : ℝ))) atTop)
    (norm_causalUnitBoundaryEigenvector b) (fixed_chart_weak_null b) ε hε N
  refine ⟨s, hs, fun c => ⟨causalFrequencyPacket_norm_sq_lower_bound b s c, ?_⟩⟩
  apply (actual_finite_packet_upper b s ε hε.le hp c).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply add_le_add le_rfl
  rw [hs]
  have hratio : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  have hm := mul_le_mul_of_nonneg_right hratio
    (by positivity : 0 ≤ ((k : ℝ) + 1)⁻¹)
  simpa only [ε, div_eq_mul_inv, mul_assoc, one_mul] using hm

end RHTower.FokasLenells
