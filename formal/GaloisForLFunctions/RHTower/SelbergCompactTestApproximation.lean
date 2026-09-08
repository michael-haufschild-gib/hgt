import GaloisForLFunctions.RHTower.SelbergLocalTestGreen
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Common-compact approximation for actual upper-half-plane tests

A compact continuous test supported at positive height admits uniformly accurate
C² approximants in one fixed compact subset of the upper half-plane. A complete
metric Cauchy argument then transfers scalar convergence from eventual uniformly
accurate approximants to the original family.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergCompactTestApproximation
open SelbergLocalTestGreen
noncomputable section

/-- Every admissible continuous test has C² uniform approximants in one fixed positive-height compact, also containing its original support. -/
theorem exists_common_compact_approximation {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ {z : ℂ | 0 < z.im} ∧ tsupport phi ⊆ K ∧
      ∀ ε : ℝ, 0 < ε → ∃ psi : ℂ → ℝ, ContDiff ℝ 2 psi ∧ tsupport psi ⊆ K ∧
        ∀ z, ‖psi z - phi z‖ ≤ ε := by
  obtain ⟨chi, hq, hd, ht, _, hone⟩ := exists_nonnegative_cutoff hc hs
  let cb : C_c(ℂ, ℝ) := ⟨⟨chi, hq.continuous⟩, hd⟩
  let B : ℝ := ‖cb.toBoundedContinuousFunction‖
  have hB : 0 ≤ B := norm_nonneg _
  have hb (z : ℂ) : ‖chi z‖ ≤ B := cb.toBoundedContinuousFunction.norm_coe_le_norm z
  refine ⟨tsupport chi ∪ tsupport phi, hd.union hc, union_subset ht hs, subset_union_right, ?_⟩
  intro ε hε
  obtain ⟨g, hg, hge⟩ := (hc.uniformContinuous_of_continuous hp).exists_contDiff_dist_le
    (div_pos hε (by linarith : 0 < B + 1))
  have hg2 : ContDiff ℝ 2 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨fun z => chi z * g z, hq.mul hg2,
    tsupport_mul_subset_left.trans subset_union_left, ?_⟩
  intro z
  have he : chi z * phi z = phi z := by
    by_cases hz : z ∈ tsupport phi
    · rw [hone z hz, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  calc
    ‖chi z * g z - phi z‖ = ‖chi z * (g z - phi z)‖ := by rw [mul_sub, he]
    _ = ‖chi z‖ * ‖g z - phi z‖ := norm_mul _ _
    _ ≤ B * (ε / (B + 1)) := mul_le_mul (hb z)
      (by simpa only [Real.dist_eq, Real.norm_eq_abs] using (hge z).le) (norm_nonneg _) hB
    _ ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < B + 1)]
      nlinarith

/-- Eventual approximation to convergent real families at every positive accuracy forces a real limit along the original nontrivial filter. -/
theorem exists_limit_of_eventual_approximation {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ (v : ι → ℝ) (a : ℝ), Tendsto v l (𝓝 a) ∧
      ∀ᶠ i in l, ‖u i - v i‖ ≤ ε) : ∃ a : ℝ, Tendsto u l (𝓝 a) := by
  apply cauchy_map_iff_exists_tendsto.mp
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  let δ : ℝ := ε / 5
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨v, a, hv, he⟩ := h δ hδ
  have ha : ∀ᶠ i in l, dist (v i) a < δ := (Metric.tendsto_nhds.mp hv) δ hδ
  let S : Set ι := {i | ‖u i - v i‖ ≤ δ ∧ dist (v i) a < δ}
  have hS : S ∈ l := he.and ha
  refine ⟨u '' S, Filter.image_mem_map hS, ?_⟩
  rintro x ⟨i, hi, rfl⟩ y ⟨j, hj, rfl⟩
  have hi1 : dist (u i) (v i) ≤ δ := by simpa only [dist_eq_norm] using hi.1
  have hj1 : dist (u j) (v j) ≤ δ := by simpa only [dist_eq_norm] using hj.1
  calc
    dist (u i) (u j) ≤ dist (u i) a + dist a (u j) := dist_triangle _ _ _
    _ ≤ (dist (u i) (v i) + dist (v i) a) + (dist a (v j) + dist (v j) (u j)) :=
      add_le_add (dist_triangle _ _ _) (dist_triangle _ _ _)
    _ < ε := by
      rw [dist_comm a (v j), dist_comm (v j) (u j)]
      have hi2 := hi.2
      have hj2 := hj.2
      dsimp [δ] at hi1 hj1 hi2 hj2
      linarith

end
end GaloisForLFunctions.RHTower.SelbergCompactTestApproximation
