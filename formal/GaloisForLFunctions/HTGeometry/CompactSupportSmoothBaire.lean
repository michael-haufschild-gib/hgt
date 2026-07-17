import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Baire completeness of fixed-support smooth test functions

Mathlib equips `ContDiffMapSupportedIn` with its natural countable family of
uniform derivative seminorms, but does not yet provide completeness for the
infinite-order space.  This file supplies that missing Fréchet-space fact for
real test functions on the real line.  It is the topological parent needed for
residual compact-support profile arguments.
-/

open Filter Function Set TopologicalSpace Topology
open scoped Distributions NNReal Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Smooth real functions on `ℝ` which vanish off the fixed compact set `K`. -/
abbrev CompactSupportSmooth (K : Compacts ℝ) :=
  ContDiffMapSupportedIn ℝ ℝ ⊤ K

noncomputable instance compactSupportSmooth_firstCountable (K : Compacts ℝ) :
    FirstCountableTopology (CompactSupportSmooth K) :=
  (ContDiffMapSupportedIn.withSeminorms ℝ ℝ ℝ ⊤ K).firstCountableTopology

noncomputable instance compactSupportSmooth_uniformity_countablyGenerated
    (K : Compacts ℝ) : IsCountablyGenerated (uniformity (CompactSupportSmooth K)) := by
  rw [uniformity_eq_comap_nhds_zero]
  infer_instance

/-- The geometric scale used to extract an absolutely summable smooth
subsequence from an arbitrary Cauchy sequence. -/
private def compactSupportSmoothScale (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

private theorem compactSupportSmoothScale_pos (n : ℕ) :
    0 < compactSupportSmoothScale n := by
  simp only [compactSupportSmoothScale]
  positivity

private theorem compactSupportSmoothScale_summable :
    Summable compactSupportSmoothScale := by
  exact summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)

/-- An entourage controlling the first `n + 1` derivative seminorms at
geometric scale `2⁻ⁿ`. -/
private def compactSupportSmoothEntourage (K : Compacts ℝ) (n : ℕ) :
    SetRel (CompactSupportSmooth K) (CompactSupportSmooth K) :=
  (fun p : CompactSupportSmooth K × CompactSupportSmooth K => p.2 - p.1) ⁻¹'
    (((Finset.range (n + 1)).sup
      (ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ K)).ball 0
        (compactSupportSmoothScale n))

private theorem compactSupportSmoothEntourage_mem
    (K : Compacts ℝ) (n : ℕ) :
    compactSupportSmoothEntourage K n ∈ uniformity (CompactSupportSmooth K) := by
  rw [uniformity_eq_comap_nhds_zero]
  apply preimage_mem_comap
  exact (ContDiffMapSupportedIn.withSeminorms ℝ ℝ ℝ ⊤ K).hasBasis_zero_ball.mem_iff.mpr
    ⟨((Finset.range (n + 1)), compactSupportSmoothScale n),
      compactSupportSmoothScale_pos n, Subset.rfl⟩

private theorem compactSupportSmoothEntourage_seminorm
    (K : Compacts ℝ) {n i : ℕ} (hi : i < n + 1)
    {f g : CompactSupportSmooth K}
    (hfg : (f, g) ∈ compactSupportSmoothEntourage K n) :
    ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ K i (g - f) <
      compactSupportSmoothScale n := by
  rw [compactSupportSmoothEntourage, Set.mem_preimage,
    Seminorm.mem_ball_zero] at hfg
  have hle : ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ K i ≤
      (Finset.range (n + 1)).sup
        (ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ K) := by
    exact Finset.le_sup_of_le (Finset.mem_range.mpr hi) le_rfl
  exact lt_of_le_of_lt (hle (g - f)) hfg

/-- A Cauchy sequence has a strictly increasing subsequence whose consecutive
differences are geometrically small in every derivative order already reached
by the diagonal. -/
private theorem exists_compactSupportSmooth_subsequence
    (K : Compacts ℝ) (u : ℕ → CompactSupportSmooth K) (hu : CauchySeq u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n i, i ≤ n →
        ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ K i
            (u (φ (n + 1)) - u (φ n)) < compactSupportSmoothScale n := by
  obtain ⟨φ, hφ, hstep⟩ := hu.subseq_mem
    (fun n => compactSupportSmoothEntourage_mem K n)
  refine ⟨φ, hφ, fun n i hi => ?_⟩
  have h := compactSupportSmoothEntourage_seminorm K
    (Nat.lt_succ_of_le hi) (hstep n)
  rw [show u (φ (n + 1)) - u (φ n) =
    -(u (φ n) - u (φ (n + 1))) by abel, map_neg_eq_map]
  exact h

set_option maxHeartbeats 1600000 in
/-- The fixed-support smooth real test-function space is complete in its
natural topology of uniform convergence of every derivative. -/
noncomputable instance compactSupportSmooth_complete (K : Compacts ℝ) :
    CompleteSpace (CompactSupportSmooth K) :=
  UniformSpace.complete_of_cauchySeq_tendsto fun u hu => by
    obtain ⟨φ, hφ, hsmall⟩ :=
      exists_compactSupportSmooth_subsequence K u hu
    let d : ℕ → CompactSupportSmooth K
      | 0 => u (φ 0)
      | n + 1 => u (φ (n + 1)) - u (φ n)
    let v : ℕ → ℕ → ℝ := fun k n =>
      if n ≤ k then
        ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ K k (d n)
      else 2 * compactSupportSmoothScale n
    have hv (k : ℕ) : Summable (v k) := by
      apply (compactSupportSmoothScale_summable.mul_left 2).congr_atTop
      filter_upwards [eventually_gt_atTop k] with n hn
      simp only [v, if_neg (not_le_of_gt hn)]
    have hsemi (k n : ℕ) :
        ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ K k (d n) ≤ v k n := by
      by_cases hn : n ≤ k
      · simp only [v, if_pos hn]
        exact le_rfl
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        have hkm : k ≤ m := by omega
        have hs := hsmall m k hkm
        have hscale : compactSupportSmoothScale m =
            2 * compactSupportSmoothScale (m + 1) := by
          simp only [compactSupportSmoothScale, pow_succ]
          ring
        simpa only [d, v, if_neg (by omega : ¬m + 1 ≤ k), hscale] using hs.le
    have hderiv (k n : ℕ) (x : ℝ) :
        ‖iteratedFDeriv ℝ k (d n : ℝ → ℝ) x‖ ≤ v k n :=
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top
        ℝ (f := d n) (x := x)).trans (hsemi k n)
    have hdSmooth (n : ℕ) := (d n).contDiff
    have hsumSmooth : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun x : ℝ => ∑' n, d n x) := by
      exact contDiff_tsum hdSmooth (fun k _ => hv k)
        (fun k n x _ => hderiv k n x)
    have hpointSummable (x : ℝ) : Summable (fun n => d n x) := by
      apply (hv 0).of_norm_bounded
      intro n
      simpa only [norm_iteratedFDeriv_zero] using hderiv 0 n x
    let f : CompactSupportSmooth K :=
      { toFun := fun x => ∑' n, d n x
        contDiff' := hsumSmooth
        zero_on_compl' := by
          intro x hx
          have hz : ∀ n, d n x = 0 := fun n => (d n).zero_on_compl hx
          simp only [hz, tsum_zero, Pi.zero_apply] }
    have hdJetSummable (k : ℕ) : Summable (fun n =>
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (d n)) := by
      refine Summable.of_norm_bounded
        (f := fun n => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (d n))
        (hv k) ?_
      exact fun n => by
        simpa only [ContDiffMapSupportedIn.seminorm_apply] using hsemi k n
    have hjet (k : ℕ) :
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k f =
          ∑' n, ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (d n) := by
      apply BoundedContinuousFunction.ext
      intro x
      change iteratedFDeriv ℝ k (fun y : ℝ => ∑' n, d n y) x =
        (∑' n, ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (d n)) x
      rw [iteratedFDeriv_tsum_apply hdSmooth (fun j _ => hv j)
        (fun j n y _ => hderiv j n y) (by simp)]
      exact ((BoundedContinuousFunction.evalCLM ℝ x).map_tsum
        (hdJetSummable k)).symm
    have htelescope (n : ℕ) :
        ∑ i ∈ Finset.range (n + 1), d i = u (φ n) := by
      induction n with
      | zero => simp [d]
      | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          simp only [d]
          abel
    have hsubseq : Tendsto (u ∘ φ) atTop (𝓝 f) := by
      rw [(ContDiffMapSupportedIn.withSeminorms ℝ ℝ ℝ ⊤ K).tendsto_nhds_atTop]
      intro k ε hε
      have hsum := (hdJetSummable k).hasSum
      have htend : Tendsto (fun n =>
          ∑ i ∈ Finset.range n,
            ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (d i))
          atTop
          (𝓝 (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k f)) := by
        simpa only [hjet k] using hsum.tendsto_sum_nat
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
        (htend.comp (tendsto_add_atTop_nat 1)) ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hlt := hN n hn
      simp only [Function.comp_apply] at hlt
      have hdistnorm :
          dist (∑ i ∈ Finset.range (n + 1),
              ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (d i))
            (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k f) =
            ‖(∑ i ∈ Finset.range (n + 1),
                ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (d i)) -
              ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k f‖ := by
        exact dist_eq_norm
          (∑ i ∈ Finset.range (n + 1),
            ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (d i))
          (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k f)
      rw [hdistnorm] at hlt
      rw [Function.comp_apply, ← htelescope n]
      simpa only [ContDiffMapSupportedIn.seminorm_apply, map_sub, map_sum,
        Function.comp_apply] using hlt
    refine ⟨f, tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hsubseq⟩

noncomputable instance compactSupportSmooth_completelyMetrizable
    (K : Compacts ℝ) : IsCompletelyMetrizableSpace (CompactSupportSmooth K) := by
  infer_instance

noncomputable instance compactSupportSmooth_baire (K : Compacts ℝ) :
    BaireSpace (CompactSupportSmooth K) := by
  infer_instance

end GaloisForLFunctions.HTGeometry
