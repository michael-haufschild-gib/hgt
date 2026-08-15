import GaloisForLFunctions.SelbergClass.MultipleStandardTwistInitialUndamping

/-!
# Local-uniform initial-domain undamping for multiple standard twists

The ball-uniform undamping theorem applies at every point of the initial
absolute-convergence domain: finite coordinate dimension supplies one positive
minimum distance from its boundary.  This module packages that concrete fact as
local-uniform convergence, without a normal-family or continuation interface.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass

/-- The concrete damped Kaczorowski--Perelli tensor tends locally uniformly to
its initial tensor on the exact initial absolute-convergence domain. -/
theorem MultipleStandardTwistData.tendstoLocallyUniformlyOn_damped_atTop_initial
    {N : ℕ} (D : MultipleStandardTwistData N) :
    TendstoLocallyUniformlyOn (fun X : ℝ => D.damped X) D.initial atTop
      (multipleStandardTwistInitialDomain N) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε s hs
  have hs' : ∀ i, 1 < (s i).re := by
    simpa only [multipleStandardTwistInitialDomain, Set.mem_setOf_eq] using hs
  letI : Nonempty (Fin N) := ⟨⟨0, lt_of_lt_of_le (by norm_num) D.two_le_card⟩⟩
  let gaps : Finset ℝ := Finset.univ.image (fun i : Fin N => (s i).re - 1)
  have hgaps_nonempty : gaps.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let m : ℝ := gaps.min' hgaps_nonempty
  have hm_pos : 0 < m := by
    have hm_mem := Finset.min'_mem gaps hgaps_nonempty
    rcases Finset.mem_image.mp hm_mem with ⟨i, hi, him⟩
    change 0 < gaps.min' hgaps_nonempty
    rw [← him]
    exact sub_pos.mpr (hs' i)
  have hm_le : ∀ i, m ≤ (s i).re - 1 := by
    intro i
    exact Finset.min'_le gaps ((s i).re - 1)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let r : ℝ := m / 4
  have hr : 0 < r := by positivity
  have hshift : ∀ i, 1 < (s i - (2 * r : ℝ)).re := by
    intro i
    simp only [Complex.sub_re, Complex.ofReal_re]
    dsimp [r]
    linarith [hm_le i]
  have hball := D.tendstoUniformlyOn_damped_atTop_initial_on_ball s hr hshift
  refine ⟨Metric.ball s r,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds s hr), ?_⟩
  exact (Metric.tendstoUniformlyOn_iff.mp hball) ε hε

end GaloisForLFunctions.SelbergClass
