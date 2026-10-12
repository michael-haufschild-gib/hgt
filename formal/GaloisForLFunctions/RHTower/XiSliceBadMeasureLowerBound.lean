import GaloisForLFunctions.RHTower.XiLaguerreOffLineNeighbourhood
import GaloisForLFunctions.RHTower.XiSlicePolyaFrequencyDensityZeroOne

/-!
# The slice failure set has measure at least the displacement of each isolated off-line pair

The set of heights where some slice coefficient has negative real part is open, and RH holds iff it
is empty, iff it is null (`riemannHypothesis_iff_ae_xiSliceCoeff_nonneg`).  The cone criterion bounds
it from above by the shadows of the off-line zeros, of total length `≤ 2 Σ δ`.  This file gives the
matching bound from below.

**Theorem** (`volume_xiSliceCoeff_two_neg_ge_of_isolated_pairs`).  Let finitely many off-line pairs
`γ_i ∓ δ_i i` (`δ_i > 0`) have pairwise disjoint intervals `J_i = [γ_i − δ_i/2, γ_i + δ_i/2]`, and
suppose that on `J_i` the remaining zero copies carry inverse-square mass `S_i(t)` with
`δ_i² S_i(t) < 24/25`.  Then

  `vol{t : Re c₂(t) < 0} ≥ Σ_i δ_i`.

Each `J_i` lies in the failure set up to the countable set of real zeros of `Ξ`
(`xiSliceCoeff_two_re_neg_near_offLine_pair`).  So for isolated off-line pairs near the critical line
the measure of the slice failure set is comparable to their total displacement: between `Σ δ_i` and
`2 Σ δ_i`.
-/

open MeasureTheory Set Complex

namespace RHTower

noncomputable section

/-- **The slice failure set has measure at least the displacement of each isolated pair.** -/
theorem volume_xiSliceCoeff_two_neg_ge_of_isolated_pairs {ι : Type*} (s : Finset ι)
    (γ δ : ι → ℝ) (hδ : ∀ i ∈ s, 0 < δ i) (q₁ q₂ : ι → XiZeroCopy)
    (h12 : ∀ i ∈ s, q₁ i ≠ q₂ i)
    (h1 : ∀ i ∈ s, xiSpectralPoint (q₁ i) = (γ i : ℂ) - (δ i : ℂ) * I)
    (h2 : ∀ i ∈ s, xiSpectralPoint (q₂ i) = (γ i : ℂ) + (δ i : ℂ) * I)
    (S : ι → ℝ → ℝ)
    (hS : ∀ i ∈ s, ∀ t ∈ Icc (γ i - δ i / 2) (γ i + δ i / 2),
      ∀ F : Finset XiZeroCopy, (∀ q ∈ F, q ≠ q₁ i ∧ q ≠ q₂ i) →
        ∑ q ∈ F, 1 / ‖(t : ℂ) - xiSpectralPoint q‖ ^ 2 ≤ S i t)
    (hsmall : ∀ i ∈ s, ∀ t ∈ Icc (γ i - δ i / 2) (γ i + δ i / 2), δ i ^ 2 * S i t < 24 / 25)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => Icc (γ i - δ i / 2) (γ i + δ i / 2)) :
    ENNReal.ofReal (∑ i ∈ s, δ i) ≤ volume {t : ℝ | (xiSliceCoeff t 2).re < 0} := by
  set J : ι → Set ℝ := fun i => Icc (γ i - δ i / 2) (γ i + δ i / 2) with hJ
  set Z : Set ℝ := {t : ℝ | XiC (t : ℂ) = 0} with hZ
  have hZnull : volume Z = 0 := countable_setOf_XiC_ofReal_eq_zero.measure_zero _
  have hsub : (⋃ i ∈ s, J i) \ Z ⊆ {t : ℝ | (xiSliceCoeff t 2).re < 0} := by
    intro t ht
    obtain ⟨hU, hZt⟩ := ht
    obtain ⟨i, hi, htJ⟩ := mem_iUnion₂.mp hU
    have hδi := hδ i hi
    have habs : |t - γ i| ≤ |δ i| / 2 := by
      rw [abs_of_pos hδi, abs_le]
      obtain ⟨hl, hr⟩ := htJ
      constructor <;> linarith
    exact xiSliceCoeff_two_re_neg_near_offLine_pair hδi.ne' (h12 i hi) (h1 i hi) (h2 i hi) habs hZt
      (hS i hi t htJ) (hsmall i hi t htJ)
  have hvolU : volume (⋃ i ∈ s, J i) = ∑ i ∈ s, ENNReal.ofReal (δ i) := by
    rw [measure_biUnion_finset hdisj fun i _ => measurableSet_Icc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hJ, Real.volume_Icc]
    congr 1
    ring
  calc ENNReal.ofReal (∑ i ∈ s, δ i) = ∑ i ∈ s, ENNReal.ofReal (δ i) :=
        ENNReal.ofReal_sum_of_nonneg fun i hi => (hδ i hi).le
    _ = volume ((⋃ i ∈ s, J i) \ Z) := by rw [measure_sdiff_null hZnull, hvolU]
    _ ≤ volume {t : ℝ | (xiSliceCoeff t 2).re < 0} := measure_mono hsub

end

end RHTower
