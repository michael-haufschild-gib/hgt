import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPartitionMomentClosed

/-!
# The covering half of the discrete-to-measure bridge

Huxley's large-values estimate bounds the cardinality of a spaced family inside a level set; the
receivers of this chain consume a measure.  The standard bridge partitions the window into
intervals of length `delta`, notes that the level set is covered by the ones it meets, and extracts
two spaced families from those.  This file supplies the covering half, which is the reusable part:
a set covered by `#s` intervals of length `delta` has measure at most `#s * delta`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **A set covered by finitely many intervals of a common length.** -/
theorem measureReal_le_of_subset_biUnion_Ico
    {E : Set ℝ} {s : Finset ℕ} {a delta : ℝ} (hdelta : 0 ≤ delta)
    (hE : E ⊆ ⋃ i ∈ s, Set.Ico (a + (i : ℝ) * delta) (a + ((i : ℝ) + 1) * delta)) :
    volume.real E ≤ (s.card : ℝ) * delta := by
  classical
  have hcover : volume E
      ≤ ∑ i ∈ s, volume (Set.Ico (a + (i : ℝ) * delta) (a + ((i : ℝ) + 1) * delta)) :=
    le_trans (measure_mono hE) (measure_biUnion_finset_le _ _)
  have hone : ∀ i ∈ s,
      volume (Set.Ico (a + (i : ℝ) * delta) (a + ((i : ℝ) + 1) * delta))
        = ENNReal.ofReal delta := by
    intro i _
    rw [Real.volume_Ico]
    congr 1
    ring
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul] at hcover
  have hfin : ((s.card : ℕ) : ENNReal) * ENNReal.ofReal delta ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hmono := ENNReal.toReal_mono hfin hcover
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hdelta] at hmono
  exact hmono

end

end RHTower.Sieve
