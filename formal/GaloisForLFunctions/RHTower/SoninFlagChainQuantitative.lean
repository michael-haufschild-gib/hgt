import GaloisForLFunctions.RHTower.SoninFlagChainStrict
import GaloisForLFunctions.RHTower.SoninCouplingEnergyLowerBound

/-!
# A quantitative gap in the aperture flag law

The loss on refining a flag is exactly the coupling energy, and that energy has a uniform floor
along the crossing clock.  So the strict inequality in the flag law comes with an explicit gap, not
merely with strictness.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- **Quantitative flag law.**  There is a flag and a dilation scale at which refining the flag
costs at least a quarter. -/
theorem exists_soninApertureResidualTrace_chain_gap
    (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    ∃ (r : ℝ) (hr : 1 < r),
      c < r * a ∧
      (soninApertureResidualTrace a c r hr).re + (4 : ℝ)⁻¹ ≤
        ∑ i ∈ Finset.range 2,
          (soninApertureResidualTrace (soninTripleFlag a b c i)
            (soninTripleFlag a b c (i + 1)) r hr).re := by
  have hb : 0 < b := ha.trans hab
  have hq1 : a < (a + b) / 2 := by linarith
  have hq2 : (a + b) / 2 < b := by linarith
  have hcr : ∀ n : ℕ, c < soninCrossingClock a c n * a :=
    fun n => lt_soninCrossingClock_mul a c ha n
  have hfloor := eventually_le_hsNormSq_soninApertureCoupling a b c ha hb hab hbc
    ((a + b) / 2) hq1 hq2 (soninCrossingClock a c) (soninCrossingClock_pos a c)
    (one_lt_soninCrossingClock a c) hcr (tendsto_soninCrossingClock a c)
  obtain ⟨n, hn⟩ := hfloor.exists
  refine ⟨soninCrossingClock a c n, one_lt_soninCrossingClock a c n, hcr n, ?_⟩
  have hchain := re_soninApertureResidualTrace_chain (one_lt_soninCrossingClock a c n)
    (soninTripleFlag a b c) (by simpa using ha) (soninTripleFlag_strict a b c hab hbc) 2
    (by norm_num) (by simpa using hcr n)
  have hsum : ∑ j ∈ Finset.Ico 1 2, hsNormSq (evenSoninApertureSuccessiveLayerTransition
      (soninTripleFlag a b c 0) (soninTripleFlag a b c j)
      (soninTripleFlag a b c (j + 1)) (soninCrossingClock a c n)
      (one_lt_soninCrossingClock a c n)) =
      hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
        (soninCrossingClock a c n) (one_lt_soninCrossingClock a c n)) := by
    simp
  rw [hsum] at hchain
  have hac : (soninApertureResidualTrace (soninTripleFlag a b c 0)
      (soninTripleFlag a b c 2) (soninCrossingClock a c n)
      (one_lt_soninCrossingClock a c n)).re =
      (soninApertureResidualTrace a c (soninCrossingClock a c n)
        (one_lt_soninCrossingClock a c n)).re := by
    simp
  rw [hac] at hchain
  linarith

end RHTower
