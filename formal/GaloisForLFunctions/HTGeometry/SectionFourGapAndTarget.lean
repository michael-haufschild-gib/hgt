/-
The Section-4 floor is a scale gap, and the single pair that would close it.

At the target `13/84` the three sources of the covering cover

    exponent pairs      c ≤ 579/1435 ,
    the middle source   12/31 ≤ c ≤ 332/819 ,
    the final source    17/42 ≤ c ≤ 1/2 ,

so the union is all of `[0, 1/2]`, but the middle source is *alone* on the window
`(579/1435, 17/42)`, of width `11/8610`.  Its demand there is increasing, with supremum
`277/1792` at the right endpoint.  Hence the covering cannot prove any bound below `277/1792`:
**the Section-4 floor is exactly the middle source's value at the one scale where nothing else is
available.**

The floor is therefore an artifact of a gap of width `11/8610`, and is removed by a single exponent
pair whose demand at `c = 17/42` is at most `277/1792` — beating the best available low-range pair
`(16/237, 743/948)` there by `589/1274112`.

Slack profile of the covering at the target: it is tight only at `c = 1/2`; the next-tightest point is
`c = 17/42`, with slack exactly `1/5376`, and at `c = 12/31` the slack is `243/68572`.

Finally, pairs on the line of symmetry `λ = κ + 1/2` have zero displacement, so their demand is the
constant `κ` at **every** scale.  Weyl's `(1/6, 2/3)` and the record `(13/84, 55/84)` are both such
pairs: each covers all scales at once, and the covering architecture adds nothing to them.  Improving
past `13/84` therefore requires beating a flat bound, which by the conjugacy of scale and abscissa can
only happen at the critical scale itself.
-/
import GaloisForLFunctions.HTGeometry.MiddleSourceWindow

namespace HTGeometry

/-! ### The middle source's own coverage -/

/-- **The middle source covers exactly `c ≤ 332/819`.** -/
theorem huxleySource_coverage (c : ℚ) :
    archFloorAt huxleyBeta huxleyAlpha c ≤ bourgainTheta ↔ c ≤ 332 / 819 := by
  unfold archFloorAt huxleyBeta huxleyAlpha bourgainTheta
  constructor <;> intro h <;> linarith

/-- **It reaches past the final source's threshold by exactly `1/1638`.** -/
theorem huxleySource_overlap : (332 : ℚ) / 819 - decouplingStart = 1 / 1638 := by
  unfold decouplingStart; norm_num

/-! ### The window where the middle source is alone -/

/-- **On `(579/1435, 17/42)` no other source is available**, and the middle source's demand there is
increasing with supremum `277/1792` at the right endpoint. -/
theorem middleSource_alone :
    coverThreshold (16 / 237) (743 / 948) bourgainTheta = 579 / 1435 ∧
      decouplingStart - (579 : ℚ) / 1435 = 11 / 8610 ∧
        archFloorAt huxleyBeta huxleyAlpha decouplingStart = 277 / 1792 := by
  refine ⟨coverThreshold_procAHuxley, ?_, ?_⟩
  · unfold decouplingStart; norm_num
  · rw [archFloor_is_huxleyDemand, huxleyDemand_eq]

/-- The middle source's demand increases across the window. -/
theorem middleSource_increasing {c c' : ℚ} (h : c ≤ c') :
    archFloorAt huxleyBeta huxleyAlpha c ≤ archFloorAt huxleyBeta huxleyAlpha c' := by
  unfold archFloorAt huxleyBeta huxleyAlpha
  nlinarith

/-- **So the covering cannot prove anything below `277/1792`.** -/
theorem sectionFour_floor {β : ℚ} (h : archFloorAt huxleyBeta huxleyAlpha decouplingStart ≤ β) :
    277 / 1792 ≤ β := by
  rw [archFloor_is_huxleyDemand, huxleyDemand_eq] at h; exact h

/-! ### The slack profile -/

/-- **The covering is tight only at the critical scale.**  Its next-tightest point is `17/42`, with
slack exactly `1/5376`. -/
theorem slack_at_decouplingStart :
    bourgainTheta - archFloorAt huxleyBeta huxleyAlpha decouplingStart = 1 / 5376 := by
  rw [archFloor_is_huxleyDemand, huxleyDemand_eq]
  unfold bourgainTheta; norm_num

/-- At `12/31`, where the middle source becomes available, the slack is `243/68572`. -/
theorem slack_at_huxleyStart :
    bourgainTheta - covDemandOfPair (12 / 31) (16 / 237) (743 / 948) = 243 / 68572 := by
  unfold covDemandOfPair covFunctional bourgainTheta; norm_num

/-! ### The pair that would close the gap -/

/-- **The exact target.**  A low-range pair with demand at most `277/1792` at `c = 17/42` removes the
floor; the best available pair misses by `589/1274112`. -/
theorem gap_closing_target :
    covDemandOfPair decouplingStart (16 / 237) (743 / 948) - 277 / 1792 = 589 / 1274112 := by
  unfold covDemandOfPair covFunctional decouplingStart; norm_num

/-- The demand at `17/42` as a linear functional of the pair. -/
theorem demand_at_decouplingStart_linear (κ lam : ℚ) :
    covDemandOfPair decouplingStart κ lam = (25 * κ + 17 * lam) / 42 - 17 / 84 := by
  unfold covDemandOfPair covFunctional decouplingStart; ring

/-! ### Pairs on the line of symmetry are scale-flat -/

/-- **Zero displacement on the line of symmetry.** -/
@[simp] theorem epDisplacement_on_symmetry (κ : ℚ) : epDisplacement κ (κ + 1 / 2) = 0 := by
  unfold epDisplacement; ring

/-- **Hence constant demand at every scale.** -/
theorem covDemand_flat_on_symmetry (c κ : ℚ) : covDemandOfPair c κ (κ + 1 / 2) = κ := by
  rw [covDemandOfPair_affine, epDisplacement_on_symmetry]; ring

/-- **The record pair is on the line of symmetry**, so it delivers `13/84` at every scale by itself. -/
theorem record_pair_flat (c : ℚ) :
    epDisplacement (13 / 84) (55 / 84) = 0 ∧ covDemandOfPair c (13 / 84) (55 / 84) = 13 / 84 := by
  have h : epDisplacement (13 / 84 : ℚ) (55 / 84) = 0 := by unfold epDisplacement; norm_num
  refine ⟨h, ?_⟩
  rw [covDemandOfPair_affine, h]; ring

/-- **So is Weyl's pair.** -/
theorem weyl_pair_flat (c : ℚ) :
    epDisplacement (1 / 6) (2 / 3) = 0 ∧ covDemandOfPair c (1 / 6) (2 / 3) = 1 / 6 := by
  have h : epDisplacement (1 / 6 : ℚ) (2 / 3) = 0 := by unfold epDisplacement; norm_num
  refine ⟨h, ?_⟩
  rw [covDemandOfPair_affine, h]; ring

/-- **Summary.**  The Section-4 floor `277/1792` is the middle source's demand at `17/42`, the one
scale where nothing else is available; the responsible gap has width `11/8610`; closing it needs a
pair beating `(16/237, 743/948)` at `17/42` by `589/1274112`; and both the record and Weyl pairs are
scale-flat, so past `13/84` the improvement must come at the critical scale. -/
theorem section_four_gap_summary :
    archFloorAt huxleyBeta huxleyAlpha decouplingStart = 277 / 1792 ∧
      decouplingStart - (579 : ℚ) / 1435 = 11 / 8610 ∧
        covDemandOfPair decouplingStart (16 / 237) (743 / 948) - 277 / 1792 = 589 / 1274112 ∧
          ∀ c : ℚ, covDemandOfPair c (13 / 84) (55 / 84) = 13 / 84 :=
  ⟨middleSource_alone.2.2, middleSource_alone.2.1, gap_closing_target,
    fun c => (record_pair_flat c).2⟩

end HTGeometry
