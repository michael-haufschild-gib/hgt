import GaloisForLFunctions.RHTower.XiHurwitzPrincipalPhaseGrowth
import GaloisForLFunctions.RHTower.CCMSoninPathTropicalMemory

/-!
# The Xi--Hurwitz phase as a tropical Sonin loop memory

Encode the supremal normalized principal Hurwitz phase in the middle scale of a closed Sonin path
with endpoints `3`.  The middle scale equals `3` exactly when the phase is zero and lies below `3`
when the phase is positive.  The faithful Sonin Calkin normal form remembers precisely the minimum
scale visited, so compact equality with the direct endpoint Gram operator is equivalent to RH.

This is a consumer-side bridge.  The path is defined from the Xi phase; no source-only prime--Gamma
word selecting it, nor a source compact-equality theorem, is constructed here.
-/

namespace RHTower

noncomputable section

theorem xiHurwitzRightPrincipalPhaseSup_nonneg :
    0 ≤ xiHurwitzRightPrincipalPhaseSup := by
  by_cases hRH : RiemannHypothesis
  · rw [(riemannHypothesis_iff_xiHurwitzRightPrincipalPhaseSup_eq_zero).mp hRH]
  · exact (not_riemannHypothesis_iff_xiHurwitzRightPrincipalPhaseSup_pos.mp hRH).le

/-- Scale in `(1,3]` which drops below `3` exactly in the positive-phase chamber. -/
def xiHurwitzTropicalMiddleScale : ℝ :=
  2 + (1 + xiHurwitzRightPrincipalPhaseSup)⁻¹

theorem xiHurwitzTropicalMiddleScale_gt_one :
    1 < xiHurwitzTropicalMiddleScale := by
  have hden : 0 < 1 + xiHurwitzRightPrincipalPhaseSup := by
    linarith [xiHurwitzRightPrincipalPhaseSup_nonneg]
  have hinv := inv_pos.mpr hden
  unfold xiHurwitzTropicalMiddleScale
  linarith

theorem xiHurwitzTropicalMiddleScale_le_three :
    xiHurwitzTropicalMiddleScale ≤ 3 := by
  have hden : 1 ≤ 1 + xiHurwitzRightPrincipalPhaseSup := by
    linarith [xiHurwitzRightPrincipalPhaseSup_nonneg]
  have hinv := inv_le_one_of_one_le₀ hden
  unfold xiHurwitzTropicalMiddleScale
  linarith

theorem xiHurwitzTropicalMiddleScale_eq_three_iff :
    xiHurwitzTropicalMiddleScale = 3 ↔
      xiHurwitzRightPrincipalPhaseSup = 0 := by
  constructor
  · intro h
    have hinv : (1 + xiHurwitzRightPrincipalPhaseSup)⁻¹ = 1 := by
      unfold xiHurwitzTropicalMiddleScale at h
      linarith
    have hden : 1 + xiHurwitzRightPrincipalPhaseSup = 1 := inv_eq_one.mp hinv
    linarith
  · intro h
    rw [xiHurwitzTropicalMiddleScale, h]
    norm_num

/-- Closed three-node Sonin path `3 -> middle -> 3`. -/
def xiHurwitzTropicalLoop : SoninScalePath :=
  .extend
    (.edge 3 xiHurwitzTropicalMiddleScale (by norm_num)
      xiHurwitzTropicalMiddleScale_gt_one)
    3 (by norm_num)

@[simp] theorem xiHurwitzTropicalLoop_start : xiHurwitzTropicalLoop.start = 3 := rfl

@[simp] theorem xiHurwitzTropicalLoop_endpoint : xiHurwitzTropicalLoop.endpoint = 3 := rfl

theorem xiHurwitzTropicalLoop_minimum :
    xiHurwitzTropicalLoop.minimum = xiHurwitzTropicalMiddleScale := by
  change min (min 3 xiHurwitzTropicalMiddleScale) 3 = xiHurwitzTropicalMiddleScale
  rw [min_eq_right xiHurwitzTropicalMiddleScale_le_three,
    min_eq_left xiHurwitzTropicalMiddleScale_le_three]

/-- RH is equivalent to endpoint absorption of the phase-coded closed Sonin path in the Calkin
algebra. -/
theorem riemannHypothesis_iff_xiHurwitzTropicalLoop_compactEq_direct
    (a : ℝ) (ha : 0 < a) :
    RiemannHypothesis ↔
      xiHurwitzTropicalLoop.operator a =ₖ
        (soninGramFactorOfScales xiHurwitzTropicalLoop.start
          xiHurwitzTropicalLoop.endpoint xiHurwitzTropicalLoop.start_gt_one
          xiHurwitzTropicalLoop.endpoint_gt_one).operator a := by
  rw [SoninScalePath.operator_compactEq_direct_iff_minimum_eq_endpointMin a ha,
    xiHurwitzTropicalLoop_minimum, xiHurwitzTropicalLoop_start,
    xiHurwitzTropicalLoop_endpoint, min_self,
    xiHurwitzTropicalMiddleScale_eq_three_iff]
  exact riemannHypothesis_iff_xiHurwitzRightPrincipalPhaseSup_eq_zero

end


end RHTower
