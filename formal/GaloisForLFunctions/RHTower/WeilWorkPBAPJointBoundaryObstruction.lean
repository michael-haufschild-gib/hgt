import GaloisForLFunctions.RHTower.WeilWorkPBAPJointBoundarySeed
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointUniformHigh

/-!
# Failure of a single-node cosine certificate beyond the logarithmic boundary

The literal seed and its opposite-phase modulation have negative total full
energy for d < 1. This excludes every real coefficient for this one cosine.
It does not assert a negative all-integer-null mixture or refute full PBAP.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

private theorem boundary_opposite_height {L s : ℝ} (hL : 0 ≤ L)
    (hs : L-Real.log 2 ≤ s) : Real.exp (7*L/8) ≤ Real.pi*Real.exp s := by
  have he := Real.exp_le_exp.mpr (show L ≤ s+Real.log 2 by linarith)
  rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)] at he
  have h0 := Real.exp_le_exp.mpr (show 7*L/8 ≤ L by linarith)
  have hpi : 2 ≤ Real.pi := (by linarith [Real.pi_gt_three])
  have hp := mul_le_mul_of_nonneg_right hpi (Real.exp_pos s).le
  linarith only [he,h0,hp]

private theorem boundary_opposite_log {s : ℝ} (hs : 0 ≤ s) :
    Real.log (1+Real.pi*Real.exp s) ≤ s+Real.log (1+Real.pi) := by
  have he : 1 ≤ Real.exp s := Real.one_le_exp_iff.mpr hs
  have hp : 0 < 1+Real.pi := by positivity
  have h := Real.log_le_log (by positivity : 0 < 1+Real.pi*Real.exp s)
    (show 1+Real.pi*Real.exp s ≤ (1+Real.pi)*Real.exp s by nlinarith only [he])
  rw [Real.log_mul hp.ne' (Real.exp_pos s).ne',Real.log_exp] at h
  linarith only [h]

/-- The source seed and its exact opposite-phase test have negative combined full energy. -/
theorem eventually_jointUnitBump_boundary_opposite_negative {d : ℝ} (hd : d < 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (s : ℝ), L-Real.log 2 ≤ s → s ≤ 2*L+Real.log 2 →
      ∀ hK : 0 < jointBoundaryScale d L s,
      let W := jointBoundaryWidth jointUnitBumpTest L (jointBoundaryScale d L s)
      let hW := jointBoundaryWidth_pos jointUnitBumpTest jointUnitBumpTest_mass_pos
        jointUnitBumpTest_integral_ne_zero L hK
      let g := jointDilatedTest jointUnitBumpTest W hW
      jointPairFullEnergy g L 0+jointPairFullEnergy g L (Real.pi*Real.exp s) < 0 := by
  let A := jointBoundarySeedCost jointUnitBumpTest
  let C := A+2*Real.log (1+Real.pi)+9
  have hden : 0 < 2*(1-d) := by linarith
  have hlog := Real.tendsto_log_atTop.eventually (eventually_gt_atTop (C/(2*(1-d))))
  have hw := eventually_jointBoundaryWidth_bounds jointUnitBumpTest
    jointUnitBumpTest_mass_pos jointUnitBumpTest_integral_ne_zero
  filter_upwards [eventually_jointUnitBump_boundary_seed_expansion d,
    eventually_jointUnitBump_uniform_high_bounds,eventually_jointBoundaryScale_bounds d,
    hw,hlog,eventually_ge_atTop (3:ℝ)] with L hseed hhigh hscale hw hlog hL
  intro s hslo hshi hK
  let W := jointBoundaryWidth jointUnitBumpTest L (jointBoundaryScale d L s)
  have hW : 0 < W := jointBoundaryWidth_pos jointUnitBumpTest jointUnitBumpTest_mass_pos
    jointUnitBumpTest_integral_ne_zero L hK
  let g := jointDilatedTest jointUnitBumpTest W hW
  have hm : 0 < W*testMass jointUnitBumpTest.1.1 := mul_pos hW jointUnitBumpTest_mass_pos
  obtain ⟨hKlo,hKhi⟩ := hscale s hslo hshi
  have hwK := hw _ hKlo hKhi
  have hs0 : 0 ≤ s := by
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hL,hslo,hl2]
  have hT := boundary_opposite_height (show 0 ≤ L by linarith) hslo
  have he := (hhigh W hW hwK.2.2.2 hwK.2.1 (Real.pi*Real.exp s)
    (by simpa only [abs_of_pos (mul_pos Real.pi_pos (Real.exp_pos s))] using hT)).2
  have he0 := (abs_le.mp (hseed s hslo hshi hK)).2
  have hl := boundary_opposite_log hs0
  have hneg := (div_lt_iff₀ hden).mp hlog
  change jointPairFullEnergy g L 0+jointPairFullEnergy g L (Real.pi*Real.exp s) < 0
  have hsum : jointPairFullEnergy g L 0/(W*testMass jointUnitBumpTest.1.1)+
      jointPairFullEnergy g L (Real.pi*Real.exp s)/(W*testMass jointUnitBumpTest.1.1) < 0 := by
    rw [abs_of_pos (mul_pos Real.pi_pos (Real.exp_pos s))] at he
    change jointPairFullEnergy g L (Real.pi*Real.exp s)/(W*testMass jointUnitBumpTest.1.1) ≤ _ at he
    change jointPairFullEnergy g L 0/(W*testMass jointUnitBumpTest.1.1)+
      2*s-2*(d-1)*Real.log L ≤ A at he0
    dsimp only [C] at hneg
    linarith only [he,he0,hl,hneg]
  rw [← add_div] at hsum
  simpa only [zero_mul] using (div_lt_iff₀ hm).mp hsum

/-- No real coefficient gives a global certificate using this one actual phase scale. -/
theorem eventually_jointUnitBump_boundary_no_cosine {d : ℝ} (hd : d < 1) :
    ∀ᶠ L : ℝ in atTop, ∀ (s : ℝ), L-Real.log 2 ≤ s → s ≤ 2*L+Real.log 2 →
      ∀ hK : 0 < jointBoundaryScale d L s,
      let W := jointBoundaryWidth jointUnitBumpTest L (jointBoundaryScale d L s)
      let hW := jointBoundaryWidth_pos jointUnitBumpTest jointUnitBumpTest_mass_pos
        jointUnitBumpTest_integral_ne_zero L hK
      let g := jointDilatedTest jointUnitBumpTest W hW
      ¬ ∃ c : ℝ, ∀ T : ℝ, -c*Real.cos (Real.exp (-s)*T) ≤ jointPairFullEnergy g L T := by
  filter_upwards [eventually_jointUnitBump_boundary_opposite_negative hd] with L h
  intro s hslo hshi hK
  dsimp only
  rintro ⟨c,hc⟩
  have h0 := hc 0
  have hpi := hc (Real.pi*Real.exp s)
  have hphase : Real.exp (-s)*(Real.pi*Real.exp s)=Real.pi := by
    rw [mul_left_comm,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
  rw [hphase,Real.cos_pi] at hpi
  simp only [mul_zero,Real.cos_zero,mul_one] at h0
  have hn := h s hslo hshi hK
  dsimp only at hn
  linarith only [h0,hpi,hn]

end RHTower.WeilWorkPBAP
