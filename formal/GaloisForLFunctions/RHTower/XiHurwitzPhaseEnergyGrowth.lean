import GaloisForLFunctions.RHTower.XiHurwitzPrincipalPhaseGrowth
import GaloisForLFunctions.RHTower.XiHurwitzOrientationSourceSequenceGate

/-!
# Principal Hurwitz phase as an orientation-energy and source-value witness

The principal Hurwitz phase of a right-half Xi zero is not merely another RH reader.  Pointwise,
its squared sine is exactly the corresponding summand of the canonical Xi--Hurwitz orientation
energy.  Since that energy is the negative limit of finite continued prime--Gamma Cauchy-source
values, every positive transverse phase forces an explicit eventually negative source-value floor.

Together with `xiHurwitzPrincipalPhaseSup_is_sharp_rectangular_power_exponent`, this identifies the
same HGT value coordinate in three roles: a transverse zero displacement, a sharp rectangular
growth exponent, and a strictly positive contribution to the negative continued-source limit.
No sign theorem or RH conclusion is asserted here.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- The orientation defect of a right-half Xi zero is exactly the squared sine of its normalized
principal Hurwitz phase. -/
theorem xiHurwitzOrientationDefect_eq_sin_sq_rightPrincipalPhase
    (q : XiRightZeroCopy) :
    xiHurwitzOrientationDefect q.1.1 =
      Real.sin (2 * Real.pi * xiHurwitzRightPrincipalPhase q) ^ (2 : ℕ) := by
  rw [xiHurwitzOrientationDefect_eq_sin_sq,
    xiHurwitzRightPrincipalPhase_eq_transverse,
    xiRightCenteredZero_eq_support_sub_half]
  have hhalf : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by norm_num
  rw [Complex.sub_re, hhalf]
  rw [show 2 * Real.pi * (q.1.1 : ℂ).re =
      2 * Real.pi * ((q.1.1 : ℂ).re - 1 / 2) + Real.pi by ring,
    Real.sin_add_pi]
  ring

/-- Every right-half principal phase contributes an explicit positive term bounded above by the
global orientation energy. -/
theorem xiHurwitzRightPrincipalPhase_witness_le_orientationEnergy
    (q : XiRightZeroCopy) :
    xiHurwitzOrientationWeight q.1.1 *
        Real.sin (2 * Real.pi * xiHurwitzRightPrincipalPhase q) ^ (2 : ℕ) ≤
      xiHurwitzOrientationEnergy := by
  rw [← xiHurwitzOrientationDefect_eq_sin_sq_rightPrincipalPhase,
    ← xiHurwitzOrientationEnergyTerm]
  exact xiHurwitzOrientationEnergyTerm_le_energy q.1.1

theorem xiHurwitzRightPrincipalPhase_pos (q : XiRightZeroCopy) :
    0 < xiHurwitzRightPrincipalPhase q := by
  rw [xiHurwitzRightPrincipalPhase_eq_transverse]
  exact xiRightCenteredZero_re_pos q

theorem xiHurwitzRightPrincipalPhase_lt_half (q : XiRightZeroCopy) :
    xiHurwitzRightPrincipalPhase q < 1 / 2 := by
  rw [xiHurwitzRightPrincipalPhase_eq_transverse]
  exact (le_abs_self _).trans_lt (abs_xiRightCenteredZero_re_lt_half q)

/-- The open critical strip makes the phase witness strictly positive, with no trigonometric
aliasing. -/
theorem sin_two_pi_xiHurwitzRightPrincipalPhase_pos (q : XiRightZeroCopy) :
    0 < Real.sin (2 * Real.pi * xiHurwitzRightPrincipalPhase q) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · nlinarith [Real.pi_pos, xiHurwitzRightPrincipalPhase_pos q]
  · nlinarith [Real.pi_pos, xiHurwitzRightPrincipalPhase_lt_half q]

theorem xiHurwitzRightPrincipalPhase_energyWitness_pos (q : XiRightZeroCopy) :
    0 < xiHurwitzOrientationWeight q.1.1 *
      Real.sin (2 * Real.pi * xiHurwitzRightPrincipalPhase q) ^ (2 : ℕ) := by
  exact mul_pos (xiHurwitzOrientationWeight_pos q.1.1)
    (sq_pos_of_pos (sin_two_pi_xiHurwitzRightPrincipalPhase_pos q))

/-- **Phase-to-source negative-value law.**  A single positive transverse HGT phase forces the
unconditional continued-Cauchy reconstruction sequence eventually below minus half of that
phase's explicit orientation-energy contribution. -/
theorem exists_continuedCauchyCore_eventually_lt_neg_half_phaseWitness
    (q : XiRightZeroCopy) :
    ∃ V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
      (∀ n, V n ∈ xiWeilContinuedCauchyAlgebraicSubspace) ∧
      Tendsto V atTop (nhds xiHurwitzOrientationVector) ∧
      Tendsto (fun n => xiWeilHilbertQuadratic (V n)) atTop
        (nhds (-xiHurwitzOrientationEnergy)) ∧
      ∀ᶠ n in atTop,
        xiWeilHilbertQuadratic (V n) <
          -(xiHurwitzOrientationWeight q.1.1 *
            Real.sin (2 * Real.pi * xiHurwitzRightPrincipalPhase q) ^ (2 : ℕ)) / 2 := by
  obtain ⟨V, hVmem, hV, hQ⟩ :=
    xiHurwitzOrientationEnergy_continuedCauchy_reconstruction
  refine ⟨V, hVmem, hV, hQ, ?_⟩
  apply hQ.eventually_lt_const
  have hpos := xiHurwitzRightPrincipalPhase_energyWitness_pos q
  have hle := xiHurwitzRightPrincipalPhase_witness_le_orientationEnergy q
  nlinarith

end


end RHTower
