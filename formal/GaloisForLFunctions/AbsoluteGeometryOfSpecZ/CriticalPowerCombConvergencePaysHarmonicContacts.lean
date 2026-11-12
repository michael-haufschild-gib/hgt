import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerTailArchimedeanFinitePart
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerTailReferenceFinitePart
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ConvergentPowerCombsHaveNoNonrealBoundaryResidues

/-!
# Critical comb convergence forces convergent harmonically centered contacts

The archimedean and reference finite parts remove explicit harmonic main
terms. The remaining first-degree factor converges. The exact finite comb
identity therefore transfers convergence to the centered contact prefix.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The finite first degree converges to its absolutely summable power pole. -/
theorem tendsto_powerTailPole_prefix {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, powerTailWeight (1 + a) n)
      atTop (𝓝 (powerTailPole a)) := by
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ (-a) / a) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_div] using
      ((tendsto_rpow_neg_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))).div_const a
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' _ hz
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hb := powerTailPole_sub_sum_bounds ha hN
  rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hb.1]
  exact hb.2

/-- At the critical parameter the first-degree remainder has a finite,
generally nonzero limit. -/
theorem tendsto_criticalPowerTailCombRemainder :
    Tendsto (powerTailCombRemainder (1 / 2)) atTop
      (𝓝 (2 * powerTailPole (1 / 2) * (riemannZeta ((1 / 2 : ℝ) : ℂ)).re)) := by
  have hpC := tendsto_powerTailPrefix_finitePart
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hp : Tendsto (fun N : ℕ => powerTailPrefix (1 / 2) N -
      (N : ℝ) ^ (1 - (1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ))) atTop
        (𝓝 (riemannZeta ((1 / 2 : ℝ) : ℂ)).re) :=
    (Complex.continuous_re.continuousAt.tendsto.comp hpC).congr fun _ => rfl
  have hT := tendsto_powerTailPole_prefix (by norm_num : (0 : ℝ) < 1 / 2)
  apply ((hT.const_mul 2).mul hp).congr
  intro N
  rw [powerTailCombRemainder]
  norm_num

/-- The harmonic contact coefficient forced by the two nonprime terms. -/
def criticalPowerContactCoefficient : ℝ :=
  powerTailArchimedeanRowLimit (1 / 2) / 2 - (riemannZeta ((1 / 2 : ℝ) : ℂ)).re

/-- The actual critical contact prefix with its forced harmonic drift removed. -/
def criticalHarmonicContacts (N : ℕ) : ℝ :=
  powerContactPrefix (1 / 2) N - criticalPowerContactCoefficient * harm N

/-- Critical comb convergence is equivalent to convergence after the
forced harmonic drift is removed from its literal contact prefix. -/
theorem criticalPowerCombTailConverges_iff_harmonicContacts_converges :
    PowerCombTailConverges (1 / 2) ↔
      ∃ L : ℝ, Tendsto criticalHarmonicContacts atTop (𝓝 L) := by
  let E : ℕ → ℝ := fun N =>
    (powerTailArchimedean (1 / 2) N - powerTailArchimedeanRowLimit (1 / 2) * harm N) -
      2 * tailRiemannSum criticalPowerTailReferenceProfile N + powerTailCombRemainder (1 / 2) N
  have hA := summable_criticalPowerTailArchimedeanError.hasSum.tendsto_sum_nat.congr
    (fun N => sum_criticalPowerTailArchimedeanError N)
  have hE := (hA.sub (riemannOn_criticalPowerTailReferenceProfile.2.const_mul 2)).add
    tendsto_criticalPowerTailCombRemainder
  change Tendsto E atTop (𝓝 _) at hE
  have he (N : ℕ) (hN : 1 ≤ N) :
      powerCombTail (1 / 2) N = E N - 2 * criticalHarmonicContacts N := by
    rw [powerCombTail_eq_mellin_meshes (1 / 2) hN]
    simp only [show 2 * (1 / 2 : ℝ) - 1 = 0 by ring, Real.rpow_zero, one_mul]
    dsimp only [E, criticalHarmonicContacts, criticalPowerContactCoefficient, powerContactPrefix]
    rw [tailRiemannSum_criticalPowerTailReferenceProfile hN]
    ring
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨_, ((hE.sub hL).div_const 2).congr' ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [he N hN]
    ring
  · rintro ⟨L, hL⟩
    refine ⟨_, (hE.sub (hL.const_mul 2)).congr' ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (he N hN).symm

/-- The same convergence supplies an affine logarithmic contact asymptotic. -/
theorem exists_criticalPowerContacts_log_asymptotic
    (hc : PowerCombTailConverges (1 / 2)) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => powerContactPrefix (1 / 2) N -
      criticalPowerContactCoefficient * Real.log N) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := criticalPowerCombTailConverges_iff_harmonicContacts_converges.mp hc
  refine ⟨L + criticalPowerContactCoefficient * Real.eulerMascheroniConstant, ?_⟩
  apply (hL.add (tendsto_harm_sub_log.const_mul criticalPowerContactCoefficient)).congr
  intro N
  rw [criticalHarmonicContacts]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
