import GaloisForLFunctions.RHTower.CHMDFoldedPoleMode
import GaloisForLFunctions.RHTower.CHMDForcedSpectralMeasureAndOffLineDefectWave

/-!
# Temporal atoms of the completed folded wave

The pole cancels from the completed arithmetic identity. Its bounded spectral
shadow retains the positive mass at each actual zero frequency. These masses
will separate the completed wave from every finite combination of folds.
-/

open MeasureTheory Filter Set Topology Zeta23
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone RHTower.CHMDStage22 RHTower.CHMDGrowthCollapse
open RHTower.CHMDForcedMeasure RHTower.CHMDStage4 GaloisForLFunctions.HTGeometry
open WeilOneSided WeilSpectral

noncomputable section

/-- The complete folded Möbius series, before any temporal observation. -/
def foldedMobiusWave (y : ℝ) : ℝ :=
  ∑' m : ℕ, moebiusCoeff m * mobiusFold y (Real.log m)

/-- The explicit pole mode cancels exactly in the completed series. -/
theorem foldedMobiusWave_eq (y : ℝ) :
    foldedMobiusWave y = chmdPrimeKernel y 0 - poleShadow y -
      (1 / (2 * π)) * chmdArchWave y + chmdWave y := by
  have ht := chebyshevDiscrepancyTransport_eq_sub_tsum_mobiusFold y
  have hp := chmdPrimeWave_eq_chmdPoleWave_add_transport y
  have hw := chmdWave_eq_pole_add_arch_sub_prime y
  unfold foldedMobiusWave
  linarith

theorem chmdArchWave_hasTemporalCoefficient {lam : ℝ} (hlam : 0 < lam) :
    HasTemporalCoefficient chmdArchWave lam 0 := by
  let a : ℝ → ℝ := fun r => sechSqHalf r * EF.gammaBracket r
  have hm : Measurable a :=
    continuous_sechSqHalf.measurable.mul WeilHerglotz.continuous_gammaBracket.measurable
  have hi : Integrable a := integrable_sechSqHalf_mul_gammaBracket
  have heq (y : ℝ) : chmdArchWave y =
      ∫ r : ℝ, a r * Real.cos (Real.sqrt (r ^ 2 + 2) * y) := by
    rw [chmdArchWave_eq]
    congr 1
    funext r
    dsimp only [a]
    rw [mul_comm (Real.sqrt _) y]
    ring
  refine ⟨continuous_chmdArchWave.measurable,
    ⟨∫ r : ℝ, sechSqHalf r * |EF.gammaBracket r|, abs_chmdArchWave_le⟩, ?_⟩
  rw [funext heq]
  exact kgSpectralIntegral_temporalCoefficient_zero hm hi hlam

/-- Total half-weight at one positive zero frequency, including repeated frequencies. -/
def shadowTemporalMass (lam : ℝ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, if kgAtom ρ = lam then kgAtomWeight ρ else 0

theorem summable_shadowTemporalMass (lam : ℝ) :
    Summable (fun ρ : zetaZeroConfig.carrier => if kgAtom ρ = lam then kgAtomWeight ρ else 0) := by
  classical
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) summable_kgAtomWeight
  · split_ifs
    · exact kgAtomWeight_nonneg ρ
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact kgAtomWeight_nonneg ρ

theorem kgAtomWeight_pos (ρ : zetaZeroConfig.carrier) : 0 < kgAtomWeight ρ := by
  have hm : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ ρ.2
  unfold kgAtomWeight
  exact div_pos (mul_pos (by linarith) (re_kgWeight_pos ρ)) (by norm_num)

theorem kgAtomWeight_le_shadowTemporalMass (ρ : zetaZeroConfig.carrier) :
    kgAtomWeight ρ ≤ shadowTemporalMass (kgAtom ρ) := by
  classical
  have h := (summable_shadowTemporalMass (kgAtom ρ)).le_tsum ρ
    (fun σ _ => by split_ifs; exact kgAtomWeight_nonneg σ; exact le_rfl)
  simpa only [shadowTemporalMass, if_true] using h

theorem poleFrequency_ne_kgAtom (ρ : zetaZeroConfig.carrier) :
    Real.sqrt (7 / 4 : ℝ) ≠ kgAtom ρ :=
  ne_of_lt (RHTower.CHMDSeparationLaw.sqrt_seven_fourths_lt_re_kgFreq ρ)

/-- The spectral shadow has exactly its positive discrete masses as coefficients. -/
theorem shadowWave_hasTemporalCoefficient {lam : ℝ} (hlam : 0 < lam) :
    HasTemporalCoefficient shadowWave lam (shadowTemporalMass lam) := by
  haveI : Countable zetaZeroConfig.carrier := WeilConditional.countable_carrier.to_subtype
  have h := hasTemporalCoefficient_tsum_cos (fun ρ => 2 * kgAtomWeight ρ) kgAtom
    (fun ρ => mul_nonneg (by norm_num) (kgAtomWeight_nonneg ρ))
    (summable_kgAtomWeight.mul_left 2) (fun ρ => re_kgFreq_pos ρ) hlam
  have heq (y : ℝ) : (∑' ρ : zetaZeroConfig.carrier,
      2 * kgAtomWeight ρ * Real.cos (kgAtom ρ * y)) = shadowWave y := by
    unfold shadowWave
    refine tsum_congr fun ρ => ?_
    rw [mul_comm (kgAtom ρ) y]
    unfold kgAtomWeight
    ring
  have hmass : (∑' ρ : zetaZeroConfig.carrier,
      if kgAtom ρ = lam then 2 * kgAtomWeight ρ / 2 else 0) = shadowTemporalMass lam := by
    have hscale (x : ℝ) : 2 * x / 2 = x := by ring
    simp only [shadowTemporalMass, hscale]
  simpa only [heq, hmass] using h

theorem foldedMobiusWave_hasTemporalCoefficient_of_rh (hRH : RiemannHypothesis)
    {lam : ℝ} (hlam : 0 < lam) :
    HasTemporalCoefficient foldedMobiusWave lam (shadowTemporalMass lam) := by
  have hw := (shadowWave_hasTemporalCoefficient hlam).congr
    (fun y => (chmdWave_eq_shadowWave_of_rh hRH y).symm)
  have h := (((chmdPrimeKernel_hasTemporalCoefficient 0 hlam).sub
    (poleShadow_hasTemporalCoefficient hlam)).sub
      ((chmdArchWave_hasTemporalCoefficient hlam).const_mul (1 / (2 * π)))).add hw
  have h' := h.congr (fun y => (foldedMobiusWave_eq y).symm)
  simpa only [sub_self, mul_zero, sub_zero, zero_add] using h'

end

end RHTower.CHMDChebyshevTransport
