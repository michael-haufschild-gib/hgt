import GaloisForLFunctions.HTGeometry.HorizonBogoliubovGammaObservability
import GaloisForLFunctions.HTGeometry.ThermalCFTGammaResponseBoundary
import GaloisForLFunctions.RHTower.ZetaChiHypertranscendentalClock

/-!
# Zeta--horizon Gamma intensity separation

Conjugate-frequency multiplication has opposite differential outcomes for two exact physical
Gamma clocks.  The thermal-horizon carrier of `HorizonBogoliubovGammaObservability` is centered at
zero, and its intensity `Gamma(z)*Gamma(-z)` is differentially algebraic.  The centered zeta
completion is shifted by `1/4`; its corresponding intensity is

`Gamma(z+1/4) * Gamma(-z+1/4)`.

The general opposite-orientation classification sees the difference exactly: the horizon shifts
sum to the integer `0`, whereas the zeta shifts sum to the noninteger `1/2`.  Hence the zeta
intensity remains hypertranscendental.

This has a direct observability consequence for the RH corpus.  No scalar-aware finite
differential circuit can manufacture the zeta intensity from the horizon intensity, and no DA
multiplicative calibration identifies the zeta phase with its intensity.  Modulus-square
coarse-graining therefore does not have a universal differential effect; the affine center read
by the observable is decisive.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace RHTower

open GaloisForLFunctions Bottcher Polynomial

noncomputable section

local instance zetaHorizonGammaIntensityDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance zetaHorizonGammaIntensityDifferential :
    Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance zetaHorizonGammaIntensityRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance zetaHorizonGammaIntensityRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance zetaHorizonGammaIntensityDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance zetaHorizonGammaIntensityCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- Conjugate-frequency Gamma intensity of zeta's centered archimedean completion clock. -/
def centeredZetaGammaIntensityCoreMero : meroField Set.univ :=
  gammaReflectionProductMero (1 / 4)

/-- The zeta intensity is the quarter-weight specialization of both the thermal-CFT symmetric
kernel and the general opposite-orientation Gamma product. -/
theorem centeredZetaGammaIntensityCoreMero_eq_oppositeProduct :
    centeredZetaGammaIntensityCoreMero =
      gammaOppositeShiftProductMero (1 / 4) (1 / 4) := rfl

private theorem complex_half_ne_integer (k : ℤ) :
    (1 / 2 : ℂ) ≠ (k : ℂ) := by
  intro h
  have htwo := congrArg (fun z : ℂ => 2 * z) h
  norm_num at htwo
  have htwoZ : (1 : ℤ) = 2 * k := by exact_mod_cast htwo
  omega

/-- **Zeta intensity survival.**  The quarter-shifted conjugate-frequency pair is HT because its
physical shift sum is `1/2`, outside the integer cancellation lattice. -/
theorem hypertranscendentalOver_centeredZetaGammaIntensityCoreMero :
    HypertranscendentalOver (RatFunc ℂ)
      centeredZetaGammaIntensityCoreMero := by
  rw [centeredZetaGammaIntensityCoreMero,
    hypertranscendentalOver_gammaReflectionProductMero_iff_nonintegerWeight]
  intro k
  norm_num
  exact complex_half_ne_integer k

private theorem gammaNegativeQuarterMero_ne_zero :
    gammaNegativeShiftMero (1 / 4) ≠ 0 := by
  rw [gammaNegativeShiftMero_reflection]
  exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero (1 / 4))
    (inv_ne_zero (gammaShiftMero_ne_zero (1 - 1 / 4)))

/-- Dividing the centered zeta phase by its intensity cancels the negative-frequency factor and
leaves the inverse square of the positive-frequency Gamma carrier. -/
theorem centeredZetaGammaReflection_div_intensity_eq_inv_positivePair :
    centeredZetaGammaReflectionMero /
        centeredZetaGammaIntensityCoreMero =
      (gammaPositiveShiftPairMero (1 / 4) (1 / 4))⁻¹ := by
  rw [centeredZetaGammaReflectionMero, gammaReflectionRatioMero,
    centeredZetaGammaIntensityCoreMero, gammaReflectionProductMero,
    gammaPositiveShiftPairMero]
  have hp : gammaShiftMero (1 / 4) ≠ 0 :=
    gammaShiftMero_ne_zero (1 / 4)
  have hn : gammaNegativeShiftMero (1 / 4) ≠ 0 :=
    gammaNegativeQuarterMero_ne_zero
  field_simp [hp, hn, mul_ne_zero hn (pow_ne_zero 2 hp)]

/-- Zeta's phase and intensity retain inequivalent HT information: their quotient is itself HT. -/
theorem hypertranscendentalOver_centeredZetaGammaReflection_div_intensity :
    HypertranscendentalOver (RatFunc ℂ)
      (centeredZetaGammaReflectionMero /
        centeredZetaGammaIntensityCoreMero) := by
  rw [centeredZetaGammaReflection_div_intensity_eq_inv_positivePair,
    HTGeometry.hypertranscendentalOver_inv_iff]
  exact hypertranscendentalOver_gammaPositiveShiftPairMero (1 / 4) (1 / 4)

/-- No DA multiplicative calibration converts the zeta intensity into its oriented Gamma phase. -/
theorem centeredZetaGammaReflectionMero_ne_da_mul_intensity
    (g : meroField Set.univ)
    (hg : DifferentialAlgebraicOver (RatFunc ℂ) g) :
    centeredZetaGammaReflectionMero ≠
      g * centeredZetaGammaIntensityCoreMero := by
  intro heq
  apply hypertranscendentalOver_centeredZetaGammaReflection_div_intensity
  have hintensity : centeredZetaGammaIntensityCoreMero ≠ 0 := by
    rw [centeredZetaGammaIntensityCoreMero, gammaReflectionProductMero]
    exact mul_ne_zero (gammaShiftMero_ne_zero (1 / 4))
      gammaNegativeQuarterMero_ne_zero
  rw [heq]
  simpa [hintensity] using hg

/-- **Direct `HTGeometry` to `RHTower` obstruction.**  Rational clock data together with the DA
horizon intensity, closed under finitely many field operations and differentiations, cannot
produce zeta's HT quarter-shifted archimedean intensity. -/
theorem no_scalarAwareFiniteDifferentialCircuit_centeredZetaIntensity_from_horizonIntensity :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a = horizonBogoliubovGammaIntensityCoreMero))
      centeredZetaGammaIntensityCoreMero := by
  intro hcircuit
  obtain ⟨a, ha, hHT⟩ :=
    HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
      hypertranscendentalOver_centeredZetaGammaIntensityCoreMero hcircuit
  rw [ha] at hHT
  exact hHT differentialAlgebraicOver_horizonBogoliubovGammaIntensityCoreMero

end

end RHTower
