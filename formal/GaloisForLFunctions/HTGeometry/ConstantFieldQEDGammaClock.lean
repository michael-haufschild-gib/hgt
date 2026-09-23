import GaloisForLFunctions.HTGeometry.GammaOrientationQuotientBoundary
import GaloisForLFunctions.HTGeometry.MeromorphicGammaNatScale
import GaloisForLFunctions.HTGeometry.VenezianoGammaRatioBoundary
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Constant-field QED Gamma clock

Equations (20) and (29) of Blau--Visser--Wipf, *Analytic Results for the Effective
Action*, arXiv:0906.2851, express the two-dimensional scalar and spinor one-loop effective
Lagrangians in a constant magnetic field through

`Gamma(x + 1/2)` and `Gamma(x + 1)`, where `x = m^(2 : ℕ)/(2B)`.

After removing the displayed elementary renormalization terms and exponentiating, these are the
complete non-DA carriers.  Their quotient is the inverse reduced Veneziano ratio at separation
`1/2`; their product is a same-orientation Gamma pair; and Gauss duplication identifies that
product with the double-scale clock `Gamma(2*x+1)` up to a nonzero DA gauge.

The theorem concerns the determinant response as the dimensionless mass-to-field clock is read.
It is not a temporal evolution statement.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Gamma carrier of the renormalized exponentiated scalar determinant in the clock
`x=m^(2 : ℕ)/(2B)`. -/
def constantMagneticScalarQEDGammaCarrierMero : meroField Set.univ :=
  gammaShiftMero (1 / 2)

/-- Gamma carrier of the renormalized exponentiated spinor determinant in the same clock. -/
def constantMagneticSpinorQEDGammaCarrierMero : meroField Set.univ :=
  gammaShiftMero 1

/-- Spin-statistics comparison of the two exact determinant carriers. -/
def constantMagneticQEDSpinStatisticsRatioMero : meroField Set.univ :=
  constantMagneticSpinorQEDGammaCarrierMero /
    constantMagneticScalarQEDGammaCarrierMero

/-- Combined scalar--spinor determinant carrier. -/
def constantMagneticQEDCombinedGammaCarrierMero : meroField Set.univ :=
  constantMagneticScalarQEDGammaCarrierMero *
    constantMagneticSpinorQEDGammaCarrierMero

/-- **QED/Veneziano value relation.**  The spin-statistics determinant ratio is the inverse
Euler-beta/Veneziano ratio with half-integer channel separation. -/
theorem constantMagneticQEDSpinStatisticsRatioMero_eq_inv_reducedVeneziano :
    constantMagneticQEDSpinStatisticsRatioMero =
      (reducedVenezianoAmplitudeMero (1 / 2) (1 / 2))⁻¹ := by
  rw [constantMagneticQEDSpinStatisticsRatioMero,
    constantMagneticSpinorQEDGammaCarrierMero,
    constantMagneticScalarQEDGammaCarrierMero,
    reducedVenezianoAmplitudeMero]
  norm_num

private theorem complex_half_ne_integer (k : ℤ) :
    (1 / 2 : ℂ) ≠ (k : ℂ) := by
  intro h
  have htwo := congrArg (fun z : ℂ => 2 * z) h
  norm_num at htwo
  have htwoZ : (1 : ℤ) = 2 * k := by exact_mod_cast htwo
  omega

/-- The scalar--spinor determinant ratio is HT: the bosonic and fermionic Landau-level shifts
occupy distinct integer-translation orbits. -/
theorem hypertranscendentalOver_constantMagneticQEDSpinStatisticsRatioMero :
    HypertranscendentalOver (RatFunc ℂ)
      constantMagneticQEDSpinStatisticsRatioMero := by
  rw [constantMagneticQEDSpinStatisticsRatioMero_eq_inv_reducedVeneziano,
    HTGeometry.hypertranscendentalOver_inv_iff]
  exact (hypertranscendentalOver_reducedVenezianoAmplitudeMero_iff_nonintegerShift
    (1 / 2) (1 / 2)).2 complex_half_ne_integer

/-- The combined determinant carrier is exactly the same-orientation half/unit Gamma pair. -/
theorem constantMagneticQEDCombinedGammaCarrierMero_eq_positivePair :
    constantMagneticQEDCombinedGammaCarrierMero =
      gammaPositiveShiftPairMero (1 / 2) 1 := rfl

/-- The scalar and spinor Gamma sectors do not cancel in their product. -/
theorem hypertranscendentalOver_constantMagneticQEDCombinedGammaCarrierMero :
    HypertranscendentalOver (RatFunc ℂ)
      constantMagneticQEDCombinedGammaCarrierMero := by
  rw [constantMagneticQEDCombinedGammaCarrierMero_eq_positivePair]
  exact hypertranscendentalOver_gammaPositiveShiftPairMero (1 / 2) 1

/-- **Landau-level duplication law.**  Combining the scalar and spinor sectors produces one
double-scale Gamma clock up to the inverse standard nonzero DA Gauss gauge. -/
theorem constantMagneticQEDCombinedGammaCarrierMero_duplication :
    constantMagneticQEDCombinedGammaCarrierMero =
      (gammaNatScaleGaussGaugeMero 2 1)⁻¹ * gammaNatScaleMero 2 1 := by
  have hgauss := gammaNatScaleMero_gauss
    (n := 2) (show 0 < 2 by norm_num) (1 : ℂ)
  change gammaNatScaleMero 2 1 =
      gammaNatScaleGaussGaugeMero 2 1 *
        gammaNatScaleGaussProductMero 2 1 at hgauss
  have hprod : gammaNatScaleGaussProductMero 2 1 =
      constantMagneticQEDCombinedGammaCarrierMero := by
    norm_num [gammaNatScaleGaussProductMero,
      constantMagneticQEDCombinedGammaCarrierMero,
      constantMagneticScalarQEDGammaCarrierMero,
      constantMagneticSpinorQEDGammaCarrierMero,
      Finset.prod_range_succ]
  rw [hprod] at hgauss
  rw [hgauss]
  field_simp [gammaNatScaleGaussGaugeMero_ne_zero
    (show 0 < 2 by norm_num) (1 : ℂ)]

/-- **Renormalization obstruction.**  No differentially algebraic multiplicative counterterm can
turn the scalar determinant carrier into the spinor determinant carrier. -/
theorem constantMagneticSpinorQEDGammaCarrierMero_ne_da_mul_scalar
    (g : meroField Set.univ)
    (hg : DifferentialAlgebraicOver (RatFunc ℂ) g) :
    constantMagneticSpinorQEDGammaCarrierMero ≠
      g * constantMagneticScalarQEDGammaCarrierMero := by
  intro heq
  apply hypertranscendentalOver_constantMagneticQEDSpinStatisticsRatioMero
  have hratio : constantMagneticQEDSpinStatisticsRatioMero = g := by
    rw [constantMagneticQEDSpinStatisticsRatioMero, heq]
    rw [mul_div_cancel_right₀ g (by
      exact gammaShiftMero_ne_zero (1 / 2))]
  rw [hratio]
  exact hg

/-- The exact spin-statistics determinant ratio cannot be any rational or finite-Laurent clock
model. -/
theorem constantMagneticQEDSpinStatisticsRatioMero_ne_ratFuncModel
    (r : RatFunc ℂ) :
    constantMagneticQEDSpinStatisticsRatioMero ≠
      algebraMap (RatFunc ℂ) (meroField Set.univ) r := by
  intro heq
  apply hypertranscendentalOver_constantMagneticQEDSpinStatisticsRatioMero
  rw [heq]
  exact HTGeometry.differentialAlgebraicOver_algebraMap r

/-- Any scalar-aware finite differential circuit presenting the exact scalar--spinor comparison
contains an HT non-scalar atom. -/
theorem exists_hypertranscendental_atom_of_constantMagneticQEDSpinStatisticsCircuit
    {Atom : meroField Set.univ → Prop}
    (hcircuit : HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ) Atom)
      constantMagneticQEDSpinStatisticsRatioMero) :
    ∃ a : meroField Set.univ,
      Atom a ∧ HypertranscendentalOver (RatFunc ℂ) a :=
  HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
    hypertranscendentalOver_constantMagneticQEDSpinStatisticsRatioMero hcircuit

end

end GaloisForLFunctions
