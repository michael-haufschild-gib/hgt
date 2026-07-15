import GaloisForLFunctions.RHTower.SoninCoupledPrimeArchGramTransfer
import GaloisForLFunctions.RHTower.PrimeArchEndpointCalibratedHausdorffRH

/-!
# Complete quantum Hausdorff laws for the coupled Sonin source

The all-prime coupled source is a single Hilbert--Schmidt channel `Cₐ`.  Its positive master
effect `Tₐ = Cₐ† Cₐ` therefore inherits two complete moment constraints from quantum mechanics:

* at the fixed aperture-independent radius `R_S`, every scaled difference of
  `Re Tr(Tₐ^(k+1))` is nonnegative;
* after density normalization, every ordinary complementary difference is nonnegative.

The second statement discharges the Hausdorff/Bernstein positivity premise used by the actual
coupled-source Bernstein collar comparison.  The first supplies the all-order compact-support
constraint which was previously available only at difference order one.
-/

namespace RHTower

noncomputable section

open HTGeometry

/-- The RHTower scaled recursion on coupled trace moments is literally the general quantum
master-effect recursion. -/
theorem scaledHausdorffMomentDifference_re_soninAllPrimeCoupledTraceMoment_eq_quantum
    (a : SoninPositiveAperture) (k r : ℕ) :
    scaledHausdorffMomentDifference soninAllPrimeColumnEffectRadius
        (fun j => (soninAllPrimeCoupledTraceMoment a j).re) k r =
      quantumMasterEffectScaledDifference soninAllPrimeColumnEffectRadius
        (soninAllPrimeColumnCoordinateOperator a.1 a.2) k r := by
  induction r generalizing k with
  | zero =>
      simp only [scaledHausdorffMomentDifference,
        quantumMasterEffectScaledDifference, quantumMasterEffectMoment,
        quantumChannelEffect, soninAllPrimeCoupledTraceMoment,
        soninAllPrimeCoupledCoordinateEnergy]
  | succ r ih =>
      rw [scaledHausdorffMomentDifference, quantumMasterEffectScaledDifference,
        ih k, ih (k + 1)]

/-- **Complete fixed-radius source law.**  Every order of the scaled Hausdorff hierarchy holds
for the coupled all-prime trace moments, with one radius independent of aperture. -/
theorem re_soninAllPrimeCoupledTraceMoment_scaledHausdorffDifferencesNonnegative
    (a : SoninPositiveAperture) :
    ScaledHausdorffMomentDifferencesNonnegative soninAllPrimeColumnEffectRadius
      (fun j => (soninAllPrimeCoupledTraceMoment a j).re) := by
  intro k r
  rw [scaledHausdorffMomentDifference_re_soninAllPrimeCoupledTraceMoment_eq_quantum]
  exact quantumMasterEffectScaledDifference_nonneg
    (HilbertSchmidt.isHilbertSchmidt_toOperatorRect
      (soninAllPrimeColumnKernel_isHSRect a.1 a.2))
    (norm_soninAllPrimeColumnCoordinateOperator_sq_le_effectRadius a.1 a.2) k r

/-- The RHTower ordinary Hausdorff recursion on normalized coupled replica values is the general
quantum density-replica recursion. -/
theorem hausdorffMomentDifference_soninAllPrimeCoupledRenyiReplicaMoment_eq_quantum
    (a : SoninPositiveAperture) (k r : ℕ) :
    hausdorffMomentDifference (soninAllPrimeCoupledRenyiReplicaMoment a) k r =
      quantumMasterEffectReplicaDifference
        (soninAllPrimeColumnCoordinateOperator a.1 a.2) k r := by
  induction r generalizing k with
  | zero =>
      rw [hausdorffMomentDifference, quantumMasterEffectReplicaDifference,
        soninAllPrimeCoupledRenyiReplicaMoment_eq_quantumMasterEffectReplicaMoment]
  | succ r ih =>
      rw [hausdorffMomentDifference, quantumMasterEffectReplicaDifference,
        ih k, ih (k + 1)]

/-- **Complete normalized source law.**  The actual coupled Sonin density-replica moments form a
Hausdorff moment sequence, with no additional source hypothesis. -/
theorem soninAllPrimeCoupledRenyiReplicaMoment_hausdorffMomentDifferencesNonnegative
    (a : SoninPositiveAperture) :
    HausdorffMomentDifferencesNonnegative
      (soninAllPrimeCoupledRenyiReplicaMoment a) := by
  intro k r
  rw [hausdorffMomentDifference_soninAllPrimeCoupledRenyiReplicaMoment_eq_quantum]
  exact quantumMasterEffectReplicaDifference_nonneg
    (HilbertSchmidt.isHilbertSchmidt_toOperatorRect
      (soninAllPrimeColumnKernel_isHSRect a.1 a.2)) k r

/-- The complete quantum difference law supplies every nonnegative Bernstein coefficient packet
required by the coupled-source collar route. -/
theorem soninAllPrimeCoupledRenyiReplicaMoment_hausdorffBernsteinNonnegative
    (a : SoninPositiveAperture) :
    HausdorffBernsteinNonnegative (soninAllPrimeCoupledRenyiReplicaMoment a) :=
  hausdorffBernsteinNonnegative_of_momentDifferencesNonnegative
    (soninAllPrimeCoupledRenyiReplicaMoment_hausdorffMomentDifferencesNonnegative a)

end

end RHTower
