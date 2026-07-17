import GaloisForLFunctions.RHTower.SoninCoupledBernsteinCollarComparison
import GaloisForLFunctions.RHTower.PrimeArchEndpointCalibratedHausdorffRH
import GaloisForLFunctions.HTGeometry.QuantumReplicaHausdorff

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

/-- The normalized coupled source used by the collar comparison is exactly the density-operator
replica sequence of the actual all-prime Sonin column. -/
theorem soninCoupledNormalizedReplicaMoment_eq_quantumMasterEffectReplicaMoment
    (a : SoninPositiveAperture) (k : ℕ) :
    soninCoupledNormalizedReplicaMoment a k =
      quantumMasterEffectReplicaMoment
        (soninAllPrimeColumnCoordinateOperator a.1 a.2) k := by
  rw [soninCoupledNormalizedReplicaMoment,
    quantumMasterEffectReplicaMoment,
    quantumMasterEffectMoment,
    quantumMasterEffectMass,
    soninAllPrimeCoupledTraceMoment_zero_eq_column_hsNormSq]
  rfl

/-- The RHTower ordinary Hausdorff recursion on the collar's normalized coupled source is the
general quantum density-replica recursion. -/
theorem hausdorffMomentDifference_soninCoupledNormalizedReplicaMoment_eq_quantum
    (a : SoninPositiveAperture) (k r : ℕ) :
    hausdorffMomentDifference (soninCoupledNormalizedReplicaMoment a) k r =
      quantumMasterEffectReplicaDifference
        (soninAllPrimeColumnCoordinateOperator a.1 a.2) k r := by
  induction r generalizing k with
  | zero =>
      rw [hausdorffMomentDifference, quantumMasterEffectReplicaDifference,
        soninCoupledNormalizedReplicaMoment_eq_quantumMasterEffectReplicaMoment]
  | succ r ih =>
      rw [hausdorffMomentDifference, quantumMasterEffectReplicaDifference,
        ih k, ih (k + 1)]

/-- **Complete normalized source law.**  The actual coupled Sonin density-replica moments form a
Hausdorff moment sequence, with no additional source hypothesis. -/
theorem soninAllPrimeCoupledRenyiReplicaMoment_hausdorffMomentDifferencesNonnegative
    (a : SoninPositiveAperture) :
    HausdorffMomentDifferencesNonnegative
      (soninCoupledNormalizedReplicaMoment a) := by
  intro k r
  rw [hausdorffMomentDifference_soninCoupledNormalizedReplicaMoment_eq_quantum]
  exact quantumMasterEffectReplicaDifference_nonneg
    (HilbertSchmidt.isHilbertSchmidt_toOperatorRect
      (soninAllPrimeColumnKernel_isHSRect a.1 a.2)) k r

/-- The complete quantum difference law supplies every nonnegative Bernstein coefficient packet
required by the coupled-source collar route. -/
theorem soninAllPrimeCoupledRenyiReplicaMoment_hausdorffBernsteinNonnegative
    (a : SoninPositiveAperture) :
    HausdorffBernsteinNonnegative (soninCoupledNormalizedReplicaMoment a) :=
  hausdorffBernsteinNonnegative_of_momentDifferencesNonnegative
    (soninAllPrimeCoupledRenyiReplicaMoment_hausdorffMomentDifferencesNonnegative a)

end

end RHTower

namespace RHTower

/-- Dividing an entire moment sequence by one constant divides every scaled Hausdorff
difference by that constant; a vanishing constant degenerates both sides to zero. -/
theorem scaledHausdorffMomentDifference_div
    (R : ℝ) (m : ℕ → ℝ) (c : ℝ) (k r : ℕ) :
    scaledHausdorffMomentDifference R (fun j => m j / c) k r =
      scaledHausdorffMomentDifference R m k r / c := by
  induction r generalizing k with
  | zero => simp only [scaledHausdorffMomentDifference]
  | succ r ih =>
      rw [scaledHausdorffMomentDifference, scaledHausdorffMomentDifference,
        ih k, ih (k + 1)]
      ring

/-- **Ratio-normalized complete source law.**  After division by the zeroth coupled moment the
complete scaled hierarchy persists at the same aperture-independent radius. -/
theorem re_soninAllPrimeCoupledTraceMoment_div_zero_scaledHausdorffDifferencesNonnegative
    (a : SoninPositiveAperture) :
    ScaledHausdorffMomentDifferencesNonnegative soninAllPrimeColumnEffectRadius
      (fun j => (soninAllPrimeCoupledTraceMoment a j).re /
        (soninAllPrimeCoupledTraceMoment a 0).re) := by
  intro k r
  rw [scaledHausdorffMomentDifference_div]
  exact div_nonneg
    (re_soninAllPrimeCoupledTraceMoment_scaledHausdorffDifferencesNonnegative a k r)
    (soninAllPrimeCoupledTraceMoment_re_nonneg a 0)

/-- Complete scaled Hausdorff positivity is closed under pointwise limits of moment
sequences. -/
theorem scaledHausdorffMomentDifferencesNonnegative_of_tendsto
    {R : ℝ} {m : ℕ → ℕ → ℝ} {target : ℕ → ℝ}
    (hm : ∀ N, ScaledHausdorffMomentDifferencesNonnegative R (m N))
    (htendsto : ∀ k, Filter.Tendsto (fun N => m N k) Filter.atTop (nhds (target k))) :
    ScaledHausdorffMomentDifferencesNonnegative R target := by
  intro k r
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_scaledHausdorffMomentDifference_of_tendsto R
      (tendsto_pi_nhds.mpr htendsto) k r)
    (Filter.Eventually.of_forall fun N => hm N k r)

/-- **Aperture-schedule compatibility test.**  Every pointwise limit of ratio-normalized coupled
Sonin moment sequences obeys the complete scaled Hausdorff hierarchy at the aperture-independent
effect radius: proposed projective aperture schedules can only converge into this closed cone. -/
theorem scaledHausdorffMomentDifferencesNonnegative_of_soninCoupledRatio_tendsto
    {aperture : ℕ → SoninPositiveAperture} {target : ℕ → ℝ}
    (htendsto : ∀ k, Filter.Tendsto (fun N =>
        (soninAllPrimeCoupledTraceMoment (aperture N) k).re /
          (soninAllPrimeCoupledTraceMoment (aperture N) 0).re)
      Filter.atTop (nhds (target k))) :
    ScaledHausdorffMomentDifferencesNonnegative soninAllPrimeColumnEffectRadius target :=
  scaledHausdorffMomentDifferencesNonnegative_of_tendsto
    (fun N =>
      re_soninAllPrimeCoupledTraceMoment_div_zero_scaledHausdorffDifferencesNonnegative
        (aperture N))
    htendsto

end RHTower
