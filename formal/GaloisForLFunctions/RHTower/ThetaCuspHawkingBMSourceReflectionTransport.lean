import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralSourceReflection
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceHermitianCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedCurrentCutoff
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeField
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalModeAction

/-!
# Literal-source reflection through the constructed mixed response and physical action

The literal source theorem exchanges the two original metric branches. Here the
sum with four independent polarizations transports the whole raw Einstein source
and its nondegenerate amplitude domain. The actual switched mixed tensor, time
forcing, onset contacts, and full-gradient source obey the same branch exchange.

Reversing the three principal cusp powers transports their solved radial responses,
the original cutoff commutators, the full continued residual, its joint wave
response, and the actual volume-weighted projected Einstein action at a fixed
reader. Every physical frequency, cutoff and source onset remains unchanged.

This is the existing constructed mixed-stream response, not an identification of
all independent SS/SV/VV contributions in the fully corrected nonlinear action.
The physical reader at the reflected occurrence undergoes a half-unit spectral
shift and is provably unequal to the original reader. The remaining diagonal
action difference is exactly a change of reader. No finite-clock extinction or RH
is asserted, and no clock covariance or source-incidence hypothesis is supplied.
-/

open Complex
namespace RHTower.D4BMSourceReflectionTransport
open D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

private theorem center_reflect (q : XiZeroCopy) :
    center (xiZeroCopyReflectEquiv q) = -center q := by
  change 1-(q.1:ℂ)-1/2 = -((q.1:ℂ)-1/2)
  ring

private theorem center_nonreal (q : XiZeroCopy) : (center q).im ≠ 0 := by
  simpa [D4BMGlobalAngularResponse.center] using xi_divisor_support_im_ne_zero q.1

/-- Functional-equation reflection preserves the complete literal scalar field. -/
theorem scalar_reflect (q : XiZeroCopy) :
    D4BMLiteralCusp.scalar (center (xiZeroCopyReflectEquiv q)) = D4BMLiteralCusp.scalar (center q) := by
  rw [center_reflect]
  exact D4BMLiteralCusp.scalar_neg _ (center_nonreal q)

/-- The actual area-form rotated gradient obeys the same source reflection. -/
theorem vector_reflect (q : XiZeroCopy) :
    D4BMLiteralCusp.vector (center (xiZeroCopyReflectEquiv q)) = D4BMLiteralCusp.vector (center q) := by
  unfold D4BMLiteralCusp.vector
  rw [scalar_reflect]

/-- The literal fundamental plus branch exchanges with the minus branch without changing its clock. -/
theorem plus_reflect (q : XiZeroCopy) (aS aV : ℂ) :
    D4BMLiteralCusp.perturbation
      (d4BMCausalQNMPlus 0 (D4BMLiteralCusp.radialMomentum (center (xiZeroCopyReflectEquiv q))))
      (center (xiZeroCopyReflectEquiv q)) aS aV =
    D4BMLiteralCusp.perturbation
      (d4BMCausalQNMMinus 0 (D4BMLiteralCusp.radialMomentum (center q))) (center q) aS aV := by
  unfold D4BMLiteralCusp.perturbation
  rw [scalar_reflect, vector_reflect, center_reflect]
  simp [D4BMLiteralCusp.scalarQ, D4BMLiteralCusp.radialMomentum,
    d4BMCausalQNMPlus, d4BMCausalQNMMinus]

/-- The literal fundamental minus branch exchanges with the plus branch at the original clock. -/
theorem minus_reflect (q : XiZeroCopy) (aS aV : ℂ) :
    D4BMLiteralCusp.perturbation
      (d4BMCausalQNMMinus 0 (D4BMLiteralCusp.radialMomentum (center (xiZeroCopyReflectEquiv q))))
      (center (xiZeroCopyReflectEquiv q)) aS aV =
    D4BMLiteralCusp.perturbation
      (d4BMCausalQNMPlus 0 (D4BMLiteralCusp.radialMomentum (center q))) (center q) aS aV := by
  unfold D4BMLiteralCusp.perturbation
  rw [scalar_reflect, vector_reflect, center_reflect]
  simp [D4BMLiteralCusp.scalarQ, D4BMLiteralCusp.radialMomentum,
    d4BMCausalQNMPlus, d4BMCausalQNMMinus]

/-- The two literal branches retain four independent scalar/vector amplitudes. -/
def twoBranchField (q : XiZeroCopy) (aS aV bS bV : ℂ) : D4BMActualMetricSource.MetricField :=
  D4BMLiteralCusp.perturbation
      (d4BMCausalQNMPlus 0 (D4BMLiteralCusp.radialMomentum (center q))) (center q) aS aV +
    D4BMLiteralCusp.perturbation
      (d4BMCausalQNMMinus 0 (D4BMLiteralCusp.radialMomentum (center q))) (center q) bS bV

/-- Reflection exchanges the actual branch fields and their independent polarizations. -/
theorem twoBranchField_reflect (q : XiZeroCopy) (aS aV bS bV : ℂ) :
    twoBranchField (xiZeroCopyReflectEquiv q) aS aV bS bV = twoBranchField q bS bV aS aV := by
  unfold twoBranchField
  rw [plus_reflect, minus_reflect, add_comm]

/-- Reflection preserves the full nonlinear Einstein source after exchanging branch amplitudes. -/
theorem full_source_reflect (q : XiZeroCopy) (aS aV bS bV : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) (ε : ℂ) :
    D4BMActualMetricSource.source p (twoBranchField (xiZeroCopyReflectEquiv q) aS aV bS bV) i j ε =
      D4BMActualMetricSource.source p (twoBranchField q bS bV aS aV) i j ε := by
  rw [twoBranchField_reflect]

/-- The original nondegenerate metric-amplitude domain is preserved by the same reflection. -/
theorem amplitudeDomain_reflect (q : XiZeroCopy) (aS aV bS bV : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    D4BMActualMetricSource.amplitudeDomain p (twoBranchField (xiZeroCopyReflectEquiv q) aS aV bS bV) =
      D4BMActualMetricSource.amplitudeDomain p (twoBranchField q bS bV aS aV) := by
  rw [twoBranchField_reflect]

open D4BMModularCore

/-- Reflection exchanges the original time rates without translating or rescaling time. -/
theorem physicalRate_reflect (q : XiZeroCopy) (branch : Bool) :
    physicalRate (xiZeroCopyReflectEquiv q) branch = physicalRate q (!branch) :=
  D4BMLiteralCusp.physicalRate_reflect q branch

private theorem original_scalar_reflect (q : XiZeroCopy) :
    D4BMGlobalAngularResponse.scalar (center (xiZeroCopyReflectEquiv q)) =
      D4BMGlobalAngularResponse.scalar (center q) := scalar_reflect q

/-- The complete quadratic angular source is invariant before any projection. -/
theorem square_reflect (q : XiZeroCopy) :
    fullSquarePotential (xiZeroCopyReflectEquiv q) = fullSquarePotential q := by
  unfold fullSquarePotential
  rw [original_scalar_reflect]

/-- Reflection preserves the actual complex gradient energy, including both derivatives. -/
theorem gradientEnergy_reflect (q : XiZeroCopy) :
    fullGradientEnergy (xiZeroCopyReflectEquiv q) = fullGradientEnergy q := by
  unfold fullGradientEnergy
  rw [original_scalar_reflect]

/-- The original differentiated square source obeys the same field identity. -/
theorem squareCovector_reflect (q : XiZeroCopy) :
    fullSquareCovector (xiZeroCopyReflectEquiv q) = fullSquareCovector q := by
  unfold fullSquareCovector
  rw [original_scalar_reflect]

/-- The complete gradient covector retains its physical branch parameter under reflection. -/
theorem gradientCovector_reflect (q : XiZeroCopy) (branch : Bool) :
    fullGradientCovector (xiZeroCopyReflectEquiv q) branch = fullGradientCovector q (!branch) := by
  unfold fullGradientCovector
  rw [original_scalar_reflect, physicalRate_reflect]

/-- The full original mixed current exchanges branches before differentiating its onset. -/
theorem orbitCurrent_reflect (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (z : D4BMHorizon.Point) (k : Fin 2) :
    orbitCurrent (xiZeroCopyReflectEquiv q) branch a z k = orbitCurrent q (!branch) a z k := by
  unfold orbitCurrent
  rw [physicalRate_reflect, squareCovector_reflect, gradientCovector_reflect]

/-- The source-predeclared ingoing onset is unchanged by reflection of the literal current. -/
theorem switchedCurrent_reflect (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (z : D4BMHorizon.Point) (k : Fin 2) :
    switchedOrbitCurrent (xiZeroCopyReflectEquiv q) branch a z k =
      switchedOrbitCurrent q (!branch) a z k := by
  unfold switchedOrbitCurrent
  rw [orbitCurrent_reflect]

/-- Every original switched mixed-source tensor component, including onset derivatives, reflects. -/
theorem switchedTensor_reflect (q : XiZeroCopy) (branch : Bool) (a : ℂ) (x : Fin 4 → ℝ) :
    switchedCurrentSource (xiZeroCopyReflectEquiv q) branch a x =
      switchedCurrentSource q (!branch) a x := by
  unfold switchedCurrentSource
  simp only [switchedCurrent_reflect]

/-- The source-contact tensor itself is transported rather than discarded. -/
theorem onsetTensor_reflect (q : XiZeroCopy) (branch : Bool) (a : ℂ) (x : Fin 4 → ℝ) :
    currentOnsetTensor (xiZeroCopyReflectEquiv q) branch a x = currentOnsetTensor q (!branch) a x := by
  unfold currentOnsetTensor
  simp only [orbitCurrent_reflect]

/-- The original causal scalar source reflects with its full gradient and fixed onset retained. -/
theorem timeOriginalForcing_reflect (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    D4BMJointSource.timeOriginalForcing (xiZeroCopyReflectEquiv q) branch a =
      D4BMJointSource.timeOriginalForcing q (!branch) a := by
  unfold D4BMJointSource.timeOriginalForcing
  rw [physicalRate_reflect, square_reflect, gradientEnergy_reflect]

/-- The explicit original lift is reflected at the same static and ingoing times. -/
theorem timeLiftField_reflect (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    D4BMJointSource.timeLiftField (xiZeroCopyReflectEquiv q) branch a =
      D4BMJointSource.timeLiftField q (!branch) a := by
  unfold D4BMJointSource.timeLiftField
  rw [physicalRate_reflect, square_reflect]

/-- Reflecting the physical reader shifts its full scalar parameter by one half. -/
theorem physical_reader_reflect_half_shift (q : XiZeroCopy) :
    D4BMLiteralCusp.scalar (D4BMJointSource.physicalAngularParameter (xiZeroCopyReflectEquiv q)) =
      D4BMLiteralCusp.scalar (D4BMJointSource.physicalAngularParameter q+1/2) := by
  have hp : D4BMJointSource.physicalAngularParameter (xiZeroCopyReflectEquiv q) =
      -(D4BMJointSource.physicalAngularParameter q+1/2) := by
    rw [D4BMJointSource.physicalAngularParameter_eq, D4BMJointSource.physicalAngularParameter_eq]
    change ((1-(q.1:ℂ))-1)/2 = -(((q.1:ℂ)-1)/2+1/2)
    ring
  rw [hp]
  apply D4BMLiteralCusp.scalar_neg
  simpa [D4BMJointSource.physicalAngularParameter_eq] using xi_divisor_support_im_ne_zero q.1


open D4BMJointSource D4BMJointWave D4BMPhysicalModeAction
open GaloisForLFunctions.HTGeometry
open MeasureTheory Set

private theorem lambda_fe (s : ℂ) (hs : s.im ≠ 0) :
    reflectedCompletedLambda (1-s) = reflectedCompletedLambda s := by
  have he (z : ℂ) (hz : z.im ≠ 0) : reflectedCompletedLambda z = completedRiemannZeta z := by
    have h0 : z ≠ 0 := by intro h; exact hz (by rw [h]; rfl)
    rw [reflectedCompletedLambda, riemannZeta_def_of_ne_zero h0]
    exact mul_div_cancel₀ _ (gammaR_ne_zero_of_im_ne hz)
  rw [he s hs, he (1-s) (by simpa using neg_ne_zero.mpr hs), completedRiemannZeta_one_sub]

/-- Both original source cusp coefficients exchange without changing their normalization. -/
theorem weylCoefficient_reflect (q : XiZeroCopy) (branch : Bool) :
    weylCoefficient (xiZeroCopyReflectEquiv q) branch = weylCoefficient q (!branch) := by
  unfold weylCoefficient
  rw [center_reflect]
  have hu := center_nonreal q
  have h2 : (2*center q).im ≠ 0 := by simpa using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hu
  cases branch
  · change reflectedCompletedLambda (2*(-center q)) = reflectedCompletedLambda (1+2*center q)
    rw [show 2*(-center q)=1-(1+2*center q) by ring]
    exact lambda_fe _ (by simpa using h2)
  · change reflectedCompletedLambda (1+2*(-center q)) = reflectedCompletedLambda (2*center q)
    rw [show 1+2*(-center q)=1-(2*center q) by ring]
    exact lambda_fe _ h2

/-- Reflection reverses the three actual principal exponents, fixing their middle cross term. -/
theorem principalExponent_reflect (q : XiZeroCopy) (i : Fin 3) :
    principalExponent (xiZeroCopyReflectEquiv q) i = principalExponent q i.rev := by
  fin_cases i <;> simp [principalExponent, Fin.rev]
  all_goals ring

/-- Every principal amplitude is transported, including the independent Weyl cross product. -/
theorem principalAmplitude_reflect (q : XiZeroCopy) (i : Fin 3) :
    principalAmplitude (xiZeroCopyReflectEquiv q) i = principalAmplitude q i.rev := by
  fin_cases i <;> simp [principalAmplitude, weylCoefficient_reflect, Fin.rev, mul_comm]

/-- The source-derived principal gradient coefficient exchanges with its own branch and exponent. -/
theorem principalGradient_reflect (q : XiZeroCopy) (branch : Bool) (i : Fin 3) :
    principalGradient (xiZeroCopyReflectEquiv q) branch i = principalGradient q (!branch) i.rev := by
  unfold principalGradient
  rw [principalExponent_reflect, physicalRate_reflect, principalAmplitude_reflect]

/-- Each principal radial frequency follows its actual exponent, with no clock correction. -/
theorem principalFrequency_reflect (q : XiZeroCopy) (i : Fin 3) :
    principalFrequency (xiZeroCopyReflectEquiv q) i = principalFrequency q i.rev := by
  unfold principalFrequency
  rw [principalExponent_reflect]

private theorem principal_reflect (q : XiZeroCopy) :
    principal (center (xiZeroCopyReflectEquiv q)) = principal (center q) := by
  rw [center_reflect]
  funext z
  have hs := d4BMCompletedEisensteinScalarCuspLeg_neg (center q) (center_nonreal q) (z 0) (z 1)
  have ht : d4BMCompletedEisensteinCuspTailPart .scalar (-center q) (z 0) (z 1) =
      d4BMCompletedEisensteinCuspTailPart .scalar (center q) (z 0) (z 1) := by
    simp only [d4BMCompletedEisensteinCuspTailPart, d4BMCompletedEisensteinFullSignedZeroWord_neg]
  unfold d4BMCompletedEisensteinCuspLeg at hs
  rw [ht] at hs
  exact add_right_cancel hs

/-- The original cutoff subtraction respects reflection without removing any native remainder. -/
theorem squareResidual_reflect (q : XiZeroCopy) :
    squareResidual (xiZeroCopyReflectEquiv q) = squareResidual q := by
  unfold squareResidual principalSquare
  rw [square_reflect, principal_reflect]

/-- The entire solved principal response and its full-square subtraction exchange exactly. -/
theorem continuedPrincipalDifference_reflect (q : XiZeroCopy) (branch : Bool)
    (w a : ℂ) (i : Fin 3) :
    continuedPrincipalDifference (xiZeroCopyReflectEquiv q) branch w a i =
      continuedPrincipalDifference q (!branch) w a i.rev := by
  unfold continuedPrincipalDifference
  rw [principalFrequency_reflect, physicalRate_reflect, principalAmplitude_reflect, principalGradient_reflect]

/-- Every cutoff commutator keeps its solved radial multiplier. -/
theorem continuedCutoffRadialCoefficient_reflect (q : XiZeroCopy) (branch : Bool)
    (w a : ℂ) (i : Fin 3) :
    continuedCutoffRadialCoefficient (xiZeroCopyReflectEquiv q) branch w a i =
      continuedCutoffRadialCoefficient q (!branch) w a i.rev := by
  unfold continuedCutoffRadialCoefficient
  rw [continuedPrincipalDifference_reflect]

private theorem sum_rev (f : Fin 3 → ℂ) : (∑ i : Fin 3, f i.rev) = ∑ i : Fin 3, f i := by
  exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin 3)) f

/-- Reflection preserves the assembled continued source with all three solved cusp commutators. -/
theorem continuedCuspResidualForcing_reflect (q : XiZeroCopy) (branch : Bool) (w a : ℂ) :
    continuedCuspResidualForcing (xiZeroCopyReflectEquiv q) branch w a =
      continuedCuspResidualForcing q (!branch) w a := by
  funext p
  unfold continuedCuspResidualForcing
  simp only [physicalRate_reflect, squareResidual_reflect, continuedCutoffRadialCoefficient_reflect,
    principalExponent_reflect]
  exact congrArg (fun v : ℂ =>
    reducedCoefficient (physicalRate q (!branch)) w a (continuedOnset (physicalRate q (!branch)) w) p.1 *
      squareResidual q (coordinates p.2) + v)
    (sum_rev (fun i => continuedCutoffRadialCoefficient q (!branch) w a i p.1 *
      cutoffCommutator (principalExponent q i) (coordinates p.2)))

/-- The explicit response carries its native lift and every solved principal correction together. -/
theorem continuedExplicitField_reflect (q : XiZeroCopy) (branch : Bool) (w a : ℂ) :
    continuedExplicitField (xiZeroCopyReflectEquiv q) branch w a =
      continuedExplicitField q (!branch) w a := by
  funext t z
  unfold continuedExplicitField
  simp only [physicalRate_reflect, square_reflect, continuedPrincipalDifference_reflect,
    principalExponent_reflect]
  exact congrArg (fun v : ℂ =>
    radialLift (physicalRate q (!branch)) w a (continuedOnset (physicalRate q (!branch)) w) t *
      fullSquarePotential q z + v)
    (sum_rev (fun i => continuedPrincipalDifference q (!branch) w a i t *
      cutoffPower (principalExponent q i) z))

/-- The admitted joint forcing class is equal before the actual wave inverse is applied. -/
theorem continuedCuspResidualL2_reflect (q : XiZeroCopy) (branch : Bool) (a w : ℂ) :
    continuedCuspResidualL2 (xiZeroCopyReflectEquiv q) branch a w =
      continuedCuspResidualL2 q (!branch) a w := by
  unfold continuedCuspResidualL2
  simp only [continuedCuspResidualForcing_reflect]

/-- The complete angular source projection reflects at each unchanged reader parameter. -/
theorem continuedAngularSourceProjection_reflect (q : XiZeroCopy) (branch : Bool) (u a w : ℂ) :
    continuedAngularSourceProjection (xiZeroCopyReflectEquiv q) branch u a w =
      continuedAngularSourceProjection q (!branch) u a w := by
  unfold continuedAngularSourceProjection
  simp only [continuedCuspResidualForcing_reflect]

/-- The actual weighted physical response reflects with its reader index held fixed. -/
theorem physicalCuspResponse_reflect (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    physicalCuspResponse (xiZeroCopyReflectEquiv q) r branch w a hw hd hwi hwr =
      physicalCuspResponse q r (!branch) w a hw hd hwi hwr := by
  have he : (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ) *
      jointEmbedding (jointWaveResponse w hw
        (continuedCuspResidualL2 (xiZeroCopyReflectEquiv q) branch a w)) p) =
      (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ) *
        jointEmbedding (jointWaveResponse w hw (continuedCuspResidualL2 q (!branch) a w)) p) := by
    rw [continuedCuspResidualL2_reflect]
  unfold physicalCuspResponse
  exact congrArg (fun v : SpatialSpace => physicalJointProjection r v)
    (MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun he)))

/-- The continuous physical representative inherits source reflection. -/
theorem physicalCuspProfile_reflect (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    physicalCuspProfile (xiZeroCopyReflectEquiv q) r branch w a hw hd hwi hwr =
      physicalCuspProfile q r (!branch) w a hw hd hwi hwr := by
  unfold physicalCuspProfile
  simp only [physicalCuspResponse_reflect]

/-- The full physical metric stream uses the same reader and the same time coordinate. -/
theorem physicalProjectedStream_reflect (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    physicalProjectedStream (xiZeroCopyReflectEquiv q) r branch w a hw hd hwi hwr =
      physicalProjectedStream q r (!branch) w a hw hd hwi hwr := by
  unfold physicalProjectedStream
  rw [physicalCuspProfile_reflect]

/-- Source reflection reaches the actual volume-weighted Einstein action against the unchanged left mode. -/
theorem physicalProjectedModeAction_reflect (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (outer : Bool) (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    physicalProjectedModeAction (xiZeroCopyReflectEquiv q) r branch w a hw hd hwi hwr outer t z hz =
      physicalProjectedModeAction q r (!branch) w a hw hd hwi hwr outer t z hz := by
  unfold physicalProjectedModeAction
  rw [physicalProjectedStream_reflect]


/-- The source-contact contribution to the physical action is transported with the bulk forcing. -/
theorem physicalModeSourceContact_reflect (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (outer : Bool) :
    physicalModeSourceContact (xiZeroCopyReflectEquiv q) r branch w a outer =
      physicalModeSourceContact q r (!branch) w a outer := by
  unfold physicalModeSourceContact
  rw [continuedAngularSourceProjection_reflect]

/-- In the actual physical action, diagonal reflection leaves an exact change of reader.
This theorem asserts no cancellation of that remaining quantity. -/
theorem physicalProjectedModeAction_diagonal_defect (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (outer : Bool) (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    physicalProjectedModeAction (xiZeroCopyReflectEquiv q) (xiZeroCopyReflectEquiv q)
        branch w a hw hd hwi hwr outer t z hz -
      physicalProjectedModeAction q q (!branch) w a hw hd hwi hwr outer t z hz =
    physicalProjectedModeAction q (xiZeroCopyReflectEquiv q) (!branch) w a hw hd hwi hwr outer t z hz -
      physicalProjectedModeAction q q (!branch) w a hw hd hwi hwr outer t z hz := by
  rw [physicalProjectedModeAction_reflect]


/-- The two physical reader eigenvalues differ by half the original centered source parameter. -/
theorem physical_reader_eigenvalue_defect (q : XiZeroCopy) :
    D4BMLiteralCusp.scalarQ (physicalAngularParameter q) -
      D4BMLiteralCusp.scalarQ (physicalAngularParameter (xiZeroCopyReflectEquiv q)) = center q/2 := by
  rw [D4BMLiteralCusp.scalarQ, D4BMLiteralCusp.scalarQ,
    physicalAngularParameter_eq, physicalAngularParameter_eq]
  change (1/4-(((q.1:ℂ)-1)/2)^(2 : ℕ))-(1/4-(((1-(q.1:ℂ))-1)/2)^(2 : ℕ)) = ((q.1:ℂ)-1/2)/2
  ring

/-- Individual physical readers are unequal at every actual Xi occurrence, including on the line.
The surviving source law is fixed-reader action transport and the exact half-shift, not reader equality. -/
theorem physical_reader_reflect_ne (q : XiZeroCopy) :
    D4BMLiteralCusp.scalar (physicalAngularParameter (xiZeroCopyReflectEquiv q)) ≠
      D4BMLiteralCusp.scalar (physicalAngularParameter q) := by
  intro he
  obtain ⟨z, hz⟩ := D4BMSourceHermitianCurrent.exists_reader_ne_zero q
  have h1 := D4BMLiteralCusp.scalar_equation (physicalAngularParameter (xiZeroCopyReflectEquiv q)) z.val z.property
  have h2 := D4BMLiteralCusp.scalar_equation (physicalAngularParameter q) z.val z.property
  rw [he] at h1
  have hzero : (center q/2) * D4BMLiteralCusp.scalar (physicalAngularParameter q) z.val = 0 := by
    rw [← physical_reader_eigenvalue_defect]
    linear_combination h2 - h1
  have hu : center q ≠ 0 := by
    intro h
    exact center_nonreal q (by rw [h]; rfl)
  exact (mul_ne_zero (div_ne_zero hu (by norm_num)) hz) hzero

end
end RHTower.D4BMSourceReflectionTransport
