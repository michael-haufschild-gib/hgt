import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCovector
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralPeierlsStreamBilinear
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralSourceReflection

/-!
# Literal-source reflection of the completed angular forcing and weak response

The functional-equation reflection exchanges the two literal Weyl channels.  This
file proves that the exchange survives the complete cusp subtraction, the admitted
modular forcing vector, and the unique finite-energy weak solution.  Thus this is
source-to-solution covariance, rather than a symmetry postulated for a receiver.

It does not identify this angular response with a causal Peierls action or supply
the source-fixed Peierls incidence needed by the RBH/PW route.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff ENNReal SchwartzMap
namespace RHTower.D4BMFullAngularSourceReflection
open D4BMGlobalAngularResponse D4BMQuadraticMixedSource D4BMModularCore D4BMHorizon
noncomputable section

private theorem center_reflect (q : XiZeroCopy) :
    center (xiZeroCopyReflectEquiv q) = -center q := by
  change 1 - (q.1 : ℂ) - 1 / 2 = -((q.1 : ℂ) - 1 / 2)
  ring

private theorem coordinate_reflect (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := by
  rfl

private theorem center_nonreal (q : XiZeroCopy) :
    (D4BMGlobalAngularResponse.center q).im ≠ 0 := by
  simpa [D4BMGlobalAngularResponse.center] using xi_divisor_support_im_ne_zero q.1

private theorem lambda_eq_completed_nonreal {s : ℂ} (hs : s.im ≠ 0) :
    reflectedCompletedLambda s = completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    exact hs (by rw [h]; rfl)
  rw [reflectedCompletedLambda, riemannZeta_def_of_ne_zero hs0]
  exact mul_div_cancel₀ _ (gammaR_ne_zero_of_im_ne hs)

private theorem lambda_fe (s : ℂ) (hs : s.im ≠ 0) :
    reflectedCompletedLambda (1 - s) = reflectedCompletedLambda s := by
  rw [lambda_eq_completed_nonreal (by simpa using neg_ne_zero.mpr hs),
    lambda_eq_completed_nonreal hs, completedRiemannZeta_one_sub]

/-- Functional-equation reflection exchanges the two physical angular parameters. -/
theorem parameter_reflect (q : XiZeroCopy) (branch : Bool) :
    parameter (xiZeroCopyReflectEquiv q) branch = parameter q (!branch) := by
  cases branch
  · change resolventParameter (-(1 - (q.1 : ℂ)) - 1) =
      resolventParameter ((q.1 : ℂ) - 2)
    congr 1
    ring
  · change resolventParameter ((1 - (q.1 : ℂ)) - 2) =
      resolventParameter (-(q.1 : ℂ) - 1)
    congr 1
    ring

private theorem coefficient_reflect_true (q : XiZeroCopy) :
    d4BMCompletedEisensteinCuspConstantCoefficient
        (center (xiZeroCopyReflectEquiv q)) true =
      d4BMCompletedEisensteinCuspConstantCoefficient (center q) false := by
  rw [center_reflect]
  change reflectedCompletedLambda (1 + 2 * (-center q)) =
    reflectedCompletedLambda (2 * center q)
  rw [show 1 + 2 * (-center q) = 1 - 2 * center q by ring]
  apply lambda_fe
  simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (center_nonreal q)

private theorem coefficient_reflect_false (q : XiZeroCopy) :
    d4BMCompletedEisensteinCuspConstantCoefficient
        (center (xiZeroCopyReflectEquiv q)) false =
      d4BMCompletedEisensteinCuspConstantCoefficient (center q) true := by
  rw [center_reflect]
  change reflectedCompletedLambda (2 * (-center q)) =
    reflectedCompletedLambda (1 + 2 * center q)
  rw [show 2 * (-center q) = 1 - (1 + 2 * center q) by ring]
  apply lambda_fe
  simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (center_nonreal q)

/-- Reflection carries the exact three-power cusp particular response to its other branch. -/
theorem cuspResponse_reflect (q : XiZeroCopy) (branch : Bool) :
    cuspResponse (xiZeroCopyReflectEquiv q) branch = cuspResponse q (!branch) := by
  unfold cuspResponse
  rw [parameter_reflect, coefficient_reflect_true, coefficient_reflect_false,
    coordinate_reflect]
  funext z
  have houter : (2 : ℂ) * (1 - (q.1 : ℂ)) = 2 - 2 * (q.1 : ℂ) := by ring
  have hinner : 2 - (2 - 2 * (q.1 : ℂ)) = 2 * (q.1 : ℂ) := by ring
  simp only [cuspPowerResponse, powerResponse]
  rw [houter, hinner]
  ring

/-- Reflection retains the full cutoff response, including its transition-zone derivatives. -/
theorem cutoffResponse_reflect (q : XiZeroCopy) (branch : Bool) :
    cutoffResponse (xiZeroCopyReflectEquiv q) branch = cutoffResponse q (!branch) := by
  unfold cutoffResponse
  rw [cuspResponse_reflect]

private theorem scalar_reflect (q : XiZeroCopy) :
    scalar (center (xiZeroCopyReflectEquiv q)) = scalar (center q) := by
  rw [center_reflect]
  funext z
  exact d4BMCompletedEisensteinScalarCuspLeg_neg (center q) (center_nonreal q) (z 0) (z 1)

/-- The literal full cusp-subtracted forcing itself is branch-equivariant. -/
theorem forcing_reflect (q : XiZeroCopy) (branch : Bool) :
    forcing (xiZeroCopyReflectEquiv q) branch = forcing q (!branch) := by
  unfold forcing
  rw [parameter_reflect, scalar_reflect, cutoffResponse_reflect]

/-- The admitted modular Hilbert-space forcing vector retains literal source reflection. -/
theorem forcingVector_reflect (q : XiZeroCopy) (branch : Bool) :
    forcingVector (xiZeroCopyReflectEquiv q) branch = forcingVector q (!branch) := by
  apply Lp.ext
  filter_upwards [forcingVector_coe (xiZeroCopyReflectEquiv q) branch,
    forcingVector_coe q (!branch)] with z hleft hright
  rw [hleft, hright]
  exact congrFun (forcing_reflect q branch) (coordinates z)

/-- Uniqueness of the constructed nonreal resolvent transports the actual weak response. -/
theorem weakResponse_reflect (q : XiZeroCopy) (branch : Bool) :
    weakResponse (xiZeroCopyReflectEquiv q) branch = weakResponse q (!branch) := by
  symm
  apply full_forcing_weak_response_unique (xiZeroCopyReflectEquiv q) branch _ _ ?_
    (weakResponse_spec (xiZeroCopyReflectEquiv q) branch)
  intro v
  rw [parameter_reflect, forcingVector_reflect]
  exact weakResponse_spec q (!branch) v

/-- Reflection survives the globally glued cusp cutoff, including all cell seams. -/
theorem globalCuspCutoff_reflect (q : XiZeroCopy) (branch : Bool) :
    globalCuspCutoff (xiZeroCopyReflectEquiv q) branch = globalCuspCutoff q (!branch) := by
  apply congrArg cellGermExtension
  funext z
  exact congrFun (cutoffResponse_reflect q branch) (coordinates z)

private theorem chartSmooth_eq_of_ae_eq {f g : UpperHalfPlane → ℂ}
    (hf : ChartSmooth f) (hg : ChartSmooth g) (he : f =ᵐ[(volume : Measure UpperHalfPlane)] g) :
    f = g := by
  have hm : ∀ᵐ z ∂Measure.map UpperHalfPlane.coe (volume : Measure UpperHalfPlane),
      f (ofComplex z) = g (ofComplex z) :=
    UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mpr (by
      filter_upwards [he] with z hz
      simpa only [ofComplex_apply] using hz)
  rw [map_volume_chart_eq] at hm
  have hd : Measurable (fun z : ℂ => (chartDensity z : ℝ≥0∞)) := by
    unfold chartDensity
    fun_prop
  have hh := (ae_withDensity_iff hd).mp hm
  have hae : (fun z : ℂ => f (ofComplex z)) =ᵐ[volume.restrict {z : ℂ | 0 < z.im}]
      (fun z : ℂ => g (ofComplex z)) := by
    filter_upwards [hh, ae_restrict_mem isOpen_upperHalfPlaneSet.measurableSet] with z hz hy
    exact hz (by simp [chartDensity, ne_of_gt hy])
  have hc (a : UpperHalfPlane → ℂ) (ha : ChartSmooth a) :
      ContinuousOn (fun z : ℂ => a (ofComplex z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hh := ha (ofComplex z)
    rw [ofComplex_apply_of_im_pos hz] at hh
    exact hh.continuousAt.continuousWithinAt
  have hp := Measure.eqOn_open_of_ae_eq hae isOpen_upperHalfPlaneSet (hc f hf) (hc g hg)
  funext z
  simpa only [ofComplex_apply] using hp z.im_pos

/-- The smooth representative is canonical under literal source reflection. -/
theorem globalResponse_reflect (q : XiZeroCopy) (branch : Bool) :
    globalResponse (xiZeroCopyReflectEquiv q) branch = globalResponse q (!branch) := by
  apply chartSmooth_eq_of_ae_eq (globalResponse_smooth (xiZeroCopyReflectEquiv q) branch)
    (globalResponse_smooth q (!branch))
  filter_upwards [globalResponse_ae_lift (xiZeroCopyReflectEquiv q) branch,
    globalResponse_ae_lift q (!branch)] with z hleft hright
  rw [hleft, hright, weakResponse_reflect]

/-- The complete literal angular solution is pointwise branch-equivariant. -/
theorem fullAngular_reflect (q : XiZeroCopy) (branch : Bool) :
    fullAngular (xiZeroCopyReflectEquiv q) branch = fullAngular q (!branch) := by
  unfold fullAngular
  rw [globalCuspCutoff_reflect, globalResponse_reflect]

private theorem physicalRate_reflect (q : XiZeroCopy) (branch : Bool) :
    physicalRate (xiZeroCopyReflectEquiv q) branch = physicalRate q (!branch) :=
  D4BMLiteralCusp.physicalRate_reflect q branch

/-- The original-coordinate full angular field inherits pointwise source reflection. -/
theorem fullAngularField_reflect (q : XiZeroCopy) (branch : Bool) :
    fullAngularField (xiZeroCopyReflectEquiv q) branch = fullAngularField q (!branch) := by
  funext z
  exact congrFun (fullAngular_reflect q branch) (ofComplex (angularCoordinates.symm z))

/-- The complete coexact response covector is branch-equivariant. -/
theorem fullAngularCovector_reflect (q : XiZeroCopy) (branch : Bool) :
    fullAngularCovector (xiZeroCopyReflectEquiv q) branch =
      fullAngularCovector q (!branch) := by
  unfold fullAngularCovector
  rw [fullAngularField_reflect]

/-- The retained quadratic covector is fixed by functional-equation reflection. -/
theorem fullSquareCovector_reflect (q : XiZeroCopy) :
    fullSquareCovector (xiZeroCopyReflectEquiv q) = fullSquareCovector q := by
  unfold fullSquareCovector
  rw [scalar_reflect]

private theorem fullSquarePotential_reflect (q : XiZeroCopy) :
    fullSquarePotential (xiZeroCopyReflectEquiv q) = fullSquarePotential q := by
  unfold fullSquarePotential
  rw [scalar_reflect]

/-- The two-derivative scalar action used by the literal cyclic cap.  It is
defined here so reflection covariance remains independently source-checkable while
the canonical cap-action artifact is unavailable. -/
def literalCapScalarAction (S : Point → ℂ) (z : Point) : ℂ :=
  (z 1 : ℂ)^2 *
    (coordDeriv 0 (coordDeriv 0 S) z + coordDeriv 1 (coordDeriv 1 S) z)

/-- The complete physical cap action of the literal cyclic Peierls vertex is
functional-equation covariant.  This retains the full response, the native square
term, and its forced physical coefficient; it is the cap-side input to the remaining
causal left-reader transport. -/
theorem literalCyclicCapAction_reflect (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    literalCapScalarAction (fullAngularField (xiZeroCopyReflectEquiv q) branch)
        ![X, Real.exp k] -
      (physicalRate (xiZeroCopyReflectEquiv q) branch *
          (physicalRate (xiZeroCopyReflectEquiv q) branch - 1) / 4) *
        literalCapScalarAction (fullSquarePotential (xiZeroCopyReflectEquiv q))
          ![X, Real.exp k] =
      literalCapScalarAction (fullAngularField q (!branch)) ![X, Real.exp k] -
        (physicalRate q (!branch) * (physicalRate q (!branch) - 1) / 4) *
          literalCapScalarAction (fullSquarePotential q) ![X, Real.exp k] := by
  rw [fullAngularField_reflect, physicalRate_reflect, fullSquarePotential_reflect]

/-- The literal two-leg forced stream metric transports across functional-equation reflection.
It retains the exact full/square coefficient and has not imposed a causal boundary condition. -/
theorem forcedMetricBilinear_reflect (q : XiZeroCopy) (branch : Bool) (a d : ℂ)
    (x : Fin 4 → ℝ) :
    D4BMLiteralPeierlsStream.forcedMetricBilinear (xiZeroCopyReflectEquiv q) branch a d x =
      D4BMLiteralPeierlsStream.forcedMetricBilinear q (!branch) a d x := by
  unfold D4BMLiteralPeierlsStream.forcedMetricBilinear
  rw [physicalRate_reflect, fullAngularCovector_reflect, fullSquareCovector_reflect]

end
end RHTower.D4BMFullAngularSourceReflection
