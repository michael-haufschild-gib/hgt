import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCovector
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleReconstruction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceRadialReciprocity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralPeierlsStreamBilinear
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralSourceReflection
import GaloisForLFunctions.RHTower.DeningerDivisorSchwarzMonodromy

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
open D4BMFullAngularCircle D4BMFullAngularReconstruction D4BMFullSourceReciprocity
open D4BMJointSource
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

/-- The literal full-circle angular mean is branch-equivariant.  This is the
source-to-solution statement lifted through the actual circular average, not a
postulated symmetry of a causal kernel. -/
theorem angularMean_reflect (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) :
    angularMean (xiZeroCopyReflectEquiv q) branch d x k =
      angularMean q (!branch) d x k := by
  change D4BMNativeCircle.average
      (fun theta => fullAngularField (xiZeroCopyReflectEquiv q) branch
        (D4BMNativeCircle.logCircle d theta x k)) =
    D4BMNativeCircle.average
      (fun theta => fullAngularField q (!branch)
        (D4BMNativeCircle.logCircle d theta x k))
  congr 1
  funext theta
  rw [fullAngularField_reflect]

/-- The literal full direct-minus-image circle kernel transports under
functional-equation reflection while exchanging its physical branch. -/
theorem angularDirichletKernel_reflect (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) :
    angularDirichletKernel (xiZeroCopyReflectEquiv q) branch h x y X k =
      angularDirichletKernel q (!branch) h x y X k := by
  simp only [angularDirichletKernel, angularMean_reflect]

/-- Two source events coupled through the literal full direct-minus-image
circle kernel.  This is the unintegrated CTP density whose two orderings form
the cross-branch Peierls numerator. -/
def fullCircleSourcePairDensity (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ)
    (z : D4BMFullSourceReciprocity.Event × D4BMFullSourceReciprocity.Event) : ℂ :=
  timeReducedCoefficient (physicalRate q b) a z.1.1 z.1.2 *
    angularDirichletKernel q branch (z.2.1 - z.1.1) z.1.2 z.2.2 X k *
      timeReducedCoefficient (physicalRate q c) d z.2.1 z.2.2

/-- Functional-equation reflection transports the literal full-circle density
and exchanges both source legs. -/
theorem fullCircleSourcePairDensity_reflect (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    fullCircleSourcePairDensity (xiZeroCopyReflectEquiv q) branch b c a d X k =
      fullCircleSourcePairDensity q (!branch) (!b) (!c) a d X k := by
  funext z
  simp only [fullCircleSourcePairDensity,
    D4BMSourceReflectionTransport.physicalRate_reflect,
    angularDirichletKernel_reflect]

/-- Equal-amplitude complementary source legs, antisymmetrized in their CTP
ordering.  Its formula is intentionally kept as the literal pair of full
direct-minus-image source integrals, with neither cap nor a scalar proxy
substituted. -/
def fullCircleCrossBranchCausalPair (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (X k : ℝ) : ℂ :=
  (∫ z, fullCircleSourcePairDensity q branch false true a a X k z ∂
      D4BMFullSourceReciprocity.eventMeasure.prod D4BMFullSourceReciprocity.eventMeasure) -
    ∫ z, fullCircleSourcePairDensity q branch true false a a X k z ∂
      D4BMFullSourceReciprocity.eventMeasure.prod D4BMFullSourceReciprocity.eventMeasure

/-- **Literal full CTP reflection orientation.** Functional-equation
reflection reverses the equal-amplitude complementary-branch full-circle
Peierls numerator.  Thus its source orientation has exactly the odd parity
required by the PW forward/reverse real imbalance; only the still-open
source-to-Borel magnitude law remains. -/
theorem fullCircleCrossBranchCausalPair_reflection_odd (q : XiZeroCopy)
    (branch : Bool) (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchCausalPair (xiZeroCopyReflectEquiv q) branch a X k =
      -fullCircleCrossBranchCausalPair q (!branch) a X k := by
  have hft := fullCircleSourcePairDensity_reflect q branch false true a a X k
  have htf := fullCircleSourcePairDensity_reflect q branch true false a a X k
  rw [fullCircleCrossBranchCausalPair, fullCircleCrossBranchCausalPair, hft, htf]
  simp only [Bool.not_false, Bool.not_true]
  ring

/-- The physical two-branch completion of the literal CTP numerator.  This is
the source scalar whose proposed normalized real-part magnitude law is meant
to close the chain
`literal CTP source → PW partner balance → RH`: summing the two forced Weyl
channels is necessary before comparison with the branch-free divisor charge. -/
def fullCircleCrossBranchSymmetricCausalPair (q : XiZeroCopy)
    (a : ℂ) (X k : ℝ) : ℂ :=
  fullCircleCrossBranchCausalPair q true a X k +
    fullCircleCrossBranchCausalPair q false a X k

/-- **Source-level PW orientation.** The completed, literal two-branch CTP
numerator is reflection-odd without choosing a Weyl channel.  Hence its real
part has exactly the parity of the PW/FZZ/Deninger divisor imbalance; the only
remaining PW-B premise is an equality of normalized magnitudes. -/
theorem fullCircleCrossBranchSymmetricCausalPair_reflection_odd (q : XiZeroCopy)
    (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchSymmetricCausalPair (xiZeroCopyReflectEquiv q) a X k =
      -fullCircleCrossBranchSymmetricCausalPair q a X k := by
  change fullCircleCrossBranchCausalPair (xiZeroCopyReflectEquiv q) true a X k +
      fullCircleCrossBranchCausalPair (xiZeroCopyReflectEquiv q) false a X k =
    -(fullCircleCrossBranchCausalPair q true a X k +
      fullCircleCrossBranchCausalPair q false a X k)
  rw [
    fullCircleCrossBranchCausalPair_reflection_odd,
    fullCircleCrossBranchCausalPair_reflection_odd]
  simp only [Bool.not_true, Bool.not_false]
  ring

/-- Real source orientation in the exact codomain used by the PW partner
imbalance. -/
theorem fullCircleCrossBranchSymmetricCausalPair_re_reflection_odd (q : XiZeroCopy)
    (a : ℂ) (X k : ℝ) :
    (fullCircleCrossBranchSymmetricCausalPair (xiZeroCopyReflectEquiv q) a X k).re =
      -(fullCircleCrossBranchSymmetricCausalPair q a X k).re := by
  have h := congrArg Complex.re
    (fullCircleCrossBranchSymmetricCausalPair_reflection_odd q a X k)
  simpa using h

/-- Real observables with the functional-equation oddness inherited by the
completed CTP source. -/
def divisorReflectionOddReal (F : XiZeroCopy → ℝ) : Prop :=
  ∀ q, F (xiZeroCopyReflectEquiv q) = -F q

/-- Reflection oddness alone cannot imply PW balance on the Xi divisor: the
imaginary spectral coordinate is odd, yet every actual divisor copy has
nonzero imaginary part.  This kills the proposed parity-only source bridge. -/
theorem divisorReflectionOddReal_not_sufficient_for_balance :
    ∃ F : XiZeroCopy → ℝ,
      divisorReflectionOddReal F ∧ ∀ q, F q ≠ 0 := by
  refine ⟨fun q => (q.1 : ℂ).im, ?_, ?_⟩
  · intro q
    change ((xiZeroCopyReflectEquiv q).1 : ℂ).im = -(q.1 : ℂ).im
    rw [coordinate_reflect]
    simp
  · intro q
    exact xi_divisor_support_im_ne_zero q.1

/-- The exact positive survivor of the parity-only no-go.  A source observable
with CTP reflection oddness vanishes on the critical fibre as soon as its real
part is invariant between a divisor copy and its reflected partner there.
For the literal CTP candidate, establishing this critical-fibre invariance (or
the stronger PW magnitude law) is now a mandatory, explicitly typed premise. -/
theorem divisorReflectionOddReal_eq_zero_of_criticalFiberInvariant
    (F : XiZeroCopy → ℝ) (hodd : divisorReflectionOddReal F)
    (hinvariant : ∀ q, (q.1 : ℂ).re = 1 / 2 →
      F (xiZeroCopyReflectEquiv q) = F q)
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re = 1 / 2) :
    F q = 0 := by
  have hneg := hodd q
  have hfix := hinvariant q hq
  linarith

/-- **Exact critical-fibre survivor for PW-B.** On the critical fibre the
functional-equation partner is the canonical Schwarz-conjugate divisor copy.
Consequently, the real branch-completed literal CTP source vanishes there if
and only if it is invariant under that conjugation.  This replaces the killed
parity-only inference by one concrete source-real-structure premise. -/
theorem fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_iff_conjInvariant_on_critical
    (q : XiZeroCopy) (hq : (deningerDivisorThetaEigen q).re = 1 / 2)
    (a : ℂ) (X k : ℝ) :
    (fullCircleCrossBranchSymmetricCausalPair q a X k).re = 0 ↔
      (fullCircleCrossBranchSymmetricCausalPair (xiZeroCopyConjEquiv q) a X k).re =
        (fullCircleCrossBranchSymmetricCausalPair q a X k).re := by
  have hreflect := xiZeroCopyReflectEquiv_eq_conjEquiv_of_re_eq_half q hq
  have hodd := fullCircleCrossBranchSymmetricCausalPair_re_reflection_odd q a X k
  rw [hreflect] at hodd
  constructor <;> intro h <;> linarith

end
end RHTower.D4BMFullAngularSourceReflection
