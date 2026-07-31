import GaloisForLFunctions.RHTower.XiReciprocalSquareFixedCauchySource
import GaloisForLFunctions.RHTower.CCMUniversalWeilSourceReconstruction

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Antiholomorphic adjoint-response test attached to a continued Cauchy pole. -/
def xiReciprocalSquareCauchyAdjointResponseTest (z a : ℂ) : ℂ :=
  ((starRingEnd ℂ) a)⁻¹ ^ 2 * ((starRingEnd ℂ) a - z)⁻¹

theorem xiReciprocalSquareCauchyAdjointResponseTest_squareSummable
    (z : XiContinuedCauchyPoint) :
    XiWeilSquareSummable
      (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ)) := by
  have hsum := HilbertSchmidt.summable_coe_sq
    (xiWeilLineConjLp
      (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z)))
  apply hsum.congr
  intro q
  rw [xiWeilLineConjLp_apply, xiReciprocalSquareOperator_apply]
  symm
  simp only [xiReciprocalSquareCauchyAdjointResponseTest,
    xiSpectralPoint_lineConj, xiZeroCopyReciprocalSquare,
    xiWeilContinuedCauchyLp, xiWeilCauchyLp_apply, xiWeilCauchyTest]

theorem xiReciprocalSquareCauchyAdjointResponseTest_evaluation
    (z : XiContinuedCauchyPoint) :
    xiWeilEvaluationLp
        (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
        (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z) =
      xiWeilLineConjLp
        (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z)) := by
  apply Subtype.ext
  funext q
  rw [xiWeilEvaluationLp_apply, xiWeilLineConjLp_apply,
    xiReciprocalSquareOperator_apply]
  simp only [xiReciprocalSquareCauchyAdjointResponseTest,
    xiSpectralPoint_lineConj, xiZeroCopyReciprocalSquare,
    xiWeilContinuedCauchyLp, xiWeilCauchyLp_apply, xiWeilCauchyTest]

/-- Holomorphic reciprocal-square response before critical-line-reflection reindexing. -/
def xiReciprocalSquareCauchyHolomorphicResponseTest (z a : ℂ) : ℂ :=
  a⁻¹ ^ 2 * (a - z)⁻¹

theorem xiReciprocalSquareCauchyHolomorphicResponseTest_squareSummable
    (z : XiContinuedCauchyPoint) :
    XiWeilSquareSummable
      (xiReciprocalSquareCauchyHolomorphicResponseTest (z : ℂ)) := by
  have hsum := HilbertSchmidt.summable_coe_sq
    (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z))
  apply hsum.congr
  intro q
  rw [xiReciprocalSquareOperator_apply]
  symm
  simp only [xiReciprocalSquareCauchyHolomorphicResponseTest,
    xiZeroCopyReciprocalSquare, xiWeilContinuedCauchyLp,
    xiWeilCauchyLp_apply, xiWeilCauchyTest]

theorem xiReciprocalSquareCauchyHolomorphicResponseTest_evaluation
    (z : XiContinuedCauchyPoint) :
    xiWeilEvaluationLp
        (xiReciprocalSquareCauchyHolomorphicResponseTest (z : ℂ))
        (xiReciprocalSquareCauchyHolomorphicResponseTest_squareSummable z) =
      xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z) := by
  apply Subtype.ext
  funext q
  rw [xiWeilEvaluationLp_apply, xiReciprocalSquareOperator_apply]
  simp only [xiReciprocalSquareCauchyHolomorphicResponseTest,
    xiZeroCopyReciprocalSquare, xiWeilContinuedCauchyLp,
    xiWeilCauchyLp_apply, xiWeilCauchyTest]

/-- Every Hilbert moment of the anti-holomorphic adjoint response against a Cauchy atom is an
ordinary Xi--Weil polarization of two holomorphic source tests. -/
theorem inner_cauchyAdjointResponse_cauchy_eq_sourcePolarization
    (z w : XiContinuedCauchyPoint) :
    inner ℂ
        (xiWeilEvaluationLp
          (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
          (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z))
        (xiWeilContinuedCauchyLp w) =
      xiWeilPolarization (xiWeilCauchyTest (w : ℂ))
        (xiReciprocalSquareCauchyHolomorphicResponseTest (z : ℂ)) := by
  rw [xiReciprocalSquareCauchyAdjointResponseTest_evaluation,
    ← xiReciprocalSquareCauchyHolomorphicResponseTest_evaluation]
  change inner ℂ
      (xiWeilLineConjLp
        (xiWeilEvaluationLp
          (xiReciprocalSquareCauchyHolomorphicResponseTest (z : ℂ))
          (xiReciprocalSquareCauchyHolomorphicResponseTest_squareSummable z)))
      (xiWeilEvaluationLp (xiWeilCauchyTest (w : ℂ))
        (XiWeilSquareSummable_cauchy (w : ℂ))) = _
  exact inner_xiWeilLineConjLp_evaluation_eq_polarization
    (xiWeilCauchyTest (w : ℂ))
    (xiReciprocalSquareCauchyHolomorphicResponseTest (z : ℂ))
    (XiWeilSquareSummable_cauchy (w : ℂ))
    (xiReciprocalSquareCauchyHolomorphicResponseTest_squareSummable z)

/-- **Source-moment uniqueness.**  Inside the continued-Cauchy Hilbert closure, the holomorphic
source moments characterize the anti-holomorphic adjoint response uniquely.  No divisor
coordinate values occur in the moment data. -/
theorem eq_cauchyAdjointResponse_of_sourcePolarization_moments
    (z : XiContinuedCauchyPoint)
    (v : lp (fun _ : XiZeroCopy => ℂ) 2)
    (hv : v ∈ xiWeilContinuedCauchyHilbertSubspace)
    (hmoment : ∀ w : XiContinuedCauchyPoint,
      inner ℂ v (xiWeilContinuedCauchyLp w) =
        xiWeilPolarization (xiWeilCauchyTest (w : ℂ))
          (xiReciprocalSquareCauchyHolomorphicResponseTest (z : ℂ))) :
    v = xiWeilEvaluationLp
      (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
      (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z) := by
  let r := xiWeilEvaluationLp
    (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
    (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)
  let x := v - r
  have hr : r ∈ xiWeilContinuedCauchyHilbertSubspace := by
    exact xiWeilEvaluationLp_mem_continuedCauchyHilbertSubspace
      (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
      (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)
  have hx : x ∈ xiWeilContinuedCauchyHilbertSubspace :=
    xiWeilContinuedCauchyHilbertSubspace.sub_mem hv hr
  have hgen : ∀ w : XiContinuedCauchyPoint,
      inner ℂ x (xiWeilContinuedCauchyLp w) = 0 := by
    intro w
    simp only [x, inner_sub_left]
    rw [hmoment w,
      inner_cauchyAdjointResponse_cauchy_eq_sourcePolarization z w,
      sub_self]
  have halg : ∀ u ∈ xiWeilContinuedCauchyAlgebraicSubspace,
      inner ℂ x u = 0 := by
    intro u hu
    have hker : xiWeilContinuedCauchyAlgebraicSubspace ≤
        LinearMap.ker (innerSL ℂ x).toLinearMap := by
      rw [xiWeilContinuedCauchyAlgebraicSubspace, Submodule.span_le]
      rintro _ ⟨w, rfl⟩
      simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        innerSL_apply_apply] using! hgen w
    have hu' := hker hu
    simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply] using hu'
  have hclosed : IsClosed {u | inner ℂ x u = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hxclosure : x ∈ closure
      (↑xiWeilContinuedCauchyAlgebraicSubspace :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2)) := by
    exact hx
  have hxx : inner ℂ x x = 0 :=
    (closure_minimal halg hclosed) hxclosure
  have hxzero : x = 0 := inner_self_eq_zero.mp hxx
  exact sub_eq_zero.mp hxzero

/-- **Holomorphic replacement no-go.**  At the matching pole, replacing the adjoint response by
its holomorphic precursor makes the source polarization real unconditionally.  Its imaginary part
therefore cannot replace the fixed orientation defect. -/
theorem xiWeilPolarization_cauchy_holomorphicResponse_im_eq_zero
    (z : XiContinuedCauchyPoint) :
    (xiWeilPolarization (xiWeilCauchyTest (z : ℂ))
      (xiReciprocalSquareCauchyHolomorphicResponseTest (z : ℂ))).im = 0 := by
  have hsym :
      xiWeilPolarization (xiWeilCauchyTest (z : ℂ))
          (xiReciprocalSquareCauchyHolomorphicResponseTest (z : ℂ)) =
        xiWeilPolarization
          (xiReciprocalSquareCauchyHolomorphicResponseTest (z : ℂ))
          (xiWeilCauchyTest (z : ℂ)) := by
    unfold xiWeilPolarization
    apply tsum_congr
    intro q
    simp [xiWeilSharp, xiWeilCauchyTest,
      xiReciprocalSquareCauchyHolomorphicResponseTest]
    ring
  have hconj := xiWeilPolarization_conj_symm
    (xiWeilCauchyTest (z : ℂ))
    (xiReciprocalSquareCauchyHolomorphicResponseTest (z : ℂ))
  rw [← hsym] at hconj
  exact Complex.conj_eq_iff_im.mp hconj.symm

/-- The holomorphic response is a simple-pole difference plus the double Cauchy pole at zero.
This is the algebraic input for a split-pole source realization. -/
theorem xiReciprocalSquareCauchyHolomorphicResponseTest_partialFractions
    {z a : ℂ} (hz : z ≠ 0) (ha : a ≠ 0) (haz : a ≠ z) :
    xiReciprocalSquareCauchyHolomorphicResponseTest z a =
      z⁻¹ ^ 2 * xiWeilCauchyTest z a -
      z⁻¹ ^ 2 * xiWeilCauchyTest 0 a -
      z⁻¹ * a⁻¹ ^ 2 := by
  rw [xiReciprocalSquareCauchyHolomorphicResponseTest,
    xiWeilCauchyTest, xiWeilCauchyTest]
  field_simp [hz, ha, sub_ne_zero.mpr haz]
  ring

/-- Plus polarization test whose quadratic value contains the desired imaginary cross term. -/
def xiReciprocalSquareCauchySourcePlusTest (z a : ℂ) : ℂ :=
  xiWeilCauchyTest z a +
    I * xiReciprocalSquareCauchyAdjointResponseTest z a

/-- Minus polarization test whose quadratic value contains the opposite imaginary cross term. -/
def xiReciprocalSquareCauchySourceMinusTest (z a : ℂ) : ℂ :=
  xiWeilCauchyTest z a -
    I * xiReciprocalSquareCauchyAdjointResponseTest z a

theorem xiReciprocalSquareCauchySourcePlusTest_squareSummable
    (z : XiContinuedCauchyPoint) :
    XiWeilSquareSummable
      (xiReciprocalSquareCauchySourcePlusTest (z : ℂ)) := by
  have hsum := HilbertSchmidt.summable_coe_sq
    (xiWeilContinuedCauchyLp z +
      I • xiWeilEvaluationLp
        (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
        (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z))
  apply hsum.congr
  intro q
  symm
  change ‖xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) +
    I * xiReciprocalSquareCauchyAdjointResponseTest
      (z : ℂ) (xiSpectralPoint q)‖ ^ 2 = _
  rfl

theorem xiReciprocalSquareCauchySourceMinusTest_squareSummable
    (z : XiContinuedCauchyPoint) :
    XiWeilSquareSummable
      (xiReciprocalSquareCauchySourceMinusTest (z : ℂ)) := by
  have hsum := HilbertSchmidt.summable_coe_sq
    (xiWeilContinuedCauchyLp z -
      I • xiWeilEvaluationLp
        (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
        (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z))
  apply hsum.congr
  intro q
  symm
  change ‖xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) -
    I * xiReciprocalSquareCauchyAdjointResponseTest
      (z : ℂ) (xiSpectralPoint q)‖ ^ 2 = _
  rfl

theorem xiReciprocalSquareCauchySourcePlusTest_evaluation
    (z : XiContinuedCauchyPoint) :
    xiWeilEvaluationLp
        (xiReciprocalSquareCauchySourcePlusTest (z : ℂ))
        (xiReciprocalSquareCauchySourcePlusTest_squareSummable z) =
      xiWeilContinuedCauchyLp z +
        I • xiWeilEvaluationLp
          (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
          (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z) := by
  apply Subtype.ext
  funext q
  change xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) +
      I * xiReciprocalSquareCauchyAdjointResponseTest
        (z : ℂ) (xiSpectralPoint q) = _
  rfl

theorem xiReciprocalSquareCauchySourceMinusTest_evaluation
    (z : XiContinuedCauchyPoint) :
    xiWeilEvaluationLp
        (xiReciprocalSquareCauchySourceMinusTest (z : ℂ))
        (xiReciprocalSquareCauchySourceMinusTest_squareSummable z) =
      xiWeilContinuedCauchyLp z -
        I • xiWeilEvaluationLp
          (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
          (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z) := by
  apply Subtype.ext
  funext q
  change xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) -
      I * xiReciprocalSquareCauchyAdjointResponseTest
        (z : ℂ) (xiSpectralPoint q) = _
  rfl

theorem xiWeilHilbertQuadratic_I_polarization_difference
    (f g : lp (fun _ : XiZeroCopy => ℂ) 2)
    (hsym : inner ℂ (xiWeilLineConjLp f) g =
      (starRingEnd ℂ) (inner ℂ (xiWeilLineConjLp g) f)) :
    xiWeilHilbertQuadratic (f + I • g) -
        xiWeilHilbertQuadratic (f - I • g) =
      4 * (inner ℂ (xiWeilLineConjLp g) f).im := by
  unfold xiWeilHilbertQuadratic
  simp only [xiWeilLineConjLinearIsometry_apply,
    map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_I]
  rw [hsym]
  simp [Complex.mul_re]
  have him : (inner ℂ f (xiWeilLineConjLp g)).im =
      -(inner ℂ (xiWeilLineConjLp g) f).im := by
    have h := congrArg Complex.im
      (inner_conj_symm f (xiWeilLineConjLp g))
    simpa only [conj_im] using h.symm
  rw [him]
  ring

/-- The explicit adjoint-response test turns Weil polarization into the ordinary Hilbert
quadratic value of the reciprocal-square operator. -/
theorem xiWeilPolarization_cauchy_adjointResponse_eq
    (z : XiContinuedCauchyPoint) :
    xiWeilPolarization (xiWeilCauchyTest (z : ℂ))
        (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ)) =
      inner ℂ
        (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z))
        (xiWeilContinuedCauchyLp z) := by
  rw [xiWeilPolarization, lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  rw [xiReciprocalSquareOperator_apply]
  simp only [xiWeilContinuedCauchyLp, xiWeilCauchyLp_apply,
    xiWeilCauchyTest]
  simp [xiWeilSharp, xiReciprocalSquareCauchyAdjointResponseTest,
    RCLike.inner_apply, xiZeroCopyReciprocalSquare]

/-- Exact polarization identity: the plus/minus source quadratic contrast is four times the
continued Cauchy orientation defect. -/
theorem xiReciprocalSquareCauchySourceContrast_eq_four_mul_orientationDefect
    (z : XiContinuedCauchyPoint) :
    (xiWeilPolarization (xiReciprocalSquareCauchySourcePlusTest (z : ℂ))
          (xiReciprocalSquareCauchySourcePlusTest (z : ℂ))).re -
        (xiWeilPolarization (xiReciprocalSquareCauchySourceMinusTest (z : ℂ))
          (xiReciprocalSquareCauchySourceMinusTest (z : ℂ))).re =
      4 * xiReciprocalSquareContinuedCauchyOrientationDefect z := by
  have hsym :
      inner ℂ (xiWeilLineConjLp (xiWeilContinuedCauchyLp z))
          (xiWeilEvaluationLp
            (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
            (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)) =
        (starRingEnd ℂ)
          (inner ℂ
            (xiWeilLineConjLp
              (xiWeilEvaluationLp
                (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
                (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)))
            (xiWeilContinuedCauchyLp z)) := by
    change inner ℂ
        (xiWeilLineConjLp
          (xiWeilEvaluationLp (xiWeilCauchyTest (z : ℂ))
            (XiWeilSquareSummable_cauchy (z : ℂ))))
        (xiWeilEvaluationLp
          (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
          (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)) =
      (starRingEnd ℂ)
        (inner ℂ
          (xiWeilLineConjLp
            (xiWeilEvaluationLp
              (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
              (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)))
          (xiWeilEvaluationLp (xiWeilCauchyTest (z : ℂ))
            (XiWeilSquareSummable_cauchy (z : ℂ))))
    rw [inner_xiWeilLineConjLp_evaluation_eq_polarization,
      inner_xiWeilLineConjLp_evaluation_eq_polarization,
      xiWeilPolarization_conj_symm]
  have hcross :
      inner ℂ
          (xiWeilLineConjLp
            (xiWeilEvaluationLp
              (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
              (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)))
          (xiWeilContinuedCauchyLp z) =
        inner ℂ
          (xiReciprocalSquareOperator (xiWeilContinuedCauchyLp z))
          (xiWeilContinuedCauchyLp z) := by
    change inner ℂ
        (xiWeilLineConjLp
          (xiWeilEvaluationLp
            (xiReciprocalSquareCauchyAdjointResponseTest (z : ℂ))
            (xiReciprocalSquareCauchyAdjointResponseTest_squareSummable z)))
        (xiWeilEvaluationLp (xiWeilCauchyTest (z : ℂ))
          (XiWeilSquareSummable_cauchy (z : ℂ))) = _
    rw [inner_xiWeilLineConjLp_evaluation_eq_polarization,
      xiWeilPolarization_cauchy_adjointResponse_eq]
  rw [← xiWeilHilbertQuadratic_evaluation_eq_polarization_re
      (xiReciprocalSquareCauchySourcePlusTest (z : ℂ))
      (xiReciprocalSquareCauchySourcePlusTest_squareSummable z),
    ← xiWeilHilbertQuadratic_evaluation_eq_polarization_re
      (xiReciprocalSquareCauchySourceMinusTest (z : ℂ))
      (xiReciprocalSquareCauchySourceMinusTest_squareSummable z),
    xiReciprocalSquareCauchySourcePlusTest_evaluation,
    xiReciprocalSquareCauchySourceMinusTest_evaluation,
    xiWeilHilbertQuadratic_I_polarization_difference _ _ hsym,
    hcross]
  rfl

/-- Energy convergence is forced by evaluation convergence for any separated continued source
packet sequence.  This converse-facing form is useful when a source producer, rather than the
universal closure argument, supplies the packets. -/
theorem xiSeparatedContinuedCauchySourceEnergy_tendsto_of_evaluation_tendsto
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (nhds (xiWeilEvaluationLp F hF))) :
    Tendsto (fun n => (P n).sourceEnergy) atTop
      (nhds (xiWeilPolarization F F).re) := by
  have hQ := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hP
  rw [xiWeilHilbertQuadratic_evaluation_eq_polarization_re] at hQ
  apply hQ.congr'
  exact Eventually.of_forall fun n =>
    (P n).sourceEnergy_eq_hilbertQuadratic.symm

/-- Two separated continued prime--Gamma source-packet sequences reconstruct the fixed-pole
orientation defect as their normalized energy contrast. -/
theorem exists_separatedContinuedCauchySourceContrast_tendsto_orientationDefect
    (z : XiContinuedCauchyPoint) :
    ∃ Pplus Pminus : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (Pplus n).evaluation) atTop
        (nhds (xiWeilEvaluationLp
          (xiReciprocalSquareCauchySourcePlusTest (z : ℂ))
          (xiReciprocalSquareCauchySourcePlusTest_squareSummable z))) ∧
      Tendsto (fun n => (Pminus n).evaluation) atTop
        (nhds (xiWeilEvaluationLp
          (xiReciprocalSquareCauchySourceMinusTest (z : ℂ))
          (xiReciprocalSquareCauchySourceMinusTest_squareSummable z))) ∧
      Tendsto (fun n =>
          ((Pplus n).sourceEnergy - (Pminus n).sourceEnergy) / 4)
        atTop
        (nhds (xiReciprocalSquareContinuedCauchyOrientationDefect z)) := by
  obtain ⟨Pplus, hplusEval, hplusEnergy⟩ :=
    xiWeilPolarization_separatedContinuedSource_reconstruction
      (xiReciprocalSquareCauchySourcePlusTest (z : ℂ))
      (xiReciprocalSquareCauchySourcePlusTest_squareSummable z)
  obtain ⟨Pminus, hminusEval, hminusEnergy⟩ :=
    xiWeilPolarization_separatedContinuedSource_reconstruction
      (xiReciprocalSquareCauchySourceMinusTest (z : ℂ))
      (xiReciprocalSquareCauchySourceMinusTest_squareSummable z)
  refine ⟨Pplus, Pminus, hplusEval, hminusEval, ?_⟩
  have hcontrast := (hplusEnergy.sub hminusEnergy).const_mul (1 / 4 : ℝ)
  convert hcontrast using 1
  · funext n
    ring
  · congr 1
    linarith [
      xiReciprocalSquareCauchySourceContrast_eq_four_mul_orientationDefect z]

/-- Source-only saturation interface at the predetermined pole.  Evaluation convergence fixes
the two reconstructed tests; the final clause asks their normalized source-energy contrast to
vanish. -/
def XiReciprocalSquareFixedCauchySourceContrastSaturation : Prop :=
  ∃ Pplus Pminus : ℕ → XiSeparatedContinuedCauchyPacket,
    Tendsto (fun n => (Pplus n).evaluation) atTop
      (nhds (xiWeilEvaluationLp
        (xiReciprocalSquareCauchySourcePlusTest
          (xiReciprocalSquareFixedCauchyPole : ℂ))
        (xiReciprocalSquareCauchySourcePlusTest_squareSummable
          xiReciprocalSquareFixedCauchyPole))) ∧
    Tendsto (fun n => (Pminus n).evaluation) atTop
      (nhds (xiWeilEvaluationLp
        (xiReciprocalSquareCauchySourceMinusTest
          (xiReciprocalSquareFixedCauchyPole : ℂ))
        (xiReciprocalSquareCauchySourceMinusTest_squareSummable
          xiReciprocalSquareFixedCauchyPole))) ∧
    Tendsto (fun n =>
        ((Pplus n).sourceEnergy - (Pminus n).sourceEnergy) / 4)
      atTop (nhds 0)

/-- Exact right-to-left source criterion: a zero normalized contrast for the predetermined
prime--Gamma packet reconstructions is equivalent to RH. -/
theorem xiReciprocalSquareFixedCauchySourceContrastSaturation_iff_riemannHypothesis :
    XiReciprocalSquareFixedCauchySourceContrastSaturation ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨Pplus, Pminus, hplus, hminus, hzero⟩
    have hdefect : Tendsto (fun n =>
        ((Pplus n).sourceEnergy - (Pminus n).sourceEnergy) / 4)
        atTop
        (nhds (xiReciprocalSquareContinuedCauchyOrientationDefect
          xiReciprocalSquareFixedCauchyPole)) := by
      have hplusEnergy :=
        xiSeparatedContinuedCauchySourceEnergy_tendsto_of_evaluation_tendsto
          (xiReciprocalSquareCauchySourcePlusTest
            (xiReciprocalSquareFixedCauchyPole : ℂ))
          (xiReciprocalSquareCauchySourcePlusTest_squareSummable
            xiReciprocalSquareFixedCauchyPole) Pplus hplus
      have hminusEnergy :=
        xiSeparatedContinuedCauchySourceEnergy_tendsto_of_evaluation_tendsto
          (xiReciprocalSquareCauchySourceMinusTest
            (xiReciprocalSquareFixedCauchyPole : ℂ))
          (xiReciprocalSquareCauchySourceMinusTest_squareSummable
            xiReciprocalSquareFixedCauchyPole) Pminus hminus
      have hcontrast :=
        (hplusEnergy.sub hminusEnergy).const_mul (1 / 4 : ℝ)
      convert hcontrast using 1
      · funext n
        ring
      · congr 1
        linarith [
          xiReciprocalSquareCauchySourceContrast_eq_four_mul_orientationDefect
            xiReciprocalSquareFixedCauchyPole]
    have hdefectZero :
        xiReciprocalSquareContinuedCauchyOrientationDefect
          xiReciprocalSquareFixedCauchyPole = 0 :=
      tendsto_nhds_unique hdefect hzero
    exact
      xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis.mp
        hdefectZero
  · intro hRH
    obtain ⟨Pplus, Pminus, hplus, hminus, hdefect⟩ :=
      exists_separatedContinuedCauchySourceContrast_tendsto_orientationDefect
        xiReciprocalSquareFixedCauchyPole
    refine ⟨Pplus, Pminus, hplus, hminus, ?_⟩
    have hzero :
        xiReciprocalSquareContinuedCauchyOrientationDefect
          xiReciprocalSquareFixedCauchyPole = 0 :=
      xiReciprocalSquareFixedCauchyOrientationDefectZero_iff_riemannHypothesis.mpr
        hRH
    simpa [hzero] using hdefect

end

end RHTower
