import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianHarmonicSourcePrimitive
import GaloisForLFunctions.RHTower.MobiusThetaAdaptiveInfiniteDepthGaussianBoundary

/-!
# Deninger harmonic Green transport of the adaptive Gaussian boundary

The literal adaptive prime-normal columns converge to the negative reflected-Gaussian horizon,
whereas the oriented prime--Gamma Cauchy source integrates to the completed Green primitive.  This
module closes the missing sign and transport comparison between those two statements.

The physical harmonic multiplier converts every cofinal adaptive column into a completed source
primitive column.  These columns converge in the Xi Hilbert norm to the unique reflected-Gaussian
Green primitive.  At every finite depth, completed Green transport is exactly negative
functional-equation reflection of the original adaptive column.  On the prime--Gamma side, the
same Green transport sends the oriented Cauchy boundary pointwise to the reflected unoriented
Cauchy boundary.

Thus the adaptive and prime--Gamma sources form an unconditional Green-compatible boundary
triangle before Hellinger polarization.  This does not assert that its Green antidiagonal lies in
one fixed adaptive resolved sector; that arithmetic codiagonal-kernel membership remains the RH
selection theorem.
-/

open Complex Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-- Applying physical harmonic orientation and then completed Green transport is exactly
functional-equation reflection on the complete Xi carrier. -/
theorem deningerArithmeticCompletedSourceGreen_harmonicOrientation_apply
    (a : XiDivisorL2) (q : XiZeroCopy) :
    deningerArithmeticCompletedSourceGreen
        ((Complex.I • deningerXiHarmonicHodge) a) q =
      a (xiZeroCopyReflectEquiv q) := by
  rw [deningerArithmeticCompletedSourceGreen_apply,
    deningerArithmeticFEOrientation_eq_deningerFreqSign]
  change
    ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
        (Complex.I *
          deningerXiHarmonicHodge a (xiZeroCopyReflectEquiv q)) =
      a (xiZeroCopyReflectEquiv q)
  rw [deningerXiHarmonicHodge_apply]
  have hsign :
      (((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
        ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ)) = 1 := by
    exact_mod_cast deningerFreqSign_sq (q.1 : ℂ).im
  have hreflect :
      ((deningerFreqSign ((xiZeroCopyReflectEquiv q).1 : ℂ).im : ℝ) : ℂ) =
        -((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) := by
    rw [← deningerArithmeticFEOrientation_eq_deningerFreqSign,
      deningerArithmeticFEOrientation_reflect,
      deningerArithmeticFEOrientation_eq_deningerFreqSign]
  rw [hreflect]
  have hI : Complex.I * Complex.I = -1 := by
    simpa only [pow_two] using Complex.I_sq
  calc
    ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
        (Complex.I *
          (Complex.I * -((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
            a (xiZeroCopyReflectEquiv q))) =
      (Complex.I * Complex.I) *
        (-(((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
          ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ))) *
        a (xiZeroCopyReflectEquiv q) := by ring
    _ = a (xiZeroCopyReflectEquiv q) := by rw [hI, hsign]; ring

namespace DeningerMeyerGaussianGreen

/-- The completed Green provenance as an actual bounded linear operator.  Its factorization is
the fracture multiplier after completed source Green reflection, with the forced odd sign. -/
def deningerArithmeticCompletedGreenProvenanceCLM :
    XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  -(deningerMultiplier norm_xiNearbyPoleDualityAdjunctionFracture_le_one).comp
    deningerArithmeticCompletedSourceGreen

/-- The bounded operator is exactly the previously constructed coefficientwise Green provenance,
not a replacement with the same zero set. -/
@[simp]
theorem deningerArithmeticCompletedGreenProvenanceCLM_apply
    (a : XiDivisorL2) :
    deningerArithmeticCompletedGreenProvenanceCLM a =
      deningerArithmeticCompletedGreenProvenance a := by
  ext q
  rw [deningerArithmeticCompletedGreenProvenanceCLM]
  change
    -(xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) *
      deningerArithmeticCompletedSourceGreen a q) =
      deningerArithmeticCompletedGreenProvenance a q
  rw [deningerArithmeticCompletedSourceGreen_apply,
    deningerArithmeticCompletedGreenProvenance_apply,
    deningerArithmeticOrientedHodgeLp_apply,
    deningerArithmeticCompletedRieszConjugation_apply,
    starRingEnd_self_apply]
  ring

/-- Literal prime--Gamma Cauchy boundary after the completed Green fracture.  The fracture is
applied before Bochner integration, so the RH detector remains a source boundary value. -/
def reflectedGaussianPrimeGammaGreenFractureBoundary (x : ℝ) : XiDivisorL2 :=
  deningerArithmeticCompletedGreenProvenanceCLM
    (reflectedGaussianPrimeGammaCauchyBoundary x)

theorem integrable_reflectedGaussianPrimeGammaGreenFractureBoundary :
    Integrable reflectedGaussianPrimeGammaGreenFractureBoundary := by
  exact deningerArithmeticCompletedGreenProvenanceCLM.integrable_comp
    integrable_reflectedGaussianPrimeGammaCauchyBoundary

/-- The explicit fractured two-line Cauchy field integrates to the actual global Green detector. -/
theorem integral_reflectedGaussianPrimeGammaGreenFractureBoundary_eq_greenProvenance :
    (∫ x : ℝ, reflectedGaussianPrimeGammaGreenFractureBoundary x) =
      reflectedGaussianHorizonGreenProvenance := by
  have hcomm :=
    deningerArithmeticCompletedGreenProvenanceCLM.integral_comp_comm
      integrable_reflectedGaussianPrimeGammaCauchyBoundary
  change
    (∫ x : ℝ, deningerArithmeticCompletedGreenProvenanceCLM
      (reflectedGaussianPrimeGammaCauchyBoundary x)) = _
  rw [hcomm, integral_reflectedGaussianPrimeGammaCauchyBoundary_eq_horizonGradeL2,
    deningerArithmeticCompletedGreenProvenanceCLM_apply]
  rfl

/-- The centered Gaussian profile is even before divisor restriction. -/
theorem reflectedGaussianCauchyProfile_neg (z : ℂ) :
    reflectedGaussianCauchyProfile (-z) = reflectedGaussianCauchyProfile z := by
  simp [reflectedGaussianCauchyProfile]

/-- Functional-equation reflection of a Xi coordinate is exactly reversal of the horizontal
parameter on the literal two-line Cauchy boundary. -/
theorem reflectedGaussianPrimeGammaCauchyBoundary_reflect
    (x : ℝ) (q : XiZeroCopy) :
    reflectedGaussianPrimeGammaCauchyBoundary x
        (xiZeroCopyReflectEquiv q) =
      reflectedGaussianPrimeGammaCauchyBoundary (-x) q := by
  rw [reflectedGaussianPrimeGammaCauchyBoundary_apply,
    reflectedGaussianPrimeGammaCauchyBoundary_apply,
    xiSpectralPoint_reflect]
  simp only [Complex.ofReal_neg]
  have hprofileUpper :
      reflectedGaussianCauchyProfile (-(x : ℂ) + Complex.I) =
        reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I) := by
    rw [show -(x : ℂ) + Complex.I = -((x : ℂ) - Complex.I) by ring,
      reflectedGaussianCauchyProfile_neg]
  have hprofileLower :
      reflectedGaussianCauchyProfile (-(x : ℂ) - Complex.I) =
        reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I) := by
    rw [show -(x : ℂ) - Complex.I = -((x : ℂ) + Complex.I) by ring,
      reflectedGaussianCauchyProfile_neg]
  rw [hprofileUpper, hprofileLower]
  have hdenUpper :
      -xiSpectralPoint q - ((x : ℂ) + Complex.I) =
        -(xiSpectralPoint q - (-(x : ℂ) - Complex.I)) := by ring
  have hdenLower :
      -xiSpectralPoint q - ((x : ℂ) - Complex.I) =
        -(xiSpectralPoint q - (-(x : ℂ) + Complex.I)) := by ring
  rw [hdenUpper, hdenLower, inv_neg, inv_neg]
  ring

/-- Pointwise Green comparison with the actual prime--Gamma Cauchy boundary: source harmonic
orientation is removed by completed Green transport, leaving functional-equation reflection of
the literal two-line boundary column. -/
theorem deningerArithmeticCompletedSourceGreen_orientedCauchyBoundary_apply
    (x : ℝ) (q : XiZeroCopy) :
    deningerArithmeticCompletedSourceGreen
        (reflectedGaussianPrimeGammaOrientedCauchyBoundary x) q =
      reflectedGaussianPrimeGammaCauchyBoundary x
        (xiZeroCopyReflectEquiv q) := by
  exact deningerArithmeticCompletedSourceGreen_harmonicOrientation_apply
    (reflectedGaussianPrimeGammaCauchyBoundary x) q

/-- Source-native form of the Green comparison: completed Green transport reverses the real
Cauchy boundary parameter and removes harmonic orientation. -/
theorem deningerArithmeticCompletedSourceGreen_orientedCauchyBoundary_eq_reversed
    (x : ℝ) :
    deningerArithmeticCompletedSourceGreen
        (reflectedGaussianPrimeGammaOrientedCauchyBoundary x) =
      reflectedGaussianPrimeGammaCauchyBoundary (-x) := by
  ext q
  rw [deningerArithmeticCompletedSourceGreen_orientedCauchyBoundary_apply,
    reflectedGaussianPrimeGammaCauchyBoundary_reflect]

/-- Cofinal adaptive prime-normal realization of the actual Green provenance detector.  The
leading minus compensates the infinite-depth Mobius head. -/
def adaptivePrimeNormalInfiniteDepthGreenFractureColumn
    (p : Nat.Primes) (K : ℕ) : XiDivisorL2 :=
  -deningerArithmeticCompletedGreenProvenanceCLM
    (adaptivePrimeNormalInfiniteDepthHorizonColumn p K)

/-- **Common source boundary for the RH detector.**  Every retained prime label gives literal
adaptive columns whose completed Green fractures converge to the fixed global detector `g_G`. -/
theorem tendsto_adaptivePrimeNormalInfiniteDepthGreenFractureColumn
    (p : Nat.Primes) :
    Tendsto (adaptivePrimeNormalInfiniteDepthGreenFractureColumn p) atTop
      (nhds reflectedGaussianHorizonGreenProvenance) := by
  let F : XiDivisorL2 →L[ℂ] XiDivisorL2 :=
    -deningerArithmeticCompletedGreenProvenanceCLM
  have hmap := F.continuous.continuousAt.tendsto.comp
    (tendsto_adaptivePrimeNormalInfiniteDepthHorizonColumn p)
  have hlimit :
      F (-reflectedGaussianHorizonGradeL2) =
        reflectedGaussianHorizonGreenProvenance := by
    rw [map_neg]
    simp only [F, neg_apply, neg_neg,
      deningerArithmeticCompletedGreenProvenanceCLM_apply]
    rfl
  rw [hlimit] at hmap
  change Tendsto (fun K =>
    (-deningerArithmeticCompletedGreenProvenanceCLM)
      (adaptivePrimeNormalInfiniteDepthHorizonColumn p K)) atTop
    (nhds reflectedGaussianHorizonGreenProvenance)
  simpa only [Function.comp_def, F] using hmap

/-- Adaptive Mobius--theta source and fractured prime--Gamma Cauchy source land on the same actual
global Green detector.  This is stronger than their unfractured Gaussian boundary equality. -/
theorem tendsto_adaptivePrimeNormalInfiniteDepthGreenFractureColumn_eq_cauchyBoundary
    (p : Nat.Primes) :
    Tendsto (adaptivePrimeNormalInfiniteDepthGreenFractureColumn p) atTop
      (nhds (∫ x : ℝ, reflectedGaussianPrimeGammaGreenFractureBoundary x)) := by
  rw [integral_reflectedGaussianPrimeGammaGreenFractureBoundary_eq_greenProvenance]
  exact tendsto_adaptivePrimeNormalInfiniteDepthGreenFractureColumn p

/-- Harmonic orientation that compensates the negative infinite-depth Mobius head. -/
def reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn
    (p : Nat.Primes) (K : ℕ) : XiDivisorL2 :=
  -(Complex.I • deningerXiHarmonicHodge)
    (adaptivePrimeNormalInfiniteDepthHorizonColumn p K)

@[simp]
theorem reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn_apply
    (p : Nat.Primes) (K : ℕ) (q : XiZeroCopy) :
    reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn p K q =
      ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
        adaptivePrimeNormalDivisorReaderAtDepth K q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) *
        reflectedGaussianHorizonGrade q := by
  rw [reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn]
  change
    -(Complex.I * deningerXiHarmonicHodge
      (adaptivePrimeNormalInfiniteDepthHorizonColumn p K) q) = _
  rw [deningerXiHarmonicHodge_apply,
    adaptivePrimeNormalInfiniteDepthHorizonColumn_apply]
  have hI : Complex.I * Complex.I = -1 := by
    simpa only [pow_two] using Complex.I_sq
  calc
    -(Complex.I *
        (Complex.I * ((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
          (adaptivePrimeNormalDivisorReaderAtDepth K q
            (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) *
            reflectedGaussianHorizonGrade q))) =
      -(Complex.I * Complex.I) *
        (((deningerFreqSign (q.1 : ℂ).im : ℝ) : ℂ) *
          adaptivePrimeNormalDivisorReaderAtDepth K q
            (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) *
          reflectedGaussianHorizonGrade q) := by ring
    _ = _ := by rw [hI]; ring

/-- Finite-depth Green transport is exact: it is negative functional-equation reflection of the
unoriented adaptive horizon column. -/
theorem deningerArithmeticCompletedSourceGreen_adaptiveHarmonicColumn_apply
    (p : Nat.Primes) (K : ℕ) (q : XiZeroCopy) :
    deningerArithmeticCompletedSourceGreen
        (reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn p K) q =
      -adaptivePrimeNormalInfiniteDepthHorizonColumn p K
        (xiZeroCopyReflectEquiv q) := by
  rw [reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn, map_neg]
  change
    -(deningerArithmeticCompletedSourceGreen
      ((Complex.I • deningerXiHarmonicHodge)
        (adaptivePrimeNormalInfiniteDepthHorizonColumn p K)) q) = _
  rw [deningerArithmeticCompletedSourceGreen_harmonicOrientation_apply]

/-- **Cofinal source construction of the completed Green primitive.**  For every retained ordinary
prime label, physical harmonic orientation of the literal adaptive prime-normal columns converges
in the complete Xi norm to the unique reflected-Gaussian source Green primitive. -/
theorem tendsto_reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn
    (p : Nat.Primes) :
    Tendsto (reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn p) atTop
      (nhds reflectedGaussianHorizonCompletedGreenPrimitive) := by
  let W : XiDivisorL2 →L[ℂ] XiDivisorL2 :=
    -(Complex.I • deningerXiHarmonicHodge)
  have hmap := W.continuous.continuousAt.tendsto.comp
    (tendsto_adaptivePrimeNormalInfiniteDepthHorizonColumn p)
  have hgrade : reflectedGaussianHorizonGradeL2 =
      reflectedGaussianHorizonAdmittedResidue := by
    ext q
    rw [reflectedGaussianHorizonGradeL2_apply,
      reflectedGaussianHorizonAdmittedResidue_apply]
  have hlimit :
      W (-reflectedGaussianHorizonGradeL2) =
        reflectedGaussianHorizonCompletedGreenPrimitive := by
    rw [map_neg]
    simp only [W, neg_apply, neg_neg]
    rw [hgrade]
    exact reflectedGaussianHorizonCompletedGreenPrimitive_eq_harmonicHodge.symm
  rw [hlimit] at hmap
  change Tendsto (fun K =>
    (-(Complex.I • deningerXiHarmonicHodge))
      (adaptivePrimeNormalInfiniteDepthHorizonColumn p K)) atTop
    (nhds reflectedGaussianHorizonCompletedGreenPrimitive)
  simpa only [Function.comp_def, W] using hmap

/-- Adaptive infinite-depth source and oriented prime--Gamma Cauchy source have the same completed
Green primitive boundary value. -/
theorem tendsto_reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn_eq_orientedCauchyBoundary
    (p : Nat.Primes) :
    Tendsto (reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn p) atTop
      (nhds (∫ x : ℝ, reflectedGaussianPrimeGammaOrientedCauchyBoundary x)) := by
  rw [integral_reflectedGaussianPrimeGammaOrientedCauchyBoundary_eq_greenPrimitive]
  exact tendsto_reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn p

/-- The finite Green images of the cofinal adaptive primitive columns converge to the original
reflected-Gaussian horizon.  This is Green compatibility before taking the boundary. -/
theorem tendsto_green_reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn
    (p : Nat.Primes) :
    Tendsto (fun K => deningerArithmeticCompletedSourceGreen
        (reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn p K)) atTop
      (nhds reflectedGaussianHorizonAdmittedResidue) := by
  have h :=
    deningerArithmeticCompletedSourceGreen.continuous.continuousAt.tendsto.comp
      (tendsto_reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn p)
  rw [reflectedGaussianHorizonCompletedGreenPrimitive_green] at h
  simpa only [Function.comp_def] using h

end DeningerMeyerGaussianGreen

end

end RHTower
