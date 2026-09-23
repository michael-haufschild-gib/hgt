import GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHardySource
import GaloisForLFunctions.RHTower.EulerFisherWardComplementaryRecord

/-!
# Singular graph-normal source-to-Xi landing

The completed Möbius--Gamma/Xi transport is affine in its Fisher-source
coefficient and divides that coefficient by the normal factor

`epsilon * squarefreeBoundaryOverlap sigma epsilon u`.

Consequently it is not nonexpansive in the ambient source norm near the
critical Euler boundary.  The source graph nevertheless has one forced
normal coordinate: multiply an affine transport difference by the complete
factor `-2 I epsilon overlap`.  On every complex inward Hardy node this
recovers the literal damped squarefree source coefficient exactly.

For the actual Fisher tangent the unnormalized affine map still lands in the
completed prime--Gamma Xi trace, while the graph-normal difference is the
division-free Fisher numerator.  Thus source contractivity and analytic Xi
landing coexist before the singular normal factor is inverted.

This theorem is unconditional.  It does not assert that the inverse normal
factor stays bounded at the critical boundary, nor does it identify the
strict-right Ward component.
-/

open Complex

namespace RHTower

noncomputable section

/-- One presentation-independent complex-damped coefficient function of a
source vector.  Outside the closed inward half-plane it is extended by zero;
the Gamma/Xi graph below only uses its inward values. -/
def mobiusCriticalComplexHardySourceCoefficient
    (sigma : ℝ) (hsigma : 1 < sigma)
    (x : lp (fun _ : ℕ => ℂ) 2) (u : ℂ) : ℂ :=
  if hu : 0 ≤ u.re then
    inner ℂ x
      (infiniteMobiusCriticalComplexDampedSignedWeightLp
        sigma u hsigma hu)
  else 0

theorem mobiusCriticalComplexHardySourceCoefficient_of_re_nonneg
    {sigma : ℝ} (hsigma : 1 < sigma)
    (x : lp (fun _ : ℕ => ℂ) 2) {u : ℂ} (hu : 0 ≤ u.re) :
    mobiusCriticalComplexHardySourceCoefficient sigma hsigma x u =
      inner ℂ x
        (infiniteMobiusCriticalComplexDampedSignedWeightLp
          sigma u hsigma hu) := by
  simp only [mobiusCriticalComplexHardySourceCoefficient, dif_pos hu]

/-- Affine Gamma/Xi observation of one source vector through its one global
complex-damped coefficient function.  Prime, Gamma, and doubled-prime
correction terms remain inside the unnormalized target map. -/
def mobiusGammaXiComplexHardyAffineSourceMap
    (sigma : ℝ) (hsigma : 1 < sigma) (u : ℂ)
    (x : lp (fun _ : ℕ => ℂ) 2) : ℂ :=
  squarefreeMobiusGammaXiWardTransportV
    (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
    (mobiusCriticalComplexHardySourceCoefficient sigma hsigma x)
    u

/-- Complete singular graph normalizer forced by the source overlap and the
coefficient-two Xi convention. -/
def mobiusGammaXiComplexHardyGraphNormalizer
    (sigma : ℝ) (u : ℂ) : ℂ :=
  -2 * I * ((sigma - 1 : ℝ) : ℂ) *
    GaloisForLFunctions.squarefreeBoundaryOverlap
      (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) u

/-- Graph-normal difference of two affine source observations. -/
def mobiusGammaXiComplexHardyGraphNormalDifference
    (sigma : ℝ) (hsigma : 1 < sigma) (u : ℂ)
    (x y : lp (fun _ : ℕ => ℂ) 2) : ℂ :=
  mobiusGammaXiComplexHardyGraphNormalizer sigma u *
    (mobiusGammaXiComplexHardyAffineSourceMap sigma hsigma u x -
      mobiusGammaXiComplexHardyAffineSourceMap sigma hsigma u y)

private theorem mobiusGammaXiComplexHardy_shift
    {sigma : ℝ} (hsigma : 1 < sigma) {u : ℂ} (hu : 0 ≤ u.re) :
    1 < ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  nlinarith

private theorem mobiusGammaXiComplexHardy_graphDenominator_ne_zero
    {sigma : ℝ} (hsigma : 1 < sigma) {u : ℂ} (hu : 0 ≤ u.re) :
    ((sigma - 1 : ℝ) : ℂ) *
        GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) u ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast sub_ne_zero.mpr hsigma.ne'
  · unfold GaloisForLFunctions.squarefreeBoundaryOverlap
    exact div_ne_zero
      (GaloisForLFunctions.squarefreePartition_ne_zero
        (mobiusGammaXiComplexHardy_shift hsigma hu))
      (GaloisForLFunctions.squarefreePartition_ne_zero (by simpa using hsigma))

/-- Exact affine gain before graph normalization.  This identity retains the
singular denominator rather than hiding it in a target norm. -/
theorem mobiusGammaXiComplexHardyAffineSourceMap_sub
    {sigma : ℝ} (hsigma : 1 < sigma) {u : ℂ} (hu : 0 ≤ u.re)
    (x y : lp (fun _ : ℕ => ℂ) 2) :
    mobiusGammaXiComplexHardyAffineSourceMap sigma hsigma u x -
        mobiusGammaXiComplexHardyAffineSourceMap sigma hsigma u y =
      (I / 2) *
        (inner ℂ x
              (infiniteMobiusCriticalComplexDampedSignedWeightLp
                sigma u hsigma hu) -
          inner ℂ y
              (infiniteMobiusCriticalComplexDampedSignedWeightLp
                sigma u hsigma hu)) /
        (((sigma - 1 : ℝ) : ℂ) *
          GaloisForLFunctions.squarefreeBoundaryOverlap
            (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) u) := by
  unfold mobiusGammaXiComplexHardyAffineSourceMap
    squarefreeMobiusGammaXiWardTransportV
    squarefreeMobiusGammaCurrentTransportV
  rw [mobiusCriticalComplexHardySourceCoefficient_of_re_nonneg hsigma _ hu,
    mobiusCriticalComplexHardySourceCoefficient_of_re_nonneg hsigma _ hu]
  ring

private theorem mobiusGammaXiComplexHardy_graphNormal_cancel
    (d z : ℂ) (hd : d ≠ 0) :
    (-2 * I * d) * ((I / 2) * z / d) = z := by
  calc
    (-2 * I * d) * ((I / 2) * z / d) =
        -(I ^ (2 : ℕ)) * (d * z / d) := by ring
    _ = z := by
      rw [Complex.I_sq]
      field_simp [hd]

/-- **Exact singular graph-normal factorization.**  The full forced graph
normalizer turns the Gamma/Xi affine difference back into the literal
complex-damped source coefficient. -/
theorem mobiusGammaXiComplexHardyGraphNormalDifference_eq_inner
    {sigma : ℝ} (hsigma : 1 < sigma) {u : ℂ} (hu : 0 ≤ u.re)
    (x y : lp (fun _ : ℕ => ℂ) 2) :
    mobiusGammaXiComplexHardyGraphNormalDifference
        sigma hsigma u x y =
      inner ℂ (x - y)
        (infiniteMobiusCriticalComplexDampedSignedWeightLp
          sigma u hsigma hu) := by
  rw [mobiusGammaXiComplexHardyGraphNormalDifference,
    mobiusGammaXiComplexHardyAffineSourceMap_sub hsigma hu]
  rw [inner_sub_left]
  have hden :=
    mobiusGammaXiComplexHardy_graphDenominator_ne_zero hsigma hu
  unfold mobiusGammaXiComplexHardyGraphNormalizer
  simpa only [mul_assoc] using
    (mobiusGammaXiComplexHardy_graphNormal_cancel _ _ hden)

/-- The graph-normal source observation is nonexpansive on every complex
inward Hardy node, uniformly in imaginary displacement. -/
theorem norm_mobiusGammaXiComplexHardyGraphNormalDifference_le
    {sigma : ℝ} (hsigma : 1 < sigma) {u : ℂ} (hu : 0 ≤ u.re)
    (x y : lp (fun _ : ℕ => ℂ) 2) :
    ‖mobiusGammaXiComplexHardyGraphNormalDifference
        sigma hsigma u x y‖ ≤ ‖x - y‖ := by
  rw [mobiusGammaXiComplexHardyGraphNormalDifference_eq_inner hsigma hu]
  calc
    ‖inner ℂ (x - y)
        (infiniteMobiusCriticalComplexDampedSignedWeightLp
          sigma u hsigma hu)‖ ≤
        ‖x - y‖ *
          ‖infiniteMobiusCriticalComplexDampedSignedWeightLp
            sigma u hsigma hu‖ := norm_inner_le_norm _ _
    _ ≤ ‖x - y‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_infiniteMobiusCriticalComplexDampedSignedWeightLp_le_one
          hsigma hu)
        (norm_nonneg _)
    _ = ‖x - y‖ := mul_one _

/-- The actual Fisher tangent retains the complete unnormalized
prime--Gamma Xi landing at every complex inward Hardy node. -/
theorem mobiusGammaXiComplexHardyAffineSourceMap_actualTangent
    {sigma : ℝ} (hsigma : 1 < sigma) {u : ℂ} (hu : 0 ≤ u.re) :
    mobiusGammaXiComplexHardyAffineSourceMap sigma hsigma u
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma) =
      continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ))) := by
  unfold mobiusGammaXiComplexHardyAffineSourceMap
  simpa only [squarefreeMobiusGammaXiWardTransportV,
    squarefreeMobiusGammaCurrentTransportV,
    mobiusCriticalComplexHardySourceCoefficient_of_re_nonneg hsigma _ hu]
    using squarefreeMobiusGammaXiWardTransportV_actualComplexNode
      hsigma hu (mobiusGammaXiComplexHardy_shift hsigma hu)

/-- The signed squarefree graph source and the positive full-Euler Hilbert
source have the same completed Xi landing on every real inward ray.  This
identifies the two source constructions before the Ward complementary
channel is subtracted. -/
theorem
    mobiusGammaXiComplexHardyAffineSourceMap_actualTangent_eq_eulerPositive
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    mobiusGammaXiComplexHardyAffineSourceMap sigma hsigma (u : ℂ)
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma) =
      eulerPositiveGammaXiWardHilbertTransportAt sigma u hsigma hu := by
  rw [mobiusGammaXiComplexHardyAffineSourceMap_actualTangent hsigma
      (by simpa using hu),
    eulerPositiveGammaXiWardHilbertTransportAt_eq_continuedSource
      hsigma hu]
  simp only [eulerPositiveCriticalBoundaryParameter]
  push_cast
  rfl

/-- **Unconditional source-to-Ward complementary landing.**  On the real
inward family, the raw Xi output of the contractive graph-normal source is
exactly the full source term in the strict-right Ward decomposition.  The
only additional datum is the explicit non-right canonical-product channel
and its boundary self-symbol. -/
theorem continuedXiAntiCausalWardResponse_eq_mobiusGraphSource_sub_complement
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    let s := eulerPositiveCriticalBoundaryParameter sigma u
    let w : ℂ := ((s - 1 / 2 : ℝ) : ℂ)
    continuedXiAntiCausalWardResponse w =
      -2 * I *
          mobiusGammaXiComplexHardyAffineSourceMap sigma hsigma (u : ℂ)
            (infiniteMobiusCriticalFisherTangentLp sigma hsigma) -
        2 * I * logDeriv xiNonrightCanonicalProduct (I * w) +
        xiAntiCausalWardBoundarySelfSymbol := by
  dsimp only
  rw [
    mobiusGammaXiComplexHardyAffineSourceMap_actualTangent_eq_eulerPositive
      hsigma hu]
  exact continuedXiAntiCausalWardResponse_eq_eulerFisherTransport_sub_complement
    hsigma hu

/-- On the actual Fisher tangent, graph normalization recovers exactly the
division-free squarefree Fisher numerator. -/
theorem mobiusGammaXiComplexHardyGraphNormalDifference_actualTangent
    {sigma : ℝ} (hsigma : 1 < sigma) {u : ℂ} (hu : 0 ≤ u.re) :
    mobiusGammaXiComplexHardyGraphNormalDifference sigma hsigma u
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma) 0 =
      GaloisForLFunctions.squarefreeFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) u := by
  rw [mobiusGammaXiComplexHardyGraphNormalDifference_eq_inner hsigma hu,
    sub_zero]
  exact inner_fisherTangent_complexDamped_eq_squarefreeFisherScore
    hsigma hu (mobiusGammaXiComplexHardy_shift hsigma hu)

/-- Unconditional source-to-Xi graph package: contractive normal source
coordinate, exact division-free Fisher numerator, and raw affine Xi landing
hold simultaneously on the complete complex inward node family. -/
theorem mobiusGammaXiSingularGraphNormalSourceToXiLanding
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∀ (u : ℂ) (_hu : 0 ≤ u.re)
        (x y : lp (fun _ : ℕ => ℂ) 2),
      ‖mobiusGammaXiComplexHardyGraphNormalDifference
          sigma hsigma u x y‖ ≤ ‖x - y‖) ∧
    (∀ (u : ℂ) (_hu : 0 ≤ u.re),
      mobiusGammaXiComplexHardyGraphNormalDifference sigma hsigma u
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma) 0 =
        GaloisForLFunctions.squarefreeFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) u) ∧
    (∀ (u : ℂ) (_hu : 0 ≤ u.re),
      mobiusGammaXiComplexHardyAffineSourceMap sigma hsigma u
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma) =
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)))) := by
  exact ⟨
    fun u hu x y =>
      norm_mobiusGammaXiComplexHardyGraphNormalDifference_le hsigma hu x y,
    fun u hu =>
      mobiusGammaXiComplexHardyGraphNormalDifference_actualTangent hsigma hu,
    fun u hu =>
      mobiusGammaXiComplexHardyAffineSourceMap_actualTangent hsigma hu⟩

end

end RHTower
