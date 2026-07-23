import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentCoefficients
import GaloisForLFunctions.RHTower.XiCriticalMellinSourceFactorization
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam

/-!
# Möbius--Gamma source transport into the continued Xi trace column

The source transport in this file has two genuinely non-diagonal stages.

* The squarefree Möbius Fisher tangent is observed against the full damped source vector.  Dividing
  by the same source overlap, before continuation, recovers the completed squarefree logarithmic
  current exactly.
* The centered Xi phase is transported through a two-point Cauchy Julia cell.  Its first aperture
  tangent is the continued prime--Gamma divided-difference kernel.  Coupling every packet node to
  the common centered source anchor turns this cross-cell tangent into the continued Xi trace
  column, before anti-causal Hardy compression.

No Xi divisor, zero enumeration, positivity assumption, or RH hypothesis enters these identities.
The division by the squarefree overlap is retained explicitly: it is the source graph on which
continuation zeros become the Ward current rather than an illicit bounded scalar readout.
-/

open Complex Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The centered Xi phase and its Julia cross-cell -/

/-- The centered Xi aperture phase.  On a real boundary line its numerator and denominator are
Schwarz partners; as a complex aperture germ it is holomorphic wherever the denominator is
nonzero. -/
def xiWardSourcePhase (z alpha : ℂ) : ℂ :=
  XiC (z - alpha * I) / XiC (z + alpha * I)

@[simp] theorem xiWardSourcePhase_zero {z : ℂ} (hz : XiC z ≠ 0) :
    xiWardSourcePhase z 0 = 1 := by
  simp [xiWardSourcePhase, hz]

/-- The first aperture tangent of the Xi phase is the centered Xi logarithmic current. -/
theorem hasDerivAt_xiWardSourcePhase_zero {z : ℂ} (hz : XiC z ≠ 0) :
    HasDerivAt (xiWardSourcePhase z) (-2 * I * logDeriv XiC z) 0 := by
  have hminus : HasDerivAt (fun alpha : ℂ => z - alpha * I) (-I) 0 := by
    simpa using
      (hasDerivAt_const (x := (0 : ℂ)) (c := z)).sub
        ((hasDerivAt_id (𝕜 := ℂ) (x := (0 : ℂ))).mul_const I)
  have hplus : HasDerivAt (fun alpha : ℂ => z + alpha * I) I 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℂ)) (c := z)).add
        ((hasDerivAt_id (𝕜 := ℂ) (x := (0 : ℂ))).mul_const I) using 1
    all_goals ring_nf
  have hnum :
      HasDerivAt (fun alpha : ℂ => XiC (z - alpha * I))
        (deriv XiC z * (-I)) 0 := by
    simpa using XiC_differentiable.differentiableAt.hasDerivAt.comp 0 hminus
  have hden :
      HasDerivAt (fun alpha : ℂ => XiC (z + alpha * I))
        (deriv XiC z * I) 0 := by
    simpa using XiC_differentiable.differentiableAt.hasDerivAt.comp 0 hplus
  have hquot := hnum.div hden (by simpa using hz)
  simpa only [xiWardSourcePhase, logDeriv_apply] using
    hquot.congr_deriv (by
      field_simp [hz]
      ring)

/-- Analytic sharp ratio of two Xi phase cells.  For real aperture this is
`Theta(z) * conj(Theta(w))`, but the displayed formula remains holomorphic in the aperture. -/
def xiWardSourcePhaseCrossRatio (z w alpha : ℂ) : ℂ :=
  xiWardSourcePhase z alpha /
    xiWardSourcePhase ((starRingEnd ℂ) w) alpha

@[simp] theorem xiWardSourcePhaseCrossRatio_zero
    {z w : ℂ} (hz : XiC z ≠ 0)
    (hw : XiC ((starRingEnd ℂ) w) ≠ 0) :
    xiWardSourcePhaseCrossRatio z w 0 = 1 := by
  simp [xiWardSourcePhaseCrossRatio, xiWardSourcePhase_zero, hz, hw]

/-- The cross-ratio tangent is the difference of the two centered logarithmic currents. -/
theorem hasDerivAt_xiWardSourcePhaseCrossRatio_zero
    {z w : ℂ} (hz : XiC z ≠ 0)
    (hw : XiC ((starRingEnd ℂ) w) ≠ 0) :
    HasDerivAt (xiWardSourcePhaseCrossRatio z w)
      (2 * I *
        (logDeriv XiC ((starRingEnd ℂ) w) - logDeriv XiC z)) 0 := by
  have hzphase := hasDerivAt_xiWardSourcePhase_zero hz
  have hwphase := hasDerivAt_xiWardSourcePhase_zero hw
  have hwzero : xiWardSourcePhase ((starRingEnd ℂ) w) 0 ≠ 0 := by
    rw [xiWardSourcePhase_zero hw]
    exact one_ne_zero
  have hquot := hzphase.div hwphase hwzero
  rw [xiWardSourcePhase_zero hz, xiWardSourcePhase_zero hw] at hquot
  simpa only [xiWardSourcePhaseCrossRatio, one_pow, mul_one, one_mul,
    div_one] using hquot.congr_deriv (by ring)

/-- Cauchy Gram cell in the normalization adapted to the Xi phase aperture. -/
def xiWardCauchyGramCell (z w : ℂ) : ℂ :=
  1 / (2 * I * (z - (starRingEnd ℂ) w))

/-- Signed Julia cross-defect of the Xi phase.  It is a two-point object even when only one
source aperture is varied. -/
def xiWardJuliaCrossDefect (z w alpha : ℂ) : ℂ :=
  (xiWardSourcePhaseCrossRatio z w alpha - 1) /
    (2 * I * (z - (starRingEnd ℂ) w))

/-- Exact non-diagonal Julia/defect identity: transported Cauchy Gram minus original Cauchy Gram
is the Xi cross-defect. -/
theorem xiWardJuliaCrossDefect_eq_transport_sub_gram
    (z w alpha : ℂ) :
    xiWardJuliaCrossDefect z w alpha =
      xiWardSourcePhaseCrossRatio z w alpha *
          xiWardCauchyGramCell z w -
        xiWardCauchyGramCell z w := by
  simp only [xiWardJuliaCrossDefect, xiWardCauchyGramCell]
  ring

/-- The first Julia cross-defect tangent is the divided difference of the Xi logarithmic
current. -/
theorem hasDerivAt_xiWardJuliaCrossDefect_zero
    {z w : ℂ} (hz : XiC z ≠ 0)
    (hw : XiC ((starRingEnd ℂ) w) ≠ 0)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    HasDerivAt (xiWardJuliaCrossDefect z w)
      ((logDeriv XiC ((starRingEnd ℂ) w) - logDeriv XiC z) /
        (z - (starRingEnd ℂ) w)) 0 := by
  have hcross := hasDerivAt_xiWardSourcePhaseCrossRatio_zero hz hw
  have h :=
    (hcross.sub_const 1).div_const
      (2 * I * (z - (starRingEnd ℂ) w))
  simpa only [xiWardJuliaCrossDefect] using
    h.congr_deriv (by
      field_simp [I_ne_zero, sub_ne_zero.mpr hzw])

/-- On the continued source domain, the centered source trace is the Xi logarithmic current. -/
theorem continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC_of_domain
    {z : ℂ} (hzdom : CCMContinuedCauchyDomain z) :
    continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hzdom.1 hzdom.2.1 hzdom.2.2.1]
  symm
  exact logDeriv_XiC_eq_relativeResolventTrace
    (XiC_ne_zero_of_continuedPrimeArch_domain
      hzdom.1 hzdom.2.1 hzdom.2.2.1)

/-- The Julia cross-defect tangent is exactly the continued Xi source Cauchy kernel. -/
theorem hasDerivAt_xiWardJuliaCrossDefect_zero_eq_continuedCauchyKernel
    {z w : ℂ} (hzdom : CCMContinuedCauchyDomain z)
    (hwdom : CCMContinuedCauchyDomain w)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    HasDerivAt (xiWardJuliaCrossDefect z w)
      (ccmContinuedCauchyKernel z w) 0 := by
  have hzXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain
      hzdom.1 hzdom.2.1 hzdom.2.2.1
  have hwXi : XiC ((starRingEnd ℂ) w) ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain
      hwdom.2.2.2.1 hwdom.2.2.2.2.1 hwdom.2.2.2.2.2
  convert hasDerivAt_xiWardJuliaCrossDefect_zero hzXi hwXi hzw using 1
  rw [ccmContinuedCauchyKernel,
    continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC_of_domain hzdom]
  congr 2
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hwdom.2.2.2.1 hwdom.2.2.2.2.1 hwdom.2.2.2.2.2]
  symm
  exact logDeriv_XiC_eq_relativeResolventTrace hwXi

/-! ## Common-anchor transport into the continued Ward column -/

private theorem logDeriv_XiC_zero_eq_zero :
    logDeriv XiC 0 = 0 := by
  have hodd := deriv_XiC_neg 0
  have hderiv : deriv XiC 0 = 0 := by
    simp only [neg_zero] at hodd
    have htwo : 2 * deriv XiC 0 = 0 := by
      linear_combination hodd
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  rw [logDeriv_apply, hderiv, zero_div]

/-- Non-diagonal common-anchor source transport.  Every output node is coupled to the centered
Xi source anchor through a Julia cross-cell; no nodewise scalar multiplier can express this
construction. -/
def xiWardAnchoredSourceTransportV (z alpha : ℂ) : ℂ :=
  -z * xiWardJuliaCrossDefect z 0 alpha

/-- The anchored cross-cell tangent is the Xi logarithmic current itself. -/
theorem hasDerivAt_xiWardAnchoredSourceTransportV_zero
    {z : ℂ} (hz : XiC z ≠ 0) (hz0 : z ≠ 0) :
    HasDerivAt (xiWardAnchoredSourceTransportV z)
      (logDeriv XiC z) 0 := by
  have hXi0 : XiC ((starRingEnd ℂ) (0 : ℂ)) ≠ 0 := by
    simpa only [map_zero] using XiC_zero_ne
  have hzconj : z ≠ (starRingEnd ℂ) (0 : ℂ) := by
    simpa only [map_zero] using hz0
  have hcross := hasDerivAt_xiWardJuliaCrossDefect_zero
    (w := (0 : ℂ)) hz hXi0 hzconj
  change HasDerivAt
    (fun alpha : ℂ => -z * xiWardJuliaCrossDefect z 0 alpha)
    (logDeriv XiC z) 0
  apply (hcross.const_mul (-z)).congr_deriv
  simp only [map_zero]
  rw [logDeriv_XiC_zero_eq_zero]
  simp only [sub_zero]
  field_simp [hz0]
  ring

/-- The common-anchor Julia transport turns its aperture tangent into the continued Xi source
trace column at every noncentral regular source point. -/
theorem hasDerivAt_xiWardAnchoredSourceTransportV_zero_eq_continuedSource
    {z : ℂ} (hzdom : CCMContinuedCauchyDomain z) (hz0 : z ≠ 0) :
    HasDerivAt (xiWardAnchoredSourceTransportV z)
      (continuedPrimeArchSourceRelativeTrace z) 0 := by
  rw [continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC_of_domain hzdom]
  exact hasDerivAt_xiWardAnchoredSourceTransportV_zero
    (XiC_ne_zero_of_continuedPrimeArch_domain
      hzdom.1 hzdom.2.1 hzdom.2.2.1) hz0

/-- Finite continued Xi trace response column, before anti-causal Hardy compression. -/
def continuedXiTraceColumn {n : ℕ} (node : Fin n → ℂ) : Fin n → ℂ :=
  fun i => continuedPrimeArchSourceRelativeTrace (node i)

/-- One non-diagonal common-anchor transport constructs the whole finite continued Xi trace
column. -/
def xiWardPacketSourceTransportV {n : ℕ}
    (node : Fin n → ℂ) (alpha : ℂ) : Fin n → ℂ :=
  fun i => xiWardAnchoredSourceTransportV (node i) alpha

/-- Packet form of the source transport law: its derivative is exactly the continued Xi trace
column, entry by entry. -/
theorem hasDerivAt_xiWardPacketSourceTransportV_zero
    {n : ℕ} {node : Fin n → ℂ}
    (hdom : ∀ i, CCMContinuedCauchyDomain (node i))
    (hzero : ∀ i, node i ≠ 0) (i : Fin n) :
    HasDerivAt (fun alpha => xiWardPacketSourceTransportV node alpha i)
      (continuedXiTraceColumn node i) 0 := by
  exact hasDerivAt_xiWardAnchoredSourceTransportV_zero_eq_continuedSource
    (hdom i) (hzero i)

/-! ## The singular Möbius--Gamma graph transport -/

/-- Source graph transport from a pointed Fisher numerator to the completed squarefree current.
The overlap division is part of the graph; deleting it destroys the continued divisor response. -/
def squarefreeMobiusGammaCurrentTransportV
    (sigma epsilon : ℂ) (score : ℂ → ℂ) (u : ℂ) : ℂ :=
  2 * GaloisForLFunctions.squarefreeFixedCurrent sigma -
    score u /
      (epsilon *
        GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon u) -
    2 * logDeriv archFactor (sigma + u * epsilon)

/-- Exact graph reconstruction: the source Fisher numerator divided by its own overlap gives the
completed squarefree logarithmic current, including the Gamma completion. -/
theorem squarefreeMobiusGammaCurrentTransportV_eq_completedCurrent
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re) (hepsilon : epsilon ≠ 0) :
    squarefreeMobiusGammaCurrentTransportV sigma epsilon
        (GaloisForLFunctions.squarefreeFisherScore sigma epsilon) u =
      GaloisForLFunctions.completedSquarefreeFixedCurrent
        (sigma + u * epsilon) := by
  have hbase :
      GaloisForLFunctions.squarefreePartition sigma ≠ 0 :=
    GaloisForLFunctions.squarefreePartition_ne_zero hsigma
  have hshiftPart :
      GaloisForLFunctions.squarefreePartition (sigma + u * epsilon) ≠ 0 :=
    GaloisForLFunctions.squarefreePartition_ne_zero hshift
  have hoverlap :
      GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon u ≠ 0 := by
    exact div_ne_zero hshiftPart hbase
  have hden :
      epsilon *
        GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon u ≠ 0 :=
    mul_ne_zero hepsilon hoverlap
  rw [squarefreeMobiusGammaCurrentTransportV,
    GaloisForLFunctions.squarefreeFisherScore_eq_fixedCurrent_difference
      hsigma hshift,
    GaloisForLFunctions.completedSquarefreeFixedCurrent]
  field_simp [hden]
  ring

/-- The positive damped Möbius source overlap is exactly the real Euler-half-plane restriction of
the meromorphic squarefree overlap used by the graph transport. -/
theorem squarefreeMobiusBoundaryLayerLaplace_eq_squarefreeBoundaryOverlap
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    squarefreeMobiusBoundaryLayerLaplace sigma u =
      GaloisForLFunctions.squarefreeBoundaryOverlap
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
  have hshift : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  have hcoord :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
      sigma + u * (sigma - 1) by rfl)
  rw [squarefreeMobiusBoundaryLayerLaplace,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hshift,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma]
  simp only [GaloisForLFunctions.squarefreeBoundaryOverlap,
    GaloisForLFunctions.squarefreePartition]
  rw [hcoord]

/-- The actual Hilbert Fisher-tangent coefficient is the real source restriction of the
division-free squarefree Fisher numerator. -/
theorem inner_fisherTangent_damped_eq_squarefreeFisherScore
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
        (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu) =
      GaloisForLFunctions.squarefreeFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
  have hshift : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  have hcoord :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
      sigma + u * (sigma - 1) by rfl)
  rw [inner_fisherTangent_damped_eq_coefficient,
    infiniteMobiusCriticalFisherTangentDampedCoefficient,
    squarefreeMobiusBoundaryLayerLaplace_eq_squarefreeBoundaryOverlap hsigma hu,
    GaloisForLFunctions.squarefreeFisherScore_eq_fixedCurrent_difference]
  · push_cast
    rw [ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent hsigma,
      ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent hshift, hcoord]
    have harg :
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) =
          (sigma : ℂ) + (sigma : ℂ) * (u : ℂ) - (u : ℂ) := by
      exact_mod_cast (show sigma + u * (sigma - 1) =
        sigma + sigma * u - u by ring)
    rw [harg]
    ring
  · simpa using hsigma
  · simpa [hcoord] using hshift

/-- Applying the singular graph transport to the actual Möbius four-unit Fisher tangent
coefficient reconstructs the completed squarefree current on every safe source ray. -/
theorem squarefreeMobiusGammaCurrentTransportV_actualTangent
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    squarefreeMobiusGammaCurrentTransportV
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
        (fun v =>
          GaloisForLFunctions.squarefreeFisherScore
            (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v)
        (u : ℂ) =
      GaloisForLFunctions.completedSquarefreeFixedCurrent
        (mobiusCriticalBoundaryParameter sigma u : ℂ) := by
  have hshift : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  have hcoord :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
      sigma + u * (sigma - 1) by rfl)
  simpa only [hcoord] using
    squarefreeMobiusGammaCurrentTransportV_eq_completedCurrent
    (sigma := (sigma : ℂ)) (epsilon := ((sigma - 1 : ℝ) : ℂ))
    (u := (u : ℂ)) (by simpa using hsigma) (by simpa using hshift)
    (by exact_mod_cast sub_ne_zero.mpr hsigma.ne')

/-! ## Exact composition from the Möbius tangent graph to the Xi phase column -/

/-- Original completed coordinate as a centered Xi spectral coordinate. -/
def xiWardCenteredCoordinate (s : ℂ) : ℂ :=
  (s - 1 / 2) * (-I)

@[simp] theorem xiWardCenteredCoordinate_source (s : ℂ) :
    1 / 2 + xiWardCenteredCoordinate s * I = s := by
  rw [xiWardCenteredCoordinate, mul_assoc]
  have hI : (-I) * I = (1 : ℂ) := by
    rw [neg_mul, I_mul_I]
    ring
  rw [hI, mul_one]
  ring

/-- Global source-frame identity: the continued Xi trace is the completed squarefree current plus
the strict-right doubled-zeta correction, in the exact centered coordinate. -/
theorem continuedPrimeArchSourceRelativeTrace_eq_completedSquarefree_add_correction
    (z : ℂ) :
    continuedPrimeArchSourceRelativeTrace z =
      (-I / 2) *
        (GaloisForLFunctions.completedSquarefreeFixedCurrent
            (1 / 2 + z * I) +
          4 * infinitePrimeFlux (2 * (1 / 2 + z * I))) := by
  simp only [continuedPrimeArchSourceRelativeTrace,
    GaloisForLFunctions.completedSquarefreeFixedCurrent,
    GaloisForLFunctions.squarefreeFixedCurrent]
  ring

/-- The composed non-diagonal transport: first use the singular source-overlap graph to turn a
Fisher numerator into the completed squarefree current, then apply the exact source-framed
strict-right correction to obtain the continued Xi current. -/
def squarefreeMobiusGammaXiWardTransportV
    (sigma epsilon : ℂ) (score : ℂ → ℂ) (u : ℂ) : ℂ :=
  let s := sigma + u * epsilon
  (-I / 2) *
    (squarefreeMobiusGammaCurrentTransportV sigma epsilon score u +
      4 * infinitePrimeFlux (2 * s))

/-- Exact source graph-to-Xi weld on the Euler domain. -/
theorem squarefreeMobiusGammaXiWardTransportV_eq_continuedSource
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re) (hepsilon : epsilon ≠ 0) :
    squarefreeMobiusGammaXiWardTransportV sigma epsilon
        (GaloisForLFunctions.squarefreeFisherScore sigma epsilon) u =
      continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate (sigma + u * epsilon)) := by
  rw [squarefreeMobiusGammaXiWardTransportV,
    squarefreeMobiusGammaCurrentTransportV_eq_completedCurrent
      hsigma hshift hepsilon,
    continuedPrimeArchSourceRelativeTrace_eq_completedSquarefree_add_correction,
    xiWardCenteredCoordinate_source]

/-- The actual Hilbert Möbius Fisher tangent, observed against its full damped source vector and
passed through the singular Gamma graph, gives the continued Xi source column on every safe
critical ray. -/
theorem squarefreeMobiusGammaXiWardTransportV_actualTangent
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    squarefreeMobiusGammaXiWardTransportV
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
        (fun v =>
          GaloisForLFunctions.squarefreeFisherScore
            (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v)
        (u : ℂ) =
      continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          (mobiusCriticalBoundaryParameter sigma u : ℂ)) := by
  have hshift : 1 < mobiusCriticalBoundaryParameter sigma u := by
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  have hcoord :
      ((mobiusCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) + (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    exact_mod_cast (show mobiusCriticalBoundaryParameter sigma u =
      sigma + u * (sigma - 1) by rfl)
  simpa only [hcoord] using
    squarefreeMobiusGammaXiWardTransportV_eq_continuedSource
      (sigma := (sigma : ℂ)) (epsilon := ((sigma - 1 : ℝ) : ℂ))
      (u := (u : ℂ)) (by simpa using hsigma) (by simpa using hshift)
      (by exact_mod_cast sub_ne_zero.mpr hsigma.ne')

/-- At every safe point of the actual moving source ray, the common-anchor Julia transport has
the same tangent as the composed Möbius--Gamma graph transport. -/
theorem hasDerivAt_xiWardAnchoredSourceTransportV_actualTangent
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    HasDerivAt
      (xiWardAnchoredSourceTransportV
        (xiWardCenteredCoordinate
          (mobiusCriticalBoundaryParameter sigma u : ℂ)))
      (squarefreeMobiusGammaXiWardTransportV
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
        (fun v =>
          GaloisForLFunctions.squarefreeFisherScore
            (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v)
        (u : ℂ))
      0 := by
  let s : ℂ := (mobiusCriticalBoundaryParameter sigma u : ℂ)
  let z : ℂ := xiWardCenteredCoordinate s
  have hs : 1 < s.re := by
    dsimp only [s]
    simp only [ofReal_re]
    unfold mobiusCriticalBoundaryParameter
    nlinarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re] at hre
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have hcoord : 1 / 2 + z * I = s := by
    exact xiWardCenteredCoordinate_source s
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain
      (by rw [hcoord]; linarith) (by rw [hcoord]; exact hs1)
      (by rw [hcoord]; exact hzeta)
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, zero_mul, add_zero] at hcoord
    have hre := congrArg Complex.re hcoord
    norm_num at hre
    linarith
  have hsource :
      continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      (by rw [hcoord]; linarith) (by rw [hcoord]; exact hs1)
      (by rw [hcoord]; exact hzeta)]
    symm
    exact logDeriv_XiC_eq_relativeResolventTrace hXi
  have hphase :=
    hasDerivAt_xiWardAnchoredSourceTransportV_zero hXi hz0
  rw [← hsource] at hphase
  have hgraph :=
    squarefreeMobiusGammaXiWardTransportV_actualTangent hsigma hu
  simpa only [s, z, hgraph] using hphase

/-- **Möbius--Gamma/Xi preprojection transport package.**  The source vector is an actual Hilbert tangent
whose squared norm tends to four; its damped coefficients are the squarefree Fisher numerators;
the singular graph transport reconstructs the continued Xi trace column; and the non-diagonal
anchored Julia cell has exactly that preprojection column as its aperture tangent. -/
theorem mobiusGammaFourUnitTangent_to_continuedXiTraceColumn :
    Tendsto (fun sigma : ℝ =>
      if hsigma : 1 < sigma then
        ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2
      else 0)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 4) ∧
    (∀ ⦃sigma u : ℝ⦄ (hsigma : 1 < sigma) (hu : 0 ≤ u),
      inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
          (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu) =
        GaloisForLFunctions.squarefreeFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ)) ∧
    (∀ ⦃sigma u : ℝ⦄ (_hsigma : 1 < sigma) (_hu : 0 ≤ u),
      HasDerivAt
        (xiWardAnchoredSourceTransportV
          (xiWardCenteredCoordinate
            (mobiusCriticalBoundaryParameter sigma u : ℂ)))
        (squarefreeMobiusGammaXiWardTransportV
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v)
          (u : ℂ))
        0) := by
  exact ⟨tendsto_norm_infiniteMobiusCriticalFisherTangentLp_sq,
    fun {_ _} hsigma hu =>
      inner_fisherTangent_damped_eq_squarefreeFisherScore hsigma hu,
    fun {_ _} hsigma hu =>
      hasDerivAt_xiWardAnchoredSourceTransportV_actualTangent hsigma hu⟩

end

end RHTower
