import GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHardyBoundarySaturation
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardCofinalBoundaryLift
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiTrueWienerHopfFactorization

/-!
# Graph-normal complement tangent and escaped Hardy mass

The singular Gamma/Xi graph-normal source and its Wiener--Hopf complement
have an exact division-free difference.  After division only by the
critical clock `sigma - 1`, the difference factors as the arithmetic source
overlap times the continued strict-right Ward response.  Consequently its
critical limit is rank one in the inward node:

`(1 + u)⁻¹ * continuedXiAntiCausalWardResponse (1 / 2)`.

The scalar coefficient at `1 / 2` vanishes exactly under RH.  Combined with
the sharp four-unit Hardy/Fisher saturation theorem, any positive boundary
law containing this graph-normal tangent forces that coefficient to vanish.
-/

open Complex Filter Set Topology
open scoped BigOperators ComplexOrder

noncomputable section

namespace RHTower

/-- Real inward Ward node attached to the Euler critical ray. -/
def mobiusGammaXiWardBoundaryNode (sigma u : ℝ) : ℂ :=
  ((eulerPositiveCriticalBoundaryParameter sigma u - 1 / 2 : ℝ) : ℂ)

/-- Critical arithmetic scale before graph normalization. -/
def mobiusGammaXiCriticalOverlapScale (sigma u : ℝ) : ℂ :=
  ((sigma - 1 : ℝ) : ℂ) *
    GaloisForLFunctions.squarefreeBoundaryOverlap
      (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ)

/-- Complementary graph-normal channel: zero-source affine base,
non-right Wiener--Hopf logarithmic derivative, and boundary self-symbol. -/
def mobiusGammaXiComplexHardyWardComplement
    (sigma u : ℝ) (hsigma : 1 < sigma) : ℂ :=
  mobiusGammaXiCriticalOverlapScale sigma u *
    (2 * I *
        mobiusGammaXiComplexHardyAffineSourceMap sigma hsigma (u : ℂ)
          (0 : lp (fun _ : ℕ => ℂ) 2) +
      2 * I * logDeriv xiNonrightCanonicalProduct
        (I * mobiusGammaXiWardBoundaryNode sigma u) -
      xiAntiCausalWardBoundarySelfSymbol)

/-- **Exact complement factorization.**  The actual graph-normal Fisher
source minus its complementary channel is precisely critical overlap scale
times the strict-right Ward response. -/
theorem mobiusGammaXiGraphNormalDifference_sub_complement
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    mobiusGammaXiComplexHardyGraphNormalDifference sigma hsigma (u : ℂ)
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma) 0 -
      mobiusGammaXiComplexHardyWardComplement sigma u hsigma =
    mobiusGammaXiCriticalOverlapScale sigma u *
      continuedXiAntiCausalWardResponse
        (mobiusGammaXiWardBoundaryNode sigma u) := by
  have hraw :=
    continuedXiAntiCausalWardResponse_eq_mobiusGraphSource_sub_complement
      hsigma hu
  dsimp only at hraw
  rw [mobiusGammaXiComplexHardyGraphNormalDifference]
  unfold mobiusGammaXiComplexHardyGraphNormalizer
    mobiusGammaXiComplexHardyWardComplement
    mobiusGammaXiCriticalOverlapScale
    mobiusGammaXiWardBoundaryNode
  rw [hraw]
  ring

/-- Graph-normal complement defect after removing only the critical clock,
not the arithmetic overlap. -/
def mobiusGammaXiClockNormalizedComplementDefect
    (sigma u : ℝ) (hsigma : 1 < sigma) : ℂ :=
  (mobiusGammaXiComplexHardyGraphNormalDifference sigma hsigma (u : ℂ)
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma) 0 -
      mobiusGammaXiComplexHardyWardComplement sigma u hsigma) /
    ((sigma - 1 : ℝ) : ℂ)

/-- Exact normalized profile before the critical limit. -/
theorem mobiusGammaXiClockNormalizedComplementDefect_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    mobiusGammaXiClockNormalizedComplementDefect sigma u hsigma =
      GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) *
        continuedXiAntiCausalWardResponse
          (mobiusGammaXiWardBoundaryNode sigma u) := by
  rw [mobiusGammaXiClockNormalizedComplementDefect,
    mobiusGammaXiGraphNormalDifference_sub_complement hsigma hu,
    mobiusGammaXiCriticalOverlapScale]
  have heps : ((sigma - 1 : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (sub_ne_zero.mpr hsigma.ne')
  field_simp [heps]

/-- The strict-right factor does not vanish on the Laplace image of a
right-half-plane Ward node. -/
theorem xiRightCanonicalProduct_I_mul_ne_zero_of_re_pos
    {w : ℂ} (hw : 0 < w.re) :
    xiRightCanonicalProduct (I * w) ≠ 0 := by
  intro hzero
  obtain ⟨q, hq⟩ :=
    (xiRightCanonicalProduct_eq_zero_iff_exists (I * w)).mp hzero
  have hright := q.2
  change xiSpectralPoint q.1 = I * w at hq
  rw [hq] at hright
  have hIIw : I * (I * w) = -w := by
    rw [← mul_assoc, I_mul_I, neg_one_mul]
  rw [hIIw] at hright
  simp only [neg_re] at hright
  linarith

/-- Away from the strict-right divisor, the totalized quotient agrees on a
whole neighborhood with the genuine entire complementary product. -/
theorem xiNonrightCanonicalProduct_eventuallyEq_trueComplement_of_ne
    {z : ℂ} (hz : xiRightCanonicalProduct z ≠ 0) :
    xiNonrightCanonicalProduct =ᶠ[nhds z]
      xiRightComplementCanonicalProduct := by
  have hright : ∀ᶠ w in nhds z, xiRightCanonicalProduct w ≠ 0 :=
    (xiRightCanonicalProduct_analytic z (Set.mem_univ _)).continuousAt.eventually_ne
      hz
  filter_upwards [hright] with w hw
  rw [xiNonrightCanonicalProduct,
    xiCanonicalProduct_eq_right_mul_trueComplement w]
  field_simp [hw]

/-- Hence their logarithmic derivatives agree at every regular
strict-right-factor point. -/
theorem logDeriv_xiNonrightCanonicalProduct_eq_trueComplement_of_ne
    {z : ℂ} (hz : xiRightCanonicalProduct z ≠ 0) :
    logDeriv xiNonrightCanonicalProduct z =
      logDeriv xiRightComplementCanonicalProduct z := by
  have h :=
    xiNonrightCanonicalProduct_eventuallyEq_trueComplement_of_ne hz
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.self_of_nhds]

/-- Source-canonical version of the complementary graph-normal channel,
using the genuine entire Wiener--Hopf complement rather than totalized
division. -/
def mobiusGammaXiComplexHardyTrueWardComplement
    (sigma u : ℝ) (hsigma : 1 < sigma) : ℂ :=
  mobiusGammaXiCriticalOverlapScale sigma u *
    (2 * I *
        mobiusGammaXiComplexHardyAffineSourceMap sigma hsigma (u : ℂ)
          (0 : lp (fun _ : ℕ => ℂ) 2) +
      2 * I * logDeriv xiRightComplementCanonicalProduct
        (I * mobiusGammaXiWardBoundaryNode sigma u) -
      xiAntiCausalWardBoundarySelfSymbol)

/-- On every safe Euler ray, old quotient notation and the genuine entire
complement give exactly the same graph-normal channel. -/
theorem mobiusGammaXiComplexHardyWardComplement_eq_true
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    mobiusGammaXiComplexHardyWardComplement sigma u hsigma =
      mobiusGammaXiComplexHardyTrueWardComplement sigma u hsigma := by
  have hnode : 0 < (mobiusGammaXiWardBoundaryNode sigma u).re := by
    rw [mobiusGammaXiWardBoundaryNode]
    simp only [ofReal_re]
    have hs := one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
    linarith
  have hright := xiRightCanonicalProduct_I_mul_ne_zero_of_re_pos hnode
  rw [mobiusGammaXiComplexHardyWardComplement,
    mobiusGammaXiComplexHardyTrueWardComplement,
    logDeriv_xiNonrightCanonicalProduct_eq_trueComplement_of_ne hright]

/-- Clock-normalized defect written with the genuine entire complement. -/
def mobiusGammaXiClockNormalizedTrueComplementDefect
    (sigma u : ℝ) (hsigma : 1 < sigma) : ℂ :=
  (mobiusGammaXiComplexHardyGraphNormalDifference sigma hsigma (u : ℂ)
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma) 0 -
      mobiusGammaXiComplexHardyTrueWardComplement sigma u hsigma) /
    ((sigma - 1 : ℝ) : ℂ)

/-- Exact normalized profile for the genuine complementary factor. -/
theorem mobiusGammaXiClockNormalizedTrueComplementDefect_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    mobiusGammaXiClockNormalizedTrueComplementDefect sigma u hsigma =
      GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) *
        continuedXiAntiCausalWardResponse
          (mobiusGammaXiWardBoundaryNode sigma u) := by
  rw [mobiusGammaXiClockNormalizedTrueComplementDefect,
    ← mobiusGammaXiComplexHardyWardComplement_eq_true hsigma hu]
  exact mobiusGammaXiClockNormalizedComplementDefect_eq hsigma hu

/-- The real critical Ward nodes converge to the Euler edge base node
`1 / 2`. -/
theorem tendsto_mobiusGammaXiWardBoundaryNode
    (u : ℝ) :
    Tendsto (fun j =>
      mobiusGammaXiWardBoundaryNode
        (soninMobiusCriticalSigmaSequence j) u)
      atTop (nhds (1 / 2 : ℂ)) := by
  have hsigma : Tendsto soninMobiusCriticalSigmaSequence atTop
      (nhds (1 : ℝ)) :=
    tendsto_soninMobiusCriticalSigmaSequence.mono_right inf_le_left
  have hreal : Tendsto (fun sigma : ℝ =>
      eulerPositiveCriticalBoundaryParameter sigma u - 1 / 2)
      (nhds 1) (nhds (1 / 2)) := by
    have hcont : ContinuousAt (fun sigma : ℝ =>
        sigma + u * (sigma - 1) - 1 / 2) 1 := by
      fun_prop
    convert hcont.tendsto using 1
    · rfl
    · norm_num
  have hpath := hreal.comp hsigma
  have hcast := (Complex.continuous_ofReal.tendsto (1 / 2)).comp hpath
  convert hcast using 1
  · rfl
  · norm_num

/-- Continued Ward response converges along every fixed real critical
source ray to its base-node value. -/
theorem tendsto_continuedXiAntiCausalWardResponse_criticalNode
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun j =>
      continuedXiAntiCausalWardResponse
        (mobiusGammaXiWardBoundaryNode
          (soninMobiusCriticalSigmaSequence j) u))
      atTop
      (nhds (continuedXiAntiCausalWardResponse (1 / 2 : ℂ))) := by
  let half : ℂ := 1 / 2
  have hhalf : 0 < half.re := by
    norm_num [half]
  have hprodHalf : xiRightCanonicalProduct (I * half) ≠ 0 :=
    xiRightCanonicalProduct_I_mul_ne_zero_of_re_pos hhalf
  have hanalytic : AnalyticAt ℂ xiRightCanonicalProduct (I * half) :=
    xiRightCanonicalProduct_analytic (I * half) (Set.mem_univ _)
  have hlogcont : ContinuousAt (logDeriv xiRightCanonicalProduct)
      (I * half) := by
    rw [show logDeriv xiRightCanonicalProduct =
      fun z => deriv xiRightCanonicalProduct z /
        xiRightCanonicalProduct z by rfl]
    exact hanalytic.deriv.continuousAt.div hanalytic.continuousAt hprodHalf
  have hnode := tendsto_mobiusGammaXiWardBoundaryNode u
  have hInode : Tendsto (fun j =>
      I * mobiusGammaXiWardBoundaryNode
        (soninMobiusCriticalSigmaSequence j) u)
      atTop (nhds (I * half)) := by
    simpa only using tendsto_const_nhds.mul hnode
  have hlog := hlogcont.tendsto.comp hInode
  have hcenterLog : Tendsto (fun j =>
      2 * I * logDeriv xiRightCanonicalProduct
        (I * mobiusGammaXiWardBoundaryNode
          (soninMobiusCriticalSigmaSequence j) u))
      atTop (nhds (2 * I * logDeriv xiRightCanonicalProduct (I * half))) :=
    tendsto_const_nhds.mul hlog
  have hcenter : Tendsto (fun j =>
      continuedXiCenteredAntiCausalWardResponse
        (mobiusGammaXiWardBoundaryNode
          (soninMobiusCriticalSigmaSequence j) u))
      atTop (nhds (continuedXiCenteredAntiCausalWardResponse half)) := by
    convert hcenterLog using 1
    · funext j
      rw [continuedXiCenteredAntiCausalWardResponse,
        ← logDeriv_xiRightCanonicalProduct_eq_relativeResolventTrace
          (xiRightCanonicalProduct_I_mul_ne_zero_of_re_pos (by
            rw [mobiusGammaXiWardBoundaryNode]
            simp only [ofReal_re]
            have hs := one_lt_eulerPositiveCriticalBoundaryParameter
              (soninMobiusCriticalSigmaSequence_gt_one j) hu
            linarith))]
    · rw [continuedXiCenteredAntiCausalWardResponse,
        ← logDeriv_xiRightCanonicalProduct_eq_relativeResolventTrace hprodHalf]
  have hward := hcenter.add_const xiAntiCausalWardBoundarySelfSymbol
  simpa only [continuedXiAntiCausalWardResponse, half] using hward

/-- **Rank-one critical tangent law.**  The complete graph-normal
source/complement defect has universal escaped-mass profile `(1 + u)⁻¹`;
all Xi-divisor information is concentrated in one scalar Ward value. -/
theorem tendsto_mobiusGammaXiClockNormalizedComplementDefect
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun j =>
      mobiusGammaXiClockNormalizedTrueComplementDefect
        (soninMobiusCriticalSigmaSequence j) u
        (soninMobiusCriticalSigmaSequence_gt_one j))
      atTop
      (nhds (mobiusCriticalUniversalHardyMassProfile (u : ℂ) *
        continuedXiAntiCausalWardResponse (1 / 2 : ℂ))) := by
  have hoverlap :=
    (tendsto_squarefreeBoundaryOverlap_complexCritical
      (u := (u : ℂ)) (by simpa using hu)).comp
        tendsto_soninMobiusCriticalSigmaSequence
  have hward :=
    tendsto_continuedXiAntiCausalWardResponse_criticalNode hu
  have hmul := hoverlap.mul hward
  simpa [mobiusCriticalUniversalHardyMassProfile] using
    hmul.congr' (Filter.Eventually.of_forall fun j =>
      (mobiusGammaXiClockNormalizedTrueComplementDefect_eq
        (soninMobiusCriticalSigmaSequence_gt_one j) hu).symm)

/-- Failure of RH makes the Ward response strictly positive in real part
already at the fixed base node `1 / 2`; no zero-adapted moving node is
needed for detection. -/
theorem re_continuedXiAntiCausalWardResponse_half_pos_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    0 < (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re := by
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  have hw : 0 < ((1 / 2 : ℂ)).re := by norm_num
  have hsum := summable_xiAntiCausalWardSchwarzPairResponse hw
  have hreal : Summable (fun p : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse p (1 / 2 : ℂ)).re) := by
    simpa only [Complex.reCLM_apply] using hsum.mapL Complex.reCLM
  have hselected :
      (xiAntiCausalWardSchwarzPairResponse q (1 / 2 : ℂ)).re ≤
        ∑' p : XiRightUpperZeroCopy,
          (xiAntiCausalWardSchwarzPairResponse p (1 / 2 : ℂ)).re := by
    have hle := hreal.sum_le_tsum ({q} : Finset XiRightUpperZeroCopy)
      (fun p _ =>
        (re_xiAntiCausalWardSchwarzPairResponse_pos p hw).le)
    simpa only [Finset.sum_singleton] using hle
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
    Complex.re_tsum hsum]
  exact lt_of_lt_of_le
    (re_xiAntiCausalWardSchwarzPairResponse_pos q hw) hselected

/-- Fixed-node scalar classification exposed by the graph-normal tangent. -/
theorem continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh :
    continuedXiAntiCausalWardResponse (1 / 2 : ℂ) = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    have hpos :=
      re_continuedXiAntiCausalWardResponse_half_pos_of_not_rh hRH
    rw [hzero] at hpos
    simp at hpos
  · intro hRH
    exact continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis
      hRH (by norm_num)

/-- Exact reduction of the remaining Route-P producer.  Positivity of the
fixed-four boundary block containing the graph-normal mass coefficient on
only the canonical two-node packets already proves RH. -/
theorem riemannHypothesis_of_twoNode_graphNormalMassBoundaryPositivity
    (hpos : ∀ t : ℝ, 0 < t →
      (mobiusCriticalUniversalHardyFisherMassPerturbedGram
        (mobiusCriticalHardySaturationNodes t)
        (continuedXiAntiCausalWardResponse (1 / 2 : ℂ))).PosSemidef) :
    RiemannHypothesis := by
  apply continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mp
  exact
    eq_zero_of_all_twoNode_mobiusCriticalHardyFisherMassPerturbed_posSemidef
      hpos

end RHTower
