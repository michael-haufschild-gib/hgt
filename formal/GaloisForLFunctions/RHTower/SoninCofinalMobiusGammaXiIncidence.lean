import GaloisForLFunctions.RHTower.SoninCofinalGlobalEulerCarrier
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardJuliaTransport
import GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscape

/-!
# Cofinal Sonin incidence for the Möbius--Gamma--Xi current

The critical Möbius Fisher vector escapes every fixed compact divisor
window.  The singular Gamma graph simultaneously divides its codiagonal by
the vanishing normal parameter `sigma - 1`.  Ordinary strong convergence is
therefore insufficient.

This file applies the singular codiagonal transport law to the actual
Möbius Fisher two-jet.  For every sequence `sigma n -> 1+`, one strictly
cofinal family of genuine Sonin dilation corners transports both moving
vectors so accurately that their codiagonal error remains negligible after
the complete singular Gamma overlap division.  Substitution into the exact
Gamma weld then reconstructs the continued Xi source trace.

The conclusion is prelimit and noncompact.  No critical source vector,
finite-rank truncation, compact synthesis, inverse Sonin map, or divisor
postselection is used.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-- Continued Xi current obtained by replacing the Möbius Fisher numerator
with the codiagonal of the actual cofinal Sonin images. -/
def soninCofinalMobiusGammaXiWardTransport
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (sigma : ℕ → ℝ) (hsigma : ∀ n, 1 < sigma n)
    (u : ℝ) (hu : 0 ≤ u) (depth : ℕ → ℕ) (n : ℕ) : ℂ :=
  let corner :=
    crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a
  let fisher :=
    infiniteMobiusCriticalFisherTangentLp (sigma n) (hsigma n)
  let damped :=
    infiniteMobiusCriticalDampedSignedWeightLp
      (sigma n) u (hsigma n) hu
  let transportedScore :=
    inner ℂ
      (corner
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) fisher))
      (corner
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) damped))
  squarefreeMobiusGammaXiWardTransportV
    (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
    (fun _ => transportedScore) (u : ℂ)

/-- **Cofinal Möbius--Sonin--Gamma incidence law.**  Along every approach to
the critical Euler boundary, one strictly increasing shell schedule carries
the actual moving Fisher/damped-source codiagonal through the singular Gamma
overlap and reconstructs the full continued Xi trace with vanishing error.

The schedule is shared by both legs, may follow unbounded moving vectors,
and uses the original bounded noncompact Sonin corner. -/
theorem exists_soninCofinalMobiusGammaXiWardTransport
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (sigma : ℕ → ℝ) (hsigma : ∀ n, 1 < sigma n)
    (hsigmaOne : Tendsto sigma atTop (𝓝 1))
    (u : ℝ) (hu : 0 ≤ u) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        soninCofinalMobiusGammaXiWardTransport
            a c d r hc hcd hr sigma hsigma u hu depth n -
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate
              (mobiusCriticalBoundaryParameter (sigma n) u : ℂ)))
        atTop (𝓝 0) := by
  let fisher : ℕ → lp (fun _ : ℕ => ℂ) 2 :=
    fun n => infiniteMobiusCriticalFisherTangentLp (sigma n) (hsigma n)
  let damped : ℕ → lp (fun _ : ℕ => ℂ) 2 :=
    fun n => infiniteMobiusCriticalDampedSignedWeightLp
      (sigma n) u (hsigma n) hu
  let epsilon : ℕ → ℝ := fun n => sigma n - 1
  have hepsilon (n : ℕ) : 0 < epsilon n := by
    exact sub_pos.mpr (hsigma n)
  have hepsilonZero : Tendsto epsilon atTop (𝓝 0) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa only [epsilon, sub_self] using hsigmaOne.sub hone
  obtain ⟨depth, hdepth, _hfather, _hdetail, hcodiagonal⟩ :=
    exists_centralSoninDilationCorner_singularDiagonal_pair_codiagonal
      a c d r ha hc hcd hda hr harc fisher damped epsilon
      hepsilon hepsilonZero
  refine ⟨depth, hdepth, ?_⟩
  let corner : SoninL2 →L[ℂ] SoninL2 :=
    crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a
  let transportedScore : ℕ → ℂ := fun n =>
    inner ℂ
      (corner
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) (fisher n)))
      (corner
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) (damped n)))
  let sourceScore : ℕ → ℂ := fun n =>
    inner ℂ (fisher n) (damped n)
  have hnormal : Tendsto (fun n =>
      (transportedScore n - sourceScore n) /
        ((epsilon n : ℝ) : ℂ))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert hcodiagonal using 1
    funext n
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hepsilon n)]
  have hsigmaWithin :
      Tendsto sigma atTop (𝓝[>] (1 : ℝ)) := by
    change Tendsto sigma atTop
      (𝓝 (1 : ℝ) ⊓ Filter.principal (Set.Ioi 1))
    rw [tendsto_inf]
    exact ⟨hsigmaOne,
      tendsto_principal.mpr (Filter.Eventually.of_forall hsigma)⟩
  have hoverlap :
      Tendsto (fun n =>
        squarefreeMobiusBoundaryLayerLaplace (sigma n) u)
        atTop (𝓝 ((((1 + u : ℝ) : ℂ))⁻¹)) :=
    (tendsto_squarefreeMobiusBoundaryLayerLaplace hu).comp hsigmaWithin
  have hoverlapNe : ((((1 + u : ℝ) : ℂ))⁻¹) ≠ 0 := by
    exact inv_ne_zero
      (Complex.ofReal_ne_zero.mpr (by nlinarith))
  have hgraph := hnormal.div hoverlap hoverlapNe
  have hgraph' : Tendsto (fun n =>
      (transportedScore n - sourceScore n) /
        (((epsilon n : ℝ) : ℂ) *
          squarefreeMobiusBoundaryLayerLaplace (sigma n) u))
      atTop (𝓝 0) := by
    have hgraphZero : Tendsto
        ((fun n => (transportedScore n - sourceScore n) /
            ((epsilon n : ℝ) : ℂ)) /
          fun n => squarefreeMobiusBoundaryLayerLaplace (sigma n) u)
        atTop (𝓝 0) := by
      simpa using hgraph
    apply hgraphZero.congr'
    filter_upwards with n
    rw [Pi.div_apply, div_div]
  have htransportDifference : Tendsto (fun n =>
      soninCofinalMobiusGammaXiWardTransport
          a c d r hc hcd hr sigma hsigma u hu depth n -
        squarefreeMobiusGammaXiWardTransportV
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
          (u : ℂ))
      atTop (𝓝 0) := by
    have hscaled : Tendsto (fun n =>
        (I / 2) *
          ((transportedScore n - sourceScore n) /
            (((epsilon n : ℝ) : ℂ) *
              squarefreeMobiusBoundaryLayerLaplace (sigma n) u)))
        atTop (𝓝 0) := by
      simpa using hgraph'.const_mul (I / 2)
    convert hscaled using 1
    funext n
    rw [squarefreeMobiusBoundaryLayerLaplace_eq_squarefreeBoundaryOverlap
      (hsigma n) hu]
    rw [show sourceScore n =
        GaloisForLFunctions.squarefreeFisherScore
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u : ℂ) by
      exact inner_fisherTangent_damped_eq_squarefreeFisherScore
        (hsigma n) hu]
    simp only [soninCofinalMobiusGammaXiWardTransport,
      transportedScore, fisher, damped, corner,
      squarefreeMobiusGammaXiWardTransportV,
      squarefreeMobiusGammaCurrentTransportV]
    ring
  apply htransportDifference.congr'
  filter_upwards with n
  rw [squarefreeMobiusGammaXiWardTransportV_actualTangent
    (hsigma n) hu]

/-! ## Double-singular incidence at a fixed Euler point -/

/-- Cofinal normal coordinate which keeps a prescribed Euler point `s > 1`
fixed while the Möbius source approaches its critical boundary. -/
def fixedEulerCofinalSigma (s : ℝ) (n : ℕ) : ℝ :=
  1 + (s - 1) / ((n : ℝ) + 1)

/-- Tangential speed paired with `fixedEulerCofinalSigma`.  It diverges
cofinally, exactly compensating collapse of the normal coordinate. -/
def fixedEulerCofinalDamping (n : ℕ) : ℝ :=
  n

theorem fixedEulerCofinalSigma_gt_one
    {s : ℝ} (hs : 1 < s) (n : ℕ) :
    1 < fixedEulerCofinalSigma s n := by
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hquot : 0 < (s - 1) / ((n : ℝ) + 1) :=
    div_pos (sub_pos.mpr hs) hden
  simp only [fixedEulerCofinalSigma]
  linarith

theorem fixedEulerCofinalDamping_nonneg (n : ℕ) :
    0 ≤ fixedEulerCofinalDamping n := by
  simpa only [fixedEulerCofinalDamping] using (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

@[simp] theorem fixedEulerCofinal_boundaryParameter
    (s : ℝ) (n : ℕ) :
    mobiusCriticalBoundaryParameter
        (fixedEulerCofinalSigma s n) (fixedEulerCofinalDamping n) = s := by
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [mobiusCriticalBoundaryParameter, fixedEulerCofinalSigma,
    fixedEulerCofinalDamping]
  field_simp
  ring

theorem tendsto_fixedEulerCofinalSigma (s : ℝ) :
    Tendsto (fixedEulerCofinalSigma s) atTop (𝓝 1) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hzero :
      Tendsto (fun n : ℕ => (s - 1) * (1 / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (s - 1)
  simpa only [fixedEulerCofinalSigma, div_eq_mul_inv, one_mul, add_zero] using!
    hone.add hzero

theorem tendsto_fixedEulerCofinalSigma_nhdsWithin
    {s : ℝ} (hs : 1 < s) :
    Tendsto (fixedEulerCofinalSigma s) atTop (𝓝[>] (1 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_fixedEulerCofinalSigma s,
    Filter.Eventually.of_forall (fixedEulerCofinalSigma_gt_one hs)⟩

/-- Moving-parameter version of the cofinal Sonin--Gamma transport. -/
def soninCofinalMobiusGammaXiWardMovingTransport
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (sigma : ℕ → ℝ) (hsigma : ∀ n, 1 < sigma n)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (depth : ℕ → ℕ) (n : ℕ) : ℂ :=
  let corner :=
    crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a
  let fisher :=
    infiniteMobiusCriticalFisherTangentLp (sigma n) (hsigma n)
  let damped :=
    infiniteMobiusCriticalDampedSignedWeightLp
      (sigma n) (u n) (hsigma n) (hu n)
  let transportedScore :=
    inner ℂ
      (corner
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) fisher))
      (corner
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) damped))
  squarefreeMobiusGammaXiWardTransportV
    (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
    (fun _ => transportedScore) (u n : ℂ)

/-- Sonin--Gamma transport on the exact double-singular path to a fixed
Euler point. -/
def soninCofinalMobiusGammaXiWardFixedEulerTransport
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (s : ℝ) (hs : 1 < s) (depth : ℕ → ℕ) (n : ℕ) : ℂ :=
  soninCofinalMobiusGammaXiWardMovingTransport
    a c d r hc hcd hr
    (fixedEulerCofinalSigma s) (fixedEulerCofinalSigma_gt_one hs)
    fixedEulerCofinalDamping fixedEulerCofinalDamping_nonneg depth n

/-- **Fixed-Euler double-singular Sonin incidence law.**  Every Euler point
`s > 1`, not merely the collapsing point `s = 1`, is reconstructed by one
strictly cofinal family of genuine Sonin dilation corners.

The normal coordinate tends to the critical boundary while the tangential
speed diverges.  Their product fixes `s` exactly.  The shell schedule tracks
the smaller complete graph scale
`(sigma - 1) * squarefreeMobiusTotal s / squarefreeMobiusTotal sigma`,
so no boundedness assumption on the moving damped source is used. -/
theorem exists_soninCofinalMobiusGammaXiWardFixedEulerTransport
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (s : ℝ) (hs : 1 < s) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        soninCofinalMobiusGammaXiWardFixedEulerTransport
            a c d r hc hcd hr s hs depth n -
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate (s : ℂ)))
        atTop (𝓝 0) := by
  let sigma : ℕ → ℝ := fixedEulerCofinalSigma s
  let u : ℕ → ℝ := fixedEulerCofinalDamping
  have hsigma (n : ℕ) : 1 < sigma n :=
    fixedEulerCofinalSigma_gt_one hs n
  have hu (n : ℕ) : 0 ≤ u n :=
    fixedEulerCofinalDamping_nonneg n
  let fisher : ℕ → lp (fun _ : ℕ => ℂ) 2 :=
    fun n => infiniteMobiusCriticalFisherTangentLp (sigma n) (hsigma n)
  let damped : ℕ → lp (fun _ : ℕ => ℂ) 2 :=
    fun n => infiniteMobiusCriticalDampedSignedWeightLp
      (sigma n) (u n) (hsigma n) (hu n)
  let graphScale : ℕ → ℝ := fun n =>
    (sigma n - 1) *
      (squarefreeMobiusTotal s / squarefreeMobiusTotal (sigma n))
  have hgraphScale (n : ℕ) : 0 < graphScale n := by
    exact mul_pos (sub_pos.mpr (hsigma n))
      (div_pos (squarefreeMobiusTotal_pos hs)
        (squarefreeMobiusTotal_pos (hsigma n)))
  have hsigmaWithin :
      Tendsto sigma atTop (𝓝[>] (1 : ℝ)) := by
    simpa only [sigma] using tendsto_fixedEulerCofinalSigma_nhdsWithin hs
  have hinvTotal :
      Tendsto (fun n => (squarefreeMobiusTotal (sigma n))⁻¹)
        atTop (𝓝 0) :=
    (tendsto_inv_squarefreeMobiusTotal_zero).comp hsigmaWithin
  have hratio :
      Tendsto (fun n =>
        squarefreeMobiusTotal s / squarefreeMobiusTotal (sigma n))
        atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hinvTotal.const_mul (squarefreeMobiusTotal s)
  have hsigmaOne : Tendsto sigma atTop (𝓝 1) :=
    hsigmaWithin.mono_right inf_le_left
  have hnormal :
      Tendsto (fun n => sigma n - 1) atTop (𝓝 0) := by
    simpa using hsigmaOne.sub_const 1
  have hgraphScaleZero :
      Tendsto graphScale atTop (𝓝 0) := by
    simpa only [graphScale, zero_mul] using hnormal.mul hratio
  obtain ⟨depth, hdepth, _hfisher, _hdamped, hcodiagonal⟩ :=
    exists_centralSoninDilationCorner_singularDiagonal_pair_codiagonal
      a c d r ha hc hcd hda hr harc fisher damped graphScale
      hgraphScale hgraphScaleZero
  refine ⟨depth, hdepth, ?_⟩
  let corner : SoninL2 →L[ℂ] SoninL2 :=
    crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a
  let transportedScore : ℕ → ℂ := fun n =>
    inner ℂ
      (corner
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) (fisher n)))
      (corner
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) (damped n)))
  let sourceScore : ℕ → ℂ := fun n =>
    inner ℂ (fisher n) (damped n)
  have hnormalized : Tendsto (fun n =>
      (transportedScore n - sourceScore n) /
        ((graphScale n : ℝ) : ℂ))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert hcodiagonal using 1
    funext n
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hgraphScale n)]
  have hoverlap (n : ℕ) :
      squarefreeMobiusBoundaryLayerLaplace (sigma n) (u n) =
        (squarefreeMobiusTotal s : ℂ) /
          (squarefreeMobiusTotal (sigma n) : ℂ) := by
    simp only [squarefreeMobiusBoundaryLayerLaplace,
      sigma, u, fixedEulerCofinal_boundaryParameter]
  have htransportDifference : Tendsto (fun n =>
      soninCofinalMobiusGammaXiWardMovingTransport
          a c d r hc hcd hr sigma hsigma u hu depth n -
        squarefreeMobiusGammaXiWardTransportV
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
          (u n : ℂ))
      atTop (𝓝 0) := by
    have hscaled : Tendsto (fun n =>
        (I / 2) *
          ((transportedScore n - sourceScore n) /
            ((graphScale n : ℝ) : ℂ)))
        atTop (𝓝 0) := by
      simpa using hnormalized.const_mul (I / 2)
    convert hscaled using 1
    funext n
    rw [show sourceScore n =
        GaloisForLFunctions.squarefreeFisherScore
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u n : ℂ) by
      exact inner_fisherTangent_damped_eq_squarefreeFisherScore
        (hsigma n) (hu n)]
    simp only [graphScale, Complex.ofReal_mul, Complex.ofReal_div]
    rw [← hoverlap n]
    simp only [soninCofinalMobiusGammaXiWardMovingTransport,
      transportedScore, fisher, damped, corner,
      squarefreeMobiusGammaXiWardTransportV,
      squarefreeMobiusGammaCurrentTransportV]
    rw [squarefreeMobiusBoundaryLayerLaplace_eq_squarefreeBoundaryOverlap
      (hsigma n) (hu n)]
    ring
  have hexact : Tendsto (fun n =>
      squarefreeMobiusGammaXiWardTransportV
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
          (u n : ℂ) -
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate (s : ℂ)))
      atTop (𝓝 0) := by
    have hzero : (fun n =>
        squarefreeMobiusGammaXiWardTransportV
            (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
            (u n : ℂ) -
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate (s : ℂ))) = fun _ => 0 := by
      funext n
      rw [squarefreeMobiusGammaXiWardTransportV_actualTangent
        (hsigma n) (hu n)]
      simp only [sigma, u, fixedEulerCofinal_boundaryParameter, sub_self]
    rw [hzero]
    exact tendsto_const_nhds
  have hsum := htransportDifference.add hexact
  have hsigmaProof :
      hsigma = fixedEulerCofinalSigma_gt_one hs :=
    Subsingleton.elim _ _
  have huProof :
      hu = fixedEulerCofinalDamping_nonneg :=
    Subsingleton.elim _ _
  simpa only [soninCofinalMobiusGammaXiWardFixedEulerTransport,
    sigma, u, hsigmaProof, huProof, sub_add_sub_cancel, zero_add] using hsum

end RHTower
