import GaloisForLFunctions.RHTower.SoninCofinalContractiveInwardIncidence
import GaloisForLFunctions.RHTower.SoninCofinalMobiusGammaXiIncidence

/-!
# Contractive cofinal Sonin incidence for the Möbius--Gamma--Xi current

The existing cofinal Sonin--Gamma incidence uses the self-adjoint dilation
sum, whose operator norm has only a two-unit ceiling.  This module replaces it
by the oriented inward Sonin corner `(1 - Q) U_r Q`, which is a genuine
contraction.

The contractive corner retains arbitrary moving Möbius Fisher two-jets and
their codiagonal through the complete singular Gamma scale.  It therefore
reconstructs every fixed safe Euler coordinate of the continued Xi source
without sacrificing the norm-one carrier bound.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-- Continued Xi current obtained from the actual contractive inward Sonin
corner on a moving Möbius Fisher two-jet. -/
def soninContractiveCofinalMobiusGammaXiWardMovingTransport
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (sigma : ℕ → ℝ) (hsigma : ∀ n, 1 < sigma n)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (depth : ℕ → ℕ) (n : ℕ) : ℂ :=
  let fisher :=
    infiniteMobiusCriticalFisherTangentLp (sigma n) (hsigma n)
  let damped :=
    infiniteMobiusCriticalDampedSignedWeightLp
      (sigma n) (u n) (hsigma n) (hu n)
  let transportedScore :=
    inner ℂ
      (centralSoninInwardDilationCorner a r hr
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) fisher))
      (centralSoninInwardDilationCorner a r hr
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) damped))
  squarefreeMobiusGammaXiWardTransportV
    (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
    (fun _ => transportedScore) (u n : ℂ)

/-- Generic singular normal-coordinate form of the contractive inward
Sonin--Gamma incidence. -/
theorem exists_soninContractiveCofinalMobiusGammaXiWardMovingTransport
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (sigma : ℕ → ℝ) (hsigma : ∀ n, 1 < sigma n)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hgraphScaleZero : Tendsto (fun n =>
      (sigma n - 1) *
        (squarefreeMobiusTotal
            (mobiusCriticalBoundaryParameter (sigma n) (u n)) /
          squarefreeMobiusTotal (sigma n)))
      atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        soninContractiveCofinalMobiusGammaXiWardMovingTransport
            a c d r hc hcd hr sigma hsigma u hu depth n -
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate
              (mobiusCriticalBoundaryParameter
                (sigma n) (u n) : ℂ)))
        atTop (𝓝 0) := by
  let fisher : ℕ → lp (fun _ : ℕ => ℂ) 2 :=
    fun n => infiniteMobiusCriticalFisherTangentLp (sigma n) (hsigma n)
  let damped : ℕ → lp (fun _ : ℕ => ℂ) 2 :=
    fun n => infiniteMobiusCriticalDampedSignedWeightLp
      (sigma n) (u n) (hsigma n) (hu n)
  let graphScale : ℕ → ℝ := fun n =>
    (sigma n - 1) *
      (squarefreeMobiusTotal
          (mobiusCriticalBoundaryParameter (sigma n) (u n)) /
        squarefreeMobiusTotal (sigma n))
  have hgraphScale (n : ℕ) : 0 < graphScale n := by
    exact mul_pos (sub_pos.mpr (hsigma n))
      (div_pos
        (squarefreeMobiusTotal_pos
          (by
            have hprod :
                0 ≤ u n * (sigma n - 1) :=
              mul_nonneg (hu n)
                (sub_nonneg.mpr (hsigma n).le)
            have hs := hsigma n
            unfold mobiusCriticalBoundaryParameter
            linarith))
        (squarefreeMobiusTotal_pos (hsigma n)))
  obtain ⟨depth, hdepth, _hfather, _hdetail, hcodiagonal⟩ :=
    exists_centralSoninInwardDilationCorner_singularDiagonal_pair_codiagonal
      a c d r ha hc hcd hda hr harc fisher damped graphScale
      hgraphScale hgraphScaleZero
  refine ⟨depth, hdepth, ?_⟩
  let transportedScore : ℕ → ℂ := fun n =>
    inner ℂ
      (centralSoninInwardDilationCorner a r hr
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) (fisher n)))
      (centralSoninInwardDilationCorner a r hr
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
        (squarefreeMobiusTotal
            (mobiusCriticalBoundaryParameter (sigma n) (u n)) : ℂ) /
          (squarefreeMobiusTotal (sigma n) : ℂ) := by
    rfl
  have htransportDifference : Tendsto (fun n =>
      soninContractiveCofinalMobiusGammaXiWardMovingTransport
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
    simp only [soninContractiveCofinalMobiusGammaXiWardMovingTransport,
      transportedScore, fisher, damped,
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
          (xiWardCenteredCoordinate
            (mobiusCriticalBoundaryParameter (sigma n) (u n) : ℂ)))
      atTop (𝓝 0) := by
    have hzero : (fun n =>
        squarefreeMobiusGammaXiWardTransportV
            (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
            (u n : ℂ) -
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate
              (mobiusCriticalBoundaryParameter
                (sigma n) (u n) : ℂ))) = fun _ => 0 := by
      funext n
      rw [squarefreeMobiusGammaXiWardTransportV_actualTangent
        (hsigma n) (hu n)]
      simp
    rw [hzero]
    exact tendsto_const_nhds
  simpa only [sub_add_sub_cancel, zero_add] using
    htransportDifference.add hexact

/-- Contractive inward Sonin--Gamma transport on the exact double-singular
path to one fixed safe Euler point. -/
def soninContractiveCofinalMobiusGammaXiWardFixedEulerTransport
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (s : ℝ) (hs : 1 < s) (depth : ℕ → ℕ) (n : ℕ) : ℂ :=
  soninContractiveCofinalMobiusGammaXiWardMovingTransport
    a c d r hc hcd hr
    (fixedEulerCofinalSigma s) (fixedEulerCofinalSigma_gt_one hs)
    fixedEulerCofinalDamping fixedEulerCofinalDamping_nonneg depth n

/-- Every safe Euler point has a strictly cofinal norm-one inward Sonin
incidence reconstructing its continued Xi source coordinate. -/
theorem exists_soninContractiveCofinalMobiusGammaXiWardFixedEulerTransport
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (s : ℝ) (hs : 1 < s) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        soninContractiveCofinalMobiusGammaXiWardFixedEulerTransport
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
  have hsigmaWithin :
      Tendsto sigma atTop (𝓝[>] (1 : ℝ)) := by
    simpa only [sigma] using tendsto_fixedEulerCofinalSigma_nhdsWithin hs
  have hinvTotal :
      Tendsto (fun n => (squarefreeMobiusTotal (sigma n))⁻¹)
        atTop (𝓝 0) :=
    (tendsto_inv_squarefreeMobiusTotal_zero).comp hsigmaWithin
  have hratio :
      Tendsto (fun n =>
        squarefreeMobiusTotal
            (mobiusCriticalBoundaryParameter (sigma n) (u n)) /
          squarefreeMobiusTotal (sigma n))
        atTop (𝓝 0) := by
    have hfixed (n : ℕ) :
        mobiusCriticalBoundaryParameter (sigma n) (u n) = s := by
      exact fixedEulerCofinal_boundaryParameter s n
    have hrewrite :
        (fun n =>
          squarefreeMobiusTotal
              (mobiusCriticalBoundaryParameter (sigma n) (u n)) /
            squarefreeMobiusTotal (sigma n)) =
          fun n => squarefreeMobiusTotal s *
            (squarefreeMobiusTotal (sigma n))⁻¹ := by
      funext n
      rw [hfixed]
      simp [div_eq_mul_inv]
    rw [hrewrite]
    simpa using hinvTotal.const_mul (squarefreeMobiusTotal s)
  have hsigmaOne : Tendsto sigma atTop (𝓝 1) :=
    hsigmaWithin.mono_right inf_le_left
  have hnormal :
      Tendsto (fun n => sigma n - 1) atTop (𝓝 0) := by
    simpa using hsigmaOne.sub_const 1
  have hgraphScaleZero :
      Tendsto (fun n =>
        (sigma n - 1) *
          (squarefreeMobiusTotal
              (mobiusCriticalBoundaryParameter (sigma n) (u n)) /
            squarefreeMobiusTotal (sigma n)))
        atTop (𝓝 0) := by
    simpa only [zero_mul] using hnormal.mul hratio
  obtain ⟨depth, hdepth, hlimit⟩ :=
    exists_soninContractiveCofinalMobiusGammaXiWardMovingTransport
      a c d r ha hc hcd hda hr harc sigma hsigma u hu hgraphScaleZero
  refine ⟨depth, hdepth, ?_⟩
  simpa only [soninContractiveCofinalMobiusGammaXiWardFixedEulerTransport,
    sigma, u, fixedEulerCofinal_boundaryParameter] using hlimit

end RHTower
