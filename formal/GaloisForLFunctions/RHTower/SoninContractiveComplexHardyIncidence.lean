import GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHardySource
import GaloisForLFunctions.RHTower.SoninCofinalContractiveInwardIncidence
import GaloisForLFunctions.RHTower.SoninCofinalMobiusGammaXiIncidence

/-!
# Contractive Sonin incidence at complex Hardy nodes

The actual phase-damped Möbius source is transported through one contractive inward Sonin corner.
Reporter norm is independent of imaginary displacement and shell depth.  For arbitrary moving
complex Hardy nodes, a single cofinal schedule reconstructs the continued Xi source whenever its
exact singular Gamma graph scale tends to zero.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

def soninContractiveCofinalMobiusGammaXiWardComplexMovingTransport
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (sigma : ℕ → ℝ) (hsigma : ∀ n, 1 < sigma n)
    (u : ℕ → ℂ) (hu : ∀ n, 0 ≤ (u n).re)
    (depth : ℕ → ℕ) (n : ℕ) : ℂ :=
  let fisher :=
    infiniteMobiusCriticalFisherTangentLp (sigma n) (hsigma n)
  let damped :=
    infiniteMobiusCriticalComplexDampedSignedWeightLp
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
    (fun _ => transportedScore) (u n)

/-- Independent-quadrant control: the contractive Sonin reporter is uniformly bounded by the
Fisher-leg norm, with no dependence on imaginary displacement or shell depth. -/
theorem norm_soninContractive_complexHardyFisherReporter_le
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (N : ℕ) {sigma : ℝ} {u : ℂ}
    (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    ‖inner ℂ
        (centralSoninInwardDilationCorner a r hr
          (cofinalInverseDilatedShellEmbedding c d r hc hcd hr N
            (infiniteMobiusCriticalFisherTangentLp sigma hsigma)))
        (centralSoninInwardDilationCorner a r hr
          (cofinalInverseDilatedShellEmbedding c d r hc hcd hr N
            (infiniteMobiusCriticalComplexDampedSignedWeightLp
              sigma u hsigma hu)))‖ ≤
      ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ := by
  have hf := norm_centralSoninInwardDilationCorner_cofinalEmbedding_le
    a c d r hc hcd hr N
    (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
  have hd := norm_centralSoninInwardDilationCorner_cofinalEmbedding_le
    a c d r hc hcd hr N
    (infiniteMobiusCriticalComplexDampedSignedWeightLp sigma u hsigma hu)
  calc
    _ ≤
        ‖centralSoninInwardDilationCorner a r hr
          (cofinalInverseDilatedShellEmbedding c d r hc hcd hr N
            (infiniteMobiusCriticalFisherTangentLp sigma hsigma))‖ *
        ‖centralSoninInwardDilationCorner a r hr
          (cofinalInverseDilatedShellEmbedding c d r hc hcd hr N
            (infiniteMobiusCriticalComplexDampedSignedWeightLp
              sigma u hsigma hu))‖ := norm_inner_le_norm _ _
    _ ≤ ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ *
          ‖infiniteMobiusCriticalComplexDampedSignedWeightLp
            sigma u hsigma hu‖ :=
      mul_le_mul hf hd (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_infiniteMobiusCriticalComplexDampedSignedWeightLp_le_one
          hsigma hu)
        (norm_nonneg _)
    _ = _ := mul_one _

/-- Complex moving-node contractive Sonin incidence at the exact Gamma graph scale. -/
theorem exists_soninContractiveCofinalMobiusGammaXiWardComplexMovingTransport
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (sigma : ℕ → ℝ) (hsigma : ∀ n, 1 < sigma n)
    (u : ℕ → ℂ) (hu : ∀ n, 0 ≤ (u n).re)
    (hshift : ∀ n,
      1 < ((sigma n : ℂ) + u n * ((sigma n - 1 : ℝ) : ℂ)).re)
    (hgraphScaleZero : Tendsto (fun n =>
      ‖((sigma n - 1 : ℝ) : ℂ) *
        GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u n)‖)
      atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fun n =>
        soninContractiveCofinalMobiusGammaXiWardComplexMovingTransport
            a c d r hc hcd hr sigma hsigma u hu depth n -
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate
              ((sigma n : ℂ) +
                u n * ((sigma n - 1 : ℝ) : ℂ))))
        atTop (𝓝 0) := by
  let fisher : ℕ → lp (fun _ : ℕ => ℂ) 2 :=
    fun n => infiniteMobiusCriticalFisherTangentLp (sigma n) (hsigma n)
  let damped : ℕ → lp (fun _ : ℕ => ℂ) 2 :=
    fun n => infiniteMobiusCriticalComplexDampedSignedWeightLp
      (sigma n) (u n) (hsigma n) (hu n)
  let graphScale : ℕ → ℝ := fun n =>
    ‖((sigma n - 1 : ℝ) : ℂ) *
      GaloisForLFunctions.squarefreeBoundaryOverlap
        (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u n)‖
  have hgraphScale (n : ℕ) : 0 < graphScale n := by
    apply norm_pos_iff.mpr
    apply mul_ne_zero
    · exact_mod_cast sub_ne_zero.mpr (hsigma n).ne'
    · simp only [GaloisForLFunctions.squarefreeBoundaryOverlap]
      exact div_ne_zero
        (GaloisForLFunctions.squarefreePartition_ne_zero (hshift n))
        (GaloisForLFunctions.squarefreePartition_ne_zero
          (by simpa using hsigma n))
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
        (((sigma n - 1 : ℝ) : ℂ) *
          GaloisForLFunctions.squarefreeBoundaryOverlap
            (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u n)))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert hcodiagonal using 1
    funext n
    rw [norm_div]
  have htransportDifference : Tendsto (fun n =>
      soninContractiveCofinalMobiusGammaXiWardComplexMovingTransport
          a c d r hc hcd hr sigma hsigma u hu depth n -
        squarefreeMobiusGammaXiWardTransportV
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
          (u n))
      atTop (𝓝 0) := by
    have hscaled : Tendsto (fun n =>
        (I / 2) *
          ((transportedScore n - sourceScore n) /
            (((sigma n - 1 : ℝ) : ℂ) *
              GaloisForLFunctions.squarefreeBoundaryOverlap
                (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u n))))
        atTop (𝓝 0) := by
      simpa using hnormalized.const_mul (I / 2)
    convert hscaled using 1
    funext n
    rw [show sourceScore n =
        GaloisForLFunctions.squarefreeFisherScore
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u n) by
      exact inner_fisherTangent_complexDamped_eq_squarefreeFisherScore
        (hsigma n) (hu n) (hshift n)]
    simp only [
      soninContractiveCofinalMobiusGammaXiWardComplexMovingTransport,
      transportedScore, fisher, damped,
      squarefreeMobiusGammaXiWardTransportV,
      squarefreeMobiusGammaCurrentTransportV]
    ring
  have hexact : Tendsto (fun n =>
      squarefreeMobiusGammaXiWardTransportV
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
          (u n) -
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            ((sigma n : ℂ) +
              u n * ((sigma n - 1 : ℝ) : ℂ))))
      atTop (𝓝 0) := by
    have hzero : (fun n =>
        squarefreeMobiusGammaXiWardTransportV
            (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
            (u n) -
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate
              ((sigma n : ℂ) +
                u n * ((sigma n - 1 : ℝ) : ℂ)))) = fun _ => 0 := by
      funext n
      rw [squarefreeMobiusGammaXiWardTransportV_eq_continuedSource
        (by simpa using hsigma n) (hshift n)
        (by exact_mod_cast sub_ne_zero.mpr (hsigma n).ne')]
      simp
    rw [hzero]
    exact tendsto_const_nhds
  simpa only [sub_add_sub_cancel, zero_add] using
    htransportDifference.add hexact

/-- Every fixed complex Euler node in `re s > 1` has an unconditional contractive Sonin Rees
chart.  Imaginary height is arbitrary and does not change the source norm. -/
theorem exists_soninContractiveCofinalMobiusGammaXiWardFixedComplexNode
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (s : ℂ) (hs : 1 < s.re) :
    ∃ (sigma : ℕ → ℝ) (u : ℕ → ℂ)
        (hsigma : ∀ n, 1 < sigma n) (hu : ∀ n, 0 ≤ (u n).re)
        (depth : ℕ → ℕ),
      Tendsto sigma atTop (𝓝 1) ∧
      (∀ n,
        (sigma n : ℂ) + u n * ((sigma n - 1 : ℝ) : ℂ) = s) ∧
      StrictMono depth ∧
      Tendsto (fun n =>
        soninContractiveCofinalMobiusGammaXiWardComplexMovingTransport
            a c d r hc hcd hr sigma hsigma u hu depth n -
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate s))
        atTop (𝓝 0) := by
  let sigma : ℕ → ℝ := fixedEulerCofinalSigma s.re
  have hsigma (n : ℕ) : 1 < sigma n :=
    fixedEulerCofinalSigma_gt_one hs n
  have hsigmaOne : Tendsto sigma atTop (𝓝 1) :=
    tendsto_fixedEulerCofinalSigma s.re
  let u : ℕ → ℂ := fun n =>
    (s - (sigma n : ℂ)) / ((sigma n - 1 : ℝ) : ℂ)
  have hu (n : ℕ) : 0 ≤ (u n).re := by
    have hsigmaLe : sigma n ≤ s.re :=
      fixedEulerCofinalSigma_le_self hs.le n
    have hden : 0 < sigma n - 1 := sub_pos.mpr (hsigma n)
    have hre :
        (u n).re = (s.re - sigma n) / (sigma n - 1) := by
      dsimp [u]
      rw [Complex.div_re, Complex.normSq_ofReal]
      simp only [sub_re, ofReal_re, ofReal_im, mul_zero]
      field_simp [hden.ne']
      ring
    rw [hre]
    exact div_nonneg (sub_nonneg.mpr hsigmaLe) hden.le
  have hfixed (n : ℕ) :
      (sigma n : ℂ) + u n * ((sigma n - 1 : ℝ) : ℂ) = s := by
    have hden : ((sigma n - 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (hsigma n).ne'
    dsimp [u]
    field_simp
    ring
  have hshift (n : ℕ) :
      1 < ((sigma n : ℂ) + u n * ((sigma n - 1 : ℝ) : ℂ)).re := by
    rw [hfixed n]
    exact hs
  have hsigmaWithin :
      Tendsto sigma atTop (𝓝[>] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hsigmaOne, Filter.Eventually.of_forall hsigma⟩
  have hinvR :
      Tendsto (fun n => (squarefreeMobiusTotal (sigma n))⁻¹)
        atTop (𝓝 0) :=
    (tendsto_inv_squarefreeMobiusTotal_zero).comp hsigmaWithin
  have hinvC :
      Tendsto (fun n =>
        (((squarefreeMobiusTotal (sigma n))⁻¹ : ℝ) : ℂ))
        atTop (𝓝 0) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR using 1 <;>
      rfl
  have hoverlapEq (n : ℕ) :
      GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u n) =
        GaloisForLFunctions.squarefreePartition s *
          (((squarefreeMobiusTotal (sigma n))⁻¹ : ℝ) : ℂ) := by
    have htotal :
        (squarefreeMobiusTotal (sigma n) : ℂ) =
          GaloisForLFunctions.squarefreePartition (sigma n : ℂ) := by
      rw [ofReal_squarefreeMobiusTotal_eq_zetaRatio (hsigma n)]
      rfl
    simp only [GaloisForLFunctions.squarefreeBoundaryOverlap, hfixed n]
    rw [← htotal]
    push_cast
    rw [div_eq_mul_inv]
  have hoverlap :
      Tendsto (fun n =>
        GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u n))
        atTop (𝓝 0) := by
    have h :=
      hinvC.const_mul (GaloisForLFunctions.squarefreePartition s)
    simpa only [mul_zero] using h.congr'
      (Filter.Eventually.of_forall fun n => (hoverlapEq n).symm)
  have hepsilonR :
      Tendsto (fun n => sigma n - 1) atTop (𝓝 0) := by
    simpa using hsigmaOne.sub_const 1
  have hepsilonC :
      Tendsto (fun n => ((sigma n - 1 : ℝ) : ℂ)) atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hepsilonR
  have hgraphScaleZero : Tendsto (fun n =>
      ‖((sigma n - 1 : ℝ) : ℂ) *
        GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u n)‖)
      atTop (𝓝 0) := by
    simpa using (hepsilonC.mul hoverlap).norm
  obtain ⟨depth, hdepth, hlimit⟩ :=
    exists_soninContractiveCofinalMobiusGammaXiWardComplexMovingTransport
      a c d r ha hc hcd hda hr harc sigma hsigma u hu hshift
      hgraphScaleZero
  refine ⟨sigma, u, hsigma, hu, depth, hsigmaOne, hfixed, hdepth, ?_⟩
  simpa only [hfixed] using hlimit

end RHTower
