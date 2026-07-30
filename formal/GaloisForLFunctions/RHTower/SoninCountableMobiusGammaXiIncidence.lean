import GaloisForLFunctions.RHTower.SoninSourceGlobalGradedCorona
import GaloisForLFunctions.RHTower.SoninCofinalMobiusGammaXiIncidence

/-!
# Countable Möbius--Gamma--Xi incidence through one Sonin schedule

The finite Euler-packet Rees chart admits a source-global countable
strengthening.  A single critical normal path and a single strictly cofinal
Sonin depth schedule reconstruct every member of a countable Euler family
which remains uniformly inside `s > 1`.

The common transport grade at stage `n` is the minimum of the first `n + 1`
pointwise Gamma graph scales.  Thus each fixed coordinate is eventually
controlled at its own exact singular grade.  The theorem remains a scalar
incidence statement: it does not construct the missing polarized Hardy
morphism or prove RH.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-- **Countable Euler-family Sonin--Gamma--Xi Rees chart.**  Every countable
family of real Euler points with one uniform lower bound `base > 1` admits
one source-defined critical normal path, compatible nonnegative tangential
paths fixing all points exactly, and one strictly cofinal Sonin schedule
which reconstructs all continued Xi source coordinates.

At stage `n` the schedule controls the first `n + 1` coordinates at the
minimum of their exact Gamma graph scales.  Hence every fixed coordinate is
eventually transported with error negligible at its own graph scale. -/
theorem exists_countableEulerFamily_soninGammaXiReesChart
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (base : ℝ) (hbase : 1 < base)
    (s : ℕ → ℝ) (hs : ∀ i, base ≤ s i) :
    ∃ (sigma : ℕ → ℝ) (u : ℕ → ℕ → ℝ)
        (hsigma : ∀ n, 1 < sigma n) (hu : ∀ n i, 0 ≤ u n i)
        (depth : ℕ → ℕ),
      Tendsto sigma atTop (𝓝 1) ∧
      (∀ n i,
        mobiusCriticalBoundaryParameter (sigma n) (u n i) = s i) ∧
      StrictMono depth ∧
      ∀ i, Tendsto (fun n =>
        soninCofinalMobiusGammaXiWardMovingTransport
            a c d r hc hcd hr sigma hsigma
            (fun n => u n i) (fun n => hu n i) depth n -
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate (s i : ℂ)))
        atTop (𝓝 0) := by
  classical
  have hsStrict (i : ℕ) : 1 < s i :=
    hbase.trans_le (hs i)
  let sigma : ℕ → ℝ := fixedEulerCofinalSigma base
  have hsigma (n : ℕ) : 1 < sigma n := by
    exact fixedEulerCofinalSigma_gt_one hbase n
  have hsigmaOne : Tendsto sigma atTop (𝓝 1) := by
    exact tendsto_fixedEulerCofinalSigma base
  let u : ℕ → ℕ → ℝ := fun n i =>
    (s i - sigma n) / (sigma n - 1)
  have hu (n i : ℕ) : 0 ≤ u n i := by
    have hsigmaLe : sigma n ≤ base := by
      exact fixedEulerCofinalSigma_le_self hbase.le n
    exact div_nonneg
      (sub_nonneg.mpr (hsigmaLe.trans (hs i)))
      (sub_nonneg.mpr (hsigma n).le)
  have hfixed (n i : ℕ) :
      mobiusCriticalBoundaryParameter (sigma n) (u n i) = s i := by
    exact mobiusCriticalBoundaryParameter_solvedDamping
      (ne_of_gt (hsigma n))
  let fisher : ℕ → ℕ → lp (fun _ : ℕ => ℂ) 2 :=
    fun n _ => infiniteMobiusCriticalFisherTangentLp (sigma n) (hsigma n)
  let damped : ℕ → ℕ → lp (fun _ : ℕ => ℂ) 2 :=
    fun n i => infiniteMobiusCriticalDampedSignedWeightLp
      (sigma n) (u n i) (hsigma n) (hu n i)
  let graphScale : ℕ → ℕ → ℝ := fun n i =>
    (sigma n - 1) *
      (squarefreeMobiusTotal (s i) / squarefreeMobiusTotal (sigma n))
  have hgraphScale (n i : ℕ) : 0 < graphScale n i := by
    exact mul_pos (sub_pos.mpr (hsigma n))
      (div_pos (squarefreeMobiusTotal_pos (hsStrict i))
        (squarefreeMobiusTotal_pos (hsigma n)))
  have hsigmaWithin :
      Tendsto sigma atTop (𝓝[>] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hsigmaOne, Filter.Eventually.of_forall hsigma⟩
  have hinvTotal :
      Tendsto (fun n => (squarefreeMobiusTotal (sigma n))⁻¹)
        atTop (𝓝 0) :=
    (tendsto_inv_squarefreeMobiusTotal_zero).comp hsigmaWithin
  have hnormal :
      Tendsto (fun n => sigma n - 1) atTop (𝓝 0) := by
    simpa using hsigmaOne.sub_const 1
  have hgraphScaleZero (i : ℕ) :
      Tendsto (fun n => graphScale n i) atTop (𝓝 0) := by
    have hratio :
        Tendsto (fun n =>
          squarefreeMobiusTotal (s i) / squarefreeMobiusTotal (sigma n))
          atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        hinvTotal.const_mul (squarefreeMobiusTotal (s i))
    simpa only [graphScale, zero_mul] using hnormal.mul hratio
  let scalePacket : ℕ → Finset ℝ := fun n =>
    (Finset.range (n + 1)).image (graphScale n)
  have hscalePacketNonempty (n : ℕ) :
      (scalePacket n).Nonempty := by
    apply Finset.Nonempty.image
    exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
  let commonScale : ℕ → ℝ := fun n =>
    (scalePacket n).min' (hscalePacketNonempty n)
  have hcommonScalePos (n : ℕ) : 0 < commonScale n := by
    change 0 < (scalePacket n).min' (hscalePacketNonempty n)
    have hmem :=
      Finset.min'_mem (scalePacket n) (hscalePacketNonempty n)
    obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hmem
    rw [← hi]
    exact hgraphScale n i
  have hcommonScaleLe (n i : ℕ) (hi : i < n + 1) :
      commonScale n ≤ graphScale n i := by
    change
      (scalePacket n).min' (hscalePacketNonempty n) ≤ graphScale n i
    exact Finset.min'_le _ _ <|
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have hcommonScaleZero :
      Tendsto commonScale atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n => (hcommonScalePos n).le)
      (Filter.Eventually.of_forall fun n =>
        hcommonScaleLe n 0 (Nat.zero_lt_succ n))
      (hgraphScaleZero 0)
  obtain ⟨depth, hdepth, hpacket⟩ :=
    exists_centralSoninDilationCorner_singularDiagonal_countable_codiagonal
      a c d r ha hc hcd hda hr harc fisher damped commonScale
      hcommonScalePos hcommonScaleZero
  refine ⟨sigma, u, hsigma, hu, depth, hsigmaOne, hfixed, hdepth, ?_⟩
  intro i
  let corner : SoninL2 →L[ℂ] SoninL2 :=
    crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a
  let transportedScore : ℕ → ℂ := fun n =>
    inner ℂ
      (corner
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) (fisher n i)))
      (corner
        (cofinalInverseDilatedShellEmbedding
          c d r hc hcd hr (depth n) (damped n i)))
  let sourceScore : ℕ → ℂ := fun n =>
    inner ℂ (fisher n i) (damped n i)
  have hcodiagonal := (hpacket i).2.2
  have hcommonScaleLeEventually :
      ∀ᶠ n in atTop, commonScale n ≤ graphScale n i := by
    filter_upwards [eventually_ge_atTop i] with n hn
    exact hcommonScaleLe n i (Nat.lt_succ_of_le hn)
  have hgraphNorm : Tendsto (fun n =>
      ‖transportedScore n - sourceScore n‖ / graphScale n i)
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (norm_nonneg _) (hgraphScale n i).le)
      (hcommonScaleLeEventually.mono fun n hle => by
        exact div_le_div_of_nonneg_left
          (norm_nonneg _) (hcommonScalePos n) hle)
    convert hcodiagonal using 1
  have hnormalized : Tendsto (fun n =>
      (transportedScore n - sourceScore n) /
        ((graphScale n i : ℝ) : ℂ))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert hgraphNorm using 1
    funext n
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hgraphScale n i)]
  have hoverlap (n : ℕ) :
      squarefreeMobiusBoundaryLayerLaplace (sigma n) (u n i) =
        (squarefreeMobiusTotal (s i) : ℂ) /
          (squarefreeMobiusTotal (sigma n) : ℂ) := by
    simp only [squarefreeMobiusBoundaryLayerLaplace, hfixed n i]
  have htransportDifference : Tendsto (fun n =>
      soninCofinalMobiusGammaXiWardMovingTransport
          a c d r hc hcd hr sigma hsigma
          (fun n => u n i) (fun n => hu n i) depth n -
        squarefreeMobiusGammaXiWardTransportV
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
          (u n i : ℂ))
      atTop (𝓝 0) := by
    have hscaled : Tendsto (fun n =>
        (I / 2) *
          ((transportedScore n - sourceScore n) /
            ((graphScale n i : ℝ) : ℂ)))
        atTop (𝓝 0) := by
      simpa using hnormalized.const_mul (I / 2)
    convert hscaled using 1
    funext n
    rw [show sourceScore n =
        GaloisForLFunctions.squarefreeFisherScore
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) (u n i : ℂ) by
      exact inner_fisherTangent_damped_eq_squarefreeFisherScore
        (hsigma n) (hu n i)]
    simp only [graphScale, Complex.ofReal_mul, Complex.ofReal_div]
    rw [← hoverlap n]
    simp only [soninCofinalMobiusGammaXiWardMovingTransport,
      transportedScore, fisher, damped, corner,
      squarefreeMobiusGammaXiWardTransportV,
      squarefreeMobiusGammaCurrentTransportV]
    rw [squarefreeMobiusBoundaryLayerLaplace_eq_squarefreeBoundaryOverlap
      (hsigma n) (hu n i)]
    ring
  have hexact : Tendsto (fun n =>
      squarefreeMobiusGammaXiWardTransportV
          (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
          (u n i : ℂ) -
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate (s i : ℂ)))
      atTop (𝓝 0) := by
    have hzero : (fun n =>
        squarefreeMobiusGammaXiWardTransportV
            (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ)
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                (sigma n : ℂ) ((sigma n - 1 : ℝ) : ℂ) v)
            (u n i : ℂ) -
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate (s i : ℂ))) = fun _ => 0 := by
      funext n
      rw [squarefreeMobiusGammaXiWardTransportV_actualTangent
        (hsigma n) (hu n i)]
      rw [hfixed n i]
      simp
    rw [hzero]
    exact tendsto_const_nhds
  simpa only [sub_add_sub_cancel, zero_add] using
    htransportDifference.add hexact

end RHTower
