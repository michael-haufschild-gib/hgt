import GaloisForLFunctions.RHTower.SuzukiOnePrimeRoughPrimitiveFourierForcing
import GaloisForLFunctions.RHTower.VectorL2WeakDerivativeFourier

/-!
# Physical identification of one-prime rough-primitive forcing

For a literal two-coordinate `L²` weak derivative pair, the canonical inverse-multiplier forcing
is almost everywhere the unitary Fourier transform of the physical primitive.  The identity is
transported through both oriented variation-of-constants integrals and hence through the concrete
terminal Hardy admissions.
-/

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap LineDeriv

namespace RHTower

/-- The canonical terminal forcing of an `L²` weak derivative is exactly the unitary Fourier
representative of its physical primitive, almost everywhere. -/
theorem onePrimeTerminalRoughPrimitiveForcing_eq_sourceFourier_ae
    (G H : OnePrimeTerminalSourceL2)
    (hweak : ∂_{(1 : ℝ)} (G : 𝓢'(ℝ, OnePrimeTerminalState)) =
      (H : 𝓢'(ℝ, OnePrimeTerminalState))) :
    onePrimeTerminalRoughPrimitiveForcing H =ᵐ[volume]
      onePrimeTerminalSourceFourier G := by
  change (fun ξ : ℝ =>
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))⁻¹) •
        ((𝓕 H : OnePrimeTerminalSourceL2) : ℝ → OnePrimeTerminalState) ξ) =ᵐ[volume]
    ((𝓕 G : OnePrimeTerminalSourceL2) : ℝ → OnePrimeTerminalState)
  exact l2_roughPrimitiveForcing_eq_fourier_ae G H hweak

theorem onePrimeTerminalRoughPrimitiveForcing_eq_sourceFourier_posRay_ae
    (G H : OnePrimeTerminalSourceL2)
    (hweak : ∂_{(1 : ℝ)} (G : 𝓢'(ℝ, OnePrimeTerminalState)) =
      (H : 𝓢'(ℝ, OnePrimeTerminalState))) :
    (fun t : ℝ => onePrimeTerminalRoughPrimitiveForcing H ((1 : ℝ) * t)) =ᵐ[volume]
      fun t : ℝ => onePrimeTerminalSourceFourier G ((1 : ℝ) * t) := by
  simpa using onePrimeTerminalRoughPrimitiveForcing_eq_sourceFourier_ae G H hweak

theorem onePrimeTerminalRoughPrimitiveForcing_eq_sourceFourier_negRay_ae
    (G H : OnePrimeTerminalSourceL2)
    (hweak : ∂_{(1 : ℝ)} (G : 𝓢'(ℝ, OnePrimeTerminalState)) =
      (H : 𝓢'(ℝ, OnePrimeTerminalState))) :
    (fun t : ℝ => onePrimeTerminalRoughPrimitiveForcing H ((-1 : ℝ) * t)) =ᵐ[volume]
      fun t : ℝ => onePrimeTerminalSourceFourier G ((-1 : ℝ) * t) := by
  have hcomp := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
    |>.ae_eq_comp (onePrimeTerminalRoughPrimitiveForcing_eq_sourceFourier_ae G H hweak)
  simpa [Function.comp_def] using hcomp

/-- Variation of constants is invariant under replacing the canonical derivative quotient by
the Fourier representative of its weak primitive. -/
theorem forcedStripRay_onePrimeTerminalRoughPrimitiveForcing_eq_sourceFourier
    (G H : OnePrimeTerminalSourceL2)
    (hweak : ∂_{(1 : ℝ)} (G : 𝓢'(ℝ, OnePrimeTerminalState)) =
      (H : 𝓢'(ℝ, OnePrimeTerminalState)))
    (c : OnePrimeTerminalState) (σ ε x : ℝ) (hε : ε = 1 ∨ ε = -1) :
    GaloisForLFunctions.RHTower.forcedStripRay suzukiGammaRatioSqrtBranch
        onePrimeTerminalAdjacencyCLM c
        (onePrimeTerminalRoughPrimitiveForcing H) σ ε x =
      GaloisForLFunctions.RHTower.forcedStripRay suzukiGammaRatioSqrtBranch
        onePrimeTerminalAdjacencyCLM c
        (onePrimeTerminalSourceFourier G) σ ε x := by
  have hray :
      (fun t : ℝ => onePrimeTerminalRoughPrimitiveForcing H (ε * t)) =ᵐ[volume]
        fun t : ℝ => onePrimeTerminalSourceFourier G (ε * t) := by
    rcases hε with rfl | rfl
    · exact onePrimeTerminalRoughPrimitiveForcing_eq_sourceFourier_posRay_ae G H hweak
    · exact onePrimeTerminalRoughPrimitiveForcing_eq_sourceFourier_negRay_ae G H hweak
  unfold GaloisForLFunctions.RHTower.forcedStripRay
  congr 2
  apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [hray] with t ht _
  rw [ht]

/-- Concrete positive-ray Hardy admission for the physical Fourier primitive of every `L²` weak
derivative pair. -/
theorem lintegral_enorm_sq_onePrimeTerminalSourceFourier_forcedStripRay_pos_lt_top
    (G H : OnePrimeTerminalSourceL2)
    (hweak : ∂_{(1 : ℝ)} (G : 𝓢'(ℝ, OnePrimeTerminalState)) =
      (H : 𝓢'(ℝ, OnePrimeTerminalState)))
    (c : OnePrimeTerminalState) :
    ∫⁻ x in Set.Ioi (1 : ℝ),
      ‖GaloisForLFunctions.RHTower.forcedStripRay suzukiGammaRatioSqrtBranch
        onePrimeTerminalAdjacencyCLM c (onePrimeTerminalSourceFourier G)
          (3 / 4 : ℝ) 1 x‖ₑ ^ 2 < ⊤ := by
  have heq :
      (fun x : ℝ =>
        ‖GaloisForLFunctions.RHTower.forcedStripRay suzukiGammaRatioSqrtBranch
          onePrimeTerminalAdjacencyCLM c (onePrimeTerminalSourceFourier G)
            (3 / 4 : ℝ) 1 x‖ₑ ^ 2) =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      fun x : ℝ =>
        ‖GaloisForLFunctions.RHTower.forcedStripRay suzukiGammaRatioSqrtBranch
          onePrimeTerminalAdjacencyCLM c
            (onePrimeTerminalRoughPrimitiveForcing H) (3 / 4 : ℝ) 1 x‖ₑ ^ 2 := by
    filter_upwards with x
    rw [forcedStripRay_onePrimeTerminalRoughPrimitiveForcing_eq_sourceFourier
      G H hweak c (3 / 4 : ℝ) 1 x (Or.inl rfl)]
  rw [MeasureTheory.lintegral_congr_ae heq]
  exact lintegral_enorm_sq_onePrimeTerminalRoughPrimitive_forcedStripRay_pos_lt_top H c

/-- Concrete negative-ray Hardy admission for the physical Fourier primitive of every `L²` weak
derivative pair. -/
theorem lintegral_enorm_sq_onePrimeTerminalSourceFourier_forcedStripRay_neg_lt_top
    (G H : OnePrimeTerminalSourceL2)
    (hweak : ∂_{(1 : ℝ)} (G : 𝓢'(ℝ, OnePrimeTerminalState)) =
      (H : 𝓢'(ℝ, OnePrimeTerminalState)))
    (c : OnePrimeTerminalState) :
    ∫⁻ x in Set.Ioi (1 : ℝ),
      ‖GaloisForLFunctions.RHTower.forcedStripRay suzukiGammaRatioSqrtBranch
        onePrimeTerminalAdjacencyCLM c (onePrimeTerminalSourceFourier G)
          (3 / 4 : ℝ) (-1) x‖ₑ ^ 2 < ⊤ := by
  have heq :
      (fun x : ℝ =>
        ‖GaloisForLFunctions.RHTower.forcedStripRay suzukiGammaRatioSqrtBranch
          onePrimeTerminalAdjacencyCLM c (onePrimeTerminalSourceFourier G)
            (3 / 4 : ℝ) (-1) x‖ₑ ^ 2) =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      fun x : ℝ =>
        ‖GaloisForLFunctions.RHTower.forcedStripRay suzukiGammaRatioSqrtBranch
          onePrimeTerminalAdjacencyCLM c
            (onePrimeTerminalRoughPrimitiveForcing H) (3 / 4 : ℝ) (-1) x‖ₑ ^ 2 := by
    filter_upwards with x
    rw [forcedStripRay_onePrimeTerminalRoughPrimitiveForcing_eq_sourceFourier
      G H hweak c (3 / 4 : ℝ) (-1) x (Or.inr rfl)]
  rw [MeasureTheory.lintegral_congr_ae heq]
  exact lintegral_enorm_sq_onePrimeTerminalRoughPrimitive_forcedStripRay_neg_lt_top H c

end RHTower

end
