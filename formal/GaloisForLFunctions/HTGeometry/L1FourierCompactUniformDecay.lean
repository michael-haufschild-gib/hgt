import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import GaloisForLFunctions.HTGeometry.CompactDetectorNearRadicalAlternative

/-!
# Compact-uniform Riemann--Lebesgue decay on `L¹(ℝ)`

Mathlib bundles the Fourier transform as a continuous linear map from `L¹` to bounded continuous
functions. This file exposes the metric estimate needed by remote-divisor detector arguments:
Fourier evaluation is `1`-Lipschitz in the `L¹` datum, so pointwise Riemann--Lebesgue decay is
uniform on compact `L¹` families.

Composition with arbitrary continuous linear `L¹` preprocessing maps covers bounded Mellin tilts,
cutoffs, and reflected channels. Two such channels give the exact fourfold real quartet defect.
-/

open MeasureTheory Filter
open scoped FourierTransform Topology ENNReal BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complex `L¹(ℝ)` profiles used in logarithmic Mellin coordinates. -/
abbrev LogMellinL1 := MeasureTheory.Lp ℂ 1 (volume : Measure ℝ)

/-- Fourier evaluation of an `L¹` logarithmic profile. -/
def logMellinL1Fourier (f : LogMellinL1) (t : ℝ) : ℂ :=
  Real.Lp.fourierTransform f t

/-- Pointwise Riemann--Lebesgue decay of an `L¹` logarithmic profile. -/
theorem logMellinL1Fourier_tendsto_cocompact (f : LogMellinL1) :
    Tendsto (logMellinL1Fourier f) (cocompact ℝ) (𝓝 0) := by
  change Tendsto (fun t => Real.Lp.fourierTransform f t) (cocompact ℝ) (𝓝 0)
  simpa only [Real.Lp.fourierTransform_apply] using
    Real.zero_at_infty_fourier (fun x : ℝ => f x)

/-- Fourier evaluation respects subtraction in `L¹`. -/
theorem logMellinL1Fourier_sub (f g : LogMellinL1) (t : ℝ) :
    logMellinL1Fourier f t - logMellinL1Fourier g t =
      logMellinL1Fourier (f - g) t := by
  have h := (Real.Lp.fourierTransformCLM ℝ ℂ).map_sub f g
  simpa only [logMellinL1Fourier, Real.Lp.fourierTransformCLM_apply,
    BoundedContinuousFunction.coe_sub, Pi.sub_apply] using
    congrArg (fun q : ℝ →ᵇ ℂ => q t) h.symm

/-- Every Fourier evaluation is `1`-Lipschitz for the `L¹` metric. -/
theorem logMellinL1Fourier_lipschitz (f g : LogMellinL1) (t : ℝ) :
    ‖logMellinL1Fourier f t - logMellinL1Fourier g t‖ ≤ dist f g := by
  rw [logMellinL1Fourier_sub, dist_eq_norm, logMellinL1Fourier]
  calc
    ‖Real.Lp.fourierTransform (f - g) t‖ =
        ‖𝓕 (fun x : ℝ => (f - g) x) t‖ := by
      rw [Real.Lp.fourierTransform_apply]
    _ ≤ ∫ x : ℝ, ‖(f - g) x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ = ‖f - g‖ := (L1.norm_eq_integral_norm (f - g)).symm

/-- **Compact-uniform Riemann--Lebesgue lemma in `L¹`.** -/
theorem compact_logMellinL1Fourier_uniformVanishes
    {K : Set LogMellinL1} (hK : IsCompact K) :
    UniformlyVanishesAlong (cocompact ℝ) K
      (fun t f => logMellinL1Fourier f t) := by
  exact compact_uniformVanishesAlong_of_lipschitz hK logMellinL1Fourier
    logMellinL1Fourier_tendsto_cocompact logMellinL1Fourier_lipschitz

/-- Compact-uniform Fourier decay after any continuous linear preprocessing of the `L¹` profile. -/
theorem compact_logMellinL1Fourier_compCLM_uniformVanishes
    (T : LogMellinL1 →L[ℂ] LogMellinL1) {K : Set LogMellinL1} (hK : IsCompact K) :
    UniformlyVanishesAlong (cocompact ℝ) K
      (fun t f => logMellinL1Fourier (T f) t) := by
  have hTK : IsCompact (T '' K) := hK.image T.continuous
  have hbase := compact_logMellinL1Fourier_uniformVanishes hTK
  intro ε hε
  filter_upwards [hbase ε hε] with t ht
  intro f hf
  exact ht (T f) ⟨f, hf, rfl⟩

/-- **Compact-uniform remote-quartet defect decay.** Two continuous linear `L¹` channels, such as
the positive and negative bounded Mellin tilts, have fourfold real product defect tending uniformly
to zero on every compact profile family. -/
theorem compact_logMellinL1Fourier_quartetDefect_uniformVanishes
    (Tplus Tminus : LogMellinL1 →L[ℂ] LogMellinL1)
    {K : Set LogMellinL1} (hK : IsCompact K) :
    UniformlyVanishesAlong (cocompact ℝ) K
      (fun t f =>
        (4 * (logMellinL1Fourier (Tplus f) t *
          logMellinL1Fourier (Tminus f) t).re : ℝ)) :=
  (compact_logMellinL1Fourier_compCLM_uniformVanishes Tplus hK).quartetDefect
    (compact_logMellinL1Fourier_compCLM_uniformVanishes Tminus hK)

end

end GaloisForLFunctions.HTGeometry
