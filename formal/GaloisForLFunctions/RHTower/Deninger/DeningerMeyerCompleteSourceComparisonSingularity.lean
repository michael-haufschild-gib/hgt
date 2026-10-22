import GaloisForLFunctions.RHTower.CompleteResolutionSourceCharacterSelectionLaw
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiCofinalSynthesisSingularity

/-!
# Complete-source comparison is singular or cofinally trace-erasing

The complete high-exponent Riemann resolution gives a predeclared nonzero
vector in one fixed `ℓ¹` source space at every point of the open critical
strip.  Literal Meyer theory gives a different, all-weight logarithmic source
space whose Mellin traces satisfy vertical Fourier estimates.

This file connects those two source constructions without postulating an
arithmetic comparison.  Normalize each actual complete-resolution vector to
unit `ℓ¹` norm and let one fixed complex-linear map send the whole source
space into the literal Meyer space.  If this map is uniformly bounded for the
first vertical Meyer Sobolev cost throughout the closed critical strip, its
Mellin value on the normalized source vectors tends to zero along an actual
cofinal sequence of Xi divisor points.

Consequently no such regular comparison is uniformly Xi-trace-faithful.
Every comparison capable of retaining a uniform amount of the cofinal Xi
trace must be singular for the canonical first-order Meyer seminorm.  This is
a source-to-source obstruction: neither the comparison, a divisor-indexed
Hilbert space, nor a target-selected interpolation operator is manufactured.

All results are unconditional.  No RH, positivity, simplicity, trace formula,
inverse Mellin theorem, or numerical computation is used.
-/

open Complex Filter Function Set Topology MeasureTheory
open scoped Classical

namespace RHTower

noncomputable section

/-- Unit-norm normalization of a nonzero vector in a complex normed space. -/
def complexUnitNormalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : E) : E :=
  ((‖x‖⁻¹ : ℝ) : ℂ) • x

theorem norm_complexUnitNormalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {x : E} (hx : x ≠ 0) :
    ‖complexUnitNormalization x‖ = 1 := by
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [complexUnitNormalization, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ hxnorm]

/--
The actual complete-resolution source at the `stage`-th escaping Xi divisor
point, normalized to unit `ℓ¹` norm.
-/
def completeResolutionXiEscapeUnitSource
    (K stage : ℕ) : CompleteResolutionSourceSpace :=
  complexUnitNormalization
    (completeResolutionSourceVector K
      (deningerMeyerXiVerticalEscape stage : ℂ)
      (xi_divisor_support_re_mem_open_unit
        (deningerMeyerXiVerticalEscape stage)).1)

theorem norm_completeResolutionXiEscapeUnitSource
    (K stage : ℕ) :
    ‖completeResolutionXiEscapeUnitSource K stage‖ = 1 := by
  apply norm_complexUnitNormalization
  exact completeResolutionSourceVector_ne_zero K
    (xi_divisor_support_re_mem_open_unit
      (deningerMeyerXiVerticalEscape stage)).1

/--
One fixed comparison from the complete arithmetic `ℓ¹` source into the
literal all-weight Meyer source.
-/
abbrev DeningerMeyerCompleteSourceComparison :=
  CompleteResolutionSourceSpace →ₗ[ℂ] DeningerMeyerStrongLogTarget

/--
Uniform first-order regularity for a complete-source comparison.  The bound
is imposed on the canonical weighted `L¹` Sobolev cost, uniformly across the
closed critical strip and linearly in the source norm.
-/
def DeningerMeyerCompleteSourceComparisonFirstOrderRegular
    (T : DeningerMeyerCompleteSourceComparison) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (sigma : ℝ), 0 ≤ sigma → sigma ≤ 1 →
      ∀ x : CompleteResolutionSourceSpace,
        deningerMeyerVerticalSobolevCost 1 sigma (T x) ≤ C * ‖x‖

/-- Mellin trace of a comparison on the normalized actual source vector. -/
def deningerMeyerCompleteSourceXiEscapeTrace
    (T : DeningerMeyerCompleteSourceComparison)
    (K stage : ℕ) : ℂ :=
  deningerMeyerStrongLogMellin
    (T (completeResolutionXiEscapeUnitSource K stage))
    (deningerMeyerXiVerticalEscape stage : ℂ)

/--
Uniform first-order source regularity forces cofinal Xi-trace erasure.
-/
theorem deningerMeyerCompleteSourceXiEscapeTrace_tendsto_zero
    (T : DeningerMeyerCompleteSourceComparison)
    (hregular :
      DeningerMeyerCompleteSourceComparisonFirstOrderRegular T)
    (K : ℕ) :
    Tendsto
      (deningerMeyerCompleteSourceXiEscapeTrace T K)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hregular⟩ := hregular
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := exists_nat_gt (C / epsilon)
  refine ⟨N, ?_⟩
  intro stage hstage
  have hstrip :=
    xi_divisor_support_re_mem_open_unit
      (deningerMeyerXiVerticalEscape stage)
  have hcost :
      deningerMeyerVerticalSobolevCost 1
          (deningerMeyerXiVerticalEscape stage : ℂ).re
          (T (completeResolutionXiEscapeUnitSource K stage)) ≤ C := by
    simpa only [norm_completeResolutionXiEscapeUnitSource, mul_one] using
      hregular
        (deningerMeyerXiVerticalEscape stage : ℂ).re
        hstrip.1.le hstrip.2.le
        (completeResolutionXiEscapeUnitSource K stage)
  have hfourier :=
    abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le
      (T (completeResolutionXiEscapeUnitSource K stage))
      1
      (deningerMeyerXiVerticalEscape stage : ℂ).re
      (deningerMeyerXiVerticalEscape stage : ℂ).im
  rw [Complex.re_add_im, pow_one] at hfourier
  have hbound :
      |(deningerMeyerXiVerticalEscape stage : ℂ).im| *
          ‖deningerMeyerCompleteSourceXiEscapeTrace T K stage‖ ≤ C := by
    exact hfourier.trans hcost
  have hheight :=
    deningerMeyerXiVerticalEscape_abs_im_gt stage
  have hheightPos :
      0 < |(deningerMeyerXiVerticalEscape stage : ℂ).im| := by
    have : 0 < (stage : ℝ) + 1 := by positivity
    exact this.trans hheight
  have hNstage : (N : ℝ) ≤ (stage : ℝ) := by
    exact_mod_cast hstage
  have hratio :
      C / epsilon <
        |(deningerMeyerXiVerticalEscape stage : ℂ).im| := by
    have hNstage' : C / epsilon < (stage : ℝ) :=
      hN.trans_le hNstage
    exact hNstage'.trans (by linarith)
  have hCepsilon :
      C <
        epsilon *
          |(deningerMeyerXiVerticalEscape stage : ℂ).im| := by
    simpa only [mul_comm] using (div_lt_iff₀ hepsilon).mp hratio
  have hnorm :
      ‖deningerMeyerCompleteSourceXiEscapeTrace T K stage‖ <
        epsilon := by
    by_contra hnot
    have hepsLe :
        epsilon ≤
          ‖deningerMeyerCompleteSourceXiEscapeTrace T K stage‖ :=
      le_of_not_gt hnot
    have :
        epsilon *
            |(deningerMeyerXiVerticalEscape stage : ℂ).im| ≤ C := by
      calc
        epsilon *
            |(deningerMeyerXiVerticalEscape stage : ℂ).im| =
          |(deningerMeyerXiVerticalEscape stage : ℂ).im| *
            epsilon := by ring
        _ ≤
          |(deningerMeyerXiVerticalEscape stage : ℂ).im| *
            ‖deningerMeyerCompleteSourceXiEscapeTrace T K stage‖ :=
          mul_le_mul_of_nonneg_left hepsLe hheightPos.le
        _ ≤ C := hbound
    exact (not_lt_of_ge this) hCepsilon
  simpa only [dist_zero_right] using hnorm

/--
No first-order regular source comparison retains a uniform positive amount
of the Xi trace on the normalized complete source.
-/
theorem
    no_uniformlyXiTraceFaithful_firstOrderRegular_completeSourceComparison
    (T : DeningerMeyerCompleteSourceComparison)
    (hregular :
      DeningerMeyerCompleteSourceComparisonFirstOrderRegular T)
    (K : ℕ) :
    ¬ ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ stage,
        epsilon ≤
          ‖deningerMeyerCompleteSourceXiEscapeTrace T K stage‖ := by
  rintro ⟨epsilon, hepsilon, hlower⟩
  have htendsto :
      Tendsto
        (fun stage =>
          ‖deningerMeyerCompleteSourceXiEscapeTrace T K stage‖)
        atTop (𝓝 0) := by
    simpa using
      (deningerMeyerCompleteSourceXiEscapeTrace_tendsto_zero
        T hregular K).norm
  have heventually :
      ∀ᶠ stage in atTop,
        ‖deningerMeyerCompleteSourceXiEscapeTrace T K stage‖ <
          epsilon :=
    (tendsto_order.1 htendsto).2 epsilon hepsilon
  obtain ⟨stage, hstage⟩ := heventually.exists
  exact (not_lt_of_ge (hlower stage)) hstage

end

end RHTower
