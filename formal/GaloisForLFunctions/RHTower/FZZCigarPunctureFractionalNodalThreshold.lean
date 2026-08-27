import GaloisForLFunctions.RHTower.FZZCigarPunctureAffineChannelClassification
import GaloisForLFunctions.HTGeometry.EndpointIntegralAsymptotics

/-!
# Sharp fractional nodal threshold at FZZ puncture

The regular rank-one no-go and affine-channel classification expose a source node at embedded
energy. This file solves the exact fractional regularity problem in target-centered coordinate.
For source germ `x^α 1_(0,1)`, resolvent equation forces unique state
`-x^(α-1) 1_(0,1)` almost everywhere. That state lies in `L²` exactly when `α > 1/2`.

Thus first-order cancellation is sufficient but not sharp. Actual occurrence wall is half order:
borderline square-root node fails logarithmically, while every stronger fractional node works.
Local mode remains nonselective because any chosen `α > 1/2` works in every target-centered chart.
FZZ dynamics must therefore produce both node location and more-than-half-order strength before
divisor landing.

The `L²` power threshold is classical. Exact FZZ-puncture source equation, unique-state
classification, and route boundary are the new specialization.

`[NEW] [CLASSIFICATION] [SHARP BOUNDARY] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex MeasureTheory Set
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Target-centered right-hand fractional source germ. -/
def fzzPunctureFractionalFormFactor (alpha x : ℝ) : ℂ :=
  (Ioo (0 : ℝ) 1).indicator (fun u => ((u ^ alpha : ℝ) : ℂ)) x

/-- Formal resolvent state associated to the fractional source germ. -/
def fzzPunctureFractionalFormalState (alpha x : ℝ) : ℂ :=
  (Ioo (0 : ℝ) 1).indicator (fun u => -((u ^ (alpha - 1) : ℝ) : ℂ)) x

theorem fzzPunctureFractionalFormalState_aeStronglyMeasurable (alpha : ℝ) :
    AEStronglyMeasurable (fzzPunctureFractionalFormalState alpha) volume := by
  change AEStronglyMeasurable
    ((Ioo (0 : ℝ) 1).indicator (fun u => -((u ^ (alpha - 1) : ℝ) : ℂ))) volume
  rw [aestronglyMeasurable_indicator_iff measurableSet_Ioo]
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
  intro x hx
  fun_prop (disch := aesop)

/-- Exact `L²` threshold for resolvent state: source must vanish faster than square root. -/
theorem fzzPunctureFractionalFormalState_memLp_iff (alpha : ℝ) :
    MemLp (fzzPunctureFractionalFormalState alpha) 2 volume ↔ 1 / 2 < alpha := by
  rw [memLp_two_iff_integrable_sq_norm
    (fzzPunctureFractionalFormalState_aeStronglyMeasurable alpha)]
  have hnorm : (fun x : ℝ => ‖fzzPunctureFractionalFormalState alpha x‖ ^ 2) =
      (Ioo (0 : ℝ) 1).indicator (fun x => x ^ ((alpha - 1) * 2)) := by
    funext x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · simp only [fzzPunctureFractionalFormalState, indicator_of_mem hx, norm_neg,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (Real.rpow_pos_of_pos hx.1 _)]
      rw [← Real.rpow_two, ← Real.rpow_mul hx.1.le]
    · simp [fzzPunctureFractionalFormalState, hx]
  rw [hnorm, integrable_indicator_iff measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)]
  norm_num
  constructor <;> intro h <;> linarith

/-- Fractional form factor cancels resolvent equation pointwise. -/
theorem fzzPunctureFractionalFormalState_equation (alpha x : ℝ) :
    (x : ℂ) * fzzPunctureFractionalFormalState alpha x +
      fzzPunctureFractionalFormFactor alpha x = 0 := by
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · have hx0 : 0 < x := hx.1
    simp only [fzzPunctureFractionalFormalState, fzzPunctureFractionalFormFactor,
      indicator_of_mem hx]
    rw [show alpha = 1 + (alpha - 1) by ring, Real.rpow_add hx0]
    simp [Real.rpow_one]
  · simp [fzzPunctureFractionalFormalState, fzzPunctureFractionalFormFactor, hx]

/-- Fractional survivor is genuinely nonzero for every exponent. -/
theorem fzzPunctureFractionalFormalState_ne_ae_zero (alpha : ℝ) :
    ¬ fzzPunctureFractionalFormalState alpha =ᵐ[volume] (0 : ℝ → ℂ) := by
  intro hzero
  have hzero' : fzzPunctureFractionalFormalState alpha =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] (0 : ℝ → ℂ) := ae_restrict_of_ae hzero
  have hfalse : ∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), False := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hzero'] with x hx hxzero
    have hxpow : x ^ (alpha - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx.1 _)
    simp [fzzPunctureFractionalFormalState, hx, hxpow] at hxzero
  have hmeasure : (volume.restrict (Ioo (0 : ℝ) 1)) Set.univ = 0 := by
    simpa using ae_iff.mp hfalse
  have hinterval : volume (Ioo (0 : ℝ) 1) = 0 := by
    rw [Measure.restrict_apply_univ] at hmeasure
    exact hmeasure
  rw [Real.volume_Ioo] at hinterval
  norm_num at hinterval

/-- Target-centered fractional continuum eigen-equation. -/
def fzzPunctureFractionalEigenEquation (alpha : ℝ) (f : ℝ → ℂ) : Prop :=
  MemLp f 2 volume ∧
    ∀ᵐ x : ℝ ∂volume,
      (x : ℂ) * f x + fzzPunctureFractionalFormFactor alpha x = 0

/-- Resolvent equation has one unique representative modulo null sets. -/
theorem fzzPunctureFractionalEigenEquation_state_unique (alpha : ℝ) (f : ℝ → ℂ)
    (h : fzzPunctureFractionalEigenEquation alpha f) :
    f =ᵐ[volume] fzzPunctureFractionalFormalState alpha := by
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := (volume : Measure ℝ).ae_ne 0
  filter_upwards [h.2, hne] with x hxeq hxne
  have hformal := fzzPunctureFractionalFormalState_equation alpha x
  have hcoef : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hxne
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp ?_).resolve_left hcoef
  linear_combination hxeq - hformal

/-- Nonzero target-centered fractional embedded mode. -/
def FZZPunctureFractionalPointMode (alpha : ℝ) : Prop :=
  ∃ f : ℝ → ℂ,
    fzzPunctureFractionalEigenEquation alpha f ∧
      ¬ f =ᵐ[volume] (0 : ℝ → ℂ)

/-- Exact half-order occurrence law, with no assumptions. -/
theorem fzzPunctureFractionalPointMode_iff (alpha : ℝ) :
    FZZPunctureFractionalPointMode alpha ↔ 1 / 2 < alpha := by
  constructor
  · rintro ⟨f, heq, -⟩
    have hstate := fzzPunctureFractionalEigenEquation_state_unique alpha f heq
    exact (fzzPunctureFractionalFormalState_memLp_iff alpha).mp
      ((memLp_congr_ae hstate).mp heq.1)
  · intro h
    refine ⟨fzzPunctureFractionalFormalState alpha, ?_,
      fzzPunctureFractionalFormalState_ne_ae_zero alpha⟩
    exact ⟨(fzzPunctureFractionalFormalState_memLp_iff alpha).mpr h,
      Filter.Eventually.of_forall (fzzPunctureFractionalFormalState_equation alpha)⟩

/-- Square-root source node is exactly excluded. -/
theorem not_fzzPunctureFractionalPointMode_at_half :
    ¬ FZZPunctureFractionalPointMode (1 / 2) := by
  rw [fzzPunctureFractionalPointMode_iff]
  norm_num

/-- A strict fractional node below first order already realizes a point mode. -/
theorem fzzPunctureFractionalPointMode_three_quarters :
    FZZPunctureFractionalPointMode (3 / 4) := by
  rw [fzzPunctureFractionalPointMode_iff]
  norm_num

end

end RHTower
