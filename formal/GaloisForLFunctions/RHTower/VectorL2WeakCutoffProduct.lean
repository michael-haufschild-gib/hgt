import GaloisForLFunctions.RHTower.VectorL2WeakDerivativeFourier

/-!
# Smooth cutoffs of Hilbert-valued `L²` weak derivatives

This module supplies the vector-valued distributional Leibniz rule needed by literal CCM/Suzuki
source assembly.  Multiplication is performed in `L²`, not postulated on an abstract carrier:
bounded smooth multipliers are represented in `L∞`, their products with the primitive and its weak
derivative are actual `L²` vectors, and the resulting tempered-distribution derivative is exactly

`∂(χf) = χ ∂f + χ' f`.

The proof first establishes the product rule for arbitrary vector-valued tempered distributions
by differentiating the multiplier-times-test-function.  The `L²` theorem then follows through
Mathlib's exact Hölder multiplication and tempered-distribution embedding.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap LineDeriv

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem schwartz_deriv_smulLeft
    (χ χ' : ℝ → ℂ)
    (hχ : χ.HasTemperateGrowth) (hχ' : χ'.HasTemperateGrowth)
    (hd : ∀ x, HasDerivAt χ (χ' x) x) (φ : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.smulLeftCLM ℂ χ φ) =
      SchwartzMap.smulLeftCLM ℂ χ' φ +
        SchwartzMap.smulLeftCLM ℂ χ (SchwartzMap.derivCLM ℂ ℂ φ) := by
  ext x
  rw [SchwartzMap.derivCLM_apply]
  rw [SchwartzMap.smulLeftCLM_apply hχ]
  rw [show deriv (fun y => χ y • φ y) x =
      χ' x • φ x + χ x • deriv (φ : ℝ → ℂ) x by
        change deriv (χ * (φ : ℝ → ℂ)) x = _
        simpa [add_comm] using ((hd x).smul (φ.hasDerivAt x)).deriv]
  simp [hχ, hχ']

omit [CompleteSpace H] in
/-- Vector-valued tempered distributions satisfy the exact smooth-multiplier Leibniz rule. -/
theorem temperedDistribution_lineDeriv_smulLeft
    (χ χ' : ℝ → ℂ)
    (hχ : χ.HasTemperateGrowth) (hχ' : χ'.HasTemperateGrowth)
    (hd : ∀ x, HasDerivAt χ (χ' x) x) (T : 𝓢'(ℝ, H)) :
    ∂_{(1 : ℝ)} (TemperedDistribution.smulLeftCLM H χ T) =
      TemperedDistribution.smulLeftCLM H χ (∂_{(1 : ℝ)} T) +
        TemperedDistribution.smulLeftCLM H χ' T := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, add_apply]
  have hprod := schwartz_deriv_smulLeft χ χ' hχ hχ' hd φ
  have hline (ψ : SchwartzMap ℝ ℂ) :
      ∂_{(1 : ℝ)} ψ = SchwartzMap.derivCLM ℂ ℂ ψ := by
    ext x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.derivCLM_apply,
      fderiv_apply_one_eq_deriv]
  have hleft :
      SchwartzMap.smulLeftCLM ℂ χ (-(SchwartzMap.derivCLM ℂ ℂ φ)) =
        -(SchwartzMap.smulLeftCLM ℂ χ (SchwartzMap.derivCLM ℂ ℂ φ)) := by
    exact (SchwartzMap.smulLeftCLM ℂ χ).map_neg _
  rw [hline φ, hline (SchwartzMap.smulLeftCLM ℂ χ φ), hprod, hleft]
  simp only [map_neg, map_add, neg_add_rev]
  abel

/-- Literal `L²` multiplication by an essentially bounded scalar cutoff. -/
def l2CutoffProduct (χ : ℝ → ℂ) (hχ : MemLp χ ∞ (volume : Measure ℝ))
    (f : Lp H 2 (volume : Measure ℝ)) : Lp H 2 (volume : Measure ℝ) :=
  hχ.toLp χ • f

/-- The literal `L²` cutoff product embeds as multiplication of the associated tempered
distribution. -/
theorem l2CutoffProduct_toTemperedDistribution
    (χ : ℝ → ℂ) (hχT : χ.HasTemperateGrowth)
    (hχ : MemLp χ ∞ (volume : Measure ℝ))
    (f : Lp H 2 (volume : Measure ℝ)) :
    (l2CutoffProduct χ hχ f : 𝓢'(ℝ, H)) =
      TemperedDistribution.smulLeftCLM H χ (f : 𝓢'(ℝ, H)) := by
  exact MeasureTheory.Lp.toTemperedDistribution_smul_eq hχT hχ f

/-- Exact Hilbert-valued `L²` weak Leibniz rule.  No pointwise derivative of `f` or `g` and no
`L¹` premise is used. -/
theorem l2CutoffProduct_weakDerivative
    (χ χ' : ℝ → ℂ)
    (hχT : χ.HasTemperateGrowth) (hχ'T : χ'.HasTemperateGrowth)
    (hχ : MemLp χ ∞ (volume : Measure ℝ))
    (hχ' : MemLp χ' ∞ (volume : Measure ℝ))
    (hd : ∀ x, HasDerivAt χ (χ' x) x)
    (f g : Lp H 2 (volume : Measure ℝ))
    (hweak : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, H)) = (g : 𝓢'(ℝ, H))) :
    ∂_{(1 : ℝ)} (l2CutoffProduct χ hχ f : 𝓢'(ℝ, H)) =
      ((l2CutoffProduct χ hχ g + l2CutoffProduct χ' hχ' f :
        Lp H 2 (volume : Measure ℝ)) : 𝓢'(ℝ, H)) := by
  rw [show ((l2CutoffProduct χ hχ g + l2CutoffProduct χ' hχ' f :
      Lp H 2 (volume : Measure ℝ)) : 𝓢'(ℝ, H)) =
      (l2CutoffProduct χ hχ g : 𝓢'(ℝ, H)) +
        (l2CutoffProduct χ' hχ' f : 𝓢'(ℝ, H)) by
    exact (MeasureTheory.Lp.toTemperedDistributionCLM H volume 2).map_add _ _]
  rw [l2CutoffProduct_toTemperedDistribution χ hχT hχ f]
  rw [temperedDistribution_lineDeriv_smulLeft χ χ' hχT hχ'T hd]
  rw [hweak]
  rw [← l2CutoffProduct_toTemperedDistribution χ hχT hχ g]
  rw [← l2CutoffProduct_toTemperedDistribution χ' hχ'T hχ' f]

end RHTower

end
