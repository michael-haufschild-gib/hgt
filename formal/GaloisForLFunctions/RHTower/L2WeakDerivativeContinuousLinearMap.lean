import GaloisForLFunctions.RHTower.VectorL2WeakDerivativeFourier

/-!
# Functoriality of `L²` weak derivatives under codomain maps

Pointwise application of a continuous linear map to an `L²` representative commutes with its
tempered-distribution embedding and with distributional differentiation.  Hence weak-derivative
pairs are stable under continuous linear maps and finite addition.  This supplies the missing
assembly layer from scalar physical sources to finite-dimensional terminal state spaces.
-/

open MeasureTheory LineDeriv
open scoped ENNReal SchwartzMap LineDeriv

noncomputable section

namespace RHTower

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Applying a continuous linear map pointwise in `L²` commutes with the canonical embedding into
tempered distributions. -/
theorem l2_toTemperedDistribution_compLp
    (L : E →L[ℂ] F) (f : Lp E 2 (volume : Measure ℝ)) :
    ((L.compLp f : Lp F 2 (volume : Measure ℝ)) : 𝓢'(ℝ, F)) =
      PointwiseConvergenceCLM.postcomp 𝓢(ℝ, ℂ) L (f : 𝓢'(ℝ, E)) := by
  ext φ
  rw [MeasureTheory.Lp.toTemperedDistribution_apply]
  have hrhs :
      (PointwiseConvergenceCLM.postcomp 𝓢(ℝ, ℂ) L (f : 𝓢'(ℝ, E))) φ =
        L ((f : 𝓢'(ℝ, E)) φ) := rfl
  rw [hrhs, MeasureTheory.Lp.toTemperedDistribution_apply]
  have hint : Integrable (fun x : ℝ => φ x • (f : ℝ → E) x) volume := by
    exact memLp_one_iff_integrable.mp
      ((Lp.memLp f).smul (φ.memLp 2 (volume : Measure ℝ)))
  rw [← L.integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [L.coeFn_compLp f] with x hx
  rw [hx, L.map_smul]

/-- Codomain continuous linear maps commute with distributional line derivatives. -/
theorem temperedDistribution_lineDeriv_comp
    (L : E →L[ℂ] F) (T : 𝓢'(ℝ, E)) :
    ∂_{(1 : ℝ)}
        (PointwiseConvergenceCLM.postcomp 𝓢(ℝ, ℂ) L T : 𝓢'(ℝ, F)) =
      PointwiseConvergenceCLM.postcomp 𝓢(ℝ, ℂ) L (∂_{(1 : ℝ)} T) := by
  ext φ
  rfl

/-- Every `L²` weak-derivative pair remains a weak-derivative pair after a codomain continuous
linear map. -/
theorem l2_weakDerivative_compLp
    (L : E →L[ℂ] F) (f g : Lp E 2 (volume : Measure ℝ))
    (hweak : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, E)) = (g : 𝓢'(ℝ, E))) :
    ∂_{(1 : ℝ)}
        (L.compLp f : 𝓢'(ℝ, F)) =
      (L.compLp g : 𝓢'(ℝ, F)) := by
  rw [l2_toTemperedDistribution_compLp,
    l2_toTemperedDistribution_compLp,
    temperedDistribution_lineDeriv_comp,
    hweak]

/-- Sums of `L²` weak-derivative pairs are weak-derivative pairs. -/
theorem l2_weakDerivative_add
    (f₀ g₀ f₁ g₁ : Lp E 2 (volume : Measure ℝ))
    (h₀ : ∂_{(1 : ℝ)} (f₀ : 𝓢'(ℝ, E)) = (g₀ : 𝓢'(ℝ, E)))
    (h₁ : ∂_{(1 : ℝ)} (f₁ : 𝓢'(ℝ, E)) = (g₁ : 𝓢'(ℝ, E))) :
    ∂_{(1 : ℝ)} ((f₀ + f₁ : Lp E 2 (volume : Measure ℝ)) : 𝓢'(ℝ, E)) =
      ((g₀ + g₁ : Lp E 2 (volume : Measure ℝ)) : 𝓢'(ℝ, E)) := by
  change ∂_{(1 : ℝ)}
      ((MeasureTheory.Lp.toTemperedDistributionCLM E volume 2) (f₀ + f₁)) =
    (MeasureTheory.Lp.toTemperedDistributionCLM E volume 2) (g₀ + g₁)
  have h₀' :
      ∂_{(1 : ℝ)} ((MeasureTheory.Lp.toTemperedDistributionCLM E volume 2) f₀) =
        (MeasureTheory.Lp.toTemperedDistributionCLM E volume 2) g₀ := h₀
  have h₁' :
      ∂_{(1 : ℝ)} ((MeasureTheory.Lp.toTemperedDistributionCLM E volume 2) f₁) =
        (MeasureTheory.Lp.toTemperedDistributionCLM E volume 2) g₁ := h₁
  rw [(MeasureTheory.Lp.toTemperedDistributionCLM E volume 2).map_add,
    (MeasureTheory.Lp.toTemperedDistributionCLM E volume 2).map_add,
    lineDerivOp_add, h₀', h₁']

end RHTower

end
