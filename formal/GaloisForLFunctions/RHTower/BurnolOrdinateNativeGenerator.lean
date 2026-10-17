import GaloisForLFunctions.RHTower.BurnolRelativeOrdinateDifferentiability
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison

/-!
# Complete native generator classification at bounded ordinate clocks

The source below synthesizes the original Burnol columns, with every prime-depth
coefficient retained. For any bounded family of ordinate clocks its native orbit has
the bounded strong derivative constructed in `BurnolRelativeOrdinateFirstJet`.
The native difference quotients never converge in operator norm. Subtracting the
base-clock source restores the Hilbert–Schmidt derivative proved in the preceding module.
-/

open Complex ContinuousLinearMap Filter
open scoped BigOperators Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Source := lp (fun _ : RoutePPrimitiveIndex => ℂ) 2

/-- Complete synthesis of the original columns at the prescribed ordinate clocks. -/
def burnolOrdinateCoefficientSynthesis (kappa : RoutePPrimitiveIndex → ℝ) :
    Source →L[ℂ] routePBurnolHalfLineL2 :=
  burnolBaseCoefficientSynthesis + burnolRelativeOrdinateSource kappa

theorem hasSum_burnolOrdinateCoefficientSynthesis (kappa : RoutePPrimitiveIndex → ℝ) (x : Source) :
    HasSum (fun pe => (x : RoutePPrimitiveIndex → ℂ) pe •
      routePPrimitiveBurnolWindowFeatureLp pe (kappa pe)) (burnolOrdinateCoefficientSynthesis kappa x) := by
  have hr : HasSum (fun pe => (x : RoutePPrimitiveIndex → ℂ) pe •
      burnolRelativeOrdinateSourceField pe (kappa pe)) (burnolRelativeOrdinateSource kappa x) := by
    simpa only [burnolRelativeOrdinateSource_single] using
      (lp.hasSum_single (by norm_num) x).mapL (burnolRelativeOrdinateSource kappa)
  have h := (hasSum_burnolBaseCoefficientSynthesis x).add hr
  change HasSum _ (burnolBaseCoefficientSynthesis x + burnolRelativeOrdinateSource kappa x)
  convert h using 1
  funext pe
  dsimp only [burnolRelativeOrdinateSourceField]
  module

theorem burnolOrdinateCoefficientSynthesis_single (kappa : RoutePPrimitiveIndex → ℝ)
    (pe : RoutePPrimitiveIndex) (z : ℂ) :
    burnolOrdinateCoefficientSynthesis kappa (lp.single 2 pe z) =
      z • routePPrimitiveBurnolWindowFeatureLp pe (kappa pe) := by
  simp only [burnolOrdinateCoefficientSynthesis, add_apply, burnolBaseCoefficientSynthesis_single,
    burnolRelativeOrdinateSource_single, burnolRelativeOrdinateSourceField]
  module

theorem tendsto_burnolRelativeOrdinateDifferenceQuotient
    (kappa : RoutePPrimitiveIndex → ℝ) (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) :
    Tendsto (burnolRelativeOrdinateDifferenceQuotient kappa) (𝓝[>] (0 : ℝ))
      (𝓝 (-burnolRelativeOrdinateFirstJetSynthesis kappa hkappa)) := by
  have hn : Tendsto (fun c => ‖burnolRelativeOrdinateDifferenceQuotient kappa c +
      burnolRelativeOrdinateFirstJetSynthesis kappa hkappa‖) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun c =>
      norm_le_hsNorm ((isHilbertSchmidt_burnolRelativeOrdinateDifferenceQuotient kappa c).add
        (isHilbertSchmidt_burnolRelativeOrdinateFirstJetSynthesis kappa hkappa)))
      (tendsto_hsNorm_burnolRelativeOrdinateDifferenceQuotient kappa hkappa)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_neg_eq_add] using hn

def burnolOrdinateNativeDifferenceQuotient (kappa : RoutePPrimitiveIndex → ℝ) (c : ℝ) :
    Source →L[ℂ] routePBurnolHalfLineL2 :=
  c⁻¹ • (burnolWeightedShift c.toNNReal ∘L burnolOrdinateCoefficientSynthesis kappa -
    burnolOrdinateCoefficientSynthesis kappa)

private theorem real_inv_smul_eq_complex (c : ℝ) (x : routePBurnolHalfLineL2) :
    (c⁻¹ : ℝ) • x = ((c⁻¹ : ℝ) : ℂ) • x := by
  symm
  exact IsScalarTower.algebraMap_smul (R := ℝ) (M := routePBurnolHalfLineL2) ℂ (c⁻¹) x

theorem burnolOrdinateNativeDifferenceQuotient_eq (kappa : RoutePPrimitiveIndex → ℝ) (c : ℝ) :
    burnolOrdinateNativeDifferenceQuotient kappa c =
      burnolBaseNativeDifferenceQuotient c + burnolRelativeOrdinateDifferenceQuotient kappa c := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [burnolOrdinateNativeDifferenceQuotient, burnolBaseNativeDifferenceQuotient,
    burnolRelativeOrdinateDifferenceQuotient, burnolOrdinateCoefficientSynthesis,
    add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply, map_add]
  rw [← real_inv_smul_eq_complex]
  module

/-- The actual native right derivative on every complete source coefficient vector. -/
theorem tendsto_burnolOrdinateNativeDifferenceQuotient
    (kappa : RoutePPrimitiveIndex → ℝ) (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M) (x : Source) :
    Tendsto (fun c => burnolOrdinateNativeDifferenceQuotient kappa c x) (𝓝[>] (0 : ℝ))
      (𝓝 (-burnolOrdinateFirstJetSynthesis kappa hkappa x)) := by
  have happ : Continuous (fun T : Source →L[ℂ] routePBurnolHalfLineL2 => T x) := by fun_prop
  have hr := (happ.tendsto (-burnolRelativeOrdinateFirstJetSynthesis kappa hkappa)).comp
    (tendsto_burnolRelativeOrdinateDifferenceQuotient kappa hkappa)
  have h := (tendsto_burnolBaseNativeDifferenceQuotient x).add hr
  simpa only [burnolOrdinateNativeDifferenceQuotient_eq, burnolOrdinateFirstJetSynthesis,
    add_apply, neg_apply, neg_add, Function.comp_apply] using! h

/-- Relative smoothing cannot remove the noncompact absolute first-jet obstruction. -/
theorem not_tendsto_burnolOrdinateNativeDifferenceQuotient
    (kappa : RoutePPrimitiveIndex → ℝ) (hkappa : ∃ M : ℝ, ∀ pe, |kappa pe| ≤ M)
    (L : Source →L[ℂ] routePBurnolHalfLineL2) :
    ¬ Tendsto (burnolOrdinateNativeDifferenceQuotient kappa) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  intro hL
  apply not_tendsto_burnolBaseNativeDifferenceQuotient
    (L - (-burnolRelativeOrdinateFirstJetSynthesis kappa hkappa))
  have h := hL.sub (tendsto_burnolRelativeOrdinateDifferenceQuotient kappa hkappa)
  simpa only [burnolOrdinateNativeDifferenceQuotient_eq, add_sub_cancel_right] using h

end

end RHTower
