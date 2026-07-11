import GaloisForLFunctions.MeromorphicMultipleEllipticGamma
import GaloisForLFunctions.AnalyticSubringEvaluation

/-!
# The actual all-order hierarchy in the global meromorphic field

The pointwise hierarchy of the convergent kernel is promoted by denominator clearing and analytic
continuation to an unconditional identity between logarithmic derivatives of the genuine
parity-dependent multiple elliptic gamma products.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance multipleEllipticGammaFieldHierarchyDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance multipleEllipticGammaFieldHierarchyDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

omit [DecidableEq ι] in
@[simp] theorem univGermEval_multipleEllipticGammaForwardAnalytic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (z : ℂ) :
    univGermEval z
        (multipleEllipticGammaForwardAnalytic τ hτ : Germ (𝓟 Set.univ) ℂ) =
      multipleEllipticGammaForwardProduct τ z := by
  rfl

omit [DecidableEq ι] in
@[simp] theorem univGermEval_multipleEllipticGammaBackwardAnalytic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (z : ℂ) :
    univGermEval z
        (multipleEllipticGammaBackwardAnalytic τ hτ : Germ (𝓟 Set.univ) ℂ) =
      multipleEllipticGammaBackwardProduct τ z := by
  rfl

omit [DecidableEq ι] in
@[simp] theorem univGermEval_multipleEllipticGammaForwardAnalytic_deriv
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (z : ℂ) :
    univGermEval z
        (analyticSubringDeriv isOpen_univ
          (multipleEllipticGammaForwardAnalytic τ hτ) : Germ (𝓟 Set.univ) ℂ) =
      deriv (multipleEllipticGammaForwardProduct τ) z := by
  rfl

omit [DecidableEq ι] in
@[simp] theorem univGermEval_multipleEllipticGammaBackwardAnalytic_deriv
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (z : ℂ) :
    univGermEval z
        (analyticSubringDeriv isOpen_univ
          (multipleEllipticGammaBackwardAnalytic τ hτ) : Germ (𝓟 Set.univ) ℂ) =
      deriv (multipleEllipticGammaBackwardProduct τ) z := by
  rfl

omit [DecidableEq ι] in
/-- Evaluation of the concrete logarithmic-derivative fraction is the convergent additive kernel
on the regular locus. -/
theorem univGermEval_multipleEllipticGammaLogDeriv_div_eq_additiveKernel
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) {z : ℂ}
    (hzF : multipleEllipticGammaForwardProduct τ z ≠ 0)
    (hzB : multipleEllipticGammaBackwardProduct τ z ≠ 0) :
    univGermEval z
        (multipleEllipticGammaLogDerivNumeratorAnalytic τ hτ :
          Germ (𝓟 Set.univ) ℂ) /
      univGermEval z
        (multipleEllipticGammaLogDerivDenominatorAnalytic τ hτ :
          Germ (𝓟 Set.univ) ℂ) =
      multipleEllipticGammaAdditiveLogKernel τ z := by
  have h := logDeriv_multipleEllipticGammaProduct_eq_additiveKernel hτ hzF hzB
  change logDeriv (fun w => if Even (Fintype.card ι) then
      multipleEllipticGammaForwardProduct τ w /
        multipleEllipticGammaBackwardProduct τ w else
      multipleEllipticGammaForwardProduct τ w *
        multipleEllipticGammaBackwardProduct τ w) z = _ at h
  by_cases hcard : Even (Fintype.card ι)
  · simp only [multipleEllipticGammaLogDerivNumeratorAnalytic,
      multipleEllipticGammaLogDerivDenominatorAnalytic, hcard, if_true,
      univGermEval_analyticSubring_sub,
      univGermEval_analyticSubring_mul,
      univGermEval_multipleEllipticGammaForwardAnalytic,
      univGermEval_multipleEllipticGammaBackwardAnalytic,
      univGermEval_multipleEllipticGammaForwardAnalytic_deriv,
      univGermEval_multipleEllipticGammaBackwardAnalytic_deriv]
    simp only [hcard, if_true] at h
    rw [logDeriv_div z hzF hzB
      (differentiable_multipleEllipticGammaForwardProduct hτ z)
      (differentiable_multipleEllipticGammaBackwardProduct hτ z)] at h
    rw [logDeriv_apply, logDeriv_apply] at h
    field_simp [hzF, hzB] at h ⊢
    linear_combination h
  · simp only [multipleEllipticGammaLogDerivNumeratorAnalytic,
      multipleEllipticGammaLogDerivDenominatorAnalytic, hcard, if_false,
      univGermEval_analyticSubring_add,
      univGermEval_analyticSubring_mul,
      univGermEval_multipleEllipticGammaForwardAnalytic,
      univGermEval_multipleEllipticGammaBackwardAnalytic,
      univGermEval_multipleEllipticGammaForwardAnalytic_deriv,
      univGermEval_multipleEllipticGammaBackwardAnalytic_deriv]
    simp only [hcard, if_false] at h
    rw [logDeriv_mul z hzF hzB
      (differentiable_multipleEllipticGammaForwardProduct hτ z)
      (differentiable_multipleEllipticGammaBackwardProduct hτ z)] at h
    rw [logDeriv_apply, logDeriv_apply] at h
    field_simp [hzF, hzB] at h ⊢
    linear_combination h

/-- **Genuine all-order field hierarchy.** Translating the logarithmic derivative of the actual
multiple elliptic gamma product by one structural parameter gives exactly the logarithmic
derivative of the genuine coordinate-deletion product. -/
theorem multipleEllipticGammaLogDerivMero_addTranslation_sub
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (q : ι) :
    addTranslationMeroEquiv (τ q)
        (multipleEllipticGammaLogDerivMero τ hτ) -
      multipleEllipticGammaLogDerivMero τ hτ =
    multipleEllipticGammaLogDerivMero
      (fun i : {i : ι // i ≠ q} => τ i) (fun i => hτ i) := by
  let τq : {i : ι // i ≠ q} → ℂ := fun i => τ i
  let hτq : ∀ i, 0 < (τq i).im := fun i => hτ i
  let D := multipleEllipticGammaLogDerivDenominatorAnalytic τ hτ
  let E := multipleEllipticGammaLogDerivDenominatorAnalytic τq hτq
  have hmap_ne {a : analyticSubring Set.univ} (ha : a ≠ 0) :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a ≠ 0 :=
    fun hz => ha ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  have hD : D ≠ 0 := multipleEllipticGammaLogDerivDenominatorAnalytic_ne_zero τ hτ
  have hTD : addTranslationAnalyticEquiv (τ q) D ≠ 0 :=
    fun hz => hD ((addTranslationAnalyticEquiv (τ q)).injective (by simpa using hz))
  have hE : E ≠ 0 := multipleEllipticGammaLogDerivDenominatorAnalytic_ne_zero τq hτq
  dsimp [D, E] at hD hTD hE
  let R : analyticSubring Set.univ :=
    addTranslationAnalyticEquiv (τ q)
        (multipleEllipticGammaLogDerivDenominatorAnalytic τ hτ) *
      multipleEllipticGammaLogDerivDenominatorAnalytic τ hτ *
      multipleEllipticGammaLogDerivDenominatorAnalytic τq hτq
  have hR : R ≠ 0 := by
    dsimp [R]
    exact mul_ne_zero (mul_ne_zero hTD hD) hE
  obtain ⟨z₀, hz₀⟩ := exists_univGermEval_ne_zero_of_ne_zero hR
  have hreg := eventually_univGermEval_ne_zero hz₀
  rw [multipleEllipticGammaLogDerivMero_eq_div,
    multipleEllipticGammaLogDerivMero_eq_div]
  simp only [map_div₀, addTranslationMeroEquiv_algebraMap]
  field_simp [hmap_ne hD, hmap_ne hTD, hmap_ne hE]
  rw [eq_div_iff (hmap_ne hE)]
  simp only [← map_mul, ← map_sub]
  rw [(IsFractionRing.injective (analyticSubring Set.univ)
    (meroField Set.univ)).eq_iff]
  apply analyticSubring_eq_of_eventually_eval_eq (z₀ := z₀)
  filter_upwards [hreg] with z hzR
  have hzR' := hzR
  simp only [R, univGermEval_analyticSubring_mul,
    univGermEval_addTranslationAnalyticEquiv,
    multipleEllipticGammaLogDerivDenominatorAnalytic,
    univGermEval_multipleEllipticGammaForwardAnalytic,
    univGermEval_multipleEllipticGammaBackwardAnalytic,
    mul_ne_zero_iff] at hzR'
  rcases hzR' with ⟨⟨⟨hzqF, hzqB⟩, hzF, hzB⟩, hzEF, hzEB⟩
  have hKq := univGermEval_multipleEllipticGammaLogDeriv_div_eq_additiveKernel
    hτ hzqF hzqB
  have hK := univGermEval_multipleEllipticGammaLogDeriv_div_eq_additiveKernel
    hτ hzF hzB
  have hKE := univGermEval_multipleEllipticGammaLogDeriv_div_eq_additiveKernel
    hτq hzEF hzEB
  have hmix := multipleEllipticGammaAdditiveLogKernel_add_sub hτ q z
  have hratio :
      univGermEval (z + τ q)
          (multipleEllipticGammaLogDerivNumeratorAnalytic τ hτ :
            Germ (𝓟 Set.univ) ℂ) /
        univGermEval (z + τ q)
          (multipleEllipticGammaLogDerivDenominatorAnalytic τ hτ :
            Germ (𝓟 Set.univ) ℂ) -
      univGermEval z
          (multipleEllipticGammaLogDerivNumeratorAnalytic τ hτ :
            Germ (𝓟 Set.univ) ℂ) /
        univGermEval z
          (multipleEllipticGammaLogDerivDenominatorAnalytic τ hτ :
            Germ (𝓟 Set.univ) ℂ) =
      univGermEval z
          (multipleEllipticGammaLogDerivNumeratorAnalytic τq hτq :
            Germ (𝓟 Set.univ) ℂ) /
        univGermEval z
          (multipleEllipticGammaLogDerivDenominatorAnalytic τq hτq :
            Germ (𝓟 Set.univ) ℂ) := by
    rw [hKq, hK, hKE]
    exact hmix
  have hdq : univGermEval (z + τ q)
      (multipleEllipticGammaLogDerivDenominatorAnalytic τ hτ :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change multipleEllipticGammaForwardProduct τ (z + τ q) *
      multipleEllipticGammaBackwardProduct τ (z + τ q) ≠ 0
    exact mul_ne_zero hzqF hzqB
  have hd : univGermEval z
      (multipleEllipticGammaLogDerivDenominatorAnalytic τ hτ :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change multipleEllipticGammaForwardProduct τ z *
      multipleEllipticGammaBackwardProduct τ z ≠ 0
    exact mul_ne_zero hzF hzB
  have he : univGermEval z
      (multipleEllipticGammaLogDerivDenominatorAnalytic τq hτq :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change multipleEllipticGammaForwardProduct τq z *
      multipleEllipticGammaBackwardProduct τq z ≠ 0
    exact mul_ne_zero hzEF hzEB
  simp only [univGermEval_analyticSubring_mul,
    univGermEval_analyticSubring_sub,
    univGermEval_addTranslationAnalyticEquiv]
  field_simp [hdq, hd, he] at hratio
  linear_combination hratio

end

end GaloisForLFunctions
