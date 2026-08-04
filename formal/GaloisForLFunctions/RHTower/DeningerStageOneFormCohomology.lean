import GaloisForLFunctions.RHTower.DeningerStageOneFormExact
import GaloisForLFunctions.RHTower.DeningerDlogIndependence

/-!
# The first cohomology of a character stage, in the language of forms

Every closed holomorphic one-form on a character stage is a combination of the logarithmic
differentials plus the exterior derivative of a zero-form, and the coefficients are unique.  This
is the identification of the first cohomology of a stage with the lattice tensored with the complex
numbers, stated entirely in terms of stage forms.

* `deningerStage_one_form_cohomology` : the decomposition of a closed one-form.
* `deningerStage_one_form_cohomology_unique` : uniqueness of the coefficients.
-/

namespace RHTower

open Complex

section OneFormCohomology

variable {r : ℕ}

/-- The functional of a one-form recovers the form. -/
theorem deningerOfSubsingleton_formFunctional (ω : DeningerStageForm r 1) (z : Fin r → ℂ) :
    ContinuousAlternatingMap.ofSubsingleton ℂ (Fin r → ℂ) ℂ (0 : Fin 1)
      (deningerFormFunctional ω z) = ω z := by
  ext v
  show deningerFormFunctional ω z (v 0) = ω z v
  rw [deningerFormFunctional_apply]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]

/-- The functional of a combination of logarithmic differentials recovers the combination. -/
theorem deningerOfSubsingleton_dlogComb (c : Fin r → ℂ) (z : Fin r → ℂ) :
    ContinuousAlternatingMap.ofSubsingleton ℂ (Fin r → ℂ) ℂ (0 : Fin 1)
      (deningerDlogCombFunctional c z) = ∑ j, c j • deningerDlogForm r j z := by
  ext v
  show deningerDlogCombFunctional c z (v 0) = (∑ j, c j • deningerDlogForm r j z) v
  rw [deningerDlogCombFunctional_apply, ContinuousAlternatingMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  show c j * (z j)⁻¹ * v 0 j = c j * ((z j)⁻¹ * v 0 j)
  ring

theorem deningerOfSubsingleton_sub (A B : (Fin r → ℂ) →L[ℂ] ℂ) :
    ContinuousAlternatingMap.ofSubsingleton ℂ (Fin r → ℂ) ℂ (0 : Fin 1) (A - B) =
      ContinuousAlternatingMap.ofSubsingleton ℂ (Fin r → ℂ) ℂ (0 : Fin 1) A -
        ContinuousAlternatingMap.ofSubsingleton ℂ (Fin r → ℂ) ℂ (0 : Fin 1) B := by
  ext v
  rfl

/-- **Every closed holomorphic one-form on a character stage is a combination of the logarithmic
differentials plus an exact form**, stated in the language of stage forms. -/
theorem deningerStage_one_form_cohomology (ω : DeningerStageForm r 1)
    (hω : DeningerIsHolomorphicForm ω)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0) :
    ∃ (c : Fin r → ℂ) (H : DeningerStageForm r 0), ∀ z ∈ deningerStageTorus r,
      ω z = (∑ j, c j • deningerDlogForm r j z) + extDeriv H z := by
  obtain ⟨c, h, hh⟩ := deningerStage_closed_one_form_exact hω hclosed
  refine ⟨c, fun z => ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin r → ℂ) (Fin 0) (h z),
    fun z hz => ?_⟩
  have hfd : fderiv ℂ h z = deningerFormFunctional ω z - deningerDlogCombFunctional c z :=
    (hh z hz).fderiv
  rw [extDeriv_constOfIsEmpty, hfd, deningerOfSubsingleton_sub,
    deningerOfSubsingleton_formFunctional, deningerOfSubsingleton_dlogComb]
  abel

/-- **The coefficients are unique**: the classes of the logarithmic differentials are independent in
the first cohomology of a character stage. -/
theorem deningerStage_one_form_cohomology_unique (c c' : Fin r → ℂ) (H H' : DeningerStageForm r 0)
    (hH : DeningerIsHolomorphicForm H) (hH' : DeningerIsHolomorphicForm H')
    (heq : ∀ z ∈ deningerStageTorus r,
      (∑ j, c j • deningerDlogForm r j z) + extDeriv H z =
        (∑ j, c' j • deningerDlogForm r j z) + extDeriv H' z) (i : Fin r) :
    c i = c' i := by
  have hK : ∀ z ∈ deningerStageTorus r, extDeriv (H' + (-1 : ℂ) • H) z =
      ∑ j, (fun l => c l - c' l) j • deningerDlogForm r j z := by
    intro z hz
    have hd1 : DifferentiableAt ℂ H z := (hH z hz).differentiableAt
    have hd2 : DifferentiableAt ℂ H' z := (hH' z hz).differentiableAt
    have hsmul : DifferentiableAt ℂ ((-1 : ℂ) • H) z := hd1.const_smul _
    rw [extDeriv_add hd2 hsmul, extDeriv_smul]
    have h2 := heq z hz
    have hsub : ∑ j, (c j - c' j) • deningerDlogForm r j z =
        (∑ j, c j • deningerDlogForm r j z) - ∑ j, c' j • deningerDlogForm r j z := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      module
    rw [hsub]
    linear_combination (norm := module) -h2
  have hKhol : DeningerIsHolomorphicForm (H' + (-1 : ℂ) • H) := by
    intro z hz
    exact (hH' z hz).add (analyticAt_const.smul (hH z hz))
  have := deningerDlogForm_independent (fun l => c l - c' l) i (H' + (-1 : ℂ) • H) hKhol hK
  exact sub_eq_zero.1 this

end OneFormCohomology

end RHTower
