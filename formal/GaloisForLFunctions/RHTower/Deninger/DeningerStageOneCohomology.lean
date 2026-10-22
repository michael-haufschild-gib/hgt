import GaloisForLFunctions.RHTower.Deninger.DeningerPuncturedPrimitive
import GaloisForLFunctions.RHTower.Deninger.DeningerDlogIndependence

/-!
# The first cohomology of a one-dimensional character stage

On the one-dimensional character stage `ℂ^×` every holomorphic differential is a multiple of the
logarithmic differential plus an exact one, and the multiple is unique.  So the first cohomology of
the stage is the line spanned by `d log z`, which is the case `r = k = 1` of the identification of
the cohomology of a character stage with the exterior algebra on its lattice.

* `deningerStageOne_form_apply` : a one-form on the stage is its coefficient times the coordinate
  differential.
* `deningerStageOne_cohomology` : every holomorphic one-form is `c · d log z + d H`.
* `deningerStageOne_cohomology_unique` : the coefficient `c` is unique.
-/

namespace RHTower

open Complex

section StageOne

/-- The coordinate direction of the one-dimensional stage. -/
def deningerStageOneVector : Fin 1 → ℂ := fun _ => 1

/-- A form of degree one on a one-dimensional stage is evaluated through the corresponding
functional. -/
theorem deningerStageOne_symm_apply (A : (Fin 1 → ℂ) [⋀^Fin 1]→L[ℂ] ℂ)
    (v : Fin 1 → (Fin 1 → ℂ)) :
    A v = ((ContinuousAlternatingMap.ofSubsingleton ℂ (Fin 1 → ℂ) ℂ (0 : Fin 1)).symm A) (v 0) := by
  conv_lhs =>
    rw [← (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin 1 → ℂ) ℂ (0 : Fin 1)).apply_symm_apply A]
  rfl

/-- **A one-form on the one-dimensional stage is its coefficient times the coordinate
differential.** -/
theorem deningerStageOne_form_apply (A : (Fin 1 → ℂ) [⋀^Fin 1]→L[ℂ] ℂ)
    (v : Fin 1 → (Fin 1 → ℂ)) :
    A v = v 0 0 * A (fun _ => deningerStageOneVector) := by
  have hv : v 0 = (v 0 0) • deningerStageOneVector := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp [deningerStageOneVector]
  calc A v
      = ((ContinuousAlternatingMap.ofSubsingleton ℂ (Fin 1 → ℂ) ℂ (0 : Fin 1)).symm A) (v 0) :=
        deningerStageOne_symm_apply A v
    _ = ((ContinuousAlternatingMap.ofSubsingleton ℂ (Fin 1 → ℂ) ℂ (0 : Fin 1)).symm A)
          ((v 0 0) • deningerStageOneVector) := congrArg _ hv
    _ = v 0 0 * ((ContinuousAlternatingMap.ofSubsingleton ℂ (Fin 1 → ℂ) ℂ (0 : Fin 1)).symm A)
          deningerStageOneVector := by rw [map_smul, smul_eq_mul]
    _ = v 0 0 * A (fun _ => deningerStageOneVector) := by
        rw [deningerStageOne_symm_apply A (fun _ => deningerStageOneVector)]

/-- **Every holomorphic one-form on the one-dimensional stage is a multiple of the logarithmic
differential plus an exact form.** -/
theorem deningerStageOne_cohomology (ω : DeningerStageForm 1 1)
    (hω : DeningerIsHolomorphicForm ω) :
    ∃ (c : ℂ) (H : DeningerStageForm 1 0), DeningerIsHolomorphicForm H ∧
      ∀ z ∈ deningerStageTorus 1, ω z = c • deningerDlogForm 1 0 z + extDeriv H z := by
  classical
  set f : ℂ → ℂ := fun w => ω (fun _ => w) (fun _ => deningerStageOneVector) with hf
  have hmem : ∀ w : ℂ, w ≠ 0 → (fun _ : Fin 1 => w) ∈ deningerStageTorus 1 := fun w hw _ => hw
  have hfdiff : ∀ w : ℂ, w ≠ 0 → DifferentiableAt ℂ f w := by
    intro w hw
    have hωd : DifferentiableAt ℂ ω (fun _ : Fin 1 => w) := (hω _ (hmem w hw)).differentiableAt
    have hev : DifferentiableAt ℂ (fun y => ω y (fun _ => deningerStageOneVector))
        (fun _ : Fin 1 => w) :=
      hωd.continuousAlternatingMap_apply fun _ => differentiableAt_const _
    exact hev.comp w
      ((ContinuousLinearMap.pi fun _ : Fin 1 =>
        ContinuousLinearMap.id ℂ ℂ).differentiableAt)
  obtain ⟨h, hh⟩ := deningerPuncturedDecomposition f hfdiff
  set c : ℂ := (2 * Real.pi * Complex.I)⁻¹ * deningerPuncturedPeriod f with hc
  have hopen : IsOpen {w : ℂ | w ≠ 0} := isOpen_ne
  have hhol : AnalyticOnNhd ℂ h {w : ℂ | w ≠ 0} := by
    refine DifferentiableOn.analyticOnNhd ?_ hopen
    intro w hw
    exact ((hh w hw).differentiableAt).differentiableWithinAt
  refine ⟨c, fun z => ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin 1 → ℂ) (Fin 0) (h (z 0)),
    ?_, ?_⟩
  · intro z hz
    have hcoord : AnalyticAt ℂ (fun y : Fin 1 → ℂ => h (y 0)) z :=
      AnalyticAt.comp (f := fun y : Fin 1 → ℂ => y 0) (hhol (z 0) (hz 0))
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt z)
    exact (ContinuousLinearMap.analyticAt
      ((ContinuousAlternatingMap.constOfIsEmptyLIE ℂ (Fin 1 → ℂ) ℂ
        (Fin 0)).toContinuousLinearEquiv.toContinuousLinearMap) _).comp hcoord
  · intro z hz
    have hz0 : z 0 ≠ 0 := hz 0
    have hcoordderiv : HasDerivAt h (f (z 0) - c * (z 0)⁻¹) (z 0) := hh (z 0) hz0
    have hfderiv : HasFDerivAt (fun y : Fin 1 → ℂ => h (y 0))
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (f (z 0) - c * (z 0)⁻¹)).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0)) z :=
      (hcoordderiv.hasFDerivAt).comp z
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).hasFDerivAt
    ext v
    rw [extDeriv_constOfIsEmpty (fun y : Fin 1 → ℂ => h (y 0)) z, hfderiv.fderiv]
    have hzeq : (fun _ : Fin 1 => z 0) = z := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi]
    have hωval : ω z v = v 0 0 * f (z 0) := by
      rw [deningerStageOne_form_apply (ω z) v]
      congr 1
      show (ω z) (fun _ => deningerStageOneVector) =
        (ω fun _ : Fin 1 => z 0) (fun _ => deningerStageOneVector)
      rw [hzeq]
    rw [hωval]
    show v 0 0 * f (z 0) =
      c * ((z 0)⁻¹ * v 0 0) + (v 0 0) * (f (z 0) - c * (z 0)⁻¹)
    ring

/-- **The multiple is unique**: the first cohomology of the one-dimensional stage is the line
spanned by the logarithmic differential. -/
theorem deningerStageOne_cohomology_unique (c c' : ℂ) (H H' : DeningerStageForm 1 0)
    (hH : DeningerIsHolomorphicForm H) (hH' : DeningerIsHolomorphicForm H')
    (heq : ∀ z ∈ deningerStageTorus 1,
      c • deningerDlogForm 1 0 z + extDeriv H z = c' • deningerDlogForm 1 0 z + extDeriv H' z) :
    c = c' := by
  have hK : ∀ z ∈ deningerStageTorus 1, extDeriv (H' + (-1 : ℂ) • H) z =
      ∑ j : Fin 1, (fun _ : Fin 1 => c - c') j • deningerDlogForm 1 j z := by
    intro z hz
    have hd1 : DifferentiableAt ℂ H z := (hH z hz).differentiableAt
    have hd2 : DifferentiableAt ℂ H' z := (hH' z hz).differentiableAt
    have hsmul : DifferentiableAt ℂ ((-1 : ℂ) • H) z := hd1.const_smul _
    rw [extDeriv_add hd2 hsmul, extDeriv_smul, Fin.sum_univ_one]
    have h2 := heq z hz
    linear_combination (norm := module) -h2
  have hKhol : DeningerIsHolomorphicForm (H' + (-1 : ℂ) • H) := by
    intro z hz
    exact (hH' z hz).add (analyticAt_const.smul (hH z hz))
  have := deningerDlogForm_independent (fun _ : Fin 1 => c - c') 0 (H' + (-1 : ℂ) • H) hKhol hK
  exact sub_eq_zero.1 this

end StageOne

end RHTower
