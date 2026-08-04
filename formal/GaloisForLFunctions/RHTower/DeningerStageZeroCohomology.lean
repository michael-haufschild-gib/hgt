import GaloisForLFunctions.RHTower.DeningerClosedOneForm
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The zeroth cohomology of a character stage

A character stage is connected, so a closed holomorphic zero-form on it is constant: its
cohomology in degree zero is the constants.  This is the case `k = 0` of the identification of the
cohomology of a stage with the exterior algebra on its lattice.

* `deningerStageTorus_isPreconnected` : the stage is connected.
* `deningerStage_closed_zero_form_const` : a closed zero-form is constant on the stage.
-/

namespace RHTower

open Filter Topology

section ZeroForms

variable {r : ℕ}

/-- **A character stage is connected.** -/
theorem deningerStageTorus_isPreconnected (r : ℕ) : IsPreconnected (deningerStageTorus r) := by
  have hset : deningerStageTorus r = Set.univ.pi fun _ : Fin r => ({0}ᶜ : Set ℂ) := by
    ext z
    simp [deningerStageTorus, Set.mem_pi]
  rw [hset]
  refine isPreconnected_univ_pi fun _ => ?_
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  exact (isConnected_compl_singleton_of_one_lt_rank hrank (0 : ℂ)).isPreconnected

/-- The function underlying a zero-form. -/
noncomputable def deningerZeroFormValue (H : DeningerStageForm r 0) (z : Fin r → ℂ) : ℂ :=
  (ContinuousAlternatingMap.constOfIsEmptyLIE ℂ (Fin r → ℂ) ℂ (Fin 0)).symm (H z)

theorem deningerZeroForm_eq (H : DeningerStageForm r 0) (z : Fin r → ℂ) :
    H z = ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin r → ℂ) (Fin 0)
      (deningerZeroFormValue H z) := by
  exact ((ContinuousAlternatingMap.constOfIsEmptyLIE ℂ (Fin r → ℂ) ℂ
    (Fin 0)).apply_symm_apply (H z)).symm

theorem deningerZeroFormValue_analyticAt {H : DeningerStageForm r 0} {z : Fin r → ℂ}
    (hH : AnalyticAt ℂ H z) : AnalyticAt ℂ (deningerZeroFormValue H) z := by
  have hclm := ContinuousLinearMap.analyticAt
    ((ContinuousAlternatingMap.constOfIsEmptyLIE ℂ (Fin r → ℂ) ℂ
      (Fin 0)).symm.toContinuousLinearEquiv.toContinuousLinearMap) (H z)
  exact hclm.comp hH

/-- A closed zero-form has vanishing derivative. -/
theorem deningerZeroFormValue_fderiv_eq_zero {H : DeningerStageForm r 0} {z : Fin r → ℂ}
    (hclosed : extDeriv H z = 0) : fderiv ℂ (deningerZeroFormValue H) z = 0 := by
  have hHeq : H = fun y => ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin r → ℂ) (Fin 0)
      (deningerZeroFormValue H y) := funext fun y => deningerZeroForm_eq H y
  rw [hHeq, extDeriv_constOfIsEmpty] at hclosed
  have hlie : (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := Fin r → ℂ) (F := ℂ)
      (ι := Fin 1) (0 : Fin 1)) (fderiv ℂ (deningerZeroFormValue H) z) = 0 := hclosed
  have := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := Fin r → ℂ) (F := ℂ)
    (ι := Fin 1) (0 : Fin 1)).injective
  apply this
  rw [hlie, map_zero]

/-- **A closed holomorphic zero-form is constant on the stage**: the zeroth cohomology of a
character stage is the constants. -/
theorem deningerStage_closed_zero_form_const {H : DeningerStageForm r 0}
    (hH : DeningerIsHolomorphicForm H)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv H z = 0)
    {z w : Fin r → ℂ} (hz : z ∈ deningerStageTorus r) (hw : w ∈ deningerStageTorus r) :
    H z = H w := by
  set f : (Fin r → ℂ) → ℂ := deningerZeroFormValue H with hf
  have hana : AnalyticOnNhd ℂ f (deningerStageTorus r) := fun y hy =>
    deningerZeroFormValue_analyticAt (hH y hy)
  have hzero : ∀ y ∈ deningerStageTorus r, fderiv ℂ f y = 0 := fun y hy =>
    deningerZeroFormValue_fderiv_eq_zero (hclosed y hy)
  -- the function is locally constant, hence constant by the identity theorem
  have hloc : f =ᶠ[𝓝 z] fun _ => f z := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (deningerStageTorus_isOpen r) z hz
    filter_upwards [Metric.ball_mem_nhds z hε] with y hy
    refine (convex_ball z ε).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) ?_ ?_ hy
      (Metric.mem_ball_self hε)
    · intro x hx
      exact ((hana x (hball hx)).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx]
      exact hzero x (hball hx)
  have heq := hana.eqOn_of_preconnected_of_eventuallyEq (g := fun _ => f z)
    (analyticOnNhd_const) (deningerStageTorus_isPreconnected r) hz hloc
  have hfw : f w = f z := heq hw
  rw [deningerZeroForm_eq H z, deningerZeroForm_eq H w, ← hf, hfw]

end ZeroForms

end RHTower
