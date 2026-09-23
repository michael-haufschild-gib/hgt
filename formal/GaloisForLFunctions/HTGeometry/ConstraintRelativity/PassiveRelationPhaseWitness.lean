import GaloisForLFunctions.HTGeometry.ConstraintRelativity.PassiveRelationTriangle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases

namespace HTGeometry.ConstraintRelativity.PassiveRelationTriangle

abbrev PhaseQubit := EuclideanSpace ℂ (Fin 2)

def phaseVec (z₀ z₁ : ℂ) : PhaseQubit := WithLp.toLp 2 ![z₀, z₁]

@[simp] theorem phaseVec_zero (z₀ z₁ : ℂ) : phaseVec z₀ z₁ 0 = z₀ := rfl
@[simp] theorem phaseVec_one (z₀ z₁ : ℂ) : phaseVec z₀ z₁ 1 = z₁ := rfl

theorem phase_inner (z₀ z₁ w₀ w₁ : ℂ) :
    inner ℂ (phaseVec z₀ z₁) (phaseVec w₀ w₁) =
      (starRingEnd ℂ) z₀ * w₀ + (starRingEnd ℂ) z₁ * w₁ := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [phaseVec, RCLike.inner_apply]
  ring

theorem starProjection_span_eq_of_inner_sub_eq_zero
    (u x v : PhaseQubit) (hv : v ∈ ℂ ∙ u) (horth : inner ℂ (x - v) u = 0) :
    (ℂ ∙ u).starProjection x = v := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hv
  intro w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  simp [inner_smul_right, horth]

noncomputable def phaseTriangle (u₂ : PhaseQubit) :
    PassiveRelationTriangle PhaseQubit PhaseQubit PhaseQubit where
  L₀ := ℂ ∙ phaseVec 1 0
  L₁ := ℂ ∙ phaseVec 1 1
  L₂ := ℂ ∙ u₂
  projectable₀ := inferInstance
  projectable₁ := inferInstance
  projectable₂ := inferInstance
  U₀ := LinearIsometryEquiv.refl ℂ PhaseQubit
  U₁ := LinearIsometryEquiv.refl ℂ PhaseQubit
  U₂ := LinearIsometryEquiv.refl ℂ PhaseQubit
  rawFlat := by simp

def phaseU₂Plus : PhaseQubit := phaseVec 1 Complex.I
def phaseU₂Minus : PhaseQubit := phaseVec 1 (-Complex.I)
def phaseInput : PhaseQubit := phaseVec 1 0

theorem phase_project₁ :
    (ℂ ∙ phaseVec 1 1).starProjection phaseInput = phaseVec (1 / 2) (1 / 2) := by
  apply starProjection_span_eq_of_inner_sub_eq_zero
  · exact Submodule.mem_span_singleton.mpr ⟨(1 / 2 : ℂ), by ext i; fin_cases i <;> norm_num [phaseVec]⟩
  · rw [inner_sub_left]
    simp only [phaseInput, phase_inner]
    norm_num [map_ofNat]

theorem phase_project₂_plus :
    (ℂ ∙ phaseU₂Plus).starProjection (phaseVec (1 / 2) (1 / 2)) =
      phaseVec ((1 - Complex.I) / 4) ((1 + Complex.I) / 4) := by
  apply starProjection_span_eq_of_inner_sub_eq_zero
  · exact Submodule.mem_span_singleton.mpr ⟨((1 - Complex.I) / 4 : ℂ), by
      ext i
      fin_cases i <;> apply Complex.ext <;> norm_num [phaseU₂Plus, phaseVec]⟩
  · rw [inner_sub_left]
    simp only [phaseU₂Plus, phase_inner]
    apply Complex.ext <;> norm_num [map_ofNat, Complex.div_re, Complex.div_im]

theorem phase_project₂_minus :
    (ℂ ∙ phaseU₂Minus).starProjection (phaseVec (1 / 2) (1 / 2)) =
      phaseVec ((1 + Complex.I) / 4) ((1 - Complex.I) / 4) := by
  apply starProjection_span_eq_of_inner_sub_eq_zero
  · exact Submodule.mem_span_singleton.mpr ⟨((1 + Complex.I) / 4 : ℂ), by
      ext i
      fin_cases i <;> apply Complex.ext <;> norm_num [phaseU₂Minus, phaseVec]⟩
  · rw [inner_sub_left]
    simp only [phaseU₂Minus, phase_inner]
    apply Complex.ext <;> norm_num [map_ofNat, Complex.div_re, Complex.div_im]

theorem phase_project₀ (z₀ z₁ : ℂ) :
    (ℂ ∙ phaseVec 1 0).starProjection (phaseVec z₀ z₁) = phaseVec z₀ 0 := by
  apply starProjection_span_eq_of_inner_sub_eq_zero
  · exact Submodule.mem_span_singleton.mpr ⟨z₀, by ext i; fin_cases i <;> simp [phaseVec]⟩
  · rw [inner_sub_left, phase_inner, phase_inner]
    simp

theorem phase_norm_sq (z₀ z₁ : ℂ) :
    ‖phaseVec z₀ z₁‖ ^ (2 : ℕ) = ‖z₀‖ ^ (2 : ℕ) + ‖z₁‖ ^ (2 : ℕ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Fin.sum_univ_two]
  rfl

theorem phase_stage₁ (u₂ : PhaseQubit) :
    (phaseTriangle u₂).stage₁ phaseInput = phaseVec (1 / 2) (1 / 2) := by
  change (ℂ ∙ phaseVec 1 1).starProjection phaseInput = _
  exact phase_project₁

theorem phase_stage₂_plus :
    (phaseTriangle phaseU₂Plus).stage₂ phaseInput =
      phaseVec ((1 - Complex.I) / 4) ((1 + Complex.I) / 4) := by
  change (ℂ ∙ phaseU₂Plus).starProjection
      ((phaseTriangle phaseU₂Plus).stage₁ phaseInput) = _
  rw [phase_stage₁]
  exact phase_project₂_plus

theorem phase_stage₂_minus :
    (phaseTriangle phaseU₂Minus).stage₂ phaseInput =
      phaseVec ((1 + Complex.I) / 4) ((1 - Complex.I) / 4) := by
  change (ℂ ∙ phaseU₂Minus).starProjection
      ((phaseTriangle phaseU₂Minus).stage₁ phaseInput) = _
  rw [phase_stage₁]
  exact phase_project₂_minus

theorem phase_cycle_plus :
    (phaseTriangle phaseU₂Plus).cycleOutput phaseInput =
      phaseVec ((1 - Complex.I) / 4) 0 := by
  change (ℂ ∙ phaseVec 1 0).starProjection
      ((phaseTriangle phaseU₂Plus).stage₂ phaseInput) = _
  rw [phase_stage₂_plus]
  exact phase_project₀ _ _

theorem phase_cycle_minus :
    (phaseTriangle phaseU₂Minus).cycleOutput phaseInput =
      phaseVec ((1 + Complex.I) / 4) 0 := by
  change (ℂ ∙ phaseVec 1 0).starProjection
      ((phaseTriangle phaseU₂Minus).stage₂ phaseInput) = _
  rw [phase_stage₂_minus]
  exact phase_project₀ _ _

theorem phaseInput_mem (u₂ : PhaseQubit) : phaseInput ∈ (phaseTriangle u₂).L₀ := by
  exact Submodule.mem_span_singleton_self _

theorem phase_selected_plus :
    (phaseTriangle phaseU₂Plus).selectedHolonomy phaseInput =
      phaseVec ((1 - Complex.I) / 4) 0 := by
  rw [(phaseTriangle phaseU₂Plus).selectedHolonomy_of_mem (phaseInput_mem _), phase_cycle_plus]

theorem phase_selected_minus :
    (phaseTriangle phaseU₂Minus).selectedHolonomy phaseInput =
      phaseVec ((1 + Complex.I) / 4) 0 := by
  rw [(phaseTriangle phaseU₂Minus).selectedHolonomy_of_mem (phaseInput_mem _), phase_cycle_minus]

theorem phase_selected_conjugate :
    (starRingEnd ℂ) ((phaseTriangle phaseU₂Plus).selectedHolonomy phaseInput 0) =
      (phaseTriangle phaseU₂Minus).selectedHolonomy phaseInput 0 := by
  rw [phase_selected_plus, phase_selected_minus]
  apply Complex.ext <;> norm_num [phaseVec, Complex.div_re, Complex.div_im]

theorem phase_selected_ne :
    (phaseTriangle phaseU₂Plus).selectedHolonomy phaseInput ≠
      (phaseTriangle phaseU₂Minus).selectedHolonomy phaseInput := by
  rw [phase_selected_plus, phase_selected_minus]
  intro h
  have hzero := congrArg (fun z : PhaseQubit => z 0) h
  have him := congrArg Complex.im hzero
  norm_num [phaseVec, Complex.div_im] at him

theorem phase_leakA (u₂ : PhaseQubit) :
    (phaseTriangle u₂).leakA phaseInput = phaseVec (1 / 2) (-1 / 2) := by
  change (ℂ ∙ phaseVec 1 1)ᗮ.starProjection phaseInput = _
  rw [Submodule.starProjection_orthogonal_val, phase_project₁]
  ext i
  fin_cases i <;> norm_num [phaseInput, phaseVec]

theorem phase_leakB_plus :
    (phaseTriangle phaseU₂Plus).leakB phaseInput =
      phaseVec ((1 + Complex.I) / 4) ((1 - Complex.I) / 4) := by
  change (ℂ ∙ phaseU₂Plus)ᗮ.starProjection
      ((phaseTriangle phaseU₂Plus).stage₁ phaseInput) = _
  rw [Submodule.starProjection_orthogonal_val, phase_stage₁, phase_project₂_plus]
  ext i
  fin_cases i <;> apply Complex.ext <;> norm_num [phaseVec]

theorem phase_leakB_minus :
    (phaseTriangle phaseU₂Minus).leakB phaseInput =
      phaseVec ((1 - Complex.I) / 4) ((1 + Complex.I) / 4) := by
  change (ℂ ∙ phaseU₂Minus)ᗮ.starProjection
      ((phaseTriangle phaseU₂Minus).stage₁ phaseInput) = _
  rw [Submodule.starProjection_orthogonal_val, phase_stage₁, phase_project₂_minus]
  ext i
  fin_cases i <;> apply Complex.ext <;> norm_num [phaseVec]

theorem phase_leakC_plus :
    (phaseTriangle phaseU₂Plus).leakC phaseInput =
      phaseVec 0 ((1 + Complex.I) / 4) := by
  change (ℂ ∙ phaseVec 1 0)ᗮ.starProjection
      ((phaseTriangle phaseU₂Plus).stage₂ phaseInput) = _
  rw [Submodule.starProjection_orthogonal_val, phase_stage₂_plus, phase_project₀]
  ext i
  fin_cases i <;> simp [phaseVec]

theorem phase_leakC_minus :
    (phaseTriangle phaseU₂Minus).leakC phaseInput =
      phaseVec 0 ((1 - Complex.I) / 4) := by
  change (ℂ ∙ phaseVec 1 0)ᗮ.starProjection
      ((phaseTriangle phaseU₂Minus).stage₂ phaseInput) = _
  rw [Submodule.starProjection_orthogonal_val, phase_stage₂_minus, phase_project₀]
  ext i
  fin_cases i <;> simp [phaseVec]

theorem phase_leakA_energy (u₂ : PhaseQubit) :
    ‖(phaseTriangle u₂).leakA phaseInput‖ ^ (2 : ℕ) = 1 / 2 := by
  rw [phase_leakA, phase_norm_sq]
  norm_num [Complex.sq_norm, Complex.normSq_apply]

theorem phase_leakB_plus_energy :
    ‖(phaseTriangle phaseU₂Plus).leakB phaseInput‖ ^ (2 : ℕ) = 1 / 4 := by
  rw [phase_leakB_plus, phase_norm_sq]
  have hp : ‖(1 + Complex.I : ℂ)‖ ^ (2 : ℕ) = 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  have hm : ‖(1 - Complex.I : ℂ)‖ ^ (2 : ℕ) = 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  rw [norm_div, norm_div, div_pow, div_pow, hp, hm]
  norm_num

theorem phase_leakB_minus_energy :
    ‖(phaseTriangle phaseU₂Minus).leakB phaseInput‖ ^ (2 : ℕ) = 1 / 4 := by
  rw [phase_leakB_minus, phase_norm_sq]
  have hp : ‖(1 + Complex.I : ℂ)‖ ^ (2 : ℕ) = 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  have hm : ‖(1 - Complex.I : ℂ)‖ ^ (2 : ℕ) = 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  rw [norm_div, norm_div, div_pow, div_pow, hp, hm]
  norm_num

theorem phase_leakC_plus_energy :
    ‖(phaseTriangle phaseU₂Plus).leakC phaseInput‖ ^ (2 : ℕ) = 1 / 8 := by
  rw [phase_leakC_plus, phase_norm_sq]
  have hp : ‖(1 + Complex.I : ℂ)‖ ^ (2 : ℕ) = 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  rw [norm_zero, zero_pow (by norm_num), zero_add, norm_div, div_pow, hp]
  norm_num

theorem phase_leakC_minus_energy :
    ‖(phaseTriangle phaseU₂Minus).leakC phaseInput‖ ^ (2 : ℕ) = 1 / 8 := by
  rw [phase_leakC_minus, phase_norm_sq]
  have hm : ‖(1 - Complex.I : ℂ)‖ ^ (2 : ℕ) = 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  rw [norm_zero, zero_pow (by norm_num), zero_add, norm_div, div_pow, hm]
  norm_num

theorem positiveLeakage_not_determine_phase :
    let Tplus := phaseTriangle phaseU₂Plus
    let Tminus := phaseTriangle phaseU₂Minus
    ‖Tplus.leakA phaseInput‖ ^ (2 : ℕ) = 1 / 2 ∧
    ‖Tminus.leakA phaseInput‖ ^ (2 : ℕ) = 1 / 2 ∧
    ‖Tplus.leakB phaseInput‖ ^ (2 : ℕ) = 1 / 4 ∧
    ‖Tminus.leakB phaseInput‖ ^ (2 : ℕ) = 1 / 4 ∧
    ‖Tplus.leakC phaseInput‖ ^ (2 : ℕ) = 1 / 8 ∧
    ‖Tminus.leakC phaseInput‖ ^ (2 : ℕ) = 1 / 8 ∧
    Tplus.work phaseInput = 7 / 8 ∧
    Tminus.work phaseInput = 7 / 8 ∧
    Tplus.selectedHolonomy phaseInput = phaseVec ((1 - Complex.I) / 4) 0 ∧
    Tminus.selectedHolonomy phaseInput = phaseVec ((1 + Complex.I) / 4) 0 := by
  dsimp only
  refine ⟨phase_leakA_energy _, phase_leakA_energy _, phase_leakB_plus_energy,
    phase_leakB_minus_energy, phase_leakC_plus_energy, phase_leakC_minus_energy, ?_, ?_,
    phase_selected_plus, phase_selected_minus⟩
  · simp only [work, phase_leakA_energy, phase_leakB_plus_energy, phase_leakC_plus_energy]
    norm_num
  · simp only [work, phase_leakA_energy, phase_leakB_minus_energy, phase_leakC_minus_energy]
    norm_num

end HTGeometry.ConstraintRelativity.PassiveRelationTriangle
