import GaloisForLFunctions.HTGeometry.GomesJacobiInvariantForms

/-!
# Two-step flux and the kernel of successive observations

Application of the invariant-kernel viewpoint in https://arxiv.org/abs/2509.25276
and internal-frame geometry in https://arxiv.org/abs/2404.10461 to Jacobi
recurrences. These are new corpus applications, not paper theorem transcriptions.
Two rank-one flux observations form an explicit Gram matrix. Its factorization
classifies positivity without assumptions and yields the complete strict
positivity boundary for a two-step complex transfer.
-/

open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The Gram matrix of two consecutive rank-one flux observations. -/
def gomesJacobiTwoStepGram (a b d : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (gomesJacobiComplexStep a b z)ᴴ * gomesJacobiSource * gomesJacobiComplexStep a b z +
    (d : ℂ) • gomesJacobiSource

/-- Two observed directions factor through a weighted diagonal form. -/
theorem gomesJacobiTwoStepGram_factor (a b d : ℝ) (z : ℂ) :
    gomesJacobiTwoStepGram a b d z =
      (!![1,0;z-a,-(b : ℂ)])ᴴ * Matrix.diagonal ![(d : ℂ),1] * !![1,0;z-a,-(b : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesJacobiTwoStepGram,gomesJacobiComplexStep,gomesJacobiSource,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply]
  all_goals ring

/-- The two-observation Gram form is positive exactly when its second weight is positive and
its first step couples the otherwise invisible direction. -/
theorem gomesJacobiTwoStepGram_posDef_iff (a b d : ℝ) (z : ℂ) :
    (gomesJacobiTwoStepGram a b d z).PosDef ↔ b ≠ 0 ∧ 0 < d := by
  constructor
  · intro h
    have hb : b ≠ 0 := by
      intro he
      have h11 := h.diag_pos (i := (1 : Fin 2))
      simp [gomesJacobiTwoStepGram,gomesJacobiComplexStep,gomesJacobiSource,
        Matrix.mul_apply,Fin.sum_univ_two,he] at h11
    have hv : (![(b : ℂ),z-a] : Fin 2 → ℂ) ≠ 0 := by
      intro he
      have h0 := congrFun he 0
      exact hb (Complex.ofReal_eq_zero.mp (by simpa using h0))
    have hq := h.dotProduct_mulVec_pos hv
    have hqeq : star (![(b : ℂ),z-a] : Fin 2 → ℂ) ⬝ᵥ
        (gomesJacobiTwoStepGram a b d z *ᵥ ![(b : ℂ),z-a]) = ((d*b^(2 : ℕ) : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp [gomesJacobiTwoStepGram,gomesJacobiComplexStep,gomesJacobiSource,
          Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.conjTranspose_apply,pow_two] <;> ring
    rw [hqeq] at hq
    have hr := Complex.zero_lt_real.mp hq
    have hd : 0 < d := by
      rcases mul_pos_iff.mp hr with hh | hh
      · exact hh.1
      · exact (not_lt_of_ge (sq_nonneg b) hh.2).elim
    exact ⟨hb,hd⟩
  · rintro ⟨hb,hd⟩
    rw [gomesJacobiTwoStepGram_factor]
    apply Matrix.PosDef.conjTranspose_mul_mul_same
    · rw [Matrix.posDef_diagonal_iff]
      intro i
      fin_cases i
      · exact Complex.zero_lt_real.mpr hd
      · simp
    · intro v w he
      have h0 := congrFun he 0
      have h1 := congrFun he 1
      simp [Matrix.mulVec] at h0 h1
      change v 0 = w 0 at h0
      change (z-a)*v 0-(b : ℂ)*v 1 = (z-a)*w 0-(b : ℂ)*w 1 at h1
      have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
      have hlast : v 1 = w 1 := by
        apply (mul_left_cancel₀ hbC)
        linear_combination -h1+(z-a)*h0
      ext i
      fin_cases i <;> assumption

/-- The exact two-step flux defect is twice the imaginary part times its observation Gram matrix. -/
theorem gomesJacobiTwoStep_flux_defect (a b c d : ℝ) (z : ℂ) :
    (gomesJacobiComplexStep c d z * gomesJacobiComplexStep a b z)ᴴ * gomesJacobiFlux *
      (gomesJacobiComplexStep c d z * gomesJacobiComplexStep a b z) -
      (d*b : ℂ) • gomesJacobiFlux = (2*z.im : ℝ) • gomesJacobiTwoStepGram a b d z := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [gomesJacobiComplexStep,gomesJacobiFlux,gomesShearAreaMatrix,
      gomesJacobiTwoStepGram,gomesJacobiSource,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.conjTranspose_apply] <;> ring

/-- Strict positive flux has a sharp complete boundary: upper half-plane, nonzero first coupling,
and positive second coupling. Neither diagonal recurrence coefficient affects this boundary. -/
theorem gomesJacobiTwoStep_flux_posDef_iff (a b c d : ℝ) (z : ℂ) :
    ((gomesJacobiComplexStep c d z * gomesJacobiComplexStep a b z)ᴴ * gomesJacobiFlux *
      (gomesJacobiComplexStep c d z * gomesJacobiComplexStep a b z) -
      (d*b : ℂ) • gomesJacobiFlux).PosDef ↔ 0 < z.im ∧ b ≠ 0 ∧ 0 < d := by
  rw [gomesJacobiTwoStep_flux_defect]
  constructor
  · intro h
    have h11 := h.diag_pos (i := (1 : Fin 2))
    have he : ((2*z.im : ℝ) • gomesJacobiTwoStepGram a b d z) 1 1 =
        ((2*z.im*b^(2 : ℕ) : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp [gomesJacobiTwoStepGram,gomesJacobiComplexStep,gomesJacobiSource,
          Matrix.mul_apply,Fin.sum_univ_two,pow_two]
    rw [he] at h11
    have hr := Complex.zero_lt_real.mp h11
    have h2 : 0 < 2*z.im := by
      rcases mul_pos_iff.mp hr with hh | hh
      · exact hh.1
      · exact (not_lt_of_ge (sq_nonneg b) hh.2).elim
    have hG := h.smul (inv_pos.mpr h2)
    rw [smul_smul,inv_mul_cancel₀ h2.ne',one_smul] at hG
    exact ⟨by linarith,(gomesJacobiTwoStepGram_posDef_iff a b d z).mp hG⟩
  · rintro ⟨hi,hb,hd⟩
    exact ((gomesJacobiTwoStepGram_posDef_iff a b d z).mpr ⟨hb,hd⟩).smul (by linarith)

end GaloisForLFunctions.HTGeometry
