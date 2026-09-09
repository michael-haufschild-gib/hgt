import GaloisForLFunctions.HTGeometry.GomesJacobiInvariantForms

/-!
# Recurrence reconstruction beyond a truncated tensor menu

Application of the reconstruction limitations discussed in
https://arxiv.org/abs/2607.24901. All Jacobi spectral families have the same
space of conformally transported bilinear forms. Nevertheless a nonzero
constant intertwiner of entire families reconstructs both coefficients.
The positive survivor is an exact classification of every intertwiner.
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- A nonzero constant intertwiner of full spectral recurrence families reconstructs both coefficients. -/
theorem gomesJacobiStep_intertwiner_classification (a b c d : ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ x : ℝ, P*gomesJacobiStep a b x = gomesJacobiStep c d x*P) ↔
      P = 0 ∨ (a = c ∧ b = d ∧ ∃ k : ℝ, P = k • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  constructor
  · intro h
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) (h a)
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) (h a)
    have h01' := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) (h (a+1))
    have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 1 0) (h a)
    have h10' := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 1 0) (h (a+1))
    simp [gomesJacobiStep,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01 h01' h10 h10'
    have hp01 : P 0 1 = 0 := by linarith
    have hp10 : P 1 0 = 0 := by linarith
    have hp11 : P 1 1 = P 0 0 := by linarith
    have he : P = P 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hp01,hp10,hp11]
    by_cases hk : P 0 0 = 0
    · left
      simpa [hk] using he
    · right
      have ha : (a-c)*P 0 0 = 0 := by linear_combination -h00+hp01+d*hp10
      have hb : (b-d)*P 0 0 = 0 := by
        linear_combination -h01-(a-c)*hp01+d*hp11
      exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_right hk),
        sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right hk),P 0 0,he⟩
  · rintro (rfl | ⟨rfl,rfl,k,rfl⟩) x
    · simp
    · simp

/-- The full real spectral family has only scalar constant endomorphisms. -/
theorem gomesJacobiStep_commutant (a b : ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ x : ℝ, P*gomesJacobiStep a b x = gomesJacobiStep a b x*P) ↔
      ∃ k : ℝ, P = k • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [gomesJacobiStep_intertwiner_classification]
  constructor
  · rintro (rfl | ⟨_,_,h⟩)
    · exact ⟨0,by simp⟩
    · exact h
  · intro h
    exact Or.inr ⟨rfl,rfl,h⟩

/-- Nonzero intertwining exists exactly when the two recurrence coefficient pairs coincide. -/
theorem gomesJacobiStep_nonzero_intertwiner_iff (a b c d : ℝ) :
    (∃ P : Matrix (Fin 2) (Fin 2) ℝ, P ≠ 0 ∧
      ∀ x : ℝ, P*gomesJacobiStep a b x = gomesJacobiStep c d x*P) ↔ a = c ∧ b = d := by
  constructor
  · rintro ⟨P,hP,h⟩
    rcases (gomesJacobiStep_intertwiner_classification a b c d P).mp h with he | ⟨ha,hb,_⟩
    · exact (hP he).elim
    · exact ⟨ha,hb⟩
  · rintro ⟨rfl,rfl⟩
    refine ⟨1,?_,by simp⟩
    intro he
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) he
    simp at h00

/-- The retained conformal area-tensor menu forgets both recurrence coefficients. -/
theorem gomesJacobiStep_common_forms_independent (a b c d : ℝ)
    (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ x : ℝ, (gomesJacobiStep a b x)ᵀ*B*gomesJacobiStep a b x = b • B) ↔
      ∀ x : ℝ, (gomesJacobiStep c d x)ᵀ*B*gomesJacobiStep c d x = d • B := by
  rw [gomesJacobiStep_common_forms,gomesJacobiStep_common_forms]

/-- Distinct diagonal recurrence coefficients cannot be reconstructed from their identical area menus. -/
theorem gomesJacobiStep_area_menu_incomplete (a b : ℝ) :
    (∀ B : Matrix (Fin 2) (Fin 2) ℝ,
      (∀ x : ℝ, (gomesJacobiStep a b x)ᵀ*B*gomesJacobiStep a b x = b • B) ↔
      ∀ x : ℝ, (gomesJacobiStep (a+1) b x)ᵀ*B*gomesJacobiStep (a+1) b x = b • B) ∧
    ¬∃ P : Matrix (Fin 2) (Fin 2) ℝ, P ≠ 0 ∧
      ∀ x : ℝ, P*gomesJacobiStep a b x = gomesJacobiStep (a+1) b x*P := by
  refine ⟨fun B => gomesJacobiStep_common_forms_independent a b (a+1) b B,?_⟩
  rw [gomesJacobiStep_nonzero_intertwiner_iff]
  rintro ⟨h,_⟩
  linarith

end GaloisForLFunctions.HTGeometry
