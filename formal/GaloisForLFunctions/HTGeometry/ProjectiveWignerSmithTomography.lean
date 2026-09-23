import GaloisForLFunctions.HTGeometry.MatrixWignerSmithTomography

/-!
# Projective Wigner--Smith tomography

An overall scalar scattering phase adds a scalar multiple of the identity to the Wigner--Smith
matrix.  This module removes that central clock exactly.  For matrices of positive size `N=n+1`,
normalization at one reference channel sends `Q` to `Q-Q_ll I` and is invariant under every scalar
identity shift.

The full matrix-delay panel has `N²` ordered-pair reporters.  After normalization its reference
diagonal reporter is identically zero, so deleting that one reporter gives an exact `N²-1` panel.
Equality of these reporters is equivalent to equality modulo a scalar identity matrix.  On the
trace-zero sector the panel is injective.  The canonical traceless projection is also proved
trace-free and invariant under all scalar identity shifts.
-/

open Complex
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalize a delay matrix by subtracting its reference-channel diagonal from every diagonal
entry.  This is the affine representative with last diagonal entry zero. -/
def projectiveDelayNormalize {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j =>
  Q i j - if i = j then Q (Fin.last n) (Fin.last n) else 0

/-- The normalized reference diagonal vanishes. -/
theorem projectiveDelayNormalize_lastDiagonal {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    projectiveDelayNormalize Q (Fin.last n) (Fin.last n) = 0 := by
  simp [projectiveDelayNormalize]

/-- Reference normalization is unchanged by a scalar identity delay. -/
theorem projectiveDelayNormalize_add_scalar {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℂ) :
    projectiveDelayNormalize (Q + c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) =
      projectiveDelayNormalize Q := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [projectiveDelayNormalize]
  · simp [projectiveDelayNormalize, hij]

/-- Canonical trace-zero representative of a delay matrix modulo scalar identity shifts. -/
def matrixTracelessPart {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Q + (-(Matrix.trace Q / (n + 1 : ℂ))) •
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)

/-- The canonical traceless projection has trace zero. -/
theorem matrixTracelessPart_trace {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix.trace (matrixTracelessPart Q) = 0 := by
  rw [matrixTracelessPart, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  simp only [smul_eq_mul, Fintype.card_fin]
  have hcard : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
  field_simp
  push_cast
  ring

/-- Ordered channel pairs with the identically-zero normalized reference diagonal removed. -/
def ProjectiveDelayIndex (n : ℕ) :=
  {p : Fin (n + 1) × Fin (n + 1) // p ≠ (Fin.last n, Fin.last n)}

instance (n : ℕ) : Fintype (ProjectiveDelayIndex n) := by
  dsimp [ProjectiveDelayIndex]
  infer_instance

/-- There are exactly `(n+1)²-1` projective delay reporters. -/
theorem projectiveDelayIndex_card (n : ℕ) :
    Fintype.card (ProjectiveDelayIndex n) = (n + 1) ^ (2 : ℕ) - 1 := by
  change Fintype.card
      {p : Fin (n + 1) × Fin (n + 1) //
        ¬p = (Fin.last n, Fin.last n)} = _
  rw [Fintype.card_subtype_compl
    (fun p : Fin (n + 1) × Fin (n + 1) =>
      p = (Fin.last n, Fin.last n))]
  simp [pow_two]

/-- The nonredundant projective delay panel. -/
def projectiveDelayPanel {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ProjectiveDelayIndex n → ℂ := fun p =>
  matrixDelayPanel (projectiveDelayNormalize Q) p.1

/-- The complete projective reporter panel is blind to scalar identity delays. -/
theorem projectiveDelayPanel_add_scalar {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℂ) :
    projectiveDelayPanel (Q + c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) =
      projectiveDelayPanel Q := by
  funext p
  change matrixDelayPanel (projectiveDelayNormalize (Q + c • 1)) p.1 =
    matrixDelayPanel (projectiveDelayNormalize Q) p.1
  rw [projectiveDelayNormalize_add_scalar]

/-- Projective reporters are unchanged by passage to the canonical traceless representative. -/
theorem projectiveDelayPanel_tracelessPart {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    projectiveDelayPanel (matrixTracelessPart Q) = projectiveDelayPanel Q := by
  exact projectiveDelayPanel_add_scalar Q (-(Matrix.trace Q / (n + 1 : ℂ)))

/-- Equality of every projective reporter forces equality of the reference-normalized matrices. -/
theorem projectiveDelayPanel_eq_imp_normalize_eq {n : ℕ}
    {Q R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpanel : projectiveDelayPanel Q = projectiveDelayPanel R) :
    projectiveDelayNormalize Q = projectiveDelayNormalize R := by
  apply matrixDelayPanel_injective
  funext p
  by_cases hp : p = (Fin.last n, Fin.last n)
  · subst p
    simp [matrixDelayPanel_diagonal, projectiveDelayNormalize_lastDiagonal]
  · simpa [projectiveDelayPanel] using congrFun hpanel ⟨p, hp⟩

/-- Reference-normalized matrices are equal exactly when the original matrices differ by a scalar
identity delay. -/
theorem projectiveDelayNormalize_eq_iff_exists_add_scalar {n : ℕ}
    (Q R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    projectiveDelayNormalize Q = projectiveDelayNormalize R ↔
      ∃ c : ℂ, R = Q + c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  constructor
  · intro h
    refine ⟨R (Fin.last n) (Fin.last n) - Q (Fin.last n) (Fin.last n), ?_⟩
    ext i j
    have hij := congrFun (congrFun h i) j
    by_cases heq : i = j
    · subst j
      simp [projectiveDelayNormalize] at hij ⊢
      linear_combination -hij
    · simp [projectiveDelayNormalize, heq] at hij ⊢
      exact hij.symm
  · rintro ⟨c, rfl⟩
    exact (projectiveDelayNormalize_add_scalar Q c).symm

/-- **Projective tomography.**  Two matrices have the same `N²-1` reporters exactly when they
differ by a scalar identity matrix. -/
theorem projectiveDelayPanel_eq_iff_exists_add_scalar {n : ℕ}
    (Q R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    projectiveDelayPanel Q = projectiveDelayPanel R ↔
      ∃ c : ℂ, R = Q + c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  constructor
  · intro h
    exact (projectiveDelayNormalize_eq_iff_exists_add_scalar Q R).1
      (projectiveDelayPanel_eq_imp_normalize_eq h)
  · rintro ⟨c, rfl⟩
    exact (projectiveDelayPanel_add_scalar Q c).symm

/-- On the trace-zero sector the `N²-1` projective reporters reconstruct the complete matrix. -/
theorem projectiveDelayPanel_injective_on_trace_zero {n : ℕ}
    {Q R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hQ : Matrix.trace Q = 0) (hR : Matrix.trace R = 0)
    (hpanel : projectiveDelayPanel Q = projectiveDelayPanel R) :
    Q = R := by
  obtain ⟨c, rfl⟩ :=
    (projectiveDelayPanel_eq_iff_exists_add_scalar Q R).1 hpanel
  have hcEq : c * (Fintype.card (Fin (n + 1)) : ℂ) = 0 := by
    have htrace := hR
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, hQ, zero_add] at htrace
    simpa [smul_eq_mul] using htrace
  have hcard : (Fintype.card (Fin (n + 1)) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_add_one_ne_zero (R := ℂ) n)
  have hc : c = 0 := (mul_eq_zero.mp hcEq).resolve_right hcard
  subst c
  simp

/-- The canonical traceless representative is invariant under every scalar identity delay. -/
theorem matrixTracelessPart_add_scalar {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℂ) :
    matrixTracelessPart (Q + c • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) =
      matrixTracelessPart Q := by
  apply projectiveDelayPanel_injective_on_trace_zero
    (matrixTracelessPart_trace _) (matrixTracelessPart_trace _)
  rw [projectiveDelayPanel_tracelessPart, projectiveDelayPanel_tracelessPart,
    projectiveDelayPanel_add_scalar]

/-! ## Exact reporter minimality -/

/-- The projective delay panel is injective on the traceless matrix space. -/
theorem projectiveDelayPanel_traceLinearMap_ker_injective (n : ℕ) :
    Function.Injective (fun Q :
      LinearMap.ker (Matrix.traceLinearMap (Fin (n + 1)) ℂ ℂ) =>
        projectiveDelayPanel (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := by
  intro Q R hQR
  apply Subtype.ext
  apply projectiveDelayPanel_injective_on_trace_zero
  · have hQ := Q.property
    rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hQ
    exact hQ
  · have hR := R.property
    rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hR
    exact hR
  · exact hQR

/-- Complex dimension of the traceless `(n+1) × (n+1)` matrices. -/
theorem finrank_traceLinearMap_ker_fin_add_one (n : ℕ) :
    Module.finrank ℂ
        (LinearMap.ker (Matrix.traceLinearMap (Fin (n + 1)) ℂ ℂ)) =
      (n + 1) ^ (2 : ℕ) - 1 := by
  have hsurj : Function.Surjective (Matrix.traceLinearMap (Fin (n + 1)) ℂ ℂ) := by
    intro c
    refine ⟨(c / ((n + 1 : ℕ) : ℂ)) • 1, ?_⟩
    rw [Matrix.traceLinearMap_apply, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul, div_mul_cancel₀]
    exact_mod_cast Nat.succ_ne_zero n
  have hrange : Module.finrank ℂ
      (LinearMap.range (Matrix.traceLinearMap (Fin (n + 1)) ℂ ℂ)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hrn :=
    (Matrix.traceLinearMap (Fin (n + 1)) ℂ ℂ).finrank_range_add_finrank_ker
  rw [hrange] at hrn
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hrn
  simpa [pow_two] using (show Module.finrank ℂ
      (LinearMap.ker (Matrix.traceLinearMap (Fin (n + 1)) ℂ ℂ)) =
        (n + 1) * (n + 1) - 1 by omega)

/-- Any scalar linear reporter family reconstructing every traceless `(n+1) × (n+1)` matrix has
at least `(n+1)²-1` reporters. -/
theorem projectiveDelayReporter_card_lower_bound {n : ℕ} {J : Type*} [Fintype J]
    (R : LinearMap.ker (Matrix.traceLinearMap (Fin (n + 1)) ℂ ℂ) →ₗ[ℂ] (J → ℂ))
    (hR : Function.Injective R) :
    (n + 1) ^ (2 : ℕ) - 1 ≤ Fintype.card J := by
  have hdim := R.finrank_le_finrank_of_injective hR
  rw [finrank_traceLinearMap_ker_fin_add_one] at hdim
  simpa only [Module.finrank_fintype_fun_eq_card] using hdim

/-- **Exact minimality of projective delay tomography.**  The canonical panel reconstructs every
traceless matrix using exactly `(n+1)²-1` scalar reporters, and no injective linear scalar reporter
family can use fewer. -/
theorem projectiveDelayPanel_minimal (n : ℕ) :
    Function.Injective (fun Q :
      LinearMap.ker (Matrix.traceLinearMap (Fin (n + 1)) ℂ ℂ) =>
        projectiveDelayPanel (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ∧
      Fintype.card (ProjectiveDelayIndex n) = (n + 1) ^ (2 : ℕ) - 1 ∧
      ∀ {J : Type*} [Fintype J]
        (R : LinearMap.ker (Matrix.traceLinearMap (Fin (n + 1)) ℂ ℂ) →ₗ[ℂ] (J → ℂ)),
        Function.Injective R → Fintype.card (ProjectiveDelayIndex n) ≤ Fintype.card J := by
  refine ⟨projectiveDelayPanel_traceLinearMap_ker_injective n,
    projectiveDelayIndex_card n, ?_⟩
  intro J _ R hR
  rw [projectiveDelayIndex_card]
  exact projectiveDelayReporter_card_lower_bound R hR

end


end GaloisForLFunctions.HTGeometry
