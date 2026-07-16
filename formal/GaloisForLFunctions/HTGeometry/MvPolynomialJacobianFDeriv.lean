import GaloisForLFunctions.HTGeometry.MvPolynomialJacobianMinors
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.Basic

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem differentiable_mvPolynomial_eval_complex {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (differentiable_const c :
      Differentiable ℂ (fun _ : Fin n → ℂ => c))
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P i hP =>
      simpa using hP.mul (differentiable_apply (𝕜 := ℂ) i)

/-- The complex Fréchet derivative of polynomial evaluation is its formal gradient. -/
theorem fderiv_mvPolynomial_eval_complex_apply {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (x v : Fin n → ℂ) :
    fderiv ℂ (fun y : Fin n → ℂ => MvPolynomial.eval y P) x v =
      ∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j P) * v j := by
  let curve : ℂ → (Fin n → ℂ) := fun t j => x j + t * v j
  have hcurveCoord : ∀ j, HasDerivAt (fun t => curve t j) (v j) 0 := by
    intro j
    convert (hasDerivAt_const (x := 0) (x j)).add
      ((hasDerivAt_id 0).mul_const (v j)) using 1 <;> simp [curve]
  have hcurveValue : curve 0 = x := by
    funext j
    simp [curve]
  have hslice : HasDerivAt
      (fun t => MvPolynomial.eval (curve t) P)
      (∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j P) * v j) 0 := by
    have h := hasDerivAt_mvPolynomial_eval_curve_complex P
      (fun j t => curve t j) v 0 hcurveCoord
    simpa [hcurveValue] using h
  have hFdiff : DifferentiableAt ℂ
      (fun y : Fin n → ℂ => MvPolynomial.eval y P) (curve 0) :=
    (differentiable_mvPolynomial_eval_complex P).differentiableAt
  have hcurveDiff : DifferentiableAt ℂ curve 0 :=
    differentiableAt_pi.mpr fun j => (hcurveCoord j).differentiableAt
  have hcurveDeriv : fderiv ℂ curve 0 1 = v := by
    funext j
    have hj := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1)
      (fderiv_apply hcurveDiff j)
    rw [(hcurveCoord j).hasFDerivAt.fderiv] at hj
    simpa using hj.symm
  have hcomp := fderiv_comp' (f := curve)
    (g := fun y : Fin n → ℂ => MvPolynomial.eval y P) 0 hFdiff hcurveDiff
  have hcompAt := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) hcomp
  change fderiv ℂ (fun t => MvPolynomial.eval (curve t) P) 0 1 =
    (fderiv ℂ (fun y : Fin n → ℂ => MvPolynomial.eval y P) (curve 0)).comp
      (fderiv ℂ curve 0) 1 at hcompAt
  rw [fderiv_apply_one_eq_deriv, hslice.deriv,
    ContinuousLinearMap.comp_apply, hcurveDeriv] at hcompAt
  simpa [hcurveValue] using hcompAt.symm

theorem differentiable_complexMvPolynomialFamilyEval_complex {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (complexMvPolynomialFamilyEval P) := by
  rw [differentiable_pi]
  intro i
  exact differentiable_mvPolynomial_eval_complex (P i)

/-- The family Fréchet derivative is multiplication by the evaluated Jacobian matrix. -/
theorem fderiv_complexMvPolynomialFamilyEval_complex_apply {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) (x v : Fin n → ℂ) :
    fderiv ℂ (complexMvPolynomialFamilyEval P) x v =
      (complexMvPolynomialFamilyJacobian P x).mulVec v := by
  funext i
  have hFdiff : DifferentiableAt ℂ (complexMvPolynomialFamilyEval P) x :=
    (differentiable_complexMvPolynomialFamilyEval_complex P).differentiableAt
  have hi := congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L v)
    (fderiv_apply hFdiff i)
  change fderiv ℂ (fun y : Fin n → ℂ => MvPolynomial.eval y (P i)) x v =
    fderiv ℂ (complexMvPolynomialFamilyEval P) x v i at hi
  rw [fderiv_mvPolynomial_eval_complex_apply] at hi
  simpa [complexMvPolynomialFamilyEval, complexMvPolynomialFamilyJacobian,
    Matrix.mulVec, dotProduct] using hi.symm

theorem fderiv_complexMvPolynomialFamilyEval_real_eq_restrictScalars {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    fderiv ℝ (complexMvPolynomialFamilyEval P) x =
      (fderiv ℂ (complexMvPolynomialFamilyEval P) x).restrictScalars ℝ := by
  exact ((differentiable_complexMvPolynomialFamilyEval_complex P x).hasFDerivAt.restrictScalars
    ℝ).fderiv

theorem surjective_fderiv_complexMvPolynomialFamilyEval_real_iff_complex
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    Function.Surjective (fderiv ℝ (complexMvPolynomialFamilyEval P) x) ↔
      Function.Surjective (fderiv ℂ (complexMvPolynomialFamilyEval P) x) := by
  rw [fderiv_complexMvPolynomialFamilyEval_real_eq_restrictScalars]
  rfl

theorem surjective_fderiv_complexMvPolynomialFamilyEval_iff_jacobian
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    Function.Surjective (fderiv ℂ (complexMvPolynomialFamilyEval P) x) ↔
      Function.Surjective (complexMvPolynomialFamilyJacobian P x).mulVec := by
  constructor
  · intro h y
    obtain ⟨v, hv⟩ := h y
    exact ⟨v, by rw [← fderiv_complexMvPolynomialFamilyEval_complex_apply, hv]⟩
  · intro h y
    obtain ⟨v, hv⟩ := h y
    exact ⟨v, by rw [fderiv_complexMvPolynomialFamilyEval_complex_apply, hv]⟩

/-- Rectangular matrix row independence is equivalent to surjectivity of its row map. -/
theorem matrix_mulVec_surjective_iff_linearIndependent_rows
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Function.Surjective A.mulVec ↔ LinearIndependent ℂ A.row := by
  constructor
  · intro h
    have hrange : LinearMap.range A.mulVecLin = ⊤ :=
      LinearMap.range_eq_top.mpr h
    have hrank : A.rank = Fintype.card (Fin m) := by
      rw [Matrix.rank, hrange]
      simp [Module.finrank_pi_fintype]
    rw [linearIndependent_iff_card_eq_finrank_span]
    rw [Set.finrank, ← A.rank_eq_finrank_span_row, hrank]
  · intro h
    have hrank : A.rank = Fintype.card (Fin m) := h.rank_matrix
    have hfinrank : Module.finrank ℂ (LinearMap.range A.mulVecLin) =
        Module.finrank ℂ (Fin m → ℂ) := by
      simpa [Matrix.rank, Module.finrank_pi_fintype] using hrank
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hfinrank)

theorem matrix_linearIndependent_rows_of_submatrix_det_ne_zero
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (cols : Fin m → Fin n)
    (hdet : (A.submatrix id cols).det ≠ 0) :
    LinearIndependent ℂ A.row := by
  apply LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ cols)
  simpa [Function.comp_def, Matrix.row, Matrix.submatrix] using
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet)

theorem matrix_mulVec_surjective_of_submatrix_det_ne_zero
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (cols : Fin m → Fin n)
    (hdet : (A.submatrix id cols).det ≠ 0) :
    Function.Surjective A.mulVec :=
  (matrix_mulVec_surjective_iff_linearIndependent_rows A).mpr
    (matrix_linearIndependent_rows_of_submatrix_det_ne_zero A cols hdet)

/-- A surjective rectangular matrix contains a nonsingular maximal square minor. -/
theorem matrix_exists_submatrix_det_ne_zero_of_mulVec_surjective
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (hA : Function.Surjective A.mulVec) :
    ∃ cols : Fin m → Fin n, (A.submatrix id cols).det ≠ 0 := by
  have hspan : Submodule.span ℂ (Set.range A.col) = ⊤ := by
    rw [← A.range_mulVecLin, LinearMap.range_eq_top.mpr hA]
  obtain ⟨s, hsLI, hsmax⟩ := exists_maximal_linearIndepOn ℂ A.col
  have hall : ∀ j, A.col j ∈ Submodule.span ℂ (A.col '' s) := by
    intro j
    by_cases hjs : j ∈ s
    · exact Submodule.subset_span ⟨j, hjs, rfl⟩
    · obtain ⟨a, ha, haj⟩ := hsmax j hjs
      have heq : A.col j = a⁻¹ • (a • A.col j) := by
        rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      rw [heq]
      exact Submodule.smul_mem _ _ haj
  have hsSpan : Submodule.span ℂ (A.col '' s) = ⊤ := by
    apply top_unique
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hall j
  have hsSpan' : Submodule.span ℂ
      (Set.range (fun j : s => A.col j.1)) = ⊤ := by
    rw [show Set.range (fun j : s => A.col j.1) = A.col '' s by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j.1, j.2, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, hj⟩, rfl⟩]
    exact hsSpan
  let b : Module.Basis s ℂ (Fin m → ℂ) := Module.Basis.mk hsLI hsSpan'.ge
  letI : Fintype s := Fintype.ofFinite s
  have hcard : Fintype.card s = m := by
    rw [← Module.finrank_eq_card_basis b]
    simp [Module.finrank_pi_fintype]
  let e : Fin m ≃ s := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let cols : Fin m → Fin n := fun i => (e i).1
  refine ⟨cols, ?_⟩
  have hselected : LinearIndependent ℂ (fun i : Fin m => A.col (cols i)) := by
    exact hsLI.comp (fun i => (e i : s)) e.injective
  have hcols : LinearIndependent ℂ (A.submatrix id cols).col := by
    simpa [Matrix.col, Matrix.submatrix, cols] using hselected
  have hunit : IsUnit (A.submatrix id cols) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
  exact hunit

theorem matrix_mulVec_surjective_iff_exists_submatrix_det_ne_zero
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Function.Surjective A.mulVec ↔
      ∃ cols : Fin m → Fin n, (A.submatrix id cols).det ≠ 0 := by
  constructor
  · exact matrix_exists_submatrix_det_ne_zero_of_mulVec_surjective A
  · rintro ⟨cols, hcols⟩
    exact matrix_mulVec_surjective_of_submatrix_det_ne_zero A cols hcols

/-- A nonzero maximal Jacobian minor makes the real derivative surjective. -/
theorem surjective_fderiv_complexMvPolynomialFamilyEval_real_of_minor_ne_zero
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (cols : Fin m → Fin n)
    (hminor : MvPolynomial.eval x
      (complexMvPolynomialFamilyJacobianMinor P cols) ≠ 0) :
    Function.Surjective (fderiv ℝ (complexMvPolynomialFamilyEval P) x) := by
  rw [surjective_fderiv_complexMvPolynomialFamilyEval_real_iff_complex,
    surjective_fderiv_complexMvPolynomialFamilyEval_iff_jacobian]
  apply matrix_mulVec_surjective_of_submatrix_det_ne_zero
  rwa [← eval_complexMvPolynomialFamilyJacobianMinor]

/-- Outside the algebraic maximal-minor defect, the real derivative is surjective. -/
theorem surjective_fderiv_complexMvPolynomialFamilyEval_real_of_notMem_rankDefect
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (hx : x ∉ complexMvPolynomialFamilyJacobianRankDefect P) :
    Function.Surjective (fderiv ℝ (complexMvPolynomialFamilyEval P) x) := by
  simp only [complexMvPolynomialFamilyJacobianRankDefect, Set.mem_setOf_eq,
    not_forall] at hx
  obtain ⟨cols, hcols⟩ := hx
  exact surjective_fderiv_complexMvPolynomialFamilyEval_real_of_minor_ne_zero
    P x cols hcols

/-- The algebraic maximal-minor defect is exactly real derivative rank loss. -/
theorem surjective_fderiv_complexMvPolynomialFamilyEval_real_iff_notMem_rankDefect
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    Function.Surjective (fderiv ℝ (complexMvPolynomialFamilyEval P) x) ↔
      x ∉ complexMvPolynomialFamilyJacobianRankDefect P := by
  constructor
  · intro h
    have hcomplex :=
      (surjective_fderiv_complexMvPolynomialFamilyEval_real_iff_complex P x).mp h
    have hjac :=
      (surjective_fderiv_complexMvPolynomialFamilyEval_iff_jacobian P x).mp hcomplex
    obtain ⟨cols, hcols⟩ :=
      matrix_exists_submatrix_det_ne_zero_of_mulVec_surjective _ hjac
    simp only [complexMvPolynomialFamilyJacobianRankDefect, Set.mem_setOf_eq,
      not_forall]
    exact ⟨cols, by rwa [eval_complexMvPolynomialFamilyJacobianMinor]⟩
  · exact surjective_fderiv_complexMvPolynomialFamilyEval_real_of_notMem_rankDefect P x

end

end GaloisForLFunctions.HTGeometry
