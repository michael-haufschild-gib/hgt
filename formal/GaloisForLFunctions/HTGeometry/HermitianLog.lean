import GaloisForLFunctions.HTGeometry.HermitianFlagUniqueness
import GaloisForLFunctions.HTGeometry.ObserverMetricSpace

/-!
# The exponential is a bijection onto the observer metrics

The exponential of a Hermitian direction is an observer metric, and every observer metric is the
exponential of exactly one direction: its logarithm, built from the spectral decomposition.

The two identities `log (exp T) = T` and `exp (log P) = P` are proved through the flag: the flag of
a logarithm is the flag of the operator at the exponentiated threshold, and a Hermitian operator is
determined by its flag.  So the space of observer metrics is parametrized by its directions — the
tangent picture the boundary construction starts from.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {P T : E →ₗ[ℂ] E}

/-! ## The logarithm of a positive-definite form -/

/-- The Hermitian logarithm of a positive-definite form, built from its spectral decomposition. -/
noncomputable def logOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n) : E →ₗ[ℂ] E :=
  pieceOperator (fun i : Fin n => (ℂ ∙ (hP.eigenvectorBasis hn) i))
    (fun i => Real.log (hP.eigenvalues hn i))

theorem isSymmetric_logOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n) :
    (logOp hP hn).IsSymmetric :=
  isSymmetric_pieceOperator _ _

theorem logOp_apply_basis (hP : P.IsSymmetric) (hn : finrank ℂ E = n) (i : Fin n) :
    logOp hP hn ((hP.eigenvectorBasis hn) i)
      = ((Real.log (hP.eigenvalues hn i) : ℝ) : ℂ) • (hP.eigenvectorBasis hn) i :=
  pieceOperator_apply_of_mem _
    (fun _ _ hij _ hx _ hy =>
      inner_eq_zero_of_mem_span_singleton (hP.eigenvectorBasis hn).orthonormal hij hx hy)
    (Submodule.mem_span_singleton_self _)

/-! ## Flags of exponentials and logarithms -/

/-- **The flag of an exponential is the flag of the direction at the logarithmic threshold.** -/
theorem eigenSum_metricRay (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {t : ℝ} (ht : 0 < t)
    {c : ℝ} (hc : 0 < c) :
    eigenSum ((metricRay T t : E →ₗ[ℂ] E)) c = eigenSum T (Real.log c / t) := by
  classical
  rw [eigenSum_eq_span_of_eigenbasis (hT.eigenvectorBasis hn).toBasis
      (w := fun i => Real.exp (t * hT.eigenvalues hn i)) (fun i => by
        rw [OrthonormalBasis.coe_toBasis]
        exact metricRay_eigenvectorBasis hT hn i t) c,
    eigenSum_eq_span hT hn (Real.log c / t), OrthonormalBasis.coe_toBasis]
  have hset : {i : Fin n | c < Real.exp (t * hT.eigenvalues hn i)}
      = {i : Fin n | Real.log c / t < hT.eigenvalues hn i} := by
    ext i
    simp only [Set.mem_setOf_eq]
    rw [← Real.log_lt_iff_lt_exp hc, div_lt_iff₀ ht, mul_comm (hT.eigenvalues hn i) t]
  rw [hset]

/-- **The flag of a logarithm is the flag of the form at the exponentiated threshold.** -/
theorem eigenSum_logOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (c : ℝ) :
    eigenSum (logOp hP hn) c = eigenSum P (Real.exp c) := by
  classical
  rw [eigenSum_eq_span_of_eigenbasis (hP.eigenvectorBasis hn).toBasis
      (w := fun i => Real.log (hP.eigenvalues hn i)) (fun i => by
        rw [OrthonormalBasis.coe_toBasis]
        exact logOp_apply_basis hP hn i) c,
    eigenSum_eq_span hP hn (Real.exp c), OrthonormalBasis.coe_toBasis]
  have hset : {i : Fin n | c < Real.log (hP.eigenvalues hn i)}
      = {i : Fin n | Real.exp c < hP.eigenvalues hn i} := by
    ext i
    simp only [Set.mem_setOf_eq]
    rw [Real.lt_log_iff_exp_lt (eigenvalues_pos hP hn hpos i)]
  rw [hset]

/-! ## The exponential and the logarithm are inverse -/

/-- **The logarithm of an exponential is the direction.** -/
theorem logOp_metricRay (hT : T.IsSymmetric) (hn : finrank ℂ E = n) :
    logOp (isSymmetric_metricRay hT hn 1) hn = T := by
  refine eq_of_eigenSum_eq (isSymmetric_logOp _ hn) hT hn fun c => ?_
  rw [eigenSum_logOp (isSymmetric_metricRay hT hn 1) hn
      (fun v hv => inner_metricRay_pos hT hn hv 1) c,
    eigenSum_metricRay hT hn one_pos (Real.exp_pos c), Real.log_exp, div_one]

/-- **The exponential of a logarithm is the form.** -/
theorem metricRay_logOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) :
    ((metricRay (logOp hP hn) 1 : E →ₗ[ℂ] E)) = P := by
  refine eq_of_eigenSum_eq (isSymmetric_metricRay (isSymmetric_logOp hP hn) hn 1) hP hn fun c => ?_
  rcases le_or_gt c 0 with hc | hc
  · have hleft : eigenSum ((metricRay (logOp hP hn) 1 : E →ₗ[ℂ] E)) c = ⊤ := by
      refine (eigenSum_eq_top_iff (isSymmetric_metricRay (isSymmetric_logOp hP hn) hn 1) hn c).2
        fun i => ?_
      have hpos' := eigenvalues_pos (isSymmetric_metricRay (isSymmetric_logOp hP hn) hn 1) hn
        (fun v hv => inner_metricRay_pos (isSymmetric_logOp hP hn) hn hv 1) i
      linarith
    have hright : eigenSum P c = ⊤ := by
      refine (eigenSum_eq_top_iff hP hn c).2 fun i => ?_
      exact lt_of_le_of_lt hc (eigenvalues_pos hP hn hpos i)
    rw [hleft, hright]
  · rw [eigenSum_metricRay (isSymmetric_logOp hP hn) hn one_pos hc, div_one,
      eigenSum_logOp hP hn hpos (Real.log c), Real.exp_log hc]

/-! ## The traceless normalization -/

/-- **The trace of a logarithm is the sum of the logarithms of the eigenvalues.** -/
theorem trace_logOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n) :
    LinearMap.trace ℂ E (logOp hP hn)
      = ((∑ i, Real.log (hP.eigenvalues hn i) : ℝ) : ℂ) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (hP.eigenvectorBasis hn).toBasis,
    toMatrix_diagonal_of_orthonormalBasis (hP.eigenvectorBasis hn) (logOp_apply_basis hP hn),
    Matrix.trace_diagonal, Complex.ofReal_sum]

/-- **A determinant-one form has a traceless logarithm**, so its direction is one of those whose
rays stay inside the determinant-one space of observer metrics. -/
theorem trace_logOp_eq_zero (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (hdet : LinearMap.det P = 1) :
    LinearMap.trace ℂ E (logOp hP hn) = 0 := by
  have hdetprod := hP.det_eq_prod_eigenvalues hn
  rw [hdet] at hdetprod
  have h2 : ((∏ i, hP.eigenvalues hn i : ℝ) : ℂ) = 1 := by
    push_cast
    exact hdetprod.symm
  have hprod : ∏ i, hP.eigenvalues hn i = 1 := by exact_mod_cast h2
  have hlog : ∑ i, Real.log (hP.eigenvalues hn i) = Real.log (∏ i, hP.eigenvalues hn i) :=
    (Real.log_prod (f := fun i => hP.eigenvalues hn i) (s := Finset.univ)
      (fun i _ => ne_of_gt (eigenvalues_pos hP hn hpos i))).symm
  rw [trace_logOp hP hn, hlog, hprod, Real.log_one]
  simp

/-- **The observer metrics are exactly the exponentials of the directions.**  Every
positive-definite Hermitian form is the exponential of one and only one Hermitian direction. -/
theorem exists_unique_isSymmetric_metricRay (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) :
    ∃ T : E →ₗ[ℂ] E, T.IsSymmetric ∧ ((metricRay T 1 : E →ₗ[ℂ] E)) = P ∧
      ∀ T' : E →ₗ[ℂ] E, T'.IsSymmetric → ((metricRay T' 1 : E →ₗ[ℂ] E)) = P → T' = T := by
  refine ⟨logOp hP hn, isSymmetric_logOp hP hn, metricRay_logOp hP hn hpos, fun T' hT' hT'P => ?_⟩
  refine eq_of_eigenSum_eq hT' (isSymmetric_logOp hP hn) hn fun c => ?_
  rw [eigenSum_logOp hP hn hpos c, ← hT'P, eigenSum_metricRay hT' hn one_pos (Real.exp_pos c),
    Real.log_exp, div_one]

/-- **The exponential is a bijection from the traceless directions onto the observer metrics.**
Every positive-definite Hermitian form of determinant one lies on exactly one ray
`t ↦ exp (t T)` of a traceless Hermitian direction, and conversely every such ray stays inside the
space of observer metrics.  So the observer-metric space is parametrized by its directions at the
reference point. -/
theorem exists_unique_traceless_metricRay (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (hdet : LinearMap.det P = 1) :
    ∃ T : E →ₗ[ℂ] E, T.IsSymmetric ∧ LinearMap.trace ℂ E T = 0 ∧
      ((metricRay T 1 : E →ₗ[ℂ] E)) = P ∧
      ∀ T' : E →ₗ[ℂ] E, T'.IsSymmetric → ((metricRay T' 1 : E →ₗ[ℂ] E)) = P → T' = T := by
  obtain ⟨T, hTsym, hTP, hTuniq⟩ := exists_unique_isSymmetric_metricRay hP hn hpos
  refine ⟨T, hTsym, ?_, hTP, hTuniq⟩
  have hlog : T = logOp hP hn := (hTuniq (logOp hP hn) (isSymmetric_logOp hP hn)
    (metricRay_logOp hP hn hpos)).symm
  rw [hlog]
  exact trace_logOp_eq_zero hP hn hpos hdet

end GaloisForLFunctions.HTGeometry
