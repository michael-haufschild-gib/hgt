import GaloisForLFunctions.HTGeometry.HermitianObserverMetric
import GaloisForLFunctions.HTGeometry.HermitianFlagRealization

/-!
# The space of observer metrics is one orbit

An observer metric is a positive-definite Hermitian form of determinant one.  Every such form is the
pullback of the reference form by a determinant-one symmetry — its positive square root — and the
symmetries fixing the reference form are exactly the isometries.  So the space of observer metrics
is a single orbit of the observer group with the unitary group as stabilizer, which is the
description of the symmetric space that the boundary picture starts from.

The rays `t ↦ exp (t T)` of traceless Hermitian directions stay inside that space.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## Positive-definite symmetric operators have positive eigenvalues -/

theorem eigenvalues_pos {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (i : Fin n) :
    0 < hP.eigenvalues hn i := by
  have hne : (hP.eigenvectorBasis hn) i ≠ 0 := by
    intro hcon
    have hnorm : ‖(hP.eigenvectorBasis hn) i‖ = 1 := (hP.eigenvectorBasis hn).orthonormal.1 i
    rw [hcon, norm_zero] at hnorm
    exact absurd hnorm (by norm_num)
  have hval : inner ℂ ((hP.eigenvectorBasis hn) i) (P ((hP.eigenvectorBasis hn) i))
      = ((hP.eigenvalues hn i : ℝ) : ℂ) := by
    rw [hP.apply_eigenvectorBasis hn i, inner_smul_right,
      inner_self_eq_norm_sq_to_K, (hP.eigenvectorBasis hn).orthonormal.1 i]
    simp
  have := hpos _ hne
  rw [hval] at this
  simpa using this

/-! ## The positive square root -/

omit [FiniteDimensional ℂ E] in
theorem inner_eq_zero_of_mem_span_singleton {b : Fin n → E} (hb : Orthonormal ℂ b) {i j : Fin n}
    (hij : i ≠ j) {x y : E} (hx : x ∈ (ℂ ∙ b i)) (hy : y ∈ (ℂ ∙ b j)) :
    inner ℂ x y = (0 : ℂ) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [inner_smul_left, inner_smul_right, hb.2 hij]
  ring

omit [FiniteDimensional ℂ E] in
theorem iSup_span_singleton_eq_top (b : OrthonormalBasis (Fin n) ℂ E) :
    (⨆ i, (ℂ ∙ b i)) = ⊤ := by
  rw [← Submodule.span_range_eq_iSup]
  exact b.toBasis.span_eq

/-- The positive square root of a positive-definite Hermitian form, built from its spectral
decomposition. -/
noncomputable def sqrtOp {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n) :
    E →ₗ[ℂ] E :=
  pieceOperator (fun i : Fin n => (ℂ ∙ (hP.eigenvectorBasis hn) i))
    (fun i => Real.sqrt (hP.eigenvalues hn i))

theorem isSymmetric_sqrtOp {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n) :
    (sqrtOp hP hn).IsSymmetric :=
  isSymmetric_pieceOperator _ _

theorem sqrtOp_apply_basis {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (i : Fin n) :
    sqrtOp hP hn ((hP.eigenvectorBasis hn) i)
      = ((Real.sqrt (hP.eigenvalues hn i) : ℝ) : ℂ) • (hP.eigenvectorBasis hn) i :=
  pieceOperator_apply_of_mem _
    (fun _ _ hij _ hx _ hy =>
      inner_eq_zero_of_mem_span_singleton (hP.eigenvectorBasis hn).orthonormal hij hx hy)
    (Submodule.mem_span_singleton_self _)

/-- **The square root squares to the form.** -/
theorem sqrtOp_comp_sqrtOp {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (v : E) :
    sqrtOp hP hn (sqrtOp hP hn v) = P v := by
  have hbasis : ∀ i : Fin n, sqrtOp hP hn (sqrtOp hP hn ((hP.eigenvectorBasis hn) i))
      = P ((hP.eigenvectorBasis hn) i) := by
    intro i
    rw [sqrtOp_apply_basis hP hn i, map_smul, sqrtOp_apply_basis hP hn i, smul_smul,
      hP.apply_eigenvectorBasis hn i]
    congr 1
    norm_cast
    rw [Real.mul_self_sqrt (le_of_lt (eigenvalues_pos hP hn hpos i))]
    rfl
  have hext : (sqrtOp hP hn) ∘ₗ (sqrtOp hP hn) = P := by
    refine Basis.ext (hP.eigenvectorBasis hn).toBasis fun i => ?_
    rw [LinearMap.comp_apply]
    simpa [OrthonormalBasis.coe_toBasis] using hbasis i
  exact congrArg (fun f : E →ₗ[ℂ] E => f v) hext

theorem det_sqrtOp {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (hdet : LinearMap.det P = 1) :
    LinearMap.det (sqrtOp hP hn) = 1 := by
  have hmat : LinearMap.det (sqrtOp hP hn)
      = ∏ i, ((Real.sqrt (hP.eigenvalues hn i) : ℝ) : ℂ) := by
    rw [← LinearMap.det_toMatrix (hP.eigenvectorBasis hn).toBasis,
      toMatrix_of_diagonal hP hn (sqrtOp_apply_basis hP hn), Matrix.det_diagonal]
  have hprodsq : (∏ i, Real.sqrt (hP.eigenvalues hn i)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    have hsq : ∀ i : Fin n, Real.sqrt (hP.eigenvalues hn i) ^ 2 = hP.eigenvalues hn i :=
      fun i => Real.sq_sqrt (le_of_lt (eigenvalues_pos hP hn hpos i))
    rw [Finset.prod_congr rfl fun i _ => hsq i]
    have h := hP.det_eq_prod_eigenvalues hn
    rw [hdet] at h
    have h2 : ((∏ i, hP.eigenvalues hn i : ℝ) : ℂ) = 1 := by
      push_cast
      exact h.symm
    exact_mod_cast h2
  have hpos' : 0 < ∏ i, Real.sqrt (hP.eigenvalues hn i) :=
    Finset.prod_pos fun i _ => Real.sqrt_pos.2 (eigenvalues_pos hP hn hpos i)
  have hone : (∏ i, Real.sqrt (hP.eigenvalues hn i)) = 1 := by
    nlinarith [hprodsq, hpos']
  rw [hmat, ← Complex.ofReal_prod, hone, Complex.ofReal_one]

/-! ## The observer group is transitive on observer metrics -/

/-- **Every observer metric is the pullback of the reference metric by a determinant-one
symmetry.**  So the positive-definite Hermitian forms of determinant one are a single orbit of the
observer group: the symmetric space of the boundary picture. -/
theorem exists_congruence_of_observerMetric {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re)
    (hdet : LinearMap.det P = 1) :
    ∃ g : E →ₗ[ℂ] E, LinearMap.det g = 1 ∧
      ∀ v w : E, inner ℂ v (P w) = inner ℂ (g v) (g w) := by
  refine ⟨sqrtOp hP hn, det_sqrtOp hP hn hpos hdet, fun v w => ?_⟩
  rw [isSymmetric_sqrtOp hP hn v (sqrtOp hP hn w), sqrtOp_comp_sqrtOp hP hn hpos w]

omit [FiniteDimensional ℂ E] in
/-- **The stabilizer of the reference metric is the group of isometries.** -/
theorem congruence_eq_refl_iff (g : E ≃ₗ[ℂ] E) :
    (∀ v w : E, inner ℂ v w = inner ℂ (g v) (g w)) ↔ ∀ v : E, ‖g v‖ = ‖v‖ := by
  constructor
  · intro h v
    have hvv := h v v
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hvv
    have hsq : ‖g v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast hvv.symm
    calc ‖g v‖ = Real.sqrt (‖g v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖v‖ ^ 2) := by rw [hsq]
      _ = ‖v‖ := Real.sqrt_sq (norm_nonneg _)
  · intro h v w
    exact ((LinearMap.norm_map_iff_inner_map_map (𝕜 := ℂ) (g : E →ₗ[ℂ] E)).1 h v w).symm

/-! ## The rays stay in the space -/

theorem det_metricRay_eq_one_of_trace_zero {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : finrank ℂ E = n) (htr : LinearMap.trace ℂ E T = 0) (t : ℝ) :
    LinearMap.det ((metricRay T t : E →ₗ[ℂ] E)) = 1 := by
  rw [det_metricRay hT hn t]
  have hsum : ∑ i, hT.eigenvalues hn i = 0 := by
    have := trace_eq_sum_eigenvalues hT hn
    rw [htr] at this
    exact_mod_cast this.symm
  rw [hsum]
  simp

/-- **A traceless direction stays inside the space of observer metrics.**  Its ray consists of
positive-definite Hermitian forms of determinant one. -/
theorem metricRay_mem_observerMetric {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : finrank ℂ E = n)
    (htr : LinearMap.trace ℂ E T = 0) (t : ℝ) :
    ((metricRay T t : E →ₗ[ℂ] E)).IsSymmetric
      ∧ (∀ v : E, v ≠ 0 → 0 < (inner ℂ v (metricRay T t v)).re)
      ∧ LinearMap.det ((metricRay T t : E →ₗ[ℂ] E)) = 1 :=
  ⟨isSymmetric_metricRay hT hn t, fun _ hv => inner_metricRay_pos hT hn hv t,
    det_metricRay_eq_one_of_trace_zero hT hn htr t⟩

end GaloisForLFunctions.HTGeometry
