import GaloisForLFunctions.HTGeometry.HermitianGeodesicRay

/-!
# The observer metric along a ray

The value `exp (t T)` of the ray of a Hermitian direction is itself a positive-definite Hermitian
form — an observer metric — whose determinant is the exponential of `t` times the trace of the
direction.  So the ray stays inside the determinant-one space of observer metrics exactly when the
direction is traceless, which is the normalization the boundary picture uses.

The degeneration of that form is read off by the flag: on the flag member at threshold `c` the form
dominates `exp (c t)` times the reference form, and orthogonally to it is dominated by it.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {T : E →ₗ[ℂ] E}

/-! ## The form in eigencoordinates -/

theorem inner_eq_sum_repr (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (v w : E) :
    inner ℂ v w = ∑ i, (starRingEnd ℂ) ((hT.eigenvectorBasis hn).repr v i)
      * (hT.eigenvectorBasis hn).repr w i :=
  inner_eq_sum_repr_of_orthonormalBasis (hT.eigenvectorBasis hn) v w

theorem norm_sq_eq_sum_repr (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (v : E) :
    ‖v‖ ^ 2 = ∑ i, ‖(hT.eigenvectorBasis hn).repr v i‖ ^ 2 := by
  rw [norm_sq_repr hT hn v, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem conj_mul_ofReal_mul (z : ℂ) (r : ℝ) :
    (starRingEnd ℂ) z * ((r : ℂ) * z) = ((r * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h : (starRingEnd ℂ) z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := RCLike.conj_mul z
  calc (starRingEnd ℂ) z * ((r : ℂ) * z) = (r : ℂ) * ((starRingEnd ℂ) z * z) := by ring
    _ = (r : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2 := by rw [h]
    _ = ((r * ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring

/-- **The observer metric in eigencoordinates**: along the ray each eigencoordinate is weighted by
the exponential of its eigenvalue. -/
theorem inner_metricRay_eq_sum (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (v : E) (t : ℝ) :
    inner ℂ v (metricRay T t v)
      = ((∑ i, Real.exp (t * hT.eigenvalues hn i)
          * ‖(hT.eigenvectorBasis hn).repr v i‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_eq_sum_repr hT hn v (metricRay T t v), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_metricRay hT hn v t i]
  exact conj_mul_ofReal_mul _ _

/-- **The observer metric is a Hermitian form.** -/
theorem isSymmetric_metricRay (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (t : ℝ) :
    ((metricRay T t : E →ₗ[ℂ] E)).IsSymmetric := by
  intro v w
  show inner ℂ (metricRay T t v) w = inner ℂ v (metricRay T t w)
  rw [inner_eq_sum_repr hT hn (metricRay T t v) w, inner_eq_sum_repr hT hn v (metricRay T t w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_metricRay hT hn v t i, repr_metricRay hT hn w t i, map_mul, Complex.conj_ofReal]
  ring

/-- **The observer metric is positive definite**, so the ray stays inside the space of
positive-definite Hermitian observer metrics. -/
theorem inner_metricRay_pos (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {v : E} (hv : v ≠ 0)
    (t : ℝ) : 0 < (inner ℂ v (metricRay T t v)).re := by
  rw [inner_metricRay_eq_sum hT hn v t]
  simp only [Complex.ofReal_re]
  obtain ⟨i, hi⟩ : ∃ i : Fin n, (hT.eigenvectorBasis hn).repr v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hnorm : ‖v‖ ^ 2 = 0 := by
      rw [norm_sq_eq_sum_repr hT hn v]
      exact Finset.sum_eq_zero fun i _ => by rw [hcon i]; simp
    exact hv (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hnorm))
  refine Finset.sum_pos' (fun i _ => mul_nonneg (le_of_lt (Real.exp_pos _)) (sq_nonneg _))
    ⟨i, Finset.mem_univ i, mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.2 hi) 2)⟩

/-! ## Growth of the form along the flag -/

theorem repr_eq_zero_of_mem_eigenSum (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ} {v : E}
    (hv : v ∈ eigenSum T c) {i : Fin n} (hi : hT.eigenvalues hn i ≤ c) :
    (hT.eigenvectorBasis hn).repr v i = 0 := by
  refine repr_eq_zero_of_mem_span (hT.eigenvectorBasis hn)
    (s := {j | c < hT.eigenvalues hn j}) ?_ ?_
  · rw [← eigenSum_eq_span hT hn c]
    exact hv
  · intro hmem
    exact absurd (show c < hT.eigenvalues hn i from hmem) (not_lt.2 hi)

theorem repr_eq_zero_of_mem_orthogonal (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ} {v : E}
    (hv : v ∈ (eigenSum T c)ᗮ) {i : Fin n} (hi : c < hT.eigenvalues hn i) :
    (hT.eigenvectorBasis hn).repr v i = 0 := by
  rw [(hT.eigenvectorBasis hn).repr_apply_apply]
  have hmem : (hT.eigenvectorBasis hn) i ∈ eigenSum T c :=
    eigenspace_le_eigenSum hi (hT.hasEigenvector_eigenvectorBasis hn i).1
  exact inner_eq_zero_comm ((Submodule.mem_orthogonal' _ _).1 hv _ hmem)

/-- **On the flag member at threshold `c` the observer metric grows at least at rate `c`.** -/
theorem re_inner_metricRay_ge (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ} {v : E}
    (hv : v ∈ eigenSum T c) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (c * t) * ‖v‖ ^ 2 ≤ (inner ℂ v (metricRay T t v)).re := by
  rw [inner_metricRay_eq_sum hT hn v t]
  simp only [Complex.ofReal_re]
  rw [norm_sq_eq_sum_repr hT hn v, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : hT.eigenvalues hn i ≤ c
  · rw [repr_eq_zero_of_mem_eigenSum hT hn hv hi]
    simp
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
    rw [mul_comm c t]
    exact mul_le_mul_of_nonneg_left (le_of_lt (not_le.1 hi)) ht

/-- **Orthogonally to the flag member at threshold `c` the observer metric grows at most at rate
`c`.** -/
theorem re_inner_metricRay_le (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ} {v : E}
    (hv : v ∈ (eigenSum T c)ᗮ) {t : ℝ} (ht : 0 ≤ t) :
    (inner ℂ v (metricRay T t v)).re ≤ Real.exp (c * t) * ‖v‖ ^ 2 := by
  rw [inner_metricRay_eq_sum hT hn v t]
  simp only [Complex.ofReal_re]
  rw [norm_sq_eq_sum_repr hT hn v, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : c < hT.eigenvalues hn i
  · rw [repr_eq_zero_of_mem_orthogonal hT hn hv hi]
    simp
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
    rw [mul_comm c t]
    exact mul_le_mul_of_nonneg_left (not_lt.1 hi) ht

/-! ## Determinant and trace -/

/-- **An operator diagonal in the eigenbasis has diagonal matrix.** -/
theorem toMatrix_of_diagonal (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {f : E →ₗ[ℂ] E}
    {d : Fin n → ℂ} (hd : ∀ i, f ((hT.eigenvectorBasis hn) i) = d i • (hT.eigenvectorBasis hn) i) :
    LinearMap.toMatrix (hT.eigenvectorBasis hn).toBasis (hT.eigenvectorBasis hn).toBasis f
      = Matrix.diagonal d :=
  toMatrix_diagonal_of_orthonormalBasis (hT.eigenvectorBasis hn) hd

theorem toMatrix_metricRay (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (t : ℝ) :
    LinearMap.toMatrix (hT.eigenvectorBasis hn).toBasis (hT.eigenvectorBasis hn).toBasis
        ((metricRay T t : E →ₗ[ℂ] E))
      = Matrix.diagonal (fun i => ((Real.exp (t * hT.eigenvalues hn i) : ℝ) : ℂ)) :=
  toMatrix_of_diagonal hT hn (fun i => metricRay_eigenvectorBasis hT hn i t)

/-- **The determinant along the ray is the exponential of the trace.**  Here it is proved from the
spectral decomposition, so it needs no triangularization. -/
theorem det_metricRay (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (t : ℝ) :
    LinearMap.det ((metricRay T t : E →ₗ[ℂ] E))
      = ((Real.exp (t * ∑ i, hT.eigenvalues hn i) : ℝ) : ℂ) := by
  rw [← LinearMap.det_toMatrix (hT.eigenvectorBasis hn).toBasis, toMatrix_metricRay hT hn t,
    Matrix.det_diagonal, ← Complex.ofReal_prod, Finset.mul_sum, Real.exp_sum]

theorem trace_eq_sum_eigenvalues (hT : T.IsSymmetric) (hn : finrank ℂ E = n) :
    LinearMap.trace ℂ E T = ((∑ i, hT.eigenvalues hn i : ℝ) : ℂ) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (hT.eigenvectorBasis hn).toBasis T,
    hT.toMatrix_eigenvectorBasis hn, Matrix.trace_diagonal, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **The ray stays in the determinant-one space exactly when the direction is traceless.**  That is
the normalization `det = 1` of the space of observer metrics. -/
theorem det_metricRay_eq_one_iff (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {t : ℝ} (ht : t ≠ 0) :
    LinearMap.det ((metricRay T t : E →ₗ[ℂ] E)) = 1 ↔ LinearMap.trace ℂ E T = 0 := by
  rw [det_metricRay hT hn t, trace_eq_sum_eigenvalues hT hn]
  constructor
  · intro h
    have hreal : Real.exp (t * ∑ i, hT.eigenvalues hn i) = 1 := by
      exact_mod_cast h
    have := (Real.exp_eq_one_iff _).1 hreal
    have hsum : ∑ i, hT.eigenvalues hn i = 0 := by
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 ht
      · exact h1
    rw [hsum]
    simp
  · intro h
    have hsum : ∑ i, hT.eigenvalues hn i = 0 := by exact_mod_cast h
    rw [hsum]
    simp

end GaloisForLFunctions.HTGeometry
