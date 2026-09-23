import GaloisForLFunctions.HTGeometry.FlatEuclidean

/-!
# The inverse of an observer metric

Every positive-definite Hermitian form has a positive-definite Hermitian inverse, built like its
square root and its logarithm from the spectral decomposition.  Its logarithm is the negative of the
logarithm of the form, so it lies at the same distance from the reference metric: the inversion
`P ↦ P⁻¹` is the geodesic symmetry through the reference point.

The tool that makes this cheap is a characterization of the logarithm: an operator diagonal in *any*
orthonormal frame with positive weights has as logarithm the operator diagonal in the same frame
with the logarithms of those weights.  It is proved through the flag, so no eigenbasis bookkeeping
is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {P : E →ₗ[ℂ] E}

/-! ## Positivity of a diagonal operator -/

omit [FiniteDimensional ℂ E] in
/-- **The quadratic form of an operator diagonal in an orthonormal frame** is the weighted sum of
the squared coordinates. -/
theorem inner_self_of_diagonal (b : OrthonormalBasis (Fin n) ℂ E) {f : E →ₗ[ℂ] E} {d : Fin n → ℝ}
    (hd : ∀ i, f (b i) = ((d i : ℝ) : ℂ) • b i) (v : E) :
    inner ℂ v (f v) = ((∑ i, d i * ‖b.repr v i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  classical
  rw [inner_eq_sum_repr_of_orthonormalBasis b v (f v), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_of_diagonal b hd v i]
  exact conj_mul_ofReal_mul _ _

omit [FiniteDimensional ℂ E] in
/-- **An operator with positive diagonal in an orthonormal frame is positive definite.** -/
theorem inner_self_pos_of_diagonal (b : OrthonormalBasis (Fin n) ℂ E) {f : E →ₗ[ℂ] E}
    {d : Fin n → ℝ} (hd : ∀ i, f (b i) = ((d i : ℝ) : ℂ) • b i) (hpos : ∀ i, 0 < d i)
    {v : E} (hv : v ≠ 0) : 0 < (inner ℂ v (f v)).re := by
  classical
  rw [inner_self_of_diagonal b hd v, Complex.ofReal_re]
  obtain ⟨i, hi⟩ : ∃ i, b.repr v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hv ?_
    have : v = 0 := by
      conv_lhs => rw [← b.sum_repr v]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hcon i, zero_smul]
    exact this
  refine Finset.sum_pos' (fun i _ => mul_nonneg (le_of_lt (hpos i)) (sq_nonneg _))
    ⟨i, Finset.mem_univ i, mul_pos (hpos i) (pow_pos (norm_pos_iff.2 hi) 2)⟩

/-! ## The logarithm of a diagonal operator -/

/-- **The logarithm of an operator diagonal in a frame is diagonal in the same frame**, with the
logarithms of its weights. -/
theorem logOp_eq_of_diagonal (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    {f : E →ₗ[ℂ] E} (hf : f.IsSymmetric) {d : Fin n → ℝ}
    (hd : ∀ i, f (b i) = ((d i : ℝ) : ℂ) • b i) (hpos : ∀ i, 0 < d i) :
    logOp hf hn = diagOp b (fun i => Real.log (d i)) := by
  classical
  refine eq_of_eigenSum_eq (isSymmetric_logOp hf hn) (isSymmetric_diagOp b _) hn fun c => ?_
  rw [eigenSum_logOp hf hn (fun v hv => inner_self_pos_of_diagonal b hd hpos hv) c,
    eigenSum_eq_span_of_eigenbasis b.toBasis (w := d)
      (fun i => by rw [OrthonormalBasis.coe_toBasis]; exact hd i) (Real.exp c),
    eigenSum_eq_span_of_eigenbasis b.toBasis (w := fun i => Real.log (d i))
      (fun i => by rw [OrthonormalBasis.coe_toBasis]; exact diagOp_apply_basis b _ i) c]
  have hset : {i : Fin n | Real.exp c < d i} = {i : Fin n | c < Real.log (d i)} := by
    ext i
    simp only [Set.mem_setOf_eq]
    rw [Real.lt_log_iff_exp_lt (hpos i)]
  rw [hset]

/-! ## The inverse -/

/-- The inverse of a positive-definite Hermitian form, built from its spectral decomposition. -/
noncomputable def invOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n) : E →ₗ[ℂ] E :=
  pieceOperator (fun i : Fin n => (ℂ ∙ (hP.eigenvectorBasis hn) i))
    (fun i => (hP.eigenvalues hn i)⁻¹)

theorem isSymmetric_invOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n) :
    (invOp hP hn).IsSymmetric :=
  isSymmetric_pieceOperator _ _

theorem invOp_apply_basis (hP : P.IsSymmetric) (hn : finrank ℂ E = n) (i : Fin n) :
    invOp hP hn ((hP.eigenvectorBasis hn) i)
      = (((hP.eigenvalues hn i)⁻¹ : ℝ) : ℂ) • (hP.eigenvectorBasis hn) i :=
  pieceOperator_apply_of_mem _
    (fun _ _ hij _ hx _ hy =>
      inner_eq_zero_of_mem_span_singleton (hP.eigenvectorBasis hn).orthonormal hij hx hy)
    (Submodule.mem_span_singleton_self _)

/-- **The inverse is positive definite.** -/
theorem inner_invOp_pos (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) {v : E} (hv : v ≠ 0) :
    0 < (inner ℂ v (invOp hP hn v)).re :=
  inner_self_pos_of_diagonal (hP.eigenvectorBasis hn) (invOp_apply_basis hP hn)
    (fun i => inv_pos.2 (eigenvalues_pos hP hn hpos i)) hv

/-- **The inverse inverts.** -/
theorem invOp_comp (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (v : E) :
    invOp hP hn (P v) = v := by
  have hext : (invOp hP hn) ∘ₗ P = LinearMap.id := by
    refine Basis.ext (hP.eigenvectorBasis hn).toBasis fun i => ?_
    rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, hP.apply_eigenvectorBasis hn i,
      map_smul, invOp_apply_basis hP hn i, smul_smul, LinearMap.id_apply]
    have hne : hP.eigenvalues hn i ≠ 0 := ne_of_gt (eigenvalues_pos hP hn hpos i)
    simp [hne]
  exact congrArg (fun f : E →ₗ[ℂ] E => f v) hext

/-! ## The logarithm of the inverse -/

/-- **The logarithm of the inverse is the negative of the logarithm.** -/
theorem logOp_invOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) :
    logOp (isSymmetric_invOp hP hn) hn = - logOp hP hn := by
  have hP' : logOp hP hn
      = diagOp (hP.eigenvectorBasis hn) (fun i => Real.log (hP.eigenvalues hn i)) :=
    logOp_eq_of_diagonal (hP.eigenvectorBasis hn) hn hP (hP.apply_eigenvectorBasis hn)
      (fun i => eigenvalues_pos hP hn hpos i)
  have hinv : logOp (isSymmetric_invOp hP hn) hn
      = diagOp (hP.eigenvectorBasis hn) (fun i => Real.log ((hP.eigenvalues hn i)⁻¹)) :=
    logOp_eq_of_diagonal (hP.eigenvectorBasis hn) hn (isSymmetric_invOp hP hn)
      (invOp_apply_basis hP hn) (fun i => inv_pos.2 (eigenvalues_pos hP hn hpos i))
  have hneg : (fun i => Real.log ((hP.eigenvalues hn i)⁻¹))
      = -(fun i => Real.log (hP.eigenvalues hn i)) := by
    funext i
    rw [Real.log_inv, Pi.neg_apply]
  rw [hinv, hneg, hP']
  have hmap := (diagOpₗ (hP.eigenvectorBasis hn)).map_neg
    (fun i => Real.log (hP.eigenvalues hn i))
  simpa only [diagOpₗ_apply] using hmap

/-- **Inversion is an isometry of the radial distance.**  An observer metric and its inverse are at
the same distance from the reference metric: inversion is the geodesic symmetry through the
reference point. -/
theorem distId_invOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) :
    distId (isSymmetric_invOp hP hn) hn = distId hP hn := by
  have hmap : LinearMap.toContinuousLinearMap (-(logOp hP hn))
      = (-1 : ℂ) • LinearMap.toContinuousLinearMap (logOp hP hn) := by
    ext v
    simp
  rw [distId, distId, logOp_invOp hP hn hpos, hmap,
    hsNorm_smul_of_isHilbertSchmidt (isHilbertSchmidt_toCLM (logOp hP hn))]
  simp

end GaloisForLFunctions.HTGeometry
