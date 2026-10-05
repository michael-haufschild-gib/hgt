import Mathlib

/-!
# Jacobi's formula for complex matrices and operators

The determinant is a continuous multilinear function of the rows, so its derivative at `M` in
the direction `M'` is `∑ᵢ det (M with row i replaced by M'ᵢ)`; the row expansion of each summand
turns this into `tr (adj M · M')`.  At an invertible point `adj M = det M · M⁻¹`.

For a differentiable curve of operators on a finite-dimensional complex normed space, reading
the curve in a basis gives `d/dt det G(t) = det G(t) · tr (G(t)⁻¹ G'(t))` wherever `G(t)` is
invertible.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The determinant as a continuous multilinear function of the rows. -/
def detRowsCML (n : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin n → ℂ) ℂ where
  toMultilinearMap := (Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap
  cont := by
    have : Continuous fun m : Matrix (Fin n) (Fin n) ℂ => m.det := continuous_id.matrix_det
    exact this

theorem detRowsCML_apply {n : ℕ} (m : Fin n → Fin n → ℂ) :
    detRowsCML n m = Matrix.det (Matrix.of m) := rfl

/-- Row expansion: `det (A with row i replaced by v) = ∑ⱼ adj(A)ⱼᵢ vⱼ`. -/
theorem det_updateRow_eq_sum_adjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (v : Fin n → ℂ) : (A.updateRow i v).det = ∑ j, A.adjugate j i * v j := by
  rw [← det_transpose, ← updateCol_transpose, ← cramer_apply, cramer_eq_adjugate_mulVec,
    ← adjugate_transpose, mulVec, dotProduct]
  simp [transpose_apply]

/-- **Jacobi's formula** for a curve of complex matrices: `d/dt det M = tr (adj M · M')`. -/
theorem hasDerivAt_det_complex {n : ℕ} {M : ℝ → Fin n → Fin n → ℂ} {M' : Fin n → Fin n → ℂ}
    {t : ℝ} (h : HasDerivAt M M' t) :
    HasDerivAt (fun s => Matrix.det (Matrix.of (M s)))
      (Matrix.trace ((Matrix.of (M t)).adjugate * Matrix.of M')) t := by
  have hf := ((detRowsCML n).hasFDerivAt (M t)).restrictScalars ℝ
  have h1 := hf.comp_hasDerivAt t h
  refine h1.congr_deriv ?_
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousMultilinearMap.linearDeriv_apply,
    detRowsCML_apply]
  have hrow : ∀ i, Matrix.det (Matrix.of (Function.update (M t) i (M' i))) =
      ∑ j, (Matrix.of (M t)).adjugate j i * M' i j := fun i =>
    det_updateRow_eq_sum_adjugate (Matrix.of (M t)) i (M' i)
  simp_rw [hrow]
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  exact Finset.sum_comm

/-- At an invertible point the Jacobi derivative is `det M · tr (M⁻¹ M')`. -/
theorem trace_adjugate_mul_eq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) :
    Matrix.trace (A.adjugate * B) = A.det * Matrix.trace (A⁻¹ * B) := by
  rw [Matrix.inv_def, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
    Ring.inverse_eq_inv', mul_inv_cancel₀ hA, one_mul]

section Operator

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The `(i, j)` matrix entry of an operator in the basis `b`, as a continuous functional. -/
def operatorEntry {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (i j : Fin n) : (V →L[ℂ] V) →L[ℂ] ℂ :=
  (LinearMap.toContinuousLinearMap (b.coord i)).comp (ContinuousLinearMap.apply ℂ V (b j))

theorem operatorEntry_apply {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (i j : Fin n)
    (A : V →L[ℂ] V) :
    operatorEntry b i j A = LinearMap.toMatrix b b (A : V →ₗ[ℂ] V) i j := by
  simp [operatorEntry, LinearMap.toMatrix_apply, Module.Basis.coord_apply]

/-- **Jacobi's formula for operators**: at an invertible point,
`d/dt det G = det G · tr (G⁻¹ G')`. -/
theorem hasDerivAt_det_operator {G : ℝ → V →L[ℂ] V} {G' : V →L[ℂ] V} {t : ℝ}
    (hG : HasDerivAt G G' t) (hunit : IsUnit (G t)) :
    HasDerivAt (fun s => LinearMap.det (G s : V →ₗ[ℂ] V))
      (LinearMap.det (G t : V →ₗ[ℂ] V) *
        LinearMap.trace ℂ V (Ring.inverse (G t) * G' : V →L[ℂ] V)) t := by
  set b := Module.finBasis ℂ V
  set M : ℝ → Fin (Module.finrank ℂ V) → Fin (Module.finrank ℂ V) → ℂ :=
    fun s i j => operatorEntry b i j (G s)
  have hM : HasDerivAt M (fun i j => operatorEntry b i j G') t := by
    refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
    exact ((operatorEntry b i j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hG
  have hMs : ∀ s, Matrix.of (M s) = LinearMap.toMatrix b b (G s : V →ₗ[ℂ] V) := fun s => by
    ext i j
    simp [M, operatorEntry_apply]
  have hM' : Matrix.of (fun i j => operatorEntry b i j G') =
      LinearMap.toMatrix b b (G' : V →ₗ[ℂ] V) := by
    ext i j
    simp [operatorEntry_apply]
  have hJ := hasDerivAt_det_complex hM
  simp only [hMs, hM', LinearMap.det_toMatrix] at hJ
  refine hJ.congr_deriv ?_
  have hdet : LinearMap.det (G t : V →ₗ[ℂ] V) ≠ 0 :=
    ((hunit.map ContinuousLinearMap.toLinearMapRingHom).map LinearMap.det).ne_zero
  obtain ⟨u, hu⟩ := hunit
  rw [trace_adjugate_mul_eq _ _ (by rwa [LinearMap.det_toMatrix]), LinearMap.det_toMatrix]
  congr 1
  have hinv : (LinearMap.toMatrix b b (G t : V →ₗ[ℂ] V))⁻¹ =
      LinearMap.toMatrix b b ((Ring.inverse (G t) : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [← LinearMap.toMatrix_mul, ← ContinuousLinearMap.toLinearMap_mul, ← hu, Ring.inverse_unit,
      Units.mul_inv, ContinuousLinearMap.toLinearMap_one, LinearMap.toMatrix_one]
  rw [hinv, ← LinearMap.toMatrix_mul, ← LinearMap.trace_eq_matrix_trace,
    ContinuousLinearMap.toLinearMap_mul]

end Operator

end GaloisForLFunctions.HTGeometry
