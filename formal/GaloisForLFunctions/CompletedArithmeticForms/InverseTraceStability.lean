import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Relative perturbation costs from the complete inverse

The trace of the inverse pays every coordinate evaluation in a positive quadratic
form. It turns an entrywise source estimate into a relative estimate in the full
comparison norm, retaining the effect of all mixed entries.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

private theorem real_matrix_pair_comm {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.IsHermitian) (u v : Fin N → ℝ) :
    u ⬝ᵥ G *ᵥ v = v ⬝ᵥ G *ᵥ u := by
  have hs (i j : Fin N) : G i j = G j i := by
    have h := congrFun (congrFun hG i) j
    simpa only [conjTranspose_apply, star_trivial] using h.symm
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [hs j i]
  ring

private theorem real_posSemidef_cauchy_schwarz {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosSemidef) (u v : Fin N → ℝ) :
    (u ⬝ᵥ G *ᵥ v) ^ 2 ≤ (u ⬝ᵥ G *ᵥ u) * (v ⬝ᵥ G *ᵥ v) := by
  have hquad : ∀ t : ℝ, 0 ≤ (v ⬝ᵥ G *ᵥ v) * (t * t) +
      2 * (u ⬝ᵥ G *ᵥ v) * t + (u ⬝ᵥ G *ᵥ u) := by
    intro t
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hG).2 (u + t • v)
    simp only [star_trivial, mulVec_add, mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
    rw [real_matrix_pair_comm hG.isHermitian v u] at h
    nlinarith only [h]
  have h := discrim_le_zero hquad
  rw [discrim] at h
  nlinarith only [h]

/-- Each inverse diagonal is the exact dual cost of evaluating its coordinate. -/
theorem coordinate_sq_le_inverse_diagonal {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) (v : Fin N → ℝ) (i : Fin N) :
    v i ^ 2 ≤ G⁻¹ i i * (v ⬝ᵥ G *ᵥ v) := by
  let e : Fin N → ℝ := Pi.single i 1
  let u := G⁻¹ *ᵥ e
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hG.det_pos.ne'
  have hu : G *ᵥ u = e := by
    dsimp [u]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv G hunit, one_mulVec]
  have h := real_posSemidef_cauchy_schwarz hG.posSemidef u v
  rw [real_matrix_pair_comm hG.isHermitian u v, hu] at h
  have heval (b : Fin N → ℝ) : b ⬝ᵥ e = b i := by
    rw [dotProduct_comm]
    simp only [e, single_dotProduct, one_mul]
  have hui : u i = G⁻¹ i i := heval (G⁻¹ i)
  rw [heval v, heval u, hui] at h
  exact h

/-- The complete inverse trace gives an explicit coercivity constant, also for empty heads. -/
theorem squareMass_le_inverseTrace_energy {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) (v : Fin N → ℝ) :
    v ⬝ᵥ v ≤ G⁻¹.trace * (v ⬝ᵥ G *ᵥ v) := by
  have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin N))) =>
    coordinate_sq_le_inverse_diagonal hG v i)
  simpa only [← sum_mul, Matrix.trace, Matrix.diag, dotProduct, pow_two] using h

/-- Entrywise perturbations have an explicit cost relative to the full positive form. -/
theorem relative_error_le_inverseTrace {N : ℕ} {G A : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) {ε : ℝ} (hε : 0 ≤ ε)
    (hentry : ∀ i j, |A i j - G i j| ≤ ε) (v : Fin N → ℝ) :
    |v ⬝ᵥ (A - G) *ᵥ v| ≤
      ((N : ℝ) * ε * G⁻¹.trace) * (v ⬝ᵥ G *ᵥ v) := by
  have he := HTGeometry.abs_dotProduct_mulVec_le (A - G) hε hentry v
  have hc := mul_le_mul_of_nonneg_left (squareMass_le_inverseTrace_energy hG v)
    (show 0 ≤ (N : ℝ) * ε by positivity)
  exact he.trans (by convert hc using 1; ring)

/-- Paying less than half the comparison energy leaves a strict half-form reserve. -/
theorem half_relative_posDef_of_inverseTrace {N : ℕ} {G A : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) (hA : A.IsHermitian) {ε : ℝ} (hε : 0 ≤ ε)
    (hentry : ∀ i j, |A i j - G i j| ≤ ε)
    (hcost : (N : ℝ) * ε * G⁻¹.trace < 1 / 2) :
    (A - (1 / 2 : ℝ) • G).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hA.sub ((hG.smul (by norm_num : (0 : ℝ) < 1 / 2)).isHermitian), ?_⟩
  intro v hv
  rw [star_trivial]
  have hg : 0 < v ⬝ᵥ G *ᵥ v := by
    simpa only [star_trivial] using (Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 (x := v) hv
  have he := (abs_le.mp (relative_error_le_inverseTrace hG hε hentry v)).1
  have hs : v ⬝ᵥ (A - (1 / 2 : ℝ) • G) *ᵥ v =
      v ⬝ᵥ (A - G) *ᵥ v + (1 / 2) * (v ⬝ᵥ G *ᵥ v) := by
    simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring
  rw [hs]
  nlinarith only [he, mul_pos (sub_pos.mpr hcost) hg]

#print axioms squareMass_le_inverseTrace_energy
#print axioms relative_error_le_inverseTrace
#print axioms half_relative_posDef_of_inverseTrace

end GaloisForLFunctions.CompletedArithmeticForms
