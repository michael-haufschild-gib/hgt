import GaloisForLFunctions.CompletedArithmeticForms.InverseTraceStability

/-!
# Variance-weighted inverse costs of completed forms

Relative entry errors are measured in each comparison coordinate's own variance.
The exact inverse-coordinate costs then give a full mixed-form estimate without
replacing every moment by the largest entry of the comparison matrix.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The inverse-coordinate cost weighted by the variance of each source coordinate. -/
def varianceInverseCost {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, G i i * G⁻¹ i i

theorem varianceInverseCost_nonneg {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) : 0 ≤ varianceInverseCost G := by
  exact sum_nonneg fun i _ => mul_nonneg hG.posSemidef.diag_nonneg hG.inv.posSemidef.diag_nonneg

/-- The full comparison bounds a mixed entry by the geometric mean of its variances. -/
theorem posSemidef_entry_abs_le_sqrt {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosSemidef) (i j : Fin N) :
    |G i j| ≤ Real.sqrt (G i i) * Real.sqrt (G j j) := by
  have hs (v : Fin N → ℝ) : 0 ≤ G.toBilin' v v := by
    rw [Matrix.toBilin'_apply']
    simpa only [star_trivial] using (Matrix.posSemidef_iff_dotProduct_mulVec.mp hG).2 v
  have h := G.toBilin'.apply_mul_apply_le_of_forall_zero_le hs
    (Pi.single i 1) (Pi.single j 1)
  simp only [Matrix.toBilin'_single] at h
  have hij : G j i = G i j := by
    have he := congrFun (congrFun hG.isHermitian i) j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using he
  rw [hij, ← pow_two] at h
  apply abs_le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Real.sq_sqrt hG.diag_nonneg, Real.sq_sqrt hG.diag_nonneg]
  exact h

/-- Relative entry bounds are paid by the weighted square mass of the original coordinates. -/
theorem weighted_entry_error_le {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ)
    (w : Fin N → ℝ) (hw : ∀ i, 0 < w i) {ε : ℝ} (hε : 0 ≤ ε)
    (hentry : ∀ i j, |E i j| ≤ ε * w i * w j) (v : Fin N → ℝ) :
    |v ⬝ᵥ E *ᵥ v| ≤ (N : ℝ) * ε * ∑ i, w i ^ 2 * v i ^ 2 := by
  let F : Matrix (Fin N) (Fin N) ℝ := fun i j => E i j / (w i * w j)
  let u : Fin N → ℝ := fun i => w i * v i
  have hF (i j : Fin N) : |F i j| ≤ ε := by
    change |E i j / (w i * w j)| ≤ ε
    rw [_root_.abs_div, abs_of_pos (mul_pos (hw i) (hw j))]
    apply (div_le_iff₀ (mul_pos (hw i) (hw j))).mpr
    simpa only [mul_assoc] using hentry i j
  have he : v ⬝ᵥ E *ᵥ v = u ⬝ᵥ F *ᵥ u := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    dsimp only [F, u]
    field_simp [(hw i).ne', (hw j).ne']
  rw [he]
  have h := HTGeometry.abs_dotProduct_mulVec_le F hε hF u
  simpa only [dotProduct, u, ← pow_two, mul_pow] using h

/-- Variance-weighted square mass is controlled by the full positive comparison. -/
theorem weighted_squareMass_le_inverseCost {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) (v : Fin N → ℝ) :
    (∑ i, G i i * v i ^ 2) ≤ varianceInverseCost G * (v ⬝ᵥ G *ᵥ v) := by
  have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin N))) =>
    mul_le_mul_of_nonneg_left (coordinate_sq_le_inverse_diagonal hG v i)
      (hG.posSemidef.diag_nonneg (i := i)))
  simpa only [varianceInverseCost, Finset.sum_mul, mul_assoc] using h

/-- A relative entry estimate has the intrinsic variance-weighted inverse payment. -/
theorem relative_error_le_varianceInverseCost {N : ℕ} {G A : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) {ε : ℝ} (hε : 0 ≤ ε)
    (hentry : ∀ i j, |A i j - G i j| ≤
      ε * Real.sqrt (G i i) * Real.sqrt (G j j)) (v : Fin N → ℝ) :
    |v ⬝ᵥ (A - G) *ᵥ v| ≤
      ((N : ℝ) * ε * varianceInverseCost G) * (v ⬝ᵥ G *ᵥ v) := by
  have he := weighted_entry_error_le (A - G) (fun i => Real.sqrt (G i i))
    (fun i => Real.sqrt_pos.mpr hG.diag_pos) hε hentry v
  simp only [Real.sq_sqrt hG.posSemidef.diag_nonneg] at he
  have hc := mul_le_mul_of_nonneg_left (weighted_squareMass_le_inverseCost hG v)
    (show 0 ≤ (N : ℝ) * ε by positivity)
  exact he.trans (by convert hc using 1; ring)

/-- Errors relative to the actual mixed comparison entries satisfy the same complete-form payment. -/
theorem relative_entry_error_le_varianceInverseCost {N : ℕ}
    {G A : Matrix (Fin N) (Fin N) ℝ} (hG : G.PosDef) {ε : ℝ} (hε : 0 ≤ ε)
    (hentry : ∀ i j, |A i j - G i j| ≤ ε * |G i j|) (v : Fin N → ℝ) :
    |v ⬝ᵥ (A - G) *ᵥ v| ≤
      ((N : ℝ) * ε * varianceInverseCost G) * (v ⬝ᵥ G *ᵥ v) := by
  apply relative_error_le_varianceInverseCost hG hε _ v
  intro i j
  exact (hentry i j).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (posSemidef_entry_abs_le_sqrt hG.posSemidef i j) hε)

/-- Every variance pays at least one unit of its own dual evaluation cost. -/
theorem dimension_le_varianceInverseCost {N : ℕ} {G : Matrix (Fin N) (Fin N) ℝ}
    (hG : G.PosDef) : (N : ℝ) ≤ varianceInverseCost G := by
  have he (i : Fin N) : (Pi.single i 1 : Fin N → ℝ) ⬝ᵥ G *ᵥ Pi.single i 1 = G i i := by
    simpa only [Matrix.toBilin'_apply'] using Matrix.toBilin'_single G i i
  have h (i : Fin N) : (1 : ℝ) ≤ G i i * G⁻¹ i i := by
    have hc := coordinate_sq_le_inverse_diagonal hG (Pi.single i 1) i
    simpa only [Pi.single_eq_same, one_pow, he, mul_comm] using hc
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    varianceInverseCost] using sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin N))) => h i)

/-- The payment is an explicit cofactor expression in the complete comparison entries. -/
theorem varianceInverseCost_eq_cofactor_div {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    varianceInverseCost G = (∑ i, G i i * G.adjugate i i) / G.det := by
  simp only [varianceInverseCost, Matrix.inv_def, Ring.inverse_eq_inv,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_div]
  apply sum_congr rfl
  intro i _
  ring

#print axioms posSemidef_entry_abs_le_sqrt
#print axioms relative_error_le_varianceInverseCost
#print axioms relative_entry_error_le_varianceInverseCost
#print axioms dimension_le_varianceInverseCost
#print axioms varianceInverseCost_eq_cofactor_div

end GaloisForLFunctions.CompletedArithmeticForms
