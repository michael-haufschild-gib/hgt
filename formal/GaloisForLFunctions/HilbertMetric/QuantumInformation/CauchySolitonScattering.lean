import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDephasing

/-!
# Cubic-graph scattering factors in the Cauchy coherence matrix

For positive momenta, the common two-soliton phase of family (a) in
Shi, arXiv:2611.22194, Theorem 6.2, is the squared signed contrast below.
Eliminating one rate from the normalized Cauchy kernel multiplies each
remaining row and column by its signed contrast with that rate. Hence
every principal determinant equals the corresponding Hirota pair product,
including at collisions.
-/

noncomputable section
open Matrix Finset
namespace GaloisForLFunctions.HilbertMetric.CauchyDephasing

/-- Signed square root of the KdV scattering factor, in logarithmic momenta. -/
def contrast (s t : ℝ) : ℝ := (Real.exp s - Real.exp t) / (Real.exp s + Real.exp t)

private theorem half_square (u : ℝ) : Real.exp (u / 2) ^ 2 = Real.exp u := by
  rw [pow_two, ← Real.exp_add, add_halves]

/-- Exact Schur complement after conditioning on a single rate. -/
theorem coherence_schur_contrast (s t u : ℝ) :
    coherence s t - coherence s u * coherence u t =
      contrast s u * contrast t u * coherence s t := by
  unfold coherence contrast
  have h (x y : ℝ) : Real.exp x + Real.exp y ≠ 0 := (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  field_simp [h]
  rw [← half_square u]
  ring

/-- The two-soliton phase is exactly the squared coherence lost in a pair. -/
theorem contrast_sq_eq_coherence_loss (s t : ℝ) :
    contrast s t ^ 2 = 1 - coherence s t ^ 2 := by
  simpa only [coherence_self, coherence_symm t s, mul_one, pow_two] using
    (coherence_schur_contrast s s t).symm

theorem contrast_eq_zero_iff (s t : ℝ) : contrast s t = 0 ↔ s = t := by
  simp [contrast, div_eq_zero_iff, (add_pos (Real.exp_pos s) (Real.exp_pos t)).ne',
    sub_eq_zero, Real.exp_injective.eq_iff]

/-- Adjoining a rate multiplies the determinant by all its pair phases,
even when the previous determinant vanishes. -/
theorem coherence_det_cons {n : ℕ} (r : Fin (n + 1) → ℝ) :
    (Matrix.of fun i j => coherence (r i) (r j)).det =
      (∏ i : Fin n, contrast (r i.succ) (r 0) ^ 2) *
        (Matrix.of fun i j : Fin n => coherence (r i.succ) (r j.succ)).det := by
  let A := Matrix.of fun i j => coherence (r i) (r j)
  let c := fun i => if i = 0 then 0 else -coherence (r i) (r 0)
  let B := Matrix.of fun i j => A i j + c i * A 0 j
  have hdet : B.det = A.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c]) (fun _ _ => rfl)
  have hsub : B.submatrix Fin.succ Fin.succ = Matrix.of fun i j =>
      contrast (r i.succ) (r 0) * (Matrix.of fun i j : Fin n =>
        contrast (r j.succ) (r 0) * coherence (r i.succ) (r j.succ)) i j := by
    ext i j
    simpa only [B, A, c, Matrix.of_apply, Matrix.submatrix_apply, Fin.succ_ne_zero,
      if_false, neg_mul, ← sub_eq_add_neg, mul_assoc] using
      coherence_schur_contrast (r i.succ) (r j.succ) (r 0)
  change A.det = _
  rw [← hdet, Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    rw [show B 0 0 = 1 by simp [B, A, c, coherence_self], one_mul, hsub,
      Matrix.det_mul_column, Matrix.det_mul_row, ← mul_assoc, ← Finset.prod_mul_distrib]
    simp only [pow_two]
    rfl
  · intro i _ hi
    simp [B, A, c, hi, coherence_self]
  · simp

/-- In every dimension the volume determinant is the product of the phases
among unordered pairs. The empty determinant has the empty product as value. -/
theorem coherence_det_eq_scattering {n : ℕ} (r : Fin n → ℝ) :
    (Matrix.of fun i j => coherence (r i) (r j)).det =
      ∏ i, ∏ j ∈ Ioi i, contrast (r j) (r i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [coherence_det_cons, ih, Fin.prod_univ_succ, Fin.prod_Ioi_zero]
    congr 1
    exact Finset.prod_congr rfl fun i _ => (Fin.prod_Ioi_succ (fun j => contrast (r j) (r i.succ) ^ 2) i).symm

/-- Colliding momenta are exactly the singular configurations. -/
theorem coherence_det_ne_zero_iff {n : ℕ} (r : Fin n → ℝ) :
    (Matrix.of fun i j => coherence (r i) (r j)).det ≠ 0 ↔ Function.Injective r := by
  constructor
  · intro hd i j hij
    by_contra h
    apply hd
    apply Matrix.det_zero_of_row_eq h
    exact congrArg (fun t => fun k => coherence t (r k)) hij
  · intro hr
    rw [coherence_det_eq_scattering]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj =>
      pow_ne_zero _ fun h => (Finset.mem_Ioi.mp hj).ne' (hr ((contrast_eq_zero_iff _ _).mp h))

#print axioms coherence_schur_contrast
#print axioms contrast_sq_eq_coherence_loss
#print axioms contrast_eq_zero_iff
#print axioms coherence_det_cons
#print axioms coherence_det_eq_scattering
#print axioms coherence_det_ne_zero_iff

end GaloisForLFunctions.HilbertMetric.CauchyDephasing
