import GaloisForLFunctions.HTGeometry.SiegelWeightedGram

/-!
# Hermitian weighted Gram determinants

Complex Cauchy--Binet expands a Hermitian weighted Gram determinant into nonnegative squared
moduli of its ordered maximal minors.  The selected-minor inequality retains one prescribed term;
this is needed to use one global algebraic-integer minor simultaneously at every complex embedding.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- Complex Cauchy--Binet for a Hermitian weighted Gram matrix, indexed by ordered row selections. -/
theorem factorial_mul_det_complexWeightedGram {k N : ℕ}
    (d : Fin N → ℝ) (C : Matrix (Fin N) (Fin k) ℂ) :
    (Nat.factorial k : ℂ) *
        (Matrix.conjTranspose C * Matrix.diagonal (fun i => (d i : ℂ)) * C).det =
      ∑ f : Fin k → Fin N,
        ((∏ b, d (f b) : ℝ) : ℂ) *
          (star ((C.submatrix f id).det) * (C.submatrix f id).det) := by
  classical
  rw [GaloisForLFunctions.factorial_mul_det_mul
    (Matrix.conjTranspose C * Matrix.diagonal (fun i => (d i : ℂ))) C]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hsub : ((Matrix.conjTranspose C *
      Matrix.diagonal (fun i => (d i : ℂ))).submatrix id f) =
      Matrix.conjTranspose (C.submatrix f id) *
        Matrix.diagonal (fun b : Fin k => (d (f b) : ℂ)) := by
    ext a b
    have hL : (Matrix.conjTranspose C *
        Matrix.diagonal (fun i => (d i : ℂ))) a (f b) =
        star (C (f b) a) * (d (f b) : ℂ) := by
      rw [Matrix.mul_apply,
        Finset.sum_eq_single (f b)
          (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
          (fun hcon => absurd (Finset.mem_univ (f b)) hcon),
        Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
    have hR : (Matrix.conjTranspose (C.submatrix f id) *
        Matrix.diagonal (fun b : Fin k => (d (f b) : ℂ))) a b =
        star (C (f b) a) * (d (f b) : ℂ) := by
      rw [Matrix.mul_apply,
        Finset.sum_eq_single b
          (fun q _ hq => by rw [Matrix.diagonal_apply_ne _ hq, mul_zero])
          (fun hcon => absurd (Finset.mem_univ b) hcon),
        Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
      rfl
    exact hL.trans hR.symm
  rw [hsub, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal]
  push_cast
  ring

/-- One prescribed minor term is bounded by the full Hermitian weighted Gram determinant. -/
theorem complexWeightedMinor_le_factorial_mul_det_re {k N : ℕ}
    (d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i)
    (C : Matrix (Fin N) (Fin k) ℂ) (f : Fin k → Fin N) :
    (∏ b, d (f b)) * ‖(C.submatrix f id).det‖ ^ (2 : ℕ) ≤
      (Nat.factorial k : ℝ) *
        (Matrix.conjTranspose C * Matrix.diagonal (fun i => (d i : ℂ)) * C).det.re := by
  classical
  have hnorm (z : ℂ) : star z * z = (‖z‖ : ℂ) ^ (2 : ℕ) := by
    change (starRingEnd ℂ) z * z = _
    rw [mul_comm]
    exact Complex.mul_conj' z
  have hCBre :
      (Nat.factorial k : ℝ) *
          (Matrix.conjTranspose C * Matrix.diagonal (fun i => (d i : ℂ)) * C).det.re =
        ∑ g : Fin k → Fin N,
          (∏ b, d (g b)) * ‖(C.submatrix g id).det‖ ^ (2 : ℕ) := by
    have hcomplex :
        (Nat.factorial k : ℂ) *
            (Matrix.conjTranspose C * Matrix.diagonal (fun i => (d i : ℂ)) * C).det =
          ∑ g : Fin k → Fin N,
            (((∏ b, d (g b)) * ‖(C.submatrix g id).det‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [factorial_mul_det_complexWeightedGram d C]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hnorm]
      push_cast
      rfl
    calc
      (Nat.factorial k : ℝ) *
          (Matrix.conjTranspose C * Matrix.diagonal (fun i => (d i : ℂ)) * C).det.re =
          ((Nat.factorial k : ℂ) *
            (Matrix.conjTranspose C * Matrix.diagonal (fun i => (d i : ℂ)) * C).det).re := by
              simp
      _ = (∑ g : Fin k → Fin N,
            (((∏ b, d (g b)) * ‖(C.submatrix g id).det‖ ^ (2 : ℕ) : ℝ) : ℂ)).re :=
          congrArg Complex.re hcomplex
      _ = ∑ g : Fin k → Fin N,
            (∏ b, d (g b)) * ‖(C.submatrix g id).det‖ ^ (2 : ℕ) := by
          let T : (Fin k → Fin N) → ℝ := fun g =>
            (∏ b, d (g b)) * ‖(C.submatrix g id).det‖ ^ (2 : ℕ)
          have hfinset : ∀ s : Finset (Fin k → Fin N),
              (∑ g ∈ s, ((T g : ℝ) : ℂ)).re = ∑ g ∈ s, T g := by
            intro s
            induction s using Finset.induction_on with
            | empty => simp
            | @insert a s ha ih =>
                rw [Finset.sum_insert ha, Finset.sum_insert ha]
                simp only [Complex.add_re, Complex.ofReal_re, ih]
          simpa [T] using hfinset (Finset.univ : Finset (Fin k → Fin N))
  have hnonneg : ∀ g : Fin k → Fin N,
      0 ≤ (∏ b, d (g b)) * ‖(C.submatrix g id).det‖ ^ (2 : ℕ) := by
    intro g
    exact mul_nonneg (Finset.prod_nonneg fun b _ => hd _) (sq_nonneg _)
  rw [hCBre]
  exact Finset.single_le_sum (fun g _ => hnonneg g) (Finset.mem_univ f)

end GaloisForLFunctions.HTGeometry
