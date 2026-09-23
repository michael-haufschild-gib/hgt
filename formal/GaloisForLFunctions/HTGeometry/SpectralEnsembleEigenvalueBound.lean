/-
# A uniform bound on the spectrum of a Hermitian ensemble

Eigenvalues of a Hermitian matrix are not continuous in its entries, but they are uniformly
bounded: their squares sum to the real trace of the square, which for the ensemble matrix is a
quadratic form in the coefficients.  On the shell that form is bounded by the total absolute
trace mass of the family, so every polynomial in the spectrum and the coefficients is bounded on
the shell -- a substitute for continuity in the domination step.

Main results:
* `sum_sq_eigenvalues_eq_trace_sq_re` — the eigenvalue energy is the real trace of the square.
* `abs_eigenvalues_le_sqrt_trace_sq_re` — each eigenvalue is bounded by its square root.
* `ensembleTraceBound`, `abs_eigenvalues_spectralEnsembleMatrix_le` — **the uniform spectral
  bound on the shell**.
* `exists_bound_eval_of_abs_le` — a polynomial is bounded on a box.
* `exists_bound_eval_joint` — **a joint polynomial is bounded on the shell**.
-/
import GaloisForLFunctions.HTGeometry.RankEnergyPowerSum
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Eigenvalues

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The eigenvalue energy of a Hermitian matrix is the real trace of its square. -/
theorem sum_sq_eigenvalues_eq_trace_sq_re {H : Matrix d d ℂ} (hH : H.IsHermitian) :
    ∑ i, (hH.eigenvalues i) ^ (2 : ℕ) = ((H ^ (2 : ℕ)).trace).re := by
  rw [trace_pow_eq_sum_eigenvalues_pow hH 2, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Each eigenvalue of a Hermitian matrix is bounded by the square root of the eigenvalue
energy. -/
theorem abs_eigenvalues_le_sqrt_trace_sq_re {H : Matrix d d ℂ} (hH : H.IsHermitian) (j : d) :
    |hH.eigenvalues j| ≤ Real.sqrt (((H ^ (2 : ℕ)).trace).re) := by
  have hle : (hH.eigenvalues j) ^ (2 : ℕ) ≤ ∑ i, (hH.eigenvalues i) ^ (2 : ℕ) :=
    Finset.single_le_sum (f := fun i => (hH.eigenvalues i) ^ (2 : ℕ))
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  rw [sum_sq_eigenvalues_eq_trace_sq_re hH] at hle
  calc |hH.eigenvalues j| = Real.sqrt ((hH.eigenvalues j) ^ (2 : ℕ)) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (((H ^ (2 : ℕ)).trace).re) := Real.sqrt_le_sqrt hle

end Eigenvalues

section Ensemble

variable {N D : ℕ}

/-- The total absolute trace mass of a Hermitian family. -/
def ensembleTraceBound (P : Fin N → Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  ∑ a, ∑ b, ‖(P a * P b).trace‖

theorem trace_sq_spectralEnsembleMatrix (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    (θ : Fin N → ℝ) :
    ((spectralEnsembleMatrix P θ) ^ (2 : ℕ)).trace
      = ∑ a, ∑ b, ((θ a : ℂ) * (θ b : ℂ)) * (P a * P b).trace := by
  rw [sq, spectralEnsembleMatrix, Finset.sum_mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc]

theorem trace_sq_spectralEnsembleMatrix_re_le (P : Fin N → Matrix (Fin D) (Fin D) ℂ)
    {θ : Fin N → ℝ} (hθ : ∀ a, |θ a| ≤ 1) :
    (((spectralEnsembleMatrix P θ) ^ (2 : ℕ)).trace).re ≤ ensembleTraceBound P := by
  have h1 : (((spectralEnsembleMatrix P θ) ^ (2 : ℕ)).trace).re
      ≤ ‖((spectralEnsembleMatrix P θ) ^ (2 : ℕ)).trace‖ := Complex.re_le_norm _
  refine le_trans h1 ?_
  rw [trace_sq_spectralEnsembleMatrix]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun a _ => ?_
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun b _ => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have hab : |θ a| * |θ b| ≤ 1 :=
    mul_le_one₀ (hθ a) (abs_nonneg _) (hθ b)
  calc |θ a| * |θ b| * ‖(P a * P b).trace‖
      ≤ 1 * ‖(P a * P b).trace‖ :=
        mul_le_mul_of_nonneg_right hab (norm_nonneg _)
    _ = ‖(P a * P b).trace‖ := one_mul _

/-- **The uniform spectral bound on the shell.** -/
theorem abs_eigenvalues_spectralEnsembleMatrix_le {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) {θ : Fin N → ℝ} (hθ : ∀ a, |θ a| ≤ 1) (i : Fin D) :
    |(isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i|
      ≤ Real.sqrt (ensembleTraceBound P) :=
  le_trans (abs_eigenvalues_le_sqrt_trace_sq_re (isHermitian_spectralEnsembleMatrix hP θ) i)
    (Real.sqrt_le_sqrt (trace_sq_spectralEnsembleMatrix_re_le P hθ))

end Ensemble

section Boxes

/-- A polynomial is bounded on a box. -/
theorem exists_bound_eval_of_abs_le {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ι → ℝ, (∀ i, |x i| ≤ B) → |MvPolynomial.eval x p| ≤ C := by
  classical
  set K : Set (ι → ℝ) := Set.univ.pi (fun _ : ι => Set.Icc (-B) B) with hK
  have hKcomp : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hbdd : BddAbove ((fun x => |MvPolynomial.eval x p|) '' K) :=
    hKcomp.bddAbove_image (MvPolynomial.continuous_eval p).abs.continuousOn
  obtain ⟨C₀, hC₀⟩ := hbdd
  refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => ?_⟩
  have hmem : x ∈ K := by
    intro i _
    exact abs_le.mp (hx i)
  exact le_trans (hC₀ ⟨x, hmem, rfl⟩) (le_max_left _ _)

variable {N D : ℕ}

/-- **A joint polynomial is bounded on the shell.** -/
theorem exists_bound_eval_joint {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (p : MvPolynomial (Fin D ⊕ Fin N) ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : Fin N → ℝ, (∀ a, |θ a| ≤ 1) →
      |MvPolynomial.eval
          (Sum.elim (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) θ) p|
        ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_bound_eval_of_abs_le p (max 1 (Real.sqrt (ensembleTraceBound P)))
  refine ⟨C, hC, fun θ hθ => ?_⟩
  refine hbound _ fun x => ?_
  rcases x with i | a
  · exact le_trans (abs_eigenvalues_spectralEnsembleMatrix_le hP hθ i) (le_max_right _ _)
  · exact le_trans (hθ a) (le_max_left _ _)

end Boxes

end

end GaloisForLFunctions.HTGeometry
