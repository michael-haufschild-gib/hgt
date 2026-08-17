import GaloisForLFunctions.HTGeometry.HermitianObserverMetric

/-!
# One-sided quadratic spectral classification

For a finite-dimensional Hermitian operator, the flag member `eigenSum T c` is exactly the
one-sided sector on which the quadratic form of `T - c I` is positive.  Its orthogonal complement
has the opposite weak sign.  Thus a global upper quadratic bound is equivalent to checking only
the above-threshold spectral sector, and also equivalent to that sector vanishing.

Unlike an operator-norm cutoff, this classification discards arbitrarily large negative
eigenvalues: they are harmless for upper quadratic bounds.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E}

/-- Exact eigencoordinate formula for a Hermitian quadratic form. -/
theorem inner_apply_eq_sum_eigenvalues (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (v : E) :
    inner ℂ v (T v) =
      ((∑ i, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr v i‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_eq_sum_repr hT hn v (T v), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_of_diagonal (hT.eigenvectorBasis hn) (hT.apply_eigenvectorBasis hn) v i]
  exact conj_mul_ofReal_mul _ _

/-- Orthogonally to the above-threshold spectral sector, the quadratic form is at most the
threshold times the norm square. -/
theorem re_inner_apply_le_of_mem_eigenSum_orthogonal
    (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ} {v : E}
    (hv : v ∈ (eigenSum T c)ᗮ) :
    (inner ℂ v (T v)).re ≤ c * ‖v‖ ^ 2 := by
  rw [inner_apply_eq_sum_eigenvalues hT hn v]
  simp only [Complex.ofReal_re]
  rw [norm_sq_eq_sum_repr hT hn v, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : c < hT.eigenvalues hn i
  · rw [repr_eq_zero_of_mem_orthogonal hT hn hv hi]
    simp
  · exact mul_le_mul_of_nonneg_right (not_lt.1 hi) (sq_nonneg _)

/-- Every nonzero vector in the above-threshold spectral sector has Rayleigh quotient strictly
above the threshold. -/
theorem re_inner_apply_gt_of_mem_eigenSum
    (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c : ℝ} {v : E}
    (hv : v ∈ eigenSum T c) (hv0 : v ≠ 0) :
    c * ‖v‖ ^ 2 < (inner ℂ v (T v)).re := by
  rw [inner_apply_eq_sum_eigenvalues hT hn v]
  simp only [Complex.ofReal_re]
  rw [norm_sq_eq_sum_repr hT hn v, Finset.mul_sum]
  obtain ⟨i, hi⟩ : ∃ i : Fin n, (hT.eigenvectorBasis hn).repr v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hnorm : ‖v‖ ^ 2 = 0 := by
      rw [norm_sq_eq_sum_repr hT hn v]
      exact Finset.sum_eq_zero fun i _ => by rw [hcon i]; simp
    exact hv0 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hnorm))
  refine Finset.sum_lt_sum
    (fun j _ => ?_)
    ?_
  · by_cases hj : hT.eigenvalues hn j ≤ c
    · rw [repr_eq_zero_of_mem_eigenSum hT hn hv hj]
      simp
    · exact mul_le_mul_of_nonneg_right (le_of_lt (not_le.1 hj)) (sq_nonneg _)
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    have hci : c < hT.eigenvalues hn i := by
      by_contra hnot
      have hz := repr_eq_zero_of_mem_eigenSum hT hn hv (not_lt.1 hnot)
      exact hi hz
    exact mul_lt_mul_of_pos_right hci (pow_pos (norm_pos_iff.mpr hi) 2)

/-- The above-threshold sector vanishes exactly when the Hermitian quadratic form has the global
upper bound `c`. -/
theorem eigenSum_eq_bot_iff_global_quadratic_upper
    (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (c : ℝ) :
    eigenSum T c = ⊥ ↔ ∀ v : E, (inner ℂ v (T v)).re ≤ c * ‖v‖ ^ 2 := by
  constructor
  · intro hbot v
    have hv : v ∈ (eigenSum T c)ᗮ := by rw [hbot]; simp
    exact re_inner_apply_le_of_mem_eigenSum_orthogonal hT hn hv
  · intro hupper
    apply (eigenSum_eq_bot_iff hT hn c).2
    intro i
    let v := hT.eigenvectorBasis hn i
    have hvnorm : ‖v‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.1 i
    have hvinner : inner ℂ v v = 1 := by
      change inner ℂ ((hT.eigenvectorBasis hn) i) ((hT.eigenvectorBasis hn) i) = 1
      rw [orthonormal_iff_ite.1 (hT.eigenvectorBasis hn).orthonormal, if_pos rfl]
    have happly := hT.apply_eigenvectorBasis hn i
    have h := hupper v
    rw [happly, inner_smul_right, hvinner, mul_one, hvnorm, one_pow, mul_one] at h
    exact_mod_cast h

/-- A global Hermitian upper bound needs to be tested only on the one-sided above-threshold sector.
Large negative eigenspaces play no role. -/
theorem global_quadratic_upper_iff_on_eigenSum
    (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (c : ℝ) :
    (∀ v : E, (inner ℂ v (T v)).re ≤ c * ‖v‖ ^ 2) ↔
      ∀ v : eigenSum T c,
        (inner ℂ (v : E) (T (v : E))).re ≤ c * ‖(v : E)‖ ^ 2 := by
  constructor
  · exact fun h v => h v
  · intro h
    have hbot : eigenSum T c = ⊥ := by
      by_contra hne
      obtain ⟨v, hv0⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hne)
      have hlt := re_inner_apply_gt_of_mem_eigenSum hT hn v.property
        (fun hz => hv0 (Subtype.ext hz))
      exact (not_lt_of_ge (h v)) hlt
    exact (eigenSum_eq_bot_iff_global_quadratic_upper hT hn c).1 hbot

end GaloisForLFunctions.HTGeometry
