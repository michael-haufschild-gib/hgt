import GaloisForLFunctions.HTGeometry.QuenchedCentralizerDecomposition

/-!
# A positive operator has an eigenvalue at its trace density

Some member of a finite family is at least its average, so a Hermitian matrix has an eigenvalue at
least its trace divided by the dimension.  For a positive operator that eigenvalue is the operator
norm, so a projection of known rank inside a known dimension has a norm floor.

The reverse triangle inequality then converts two convergence statements and one norm floor into a
positive separation: if one family converges to a limit of norm at least `c` and another converges
to zero, the two families stay at distance at least `c` in the limit.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

section Floor

variable {n : Type*} [Fintype n] [Nonempty n]

/-- **Some member of a finite family is at least its average.** -/
theorem exists_le_of_sum_le_card_mul (f : n → ℝ) :
    ∃ j, (∑ i, f i) ≤ (Fintype.card n : ℝ) * f j := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image (Finset.univ : Finset n) f Finset.univ_nonempty
  refine ⟨j, ?_⟩
  calc (∑ i, f i) ≤ ∑ _i : n, f j := Finset.sum_le_sum fun i _ => hj i (Finset.mem_univ i)
    _ = (Fintype.card n : ℝ) * f j := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

variable [DecidableEq n]

/-- **A Hermitian matrix has an eigenvalue at least its trace density.** -/
theorem exists_eigenvalue_trace_floor {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ j, (A.trace).re ≤ (Fintype.card n : ℝ) * hA.eigenvalues j := by
  obtain ⟨j, hj⟩ := exists_le_of_sum_le_card_mul hA.eigenvalues
  refine ⟨j, ?_⟩
  have htr : A.trace = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) :=
    Matrix.IsHermitian.trace_eq_sum_eigenvalues hA
  rw [htr, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact hj

end Floor

/-! ## The quotient dimension of a nested centralizer -/

section Quotient

open Module Submodule

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **`(13)`: the quotient dimension.**  When the global commutant sits inside the centralizer, the
part of the centralizer orthogonal to it has dimension the difference. -/
theorem finrank_inf_orthogonal_eq_sub {N C : Submodule ℝ V} [FiniteDimensional ℝ ↥C]
    (h : N ≤ C) :
    finrank ℝ ↥(Nᗮ ⊓ C) = finrank ℝ ↥C - finrank ℝ ↥N := by
  have hsum := finrank_add_inf_finrank_orthogonal (𝕜 := ℝ) (K₁ := N) (K₂ := C) h
  omega

end Quotient


/-! ## Separation from a norm floor -/

section Separation

variable {E : Type*} [NormedAddCommGroup E]

/-- **The reverse triangle bound.**  If a reference vector has norm at least `c`, then anything
within `a` of it and anything of norm at most `b` are at distance at least `c - a - b`. -/
theorem norm_sub_ge_of_floor {x y z : E} {a b c : ℝ} (hc : c ≤ ‖y‖) (ha : ‖x - y‖ ≤ a)
    (hb : ‖z‖ ≤ b) : c - a - b ≤ ‖x - z‖ := by
  have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x - z‖ + ‖z‖ := by
    calc ‖y‖ = ‖(y - x) + (x - z) + z‖ := by congr 1; abel
      _ ≤ ‖(y - x) + (x - z)‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖y - x‖ + ‖x - z‖ + ‖z‖ := by
          have := norm_add_le (y - x) (x - z)
          linarith
  have h2 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
  rw [h2] at h1
  linarith

end Separation

end GaloisForLFunctions.HTGeometry
