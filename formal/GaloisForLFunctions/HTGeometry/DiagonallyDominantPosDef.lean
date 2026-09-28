import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Diagonally dominant Hermitian matrices are positive definite

For a complex Hermitian `n × n` matrix `M` with `Re M_ii ≥ δ > 0` and `|M_ij| ≤ δ/(2n)` off the
diagonal, the Hermitian form `x* M x` is real, and
`Re x* M x ≥ δ ‖x‖² - (δ/(2n)) (∑|x_i|)² ≥ (δ/2) ‖x‖²` by Cauchy–Schwarz.
-/

open Matrix Finset
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

/-- **Diagonal dominance.** A complex Hermitian `n × n` matrix whose diagonal real parts are at
least `δ > 0` and whose off-diagonal entries have norm at most `δ/(2n)` is positive definite. -/
theorem posDef_of_diag_ge_of_offDiag_le {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) {δ : ℝ} (hδ : 0 < δ) (hdiag : ∀ i, δ ≤ (M i i).re)
    (hoff : ∀ i j, i ≠ j → ‖M i j‖ ≤ δ / (2 * n)) : M.PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨hM, fun x hx => ?_⟩
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (funext fun i => i.elim0) hx
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set q := star x ⬝ᵥ M *ᵥ x
  have hq : q = ∑ i, ∑ j, star (x i) * M i j * x j := by
    simp only [q, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hHerm : ∀ i j, star (M i j) = M j i := fun i j => by
    have := congrFun (congrFun hM j) i
    simpa [conjTranspose_apply] using this
  have him : q.im = 0 := by
    have hconj : star q = q := by
      rw [hq, star_sum]
      simp_rw [star_sum, star_mul', star_star, hHerm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have := congrArg Complex.im hconj
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  set T : ℝ := ∑ i, ‖x i‖ ^ 2 with hTdef
  set A : ℝ := ∑ i, ‖x i‖ with hAdef
  have hT : 0 < T := by
    obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      exact hx (funext fun i => by by_contra hi; exact h ⟨i, hi⟩)
    exact Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, Finset.mem_univ _, by
      have := norm_pos_iff.mpr hi₀; positivity⟩
  have hA2 : A ^ 2 ≤ n * T := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => ‖x i‖)
    simpa [A, T, Finset.card_univ] using h
  have hsplit : q = ∑ i, star (x i) * M i i * x i +
      ∑ i, ∑ j ∈ Finset.univ.erase i, star (x i) * M i j * x j := by
    rw [hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hdiagre : δ * T ≤ (∑ i, star (x i) * M i i * x i).re := by
    rw [Complex.re_sum, hTdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have : star (x i) * M i i * x i = (M i i) * ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, ← Complex.mul_conj', Complex.star_def]; ring
    rw [this, Complex.re_mul_ofReal]
    exact mul_le_mul_of_nonneg_right (hdiag i) (by positivity)
  have hoffre : ‖∑ i, ∑ j ∈ Finset.univ.erase i, star (x i) * M i j * x j‖ ≤
      δ / (2 * n) * A ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    have hA : A ^ 2 = ∑ i, ∑ j, ‖x i‖ * ‖x j‖ := by
      rw [sq, hAdef, Finset.sum_mul_sum]
    rw [hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    calc ∑ j ∈ Finset.univ.erase i, ‖star (x i) * M i j * x j‖
        ≤ ∑ j ∈ Finset.univ.erase i, δ / (2 * n) * (‖x i‖ * ‖x j‖) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [norm_mul, norm_mul, norm_star]
          have := hoff i j (Finset.ne_of_mem_erase hj).symm
          nlinarith [norm_nonneg (x i), norm_nonneg (x j), norm_nonneg (M i j),
            mul_nonneg (norm_nonneg (x i)) (norm_nonneg (x j))]
      _ ≤ ∑ j, δ / (2 * n) * (‖x i‖ * ‖x j‖) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun j _ _ => by positivity
  have hre : 0 < q.re := by
    rw [hsplit, Complex.add_re]
    have h1 := Complex.re_le_norm (∑ i, ∑ j ∈ Finset.univ.erase i, star (x i) * M i j * x j)
    have h2 : -(δ / (2 * n) * A ^ 2) ≤
        (∑ i, ∑ j ∈ Finset.univ.erase i, star (x i) * M i j * x j).re := by
      have := Complex.abs_re_le_norm
        (∑ i, ∑ j ∈ Finset.univ.erase i, star (x i) * M i j * x j)
      rw [abs_le] at this; linarith
    have h3 : δ / (2 * n) * A ^ 2 ≤ δ / 2 * T := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  rw [Complex.lt_def]
  exact ⟨by simpa using hre, by simpa using him.symm⟩

end GaloisForLFunctions.HTGeometry
