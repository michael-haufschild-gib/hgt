import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.PosIndex
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith

/-!
# The trace-free spectral aperture

For a trace-free Hermitian matrix of size `n`, every squared eigenvalue is at
most `(n-1)/n` times the Frobenius energy. Equivalently,
`(n-1) ‖A‖_F² I - n AᴴA` is positive semidefinite. The scalar proof applies
Cauchy–Schwarz to all eigenvalues except the chosen one, whose negative is their
sum. This is the algebraic aperture mechanism in Luchese's trace-free Hessian
stress construction (https://arxiv.org/abs/2611.17317).
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace RiemannGaussian.HermitianRankTrace

/-- A zero-sum real family has a stronger coordinate bound than an arbitrary family. -/
theorem zero_sum_sq_gap {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (hx : ∑ j, x j = 0) (i : ι) :
    (Fintype.card ι : ℝ) * (x i)^2 ≤
      ((Fintype.card ι : ℝ) - 1) * ∑ j, (x j)^2 := by
  let t := (Finset.univ : Finset ι).erase i
  have hs : (∑ j ∈ t, x j) + x i = 0 := by
    simpa only [t, Finset.sum_erase_add _ _ (Finset.mem_univ i)] using hx
  have he : (∑ j ∈ t, (x j)^2) + (x i)^2 = ∑ j, (x j)^2 :=
    Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have hc : (t.card : ℝ) + 1 = (Fintype.card ι : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one (Finset.mem_univ i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) x
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hs' : (∑ j ∈ t, x j) = -x i := by linarith only [hs]
  rw [hs', neg_sq] at hcs
  rw [← hc, ← he]
  nlinarith only [hcs]

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- Trace zero improves the spectral energy bound by the factor `(n-1)/n`. -/
theorem tracefree_eigenvalue_sq_bound {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (ht : A.trace = 0) (i : ι) :
    (Fintype.card ι : ℝ) * (hA.eigenvalues i)^2 ≤
      ((Fintype.card ι : ℝ) - 1) * frobSq A := by
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues hA]
  apply zero_sum_sq_gap _ _ i
  rw [← rtrace_eq_sum_eigenvalues hA, rtrace, ht, map_zero]

/-- A pointwise spectral-square bound becomes a positive semidefinite matrix difference. -/
private theorem square_bound_posSemidef {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (q N : ℝ) (hb : ∀ i, N * (hA.eigenvalues i)^2 ≤ q) :
    ((q : 𝕜) • (1 : Matrix ι ι 𝕜) - (N : 𝕜) • (Aᴴ * A)).PosSemidef := by
  let D : Matrix ι ι 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  let F := Unitary.conjStarAlgAut 𝕜 (Matrix ι ι 𝕜) hA.eigenvectorUnitary
  have hF : F D = A := hA.spectral_theorem.symm
  have he : (q : 𝕜) • (1 : Matrix ι ι 𝕜) - (N : 𝕜) • (Aᴴ * A) =
      F (diagonal (fun i => ((q - N * (hA.eigenvalues i)^2 : ℝ) : 𝕜))) := by
    have hd : diagonal (fun i => ((q - N * (hA.eigenvalues i)^2 : ℝ) : 𝕜)) =
        (q : 𝕜) • (1 : Matrix ι ι 𝕜) - (N : 𝕜) • (D * D) := by
      rw [diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.diagonal_apply, Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, Function.comp_apply, smul_eq_mul]
        simp only [if_true, mul_one, map_sub, map_mul, pow_two]
      · simp [hij]
    rw [hd, map_sub, map_smul, map_smul, map_one, map_mul, hF, hA.eq]
  rw [he]
  have hd : (diagonal (fun i => ((q - N * (hA.eigenvalues i)^2 : ℝ) : 𝕜))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast sub_nonneg.mpr (hb i)
  exact hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix ι ι 𝕜)

/-- The complete positive semidefinite aperture inequality for a trace-free Hermitian matrix. -/
theorem tracefree_aperture {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (ht : A.trace = 0) :
    (((((Fintype.card ι : ℝ) - 1) * frobSq A : ℝ) : 𝕜) • (1 : Matrix ι ι 𝕜) -
      ((Fintype.card ι : ℝ) : 𝕜) • (Aᴴ * A)).PosSemidef :=
  square_bound_posSemidef hA _ _ (tracefree_eigenvalue_sq_bound hA ht)

#print axioms tracefree_eigenvalue_sq_bound
#print axioms tracefree_aperture

end RiemannGaussian.HermitianRankTrace
