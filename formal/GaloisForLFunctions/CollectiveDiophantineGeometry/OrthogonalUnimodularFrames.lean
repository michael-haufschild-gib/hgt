import GaloisForLFunctions.HTGeometry.SiegelOrbit
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Orthogonal unimodular frames over the integers

The proof after Remark 22 in Streck (arXiv:2610.23797) calls for a dense
choice of normalized orthogonal columns in integral determinant-one
matrices. In every rank these matrices are signed permutations. This
also describes the orthogonal part of the integral Siegel action.
-/

open Matrix Finset
namespace GaloisForLFunctions.CollectiveDiophantineGeometry.IntegralFrames
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pairwise orthogonality imposes no length normalization. -/
def OrthogonalColumns (A : Matrix ι ι ℤ) : Prop :=
  ∀ i j, i ≠ j → (∑ k, A k i * A k j) = 0

/-- The product of the squared column lengths is the determinant squared. -/
theorem determinant_square (A : Matrix ι ι ℤ) (h : OrthogonalColumns A) :
    A.det^2=∏ j, ∑ k, (A k j)^2 := by
  have he : A.transpose*A = diagonal (fun j => ∑ k, (A k j)^2) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.mul_apply,sq]
    · simpa [Matrix.mul_apply,diagonal_apply,hij] using h i j hij
  have hh := congrArg Matrix.det he
  simpa only [det_mul,det_transpose,det_diagonal,sq] using hh

/-- In a unimodular matrix every orthogonal column has squared length one. -/
theorem column_norm (A : Matrix ι ι ℤ) (hA : IsUnit A) (h : OrthogonalColumns A) (j : ι) :
    (∑ k, (A k j)^2)=1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have hsq : A.det^2=1 := by
    rcases Int.isUnit_iff.mp hd with hp | hp <;> rw [hp] <;> norm_num
  have hprod := (determinant_square A h).symm.trans hsq
  have hdvd := dvd_prod_of_mem (fun j => ∑ k, (A k j)^2) (mem_univ j)
  rw [hprod] at hdvd
  have hne : (∑ k, (A k j)^2) ≠ 0 := fun he => by simp [he] at hdvd
  exact le_antisymm (Int.le_of_dvd zero_lt_one hdvd)
    (by have := sum_nonneg fun (k : ι) (_ : k ∈ univ) => sq_nonneg (A k j); omega)

private theorem unit_vector (v : ι → ℤ) (h : (∑ i, (v i)^2)=1) :
    ∃ i, (v i=1 ∨ v i= -1) ∧ ∀ j, j ≠ i → v j=0 := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! H
    simp [H] at h
  obtain ⟨i,hi⟩ := hex
  have hs := single_le_sum (fun (j : ι) (_ : j ∈ univ) => sq_nonneg (v j)) (mem_univ i)
  rw [h] at hs
  have hp := sq_pos_of_ne_zero hi
  have hone : (v i)^2=1 := by omega
  refine ⟨i,sq_eq_one_iff.mp hone,?_⟩
  have hz := sum_erase_add (s := univ) (fun j => (v j)^2) (mem_univ i)
  rw [h,hone] at hz
  intro j hj
  have hh := single_le_sum (fun (a : ι) (_ : a ∈ univ.erase i) => sq_nonneg (v a))
    (mem_erase.mpr ⟨hj,mem_univ j⟩)
  by_contra hne
  have := sq_pos_of_ne_zero hne
  omega

/-- The support of the matrix is the graph of a permutation, with one sign
on each occupied entry. This holds for determinant minus one as well. -/
theorem signed_permutation (A : Matrix ι ι ℤ) (hA : IsUnit A) (h : OrthogonalColumns A) :
    ∃ σ : Equiv.Perm ι, (∀ j, A (σ j) j=1 ∨ A (σ j) j= -1) ∧
      ∀ i j, i ≠ σ j → A i j=0 := by
  choose f hsign hoff using fun j => unit_vector (fun k => A k j) (column_norm A hA h j)
  have hne (j : ι) : A (f j) j ≠ 0 := by rcases hsign j with he | he <;> simp [he]
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hij
    have hzero := h i j hij
    rw [sum_eq_single_of_mem (f i) (mem_univ _)
      (fun k _ hk => by rw [hoff i k hk,zero_mul])] at hzero
    exact mul_ne_zero (hne i) (by simpa only [he] using hne j) hzero
  exact ⟨Equiv.ofBijective f ⟨hinj,Finite.surjective_of_injective hinj⟩,
    hsign,fun i j hij => hoff j i hij⟩

/-- In the Siegel integral action, every orthogonal frame has a zero in each
row of every pair of distinct columns. -/
theorem siegel_row_obstruction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : HTGeometry.IsIntUnimodular A)
    (h : ∀ i j, i ≠ j → (∑ k, A k i*A k j)=0) (i j k : Fin n) (hjk : j ≠ k) :
    A i j=0 ∨ A i k=0 := by
  obtain ⟨B,hB,he⟩ := hA
  have ho : OrthogonalColumns B := by
    intro j k hne
    have hh := h j k hne
    simp only [he] at hh
    exact_mod_cast hh
  obtain ⟨σ,_,off⟩ := signed_permutation B hB ho
  by_cases hj : i=σ j
  · right
    rw [he,off i k (fun hk => hjk (σ.injective (hj.symm.trans hk))),Int.cast_zero]
  · left
    rw [he,off i j hj,Int.cast_zero]

end GaloisForLFunctions.CollectiveDiophantineGeometry.IntegralFrames

#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.IntegralFrames.determinant_square
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.IntegralFrames.column_norm
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.IntegralFrames.signed_permutation
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.IntegralFrames.siegel_row_obstruction
