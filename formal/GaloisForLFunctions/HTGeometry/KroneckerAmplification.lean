import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Ancilla amplification of matrix maps

A map of `d × d` matrices acts on matrices with an ancilla index blockwise; this is the
amplification which defines completely bounded norms.  The amplification of a conjugation by a
matrix is conjugation by its Kronecker product with the identity, and that Kronecker product has
the same operator norm bound as the original matrix, because it acts blockwise on the coordinate
decomposition of the amplified space.
-/

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d n : Type*} [Fintype d] [DecidableEq d] [Fintype n] [DecidableEq n]

/-- The ancilla amplification of a map on square matrices: it acts on each block. -/
def amplify (Φ : Matrix d d ℂ → Matrix d d ℂ) (n : Type*) [Fintype n]
    (X : Matrix (d × n) (d × n) ℂ) : Matrix (d × n) (d × n) ℂ :=
  fun p q => Φ (fun i j => X (i, p.2) (j, q.2)) p.1 q.1

omit [Fintype d] [DecidableEq d] [DecidableEq n] in
@[simp] theorem amplify_apply (Φ : Matrix d d ℂ → Matrix d d ℂ)
    (X : Matrix (d × n) (d × n) ℂ) (p q : d × n) :
    amplify Φ n X p q = Φ (fun i j => X (i, p.2) (j, q.2)) p.1 q.1 := rfl

omit [DecidableEq d] in
/-- Conjugation, written out entrywise. -/
theorem conj_entry (U M : Matrix d d ℂ) (i j : d) :
    (U * M * star U) i j = ∑ l, ∑ k, U i k * M k l * (starRingEnd ℂ) (U j l) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Complex.star_def]

omit [DecidableEq d] in
/-- The Kronecker conjugation, written out entrywise on blocks. -/
theorem kronecker_conj_entry (U : Matrix d d ℂ) (X : Matrix (d × n) (d × n) ℂ)
    (i j : d) (a b : n) :
    ((U ⊗ₖ (1 : Matrix n n ℂ)) * X * star (U ⊗ₖ (1 : Matrix n n ℂ))) (i, a) (j, b)
      = ∑ l, ∑ k, U i k * X (k, a) (l, b) * (starRingEnd ℂ) (U j l) := by
  classical
  rw [Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  have hstep : ∀ (l : d) (e : n),
      ((U ⊗ₖ (1 : Matrix n n ℂ)) * X) (i, a) (l, e)
          * (star (U ⊗ₖ (1 : Matrix n n ℂ))) (l, e) (j, b)
        = (if b = e then (∑ k, U i k * X (k, a) (l, e)) * (starRingEnd ℂ) (U j l) else 0) := by
    intro l e
    have hleft : ((U ⊗ₖ (1 : Matrix n n ℂ)) * X) (i, a) (l, e)
        = ∑ k, U i k * X (k, a) (l, e) := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      show (∑ c, (U ⊗ₖ (1 : Matrix n n ℂ)) (i, a) (k, c) * X (k, c) (l, e))
        = U i k * X (k, a) (l, e)
      rw [Finset.sum_eq_single a]
      · show U i k * (1 : Matrix n n ℂ) a a * X (k, a) (l, e) = _
        rw [Matrix.one_apply_eq, mul_one]
      · intro c _ hc
        show U i k * (1 : Matrix n n ℂ) a c * X (k, c) (l, e) = 0
        rw [Matrix.one_apply_ne (Ne.symm hc), mul_zero, zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ a) hcon
    have hright : (star (U ⊗ₖ (1 : Matrix n n ℂ))) (l, e) (j, b)
        = (if b = e then (1 : ℂ) else 0) * (starRingEnd ℂ) (U j l) := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
      show (starRingEnd ℂ) (U j l * (1 : Matrix n n ℂ) b e) = _
      by_cases hbe : b = e
      · subst hbe
        rw [Matrix.one_apply_eq, mul_one, if_pos rfl, one_mul]
      · rw [Matrix.one_apply_ne hbe, mul_zero, if_neg hbe, zero_mul, map_zero]
    rw [hleft, hright]
    by_cases hbe : b = e
    · rw [if_pos hbe, if_pos hbe, one_mul]
    · rw [if_neg hbe, if_neg hbe, zero_mul, mul_zero]
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
    Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hstep l e]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_univ b), Finset.sum_mul]

omit [DecidableEq d] in
/-- **Amplified conjugation.**  The ancilla amplification of a conjugation is conjugation by the
Kronecker product with the identity. -/
theorem amplify_conj (U : Matrix d d ℂ) (X : Matrix (d × n) (d × n) ℂ) :
    amplify (fun O => U * O * star U) n X
      = (U ⊗ₖ (1 : Matrix n n ℂ)) * X * star (U ⊗ₖ (1 : Matrix n n ℂ)) := by
  ext p q
  rw [amplify_apply, kronecker_conj_entry, conj_entry]

/-- The Kronecker product of a unitary with the identity is unitary. -/
theorem kronecker_one_mem_unitary {U : Matrix d d ℂ} (hU : U ∈ unitary (Matrix d d ℂ)) :
    (U ⊗ₖ (1 : Matrix n n ℂ)) ∈ unitary (Matrix (d × n) (d × n) ℂ) := by
  obtain ⟨h1, h2⟩ := hU
  constructor
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mul,
      Matrix.one_kronecker_one]
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, ← Matrix.star_eq_conjTranspose, h2, Matrix.one_mul,
      Matrix.one_kronecker_one]

theorem norm_sq_euclideanOfFun {m : Type*} [Fintype m] (f : m → ℂ) :
    ‖(EuclideanSpace.equiv m ℂ).symm f‖ ^ (2 : ℕ) = ∑ i, ‖f i‖ ^ (2 : ℕ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rfl

omit [DecidableEq d] in
/-- The Kronecker product with the identity acts blockwise on coordinates. -/
theorem kronecker_one_mulVec (A : Matrix d d ℂ) (v : d × n → ℂ) (k : d) (a : n) :
    ((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ v) (k, a) = (A *ᵥ fun l => v (l, a)) k := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single a]
  · show A k l * (1 : Matrix n n ℂ) a a * v (l, a) = _
    rw [Matrix.one_apply_eq, mul_one]
  · intro c _ hc
    show A k l * (1 : Matrix n n ℂ) a c * v (l, c) = 0
    rw [Matrix.one_apply_ne (Ne.symm hc), mul_zero, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ a) hcon

/-- **Amplification does not increase the operator norm.** -/
theorem l2_opNorm_kronecker_one_le (A : Matrix d d ℂ) :
    ‖A ⊗ₖ (1 : Matrix n n ℂ)‖ ≤ ‖A‖ := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => ?_
  set y : n → d → ℂ := fun a l => x.ofLp (l, a) with hy
  have hval : ∀ p : d × n,
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix n n ℂ)) x).ofLp p
        = (A *ᵥ y p.2) p.1 := by
    rintro ⟨k, a⟩
    rw [Matrix.ofLp_toEuclideanCLM]
    exact kronecker_one_mulVec A x.ofLp k a
  have hlhs : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix n n ℂ)) x‖ ^ (2 : ℕ)
      = ∑ a, ‖(EuclideanSpace.equiv d ℂ).symm (A *ᵥ y a)‖ ^ (2 : ℕ) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_sq_euclideanOfFun]
    exact Finset.sum_congr rfl fun k _ => by rw [hval (k, a)]
  have hrhs : ‖x‖ ^ (2 : ℕ) = ∑ a, ‖(EuclideanSpace.equiv d ℂ).symm (y a)‖ ^ (2 : ℕ) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fintype.sum_prod_type,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => (norm_sq_euclideanOfFun (y a)).symm
  have hbound : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix n n ℂ)) x‖ ^ (2 : ℕ)
      ≤ (‖A‖ * ‖x‖) ^ (2 : ℕ) := by
    rw [hlhs, mul_pow, hrhs, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have hstep := Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv d ℂ).symm (y a))
    have hstep' : ‖(EuclideanSpace.equiv d ℂ).symm (A *ᵥ y a)‖
        ≤ ‖A‖ * ‖(EuclideanSpace.equiv d ℂ).symm (y a)‖ := hstep
    calc ‖(EuclideanSpace.equiv d ℂ).symm (A *ᵥ y a)‖ ^ (2 : ℕ)
        ≤ (‖A‖ * ‖(EuclideanSpace.equiv d ℂ).symm (y a)‖) ^ (2 : ℕ) := by
          exact pow_le_pow_left₀ (norm_nonneg _) hstep' 2
      _ = ‖A‖ ^ (2 : ℕ) * ‖(EuclideanSpace.equiv d ℂ).symm (y a)‖ ^ (2 : ℕ) := by ring
  have hsqrt := Real.sqrt_le_sqrt hbound
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hsqrt

end

end GaloisForLFunctions.HTGeometry
