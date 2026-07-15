import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Full-row-rank linear forms preserve algebraic independence

If a coefficient matrix has a right inverse, substitution by its row linear forms has a left
inverse on multivariate polynomial rings.  Hence those linear forms in an algebraically independent
family remain algebraically independent.  This is the nonlinear-rank core used to pass from
polynomial differential-operator row rank to differential transcendence rank.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MvPolynomial

noncomputable section

/-- Row linear forms of a matrix, evaluated in an algebra over the coefficient ring. -/
def matrixLinearForms
    {R A m n : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype n] (M : Matrix m n R) (x : n → A) (i : m) : A :=
  ∑ j, algebraMap R A (M i j) * x j

theorem aeval_toMvPolynomial_eq_matrixLinearForms
    {R A m n : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype n] (M : Matrix m n R) (x : n → A) (i : m) :
    MvPolynomial.aeval x (M.toMvPolynomial i) = matrixLinearForms M x i := by
  simp [Matrix.toMvPolynomial, matrixLinearForms, MvPolynomial.aeval_def]

/-- A right-invertible row transformation preserves algebraic independence. -/
theorem algebraicIndependent_matrixLinearForms_of_mul_eq_one
    {R A m n : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (N : Matrix n m R) (hMN : M * N = 1)
    (x : n → A) (hx : AlgebraicIndependent R x) :
    AlgebraicIndependent R (matrixLinearForms M x) := by
  rw [algebraicIndependent_iff]
  intro p hp
  let q : MvPolynomial n R := MvPolynomial.bind₁ M.toMvPolynomial p
  have hqeval : MvPolynomial.aeval x q = 0 := by
    dsimp [q]
    rw [MvPolynomial.aeval_bind₁]
    simpa only [aeval_toMvPolynomial_eq_matrixLinearForms] using hp
  have hq : q = 0 := hx.eq_zero_of_aeval_eq_zero q hqeval
  have hundone : MvPolynomial.bind₁ N.toMvPolynomial q = p := by
    dsimp [q]
    rw [MvPolynomial.bind₁_bind₁]
    have hvar : (fun i => MvPolynomial.bind₁ N.toMvPolynomial (M.toMvPolynomial i)) =
        (MvPolynomial.X : m → MvPolynomial m R) := by
      funext i
      rw [← Matrix.toMvPolynomial_mul, hMN, Matrix.toMvPolynomial_one]
    rw [hvar]
    exact AlgHom.congr_fun MvPolynomial.bind₁_X_left p
  rw [hq, map_zero] at hundone
  exact hundone.symm

/-- A matrix over a field with linearly independent rows has a right inverse. -/
theorem exists_matrix_rightInverse_of_linearIndependent_rows
    {R m n : Type*} [Field R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (hM : LinearIndependent R M.row) :
    ∃ N : Matrix n m R, M * N = 1 := by
  have hrank : M.rank = Fintype.card m := hM.rank_matrix
  have hrange : Module.finrank R (LinearMap.range M.mulVecLin) =
      Module.finrank R (m → R) := by
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card]
  have htop : LinearMap.range M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq hrange
  have hsurj : Function.Surjective M.mulVec := by
    exact LinearMap.range_eq_top.mp htop
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.mp hsurj

/-- **Affine splitting law.**  Once a matrix right inverse exists, every other right inverse is
uniquely obtained by adding a matrix killed by left multiplication.  Thus the finite-dimensional
splitting space is a nonempty affine torsor over the kernel of `H ↦ M * H`; any obstruction to a
compatible family of splittings must be global rather than pointwise linear algebra. -/
theorem matrix_rightInverse_iff_kernelPerturbation
    {R m n : Type*} [CommRing R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (N N' : Matrix n m R) (hMN : M * N = 1) :
    M * N' = 1 ↔ ∃ H : Matrix n m R, M * H = 0 ∧ N' = N + H := by
  constructor
  · intro hMN'
    refine ⟨N' - N, ?_, ?_⟩
    · rw [Matrix.mul_sub, hMN', hMN, sub_self]
    · abel
  · rintro ⟨H, hMH, rfl⟩
    rw [Matrix.mul_add, hMN, hMH, add_zero]

/-- **Surjective splitting-tower law.**  A tower of nonempty finite-stage splitting spaces with
surjective restriction maps has a compatible global splitting.  Hence any genuine completion
obstruction must fail the Mittag--Leffler lifting property at some scale. -/
theorem exists_compatible_of_surjective_tower
    {S : ℕ → Type*} [Nonempty (S 0)]
    (restrict : ∀ n, S (n + 1) → S n)
    (hsurj : ∀ n, Function.Surjective (restrict n)) :
    ∃ q : ∀ n, S n, ∀ n, restrict n (q (n + 1)) = q n := by
  classical
  let lift : ∀ n, S n → S (n + 1) := fun n s ↦ Classical.choose (hsurj n s)
  have hlift : ∀ n s, restrict n (lift n s) = s :=
    fun n s ↦ Classical.choose_spec (hsurj n s)
  let q : ∀ n, S n := fun n ↦
    @Nat.rec (fun n ↦ S n) (Classical.choice inferInstance)
      (fun n s ↦ lift n s) n
  refine ⟨q, ?_⟩
  intro n
  change restrict n (lift n (q n)) = q n
  exact hlift n (q n)

/-!
## A genuine completion-boundary model

Finite-dimensional affine splitting towers are Mittag--Leffler, so a completion obstruction needs
an infinite-dimensional or topological boundary.  The algebraic direct sum gives the sharp model.
At scale `n`, require the first `n` coordinates of a finitely supported reconstruction to be one.
Every finite stage is nonempty, but compatibility would force one finitely supported function to be
one at every coordinate.  The product completion contains exactly that missing boundary point.
-/

/-- Finitely supported reconstructions satisfying the first `n` unit clock constraints. -/
def finitePrefixOneSplitting (R : Type*) [Semiring R] (n : ℕ) :=
  {v : ℕ →₀ R // ∀ i, i < n → v i = 1}

/-- Every finite packet of unit clock constraints has an algebraic finite-support solution. -/
instance finitePrefixOneSplitting_nonempty
    (R : Type*) [Semiring R] (n : ℕ) :
    Nonempty (finitePrefixOneSplitting R n) := by
  let v : ℕ →₀ R := Finsupp.onFinset (Finset.range n)
    (fun i ↦ if i < n then 1 else 0) (by
      intro i hi
      simp only [Finset.mem_range]
      by_contra hnot
      simp [hnot] at hi)
  refine ⟨⟨v, ?_⟩⟩
  intro i hi
  simp [v, hi, Finsupp.onFinset_apply]

/-- Forgetting the last unit constraint preserves the underlying finite-support reconstruction. -/
def finitePrefixOneSplitting_restrict
    (R : Type*) [Semiring R] (n : ℕ) :
    finitePrefixOneSplitting R (n + 1) → finitePrefixOneSplitting R n :=
  fun v ↦ ⟨v.1, fun i hi ↦ v.2 i (lt_trans hi (Nat.lt_succ_self n))⟩

/-- **Algebraic completion obstruction.**  Every finite splitting space is nonempty, but the tower
has no compatible point in the algebraic direct sum: compatibility would produce a finitely
supported function equal to one at every natural-number coordinate. -/
theorem finitePrefixOneSplitting_no_compatible
    (R : Type*) [Semiring R] [Nontrivial R] :
    ¬ ∃ q : ∀ n, finitePrefixOneSplitting R n,
      ∀ n, finitePrefixOneSplitting_restrict R n (q (n + 1)) = q n := by
  rintro ⟨q, hq⟩
  have hval : ∀ n, (q n).1 = (q 0).1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hstep := congrArg Subtype.val (hq n)
        exact hstep.trans ih
  have hall : ∀ i, (q 0).1 i = 1 := by
    intro i
    have hi := (q (i + 1)).2 i (Nat.lt_succ_self i)
    rw [hval (i + 1)] at hi
    exact hi
  by_cases hs : (q 0).1.support.Nonempty
  · let i := (q 0).1.support.max' hs + 1
    have hi : i ∉ (q 0).1.support := by
      intro himem
      have hle := (q 0).1.support.le_max' i himem
      omega
    have hzero : (q 0).1 i = 0 := by
      by_contra hne
      exact hi ((Finsupp.mem_support_iff).2 hne)
    exact one_ne_zero ((hall i).symm.trans hzero)
  · have hempty : (q 0).1.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hzero : (q 0).1 0 = 0 := by
      by_contra hne
      have hmem := (Finsupp.mem_support_iff).2 hne
      rw [hempty] at hmem
      simp at hmem
    exact one_ne_zero ((hall 0).symm.trans hzero)

/-- **Positive thin-boundary statement.**  The product completion contains exactly one
reconstruction satisfying every finite unit clock constraint: the constant-one boundary point. -/
theorem existsUnique_productCompletion_unitBoundary
    (R : Type*) [Semiring R] :
    ∃! v : ℕ → R, ∀ n i, i < n → v i = 1 := by
  refine ⟨fun _ ↦ 1, by simp, ?_⟩
  intro v hv
  funext i
  exact hv (i + 1) i (Nat.lt_succ_self i)

/-- Linearly independent matrix rows evaluated on an algebraically independent family remain
algebraically independent. -/
theorem algebraicIndependent_matrixLinearForms_of_linearIndependent_rows
    {R A m n : Type*} [Field R] [CommRing A] [Algebra R A]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n R) (hM : LinearIndependent R M.row)
    (x : n → A) (hx : AlgebraicIndependent R x) :
    AlgebraicIndependent R (matrixLinearForms M x) := by
  obtain ⟨N, hMN⟩ := exists_matrix_rightInverse_of_linearIndependent_rows M hM
  exact algebraicIndependent_matrixLinearForms_of_mul_eq_one M N hMN x hx

end

end GaloisForLFunctions.HTGeometry
