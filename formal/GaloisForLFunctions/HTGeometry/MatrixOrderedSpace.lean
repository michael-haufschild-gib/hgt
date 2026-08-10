import GaloisForLFunctions.HTGeometry.MatrixModuleMultiplication
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Matrix-ordered vector spaces

A matrix ordering on a complex `*`-vector space `V` is a family of cones `C n ⊆ Mₙ(V)`, one for
every finite index type, consisting of self-adjoint elements and stable under the compression
`x ↦ α* x α` by arbitrary rectangular scalar matrices.  Together with an Archimedean matrix order
unit this is the abstract definition of an operator system.

The compression axiom is far stronger than it looks, and this module extracts what it gives for
free.  Only self-adjointness, `0`, addition and compression are assumed; everything else is proved:

* `IsMatrixOrdering.smul_mem` — closure under nonnegative real scaling is *not* an extra axiom, it
  is compression by a scalar multiple of the identity;
* `IsMatrixOrdering.blockDiagonal_mem` — the cones are closed under direct sums, so the family is
  automatically compatible across levels;
* `IsMatrixOrdering.vecCompress_mem` — every numerical sandwich `∑ᵢⱼ vⱼ conj(vᵢ) • xᵢⱼ` of a
  positive matrix is positive at level one, the workhorse for descending from a matrix level to the
  scalar level;
* `IsMatrixOrdering.diag_mem` and `IsMatrixOrdering.twoByTwo_mem` — diagonal entries of a positive
  matrix are positive, and the `2 × 2` off-diagonal sandwich is positive for every scalar `λ`;
* `compress_amplify` — a compression acts on the amplified order unit `1ₙ ⊗ e` through the scalar
  matrix `α* α`, so isometric compressions fix the matrix order unit exactly.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MatrixModule

universe u v

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-! ## The amplified order unit -/

/-- The `n`-th amplification `1ₙ ⊗ e` of a vector `e`, i.e. the diagonal matrix with `e` on the
diagonal.  For an order unit `e` this is the candidate order unit of the `n`-th matrix level. -/
def amplifyUnit (n : Type u) [DecidableEq n] (e : V) : Matrix n n V :=
  Matrix.diagonal fun _ => e

omit [Module ℂ V] in
theorem amplifyUnit_apply {n : Type u} [DecidableEq n] (e : V) (i j : n) :
    amplifyUnit n e i j = if i = j then e else 0 := by
  simp [amplifyUnit, Matrix.diagonal_apply]

/-- A compression acts on an amplified vector through the scalar matrix `α* α`. -/
theorem compress_amplify {m n : Type u} [Fintype m] [DecidableEq m] (α : Matrix m n ℂ) (e : V) :
    compress α (amplifyUnit m e) = Matrix.of fun i j => (αᴴ * α) i j • e := by
  ext i j
  rw [compress_apply]
  have h : ∀ b : m, (∑ a, star (α a i) • amplifyUnit m e a b) = star (α b i) • e := by
    intro b
    rw [Finset.sum_eq_single b]
    · simp [amplifyUnit_apply]
    · intro a _ hab
      simp [amplifyUnit_apply, hab]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  simp only [h, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_smul,
    smul_smul]
  exact Finset.sum_congr rfl fun b _ => by rw [mul_comm]

/-- An isometric compression fixes the amplified vector. -/
theorem compress_amplify_of_isometry {m n : Type u} [Fintype m] [DecidableEq m] [DecidableEq n]
    (α : Matrix m n ℂ) (hα : αᴴ * α = 1) (e : V) :
    compress α (amplifyUnit m e) = amplifyUnit n e := by
  rw [compress_amplify, hα]
  ext i j
  by_cases h : i = j <;> simp [amplifyUnit_apply, Matrix.one_apply, h]

/-- Compression by a scalar multiple of the identity is multiplication by `c * conj c`. -/
theorem compress_smul_one {n : Type u} [Fintype n] [DecidableEq n] (c : ℂ) (x : Matrix n n V) :
    compress (c • (1 : Matrix n n ℂ)) x = (c * star c) • x := by
  ext i j
  rw [compress_apply]
  have h : ∀ b : n, (∑ a, star ((c • (1 : Matrix n n ℂ)) a i) • x a b) = star c • x i b := by
    intro b
    rw [Finset.sum_eq_single i]
    · simp
    · intro a _ hai
      simp [hai]
    · intro hb
      exact absurd (Finset.mem_univ i) hb
  simp only [h]
  rw [Finset.sum_eq_single j]
  · rw [smul_smul]
    simp
  · intro b _ hbj
    simp [hbj]
  · intro hb
    exact absurd (Finset.mem_univ j) hb

/-! ## Numerical sandwiches -/

/-- The scalar sandwich `∑ᵢⱼ vⱼ conj(vᵢ) • xᵢⱼ`, i.e. the single entry of the compression of `x` by
the column vector `v`. -/
def vecCompress {n : Type u} [Fintype n] (v : n → ℂ) (x : Matrix n n V) : V :=
  ∑ b, ∑ a, (v b * star (v a)) • x a b

/-- The sandwich is the unique entry of a genuine compression, by the column matrix of `v`. -/
theorem compress_col_eq {n : Type u} [Fintype n] (v : n → ℂ) (x : Matrix n n V) :
    compress (Matrix.of fun (a : n) (_ : PUnit.{u + 1}) => v a) x
      = Matrix.of fun _ _ => vecCompress v x := by
  ext i j
  rw [compress_apply]
  simp only [Matrix.of_apply, vecCompress, Finset.smul_sum, smul_smul]

/-! ## Matrix orderings -/

variable [StarAddMonoid V] [StarModule ℂ V]

/-- A matrix ordering on a complex `*`-vector space: a set of self-adjoint elements in every matrix
level, containing `0`, closed under addition, and stable under compression by rectangular scalar
matrices.  Closure under nonnegative scaling is deliberately *not* assumed — it follows. -/
structure IsMatrixOrdering (C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)) : Prop where
  /-- Positive elements are self-adjoint. -/
  isSelfAdjoint : ∀ (n : Type u) [Fintype n], ∀ x ∈ C n, xᴴ = x
  /-- Every level contains `0`. -/
  zero_mem : ∀ (n : Type u) [Fintype n], (0 : Matrix n n V) ∈ C n
  /-- Every level is closed under addition. -/
  add_mem : ∀ (n : Type u) [Fintype n], ∀ x ∈ C n, ∀ y ∈ C n, x + y ∈ C n
  /-- The compression axiom. -/
  compress_mem : ∀ (m n : Type u) [Fintype m] [Fintype n], ∀ α : Matrix m n ℂ, ∀ x ∈ C m,
    compress α x ∈ C n

namespace IsMatrixOrdering

variable {C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)} (hC : IsMatrixOrdering C)

include hC

omit [StarModule ℂ V] in
/-- **Positive scaling is not an axiom.**  Closure of each level under multiplication by a
nonnegative real is compression by `√c · 1`. -/
theorem smul_mem (n : Type u) [Fintype n] [DecidableEq n] (c : ℝ) (hc : 0 ≤ c)
    {x : Matrix n n V} (hx : x ∈ C n) : (c : ℂ) • x ∈ C n := by
  have h := hC.compress_mem n n ((Real.sqrt c : ℂ) • (1 : Matrix n n ℂ)) x hx
  rw [compress_smul_one] at h
  have hstar : ((Real.sqrt c : ℂ) * star (Real.sqrt c : ℂ)) = (c : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  rwa [hstar] at h

omit [StarModule ℂ V] in
/-- Embedding a level into a larger direct sum keeps positivity: `x ↦ x ⊕ 0`. -/
theorem fromBlocks_zero_mem {m p : Type u} [Fintype m] [Fintype p] [DecidableEq m]
    {x : Matrix m m V} (hx : x ∈ C m) :
    Matrix.fromBlocks x 0 0 (0 : Matrix p p V) ∈ C (m ⊕ p) := by
  have h := hC.compress_mem m (m ⊕ p)
    (Matrix.fromCols (1 : Matrix m m ℂ) (0 : Matrix m p ℂ)) x hx
  rwa [compress_fromCols, compress_one, mulRight_zero, Matrix.conjTranspose_zero, zero_mulLeft,
    zero_mulRight, zero_compress] at h

omit [StarModule ℂ V] in
/-- Embedding a level into a larger direct sum keeps positivity: `y ↦ 0 ⊕ y`. -/
theorem zero_fromBlocks_mem {m p : Type u} [Fintype m] [Fintype p] [DecidableEq p]
    {y : Matrix p p V} (hy : y ∈ C p) :
    Matrix.fromBlocks (0 : Matrix m m V) 0 0 y ∈ C (m ⊕ p) := by
  have h := hC.compress_mem p (m ⊕ p)
    (Matrix.fromCols (0 : Matrix p m ℂ) (1 : Matrix p p ℂ)) y hy
  rwa [compress_fromCols, compress_one, mulRight_zero, Matrix.conjTranspose_zero, zero_mulLeft,
    zero_mulRight, zero_compress] at h

omit [StarModule ℂ V] in
/-- **The cones are closed under direct sums.** -/
theorem blockDiagonal_mem {m p : Type u} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]
    {x : Matrix m m V} {y : Matrix p p V} (hx : x ∈ C m) (hy : y ∈ C p) :
    Matrix.fromBlocks x 0 0 y ∈ C (m ⊕ p) := by
  have h := hC.add_mem (m ⊕ p) _ (hC.fromBlocks_zero_mem (p := p) hx) _
    (hC.zero_fromBlocks_mem (m := m) hy)
  rwa [Matrix.fromBlocks_add, add_zero, add_zero, add_zero, zero_add] at h

omit [StarModule ℂ V] in
/-- **Numerical sandwiches of a positive matrix are positive.** -/
theorem vecCompress_mem {n : Type u} [Fintype n] (v : n → ℂ) {x : Matrix n n V} (hx : x ∈ C n) :
    (Matrix.of fun (_ _ : PUnit.{u + 1}) => vecCompress v x) ∈ C PUnit.{u + 1} := by
  have h := hC.compress_mem n PUnit.{u + 1} (Matrix.of fun (a : n) (_ : PUnit.{u + 1}) => v a) x hx
  rwa [compress_col_eq] at h

end IsMatrixOrdering

/-! ## Evaluating sandwiches on sparse vectors -/

variable {n : Type u} [Fintype n] [DecidableEq n]

omit [StarAddMonoid V] [StarModule ℂ V] in
/-- A sandwich by a vector supported at a single index picks out a diagonal entry. -/
theorem vecCompress_single (i : n) (x : Matrix n n V) :
    vecCompress (fun a => if a = i then (1 : ℂ) else 0) x = x i i := by
  have key : ∀ (g : n → V), (∀ a, a ≠ i → g a = 0) → ∑ a, g a = g i := by
    intro g hg
    exact Finset.sum_eq_single i (fun a _ ha => hg a ha) fun hb =>
      absurd (Finset.mem_univ i) hb
  rw [vecCompress]
  rw [key _ ?_]
  · rw [key _ ?_]
    · simp
    · intro a ha
      simp [ha]
  · intro b hb
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [hb]

omit [StarAddMonoid V] [StarModule ℂ V] in
/-- The `2 × 2` sandwich: for a positive matrix, `xᵢᵢ + λ • xᵢⱼ + conj λ • xⱼᵢ + |λ|² • xⱼⱼ` is
positive at level one. -/
theorem vecCompress_pair (i j : n) (hij : i ≠ j) (lam : ℂ) (x : Matrix n n V) :
    vecCompress (fun a => if a = i then (1 : ℂ) else if a = j then lam else 0) x
      = x i i + lam • x i j + star lam • x j i + (lam * star lam) • x j j := by
  set v : n → ℂ := fun a => if a = i then (1 : ℂ) else if a = j then lam else 0 with hv
  have hvi : v i = 1 := by simp [hv]
  have hvj : v j = lam := by simp [hv, Ne.symm hij]
  have hv0 : ∀ a, a ≠ i → a ≠ j → v a = 0 := by
    intro a hai haj; simp [hv, hai, haj]
  have key : ∀ (g : n → V), (∀ a, a ≠ i → a ≠ j → g a = 0) → ∑ a, g a = g i + g j := by
    intro g hg
    rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset n)) ?_, Finset.sum_pair hij]
    intro a _ ha
    refine hg a ?_ ?_
    · rintro rfl; exact ha (Finset.mem_insert_self _ _)
    · rintro rfl; exact ha (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [vecCompress, key _ ?_]
  · rw [key _ ?_, key _ ?_]
    · rw [hvi, hvj]
      simp only [star_one, mul_one, one_mul, one_smul]
      abel
    · intro a hai haj; simp [hv0 a hai haj]
    · intro a hai haj; simp [hv0 a hai haj]
  · intro b hbi hbj
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [hv0 b hbi hbj]

end GaloisForLFunctions.HTGeometry
