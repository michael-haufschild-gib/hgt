import GaloisForLFunctions.HTGeometry.BesselPSD
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.BipartiteMatrixDecomposition
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Chebyshev

/-!
# The exact `k`-positivity threshold of the reduction pencil

For finite index types `α` (the amplification/ancilla index) and `β` (the source aperture) this
file proves the sharp threshold

`id_α ⊗ (X ↦ c · Tr X · 1 − X)` is positive  ↔  `c ≥ min (card α) (card β)`.

The two halves of sufficiency are proved by the *same* elementary device — Cauchy–Schwarz for the
positive semidefinite sesquilinear form of `A`, applied to two different decompositions of the test
vector.  The aperture bound `c ≥ card β` needs no preparation; the amplification bound
`c ≥ card α` needs the partial trace to be diagonal first, which is arranged by conjugating with
`U ⊗ 1` for a unitary `U` diagonalizing the partial trace.  Necessity is witnessed by a maximally
entangled vector built from any pair of orthonormal families.

No Schmidt decomposition or singular value theory is used.
-/

open Matrix
open scoped ComplexOrder Kronecker
open HTGeometry.ConstraintRelativity

namespace GaloisForLFunctions.HTGeometry

/-! ## The sesquilinear form of a matrix -/

section Sesq

variable {I : Type*} [Fintype I]

/-- The sesquilinear form attached to a matrix: linear in the first slot, conjugate linear in the
second. -/
def matSesq (A : Matrix I I ℂ) (x y : I → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (y i) * A i j * x j

theorem matSesq_eq_dotProduct (A : Matrix I I ℂ) (x y : I → ℂ) :
    matSesq A x y = star y ⬝ᵥ (A *ᵥ x) := by
  simp only [matSesq, dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def,
    Finset.mul_sum, mul_assoc]

theorem matSesq_add_left (A : Matrix I I ℂ) (x x' y : I → ℂ) :
    matSesq A (x + x') y = matSesq A x y + matSesq A x' y := by
  simp only [matSesq, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem matSesq_smul_left (c : ℂ) (A : Matrix I I ℂ) (x y : I → ℂ) :
    matSesq A (c • x) y = c * matSesq A x y := by
  simp only [matSesq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem matSesq_add_right (A : Matrix I I ℂ) (x y y' : I → ℂ) :
    matSesq A x (y + y') = matSesq A x y + matSesq A x y' := by
  simp only [matSesq, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem matSesq_sum_left {ι : Type*} (A : Matrix I I ℂ) (s : Finset ι) (f : ι → I → ℂ)
    (y : I → ℂ) : matSesq A (∑ p ∈ s, f p) y = ∑ p ∈ s, matSesq A (f p) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [matSesq]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, matSesq_add_left, ih]

theorem matSesq_sum_right {ι : Type*} (A : Matrix I I ℂ) (x : I → ℂ) (s : Finset ι)
    (g : ι → I → ℂ) : matSesq A x (∑ q ∈ s, g q) = ∑ q ∈ s, matSesq A x (g q) := by
  classical
  induction s using Finset.induction with
  | empty => simp [matSesq]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, matSesq_add_right, ih]

theorem matSesq_sub_mat (M N : Matrix I I ℂ) (x y : I → ℂ) :
    matSesq (M - N) x y = matSesq M x y - matSesq N x y := by
  simp only [matSesq, Matrix.sub_apply, mul_sub, sub_mul, ← Finset.sum_sub_distrib]

theorem matSesq_smul_mat (r : ℝ) (M : Matrix I I ℂ) (x y : I → ℂ) :
    matSesq ((r : ℂ) • M) x y = (r : ℂ) * matSesq M x y := by
  simp only [matSesq, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem matSesq_conj {A : Matrix I I ℂ} (hA : A.IsHermitian) (x y : I → ℂ) :
    matSesq A y x = (starRingEnd ℂ) (matSesq A x y) := by
  simp only [matSesq, map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (starRingEnd ℂ) (A i j) = A j i := by
    have h2 := congrFun (congrFun hA j) i
    simpa [Matrix.conjTranspose_apply, Complex.star_def] using h2
  rw [h1]; ring

theorem matSesq_self_nonneg {A : Matrix I I ℂ} (hA : A.PosSemidef) (x : I → ℂ) :
    0 ≤ matSesq A x x := by
  rw [matSesq_eq_dotProduct]; exact hA.dotProduct_mulVec_nonneg x

theorem matSesq_self_re_nonneg {A : Matrix I I ℂ} (hA : A.PosSemidef) (x : I → ℂ) :
    0 ≤ (matSesq A x x).re :=
  (Complex.le_def.mp (matSesq_self_nonneg hA x)).1

theorem matSesq_self_im {A : Matrix I I ℂ} (hA : A.IsHermitian) (x : I → ℂ) :
    (matSesq A x x).im = 0 := by
  have h := congrArg Complex.im (matSesq_conj hA x x)
  simp only [Complex.conj_im] at h
  linarith

theorem posSemidef_of_matSesq_re_nonneg {M : Matrix I I ℂ} (hH : M.IsHermitian)
    (h : ∀ x, 0 ≤ (matSesq M x x).re) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
  rw [← matSesq_eq_dotProduct]
  exact Complex.le_def.mpr ⟨by simpa using h x, by simpa using (matSesq_self_im hH x).symm⟩

/-- **Cauchy–Schwarz for the sesquilinear form of a positive semidefinite matrix.** -/
theorem matSesq_norm_sq_le {A : Matrix I I ℂ} (hA : A.PosSemidef) (x y : I → ℂ) :
    ‖matSesq A x y‖ ^ 2 ≤ (matSesq A x x).re * (matSesq A y y).re :=
  _root_.HTGeometry.cauchy_schwarz_psd (matSesq A) (matSesq_add_left A)
    (fun c x y => matSesq_smul_left c A x y) (matSesq_conj hA.isHermitian)
    (matSesq_self_re_nonneg hA) x y

/-- **Master estimate.**  The diagonal value of a positive semidefinite form at a finite sum is at
most the square of the sum of the square roots of the diagonal values of the summands. -/
theorem matSesq_self_re_le_sq_sum_sqrt {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {ι : Type*} (s : Finset ι) (f : ι → I → ℂ) :
    (matSesq A (∑ p ∈ s, f p) (∑ p ∈ s, f p)).re
      ≤ (∑ p ∈ s, Real.sqrt ((matSesq A (f p) (f p)).re)) ^ 2 := by
  have hexp : matSesq A (∑ p ∈ s, f p) (∑ p ∈ s, f p)
      = ∑ p ∈ s, ∑ q ∈ s, matSesq A (f p) (f q) := by
    rw [matSesq_sum_left]
    exact Finset.sum_congr rfl fun p _ => matSesq_sum_right A (f p) s f
  rw [hexp]
  have hre : (∑ p ∈ s, ∑ q ∈ s, matSesq A (f p) (f q)).re
      = ∑ p ∈ s, ∑ q ∈ s, (matSesq A (f p) (f q)).re := by simp [Complex.re_sum]
  rw [hre]
  have hsq : (∑ p ∈ s, Real.sqrt ((matSesq A (f p) (f p)).re)) ^ 2
      = ∑ p ∈ s, ∑ q ∈ s, Real.sqrt ((matSesq A (f p) (f p)).re)
          * Real.sqrt ((matSesq A (f q) (f q)).re) := by
    rw [sq, Finset.sum_mul_sum]
  rw [hsq]
  refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
  refine (Complex.re_le_norm _).trans ?_
  have hcs := matSesq_norm_sq_le hA (f p) (f q)
  have hnn : 0 ≤ ‖matSesq A (f p) (f q)‖ := norm_nonneg _
  have hrp := matSesq_self_re_nonneg hA (f p)
  have hle : ‖matSesq A (f p) (f q)‖
      ≤ Real.sqrt ((matSesq A (f p) (f p)).re * (matSesq A (f q) (f q)).re) := by
    rw [show ‖matSesq A (f p) (f q)‖ = Real.sqrt (‖matSesq A (f p) (f q)‖ ^ 2) from
      (Real.sqrt_sq hnn).symm]
    exact Real.sqrt_le_sqrt hcs
  rwa [Real.sqrt_mul hrp] at hle

/-- Master estimate against explicit majorants of the square roots. -/
theorem matSesq_self_re_le_sq_sum {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {ι : Type*} (s : Finset ι) (f : ι → I → ℂ) (g : ι → ℝ)
    (hg : ∀ p ∈ s, 0 ≤ g p) (h : ∀ p ∈ s, (matSesq A (f p) (f p)).re ≤ (g p) ^ 2) :
    (matSesq A (∑ p ∈ s, f p) (∑ p ∈ s, f p)).re ≤ (∑ p ∈ s, g p) ^ 2 := by
  refine (matSesq_self_re_le_sq_sum_sqrt hA s f).trans ?_
  have hle : ∑ p ∈ s, Real.sqrt ((matSesq A (f p) (f p)).re) ≤ ∑ p ∈ s, g p := by
    refine Finset.sum_le_sum fun p hp => ?_
    have := Real.sqrt_le_sqrt (h p hp)
    rwa [Real.sqrt_sq (hg p hp)] at this
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => Real.sqrt_nonneg _) hle 2

/-- Cardinality form of the master estimate. -/
theorem matSesq_self_re_le_card_mul {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {ι : Type*} (s : Finset ι) (f : ι → I → ℂ) :
    (matSesq A (∑ p ∈ s, f p) (∑ p ∈ s, f p)).re
      ≤ (s.card : ℝ) * ∑ p ∈ s, (matSesq A (f p) (f p)).re := by
  refine (matSesq_self_re_le_sq_sum_sqrt hA s f).trans ?_
  refine (sq_sum_le_card_mul_sum_sq
    (s := s) (f := fun p => Real.sqrt ((matSesq A (f p) (f p)).re))).trans_eq ?_
  congr 1
  exact Finset.sum_congr rfl fun p _ => Real.sq_sqrt (matSesq_self_re_nonneg hA _)

/-- Conjugating the matrix is substituting in the vectors. -/
theorem matSesq_conjugate {J : Type*} [Fintype J] (M : Matrix I I ℂ) (B : Matrix I J ℂ)
    (x y : J → ℂ) : matSesq (Bᴴ * M * B) x y = matSesq M (B *ᵥ x) (B *ᵥ y) := by
  simp only [matSesq_eq_dotProduct]
  simp only [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul]

end Sesq

/-! ## Bipartite slices and the amplified reduction pencil -/

section Bipartite

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The reduction pencil `X ↦ c · Tr X · 1 − X` amplified by the ancilla index `α`. -/
def redPencil (c : ℝ) (A : Matrix (α × β) (α × β) ℂ) : Matrix (α × β) (α × β) ℂ :=
  (c : ℂ) • ((partialTraceRight A) ⊗ₖ (1 : Matrix β β ℂ)) - A

/-- Lift an `α`-vector into the `l`-th `β`-slice. -/
def liftSlice (x : α → ℂ) (l : β) : α × β → ℂ := fun z => if z.2 = l then x z.1 else 0

/-- The `β`-slice of a bipartite vector at a fixed second index. -/
def colSlice (φ : α × β → ℂ) (i : β) : α × β → ℂ := liftSlice (fun a => φ (a, i)) i

/-- The `α`-slice of a bipartite vector at a fixed first index. -/
def rowSlice (φ : α × β → ℂ) (a : α) : α × β → ℂ := fun z => if z.1 = a then φ z else 0

/-- The single-cell slice of a bipartite vector. -/
def cellSlice (φ : α × β → ℂ) (w : α × β) : α × β → ℂ := fun z => if z = w then φ z else 0

theorem sum_colSlice (φ : α × β → ℂ) : ∑ i, colSlice φ i = φ := by
  funext z
  simp only [Finset.sum_apply, colSlice, liftSlice]
  rw [Finset.sum_eq_single z.2]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem sum_rowSlice (φ : α × β → ℂ) : ∑ a, rowSlice φ a = φ := by
  funext z
  simp only [Finset.sum_apply, rowSlice]
  rw [Finset.sum_eq_single z.1]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem sum_cellSlice (φ : α × β → ℂ) (a : α) : ∑ m, cellSlice φ (a, m) = rowSlice φ a := by
  funext z
  simp only [Finset.sum_apply, cellSlice, rowSlice]
  by_cases h : z.1 = a
  · rw [Finset.sum_eq_single z.2]
    · simp [h, Prod.ext_iff]
    · intro m _ hm
      have hz : z ≠ (a, m) := fun hh => hm (congrArg Prod.snd hh).symm
      simp [hz]
    · simp
  · refine (Finset.sum_eq_zero fun m _ => ?_).trans (by simp [h])
    simp [Prod.ext_iff, h]

theorem matSesq_liftSlice (A : Matrix (α × β) (α × β) ℂ) (x : α → ℂ) (l : β) :
    matSesq A (liftSlice x l) (liftSlice x l)
      = ∑ a, ∑ b, (starRingEnd ℂ) (x a) * A (a, l) (b, l) * x b := by
  classical
  simp [matSesq, liftSlice, Fintype.sum_prod_type, apply_ite, ite_mul, Finset.sum_ite_eq']

theorem matSesq_cellSlice (A : Matrix (α × β) (α × β) ℂ) (φ : α × β → ℂ) (w : α × β) :
    matSesq A (cellSlice φ w) (cellSlice φ w) = (starRingEnd ℂ) (φ w) * A w w * φ w := by
  classical
  simp [matSesq, cellSlice, apply_ite, ite_mul, Finset.sum_ite_eq']

theorem matSesq_kron_one (ρ : Matrix α α ℂ) (φ : α × β → ℂ) :
    matSesq (ρ ⊗ₖ (1 : Matrix β β ℂ)) φ φ
      = ∑ a, ∑ i, ∑ b, (starRingEnd ℂ) (φ (a, i)) * ρ a b * φ (b, i) := by
  classical
  simp only [matSesq, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The partial trace of a positive semidefinite matrix, tested at `x`, is the sum over the
aperture of the tests of `A` at the lifted slices. -/
private theorem sum3_rot {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (F : ι₁ → ι₂ → ι₃ → ℂ) : (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := by
  rw [show (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c from
    Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem matSesq_partialTraceRight (A : Matrix (α × β) (α × β) ℂ) (x : α → ℂ) :
    matSesq (partialTraceRight A) x x
      = ∑ l, matSesq A (liftSlice x l) (liftSlice x l) := by
  classical
  rw [show (∑ l, matSesq A (liftSlice x l) (liftSlice x l))
      = ∑ l, ∑ a, ∑ b, (starRingEnd ℂ) (x a) * A (a, l) (b, l) * x b from
    Finset.sum_congr rfl fun l _ => matSesq_liftSlice A x l]
  simp only [matSesq, partialTraceRight, Finset.mul_sum, Finset.sum_mul]
  exact sum3_rot (fun a b l => (starRingEnd ℂ) (x a) * A (a, l) (b, l) * x b)

theorem posSemidef_partialTraceRight {A : Matrix (α × β) (α × β) ℂ} (hA : A.PosSemidef) :
    (partialTraceRight A).PosSemidef := by
  refine posSemidef_of_matSesq_re_nonneg ?_ fun x => ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, partialTraceRight, star_sum]
    exact Finset.sum_congr rfl fun l _ => congrFun (congrFun hA.isHermitian (a, l)) (b, l)
  · rw [matSesq_partialTraceRight, Complex.re_sum]
    exact Finset.sum_nonneg fun l _ => matSesq_self_re_nonneg hA _

/-- The amplified trace term decomposes into the aperture-shifted slices. -/
theorem matSesq_ptrace_kron (A : Matrix (α × β) (α × β) ℂ) (φ : α × β → ℂ) :
    matSesq ((partialTraceRight A) ⊗ₖ (1 : Matrix β β ℂ)) φ φ
      = ∑ i, ∑ l, matSesq A (liftSlice (fun a => φ (a, i)) l) (liftSlice (fun a => φ (a, i)) l) := by
  classical
  simp only [matSesq_kron_one]
  have h : ∀ i : β, (∑ a, ∑ b, (starRingEnd ℂ) (φ (a, i)) * (partialTraceRight A) a b * φ (b, i))
      = ∑ l, matSesq A (liftSlice (fun a => φ (a, i)) l) (liftSlice (fun a => φ (a, i)) l) := by
    intro i
    rw [← matSesq_partialTraceRight A (fun a => φ (a, i))]
    rfl
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (h i)

theorem partialTraceRight_kron_conj (V V' : Matrix α α ℂ) (A : Matrix (α × β) (α × β) ℂ) :
    partialTraceRight ((V ⊗ₖ (1 : Matrix β β ℂ)) * A * (V' ⊗ₖ (1 : Matrix β β ℂ)))
      = V * partialTraceRight A * V' := by
  classical
  ext a b
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_comm

theorem redPencil_isHermitian (c : ℝ) {A : Matrix (α × β) (α × β) ℂ} (hA : A.IsHermitian) :
    (redPencil c A).IsHermitian := by
  have hρ : (partialTraceRight A).IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, partialTraceRight, star_sum]
    exact Finset.sum_congr rfl fun l _ => congrFun (congrFun hA (a, l)) (b, l)
  unfold redPencil
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hA, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_kronecker, hρ]
  simp

theorem matSesq_redPencil (c : ℝ) (A : Matrix (α × β) (α × β) ℂ) (φ : α × β → ℂ) :
    matSesq (redPencil c A) φ φ
      = (c : ℂ) * matSesq ((partialTraceRight A) ⊗ₖ (1 : Matrix β β ℂ)) φ φ
        - matSesq A φ φ := by
  rw [redPencil, matSesq_sub_mat, matSesq_smul_mat]

theorem re_matSesq_redPencil (c : ℝ) (A : Matrix (α × β) (α × β) ℂ) (φ : α × β → ℂ) :
    (matSesq (redPencil c A) φ φ).re
      = c * (matSesq ((partialTraceRight A) ⊗ₖ (1 : Matrix β β ℂ)) φ φ).re
        - (matSesq A φ φ).re := by
  rw [matSesq_redPencil]
  simp [Complex.sub_re, Complex.mul_re]


/-! ## The aperture bound -/

theorem matSesq_single {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) (w : I) :
    matSesq M (fun z => if z = w then (1 : ℂ) else 0) (fun z => if z = w then (1 : ℂ) else 0)
      = M w w := by
  classical
  simp [matSesq, apply_ite, ite_mul, Finset.sum_ite_eq']

theorem re_diag_nonneg {I : Type*} [Fintype I] [DecidableEq I] {M : Matrix I I ℂ}
    (hM : M.PosSemidef) (w : I) : 0 ≤ (M w w).re := by
  have := matSesq_self_re_nonneg hM (fun z => if z = w then (1 : ℂ) else 0)
  rwa [matSesq_single] at this

private theorem conj_mul_self (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Aperture half of the threshold.**  Coefficient at least the aperture always works, at every
amplification depth. -/
theorem redPencil_posSemidef_of_card_right_le {c : ℝ} {A : Matrix (α × β) (α × β) ℂ}
    (hA : A.PosSemidef) (hc : (Fintype.card β : ℝ) ≤ c) : (redPencil c A).PosSemidef := by
  classical
  refine posSemidef_of_matSesq_re_nonneg (redPencil_isHermitian c hA.isHermitian) fun φ => ?_
  rw [re_matSesq_redPencil]
  set r : β → β → ℝ := fun i l =>
    (matSesq A (liftSlice (fun a => φ (a, i)) l) (liftSlice (fun a => φ (a, i)) l)).re with hrdef
  have hT : (matSesq ((partialTraceRight A) ⊗ₖ (1 : Matrix β β ℂ)) φ φ).re = ∑ i, ∑ l, r i l := by
    rw [matSesq_ptrace_kron]
    simp only [Complex.re_sum, hrdef]
  have hrnn : ∀ i l, 0 ≤ r i l := fun i l => matSesq_self_re_nonneg hA _
  have hS : ∑ i, r i i ≤ (matSesq ((partialTraceRight A) ⊗ₖ (1 : Matrix β β ℂ)) φ φ).re := by
    rw [hT]
    exact Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun l => r i l) (fun l _ => hrnn i l) (Finset.mem_univ i)
  have hSnn : 0 ≤ ∑ i, r i i := Finset.sum_nonneg fun i _ => hrnn i i
  have hmaster : (matSesq A φ φ).re ≤ (Fintype.card β : ℝ) * ∑ i, r i i := by
    have h := matSesq_self_re_le_card_mul hA (Finset.univ : Finset β) (colSlice φ)
    rw [sum_colSlice] at h
    simpa [colSlice, hrdef, Finset.card_univ] using h
  have hcnn : (0 : ℝ) ≤ c := le_trans (Nat.cast_nonneg _) hc
  nlinarith [mul_le_mul_of_nonneg_right hc hSnn, mul_le_mul_of_nonneg_left hS hcnn]

/-! ## The amplification bound -/

/-- **Amplification half of the threshold, diagonal case.** -/
theorem redPencil_posSemidef_of_card_left_le_of_diagonal {c : ℝ}
    {A : Matrix (α × β) (α × β) ℂ} (hA : A.PosSemidef)
    (hdiag : ∀ a b, a ≠ b → partialTraceRight A a b = 0)
    (hc : (Fintype.card α : ℝ) ≤ c) : (redPencil c A).PosSemidef := by
  classical
  refine posSemidef_of_matSesq_re_nonneg (redPencil_isHermitian c hA.isHermitian) fun φ => ?_
  rw [re_matSesq_redPencil]
  set N : α → ℝ := fun a => ∑ i, ‖φ (a, i)‖ ^ 2 with hNdef
  set d : α → ℝ := fun a => ((partialTraceRight A) a a).re with hddef
  have hρpsd : (partialTraceRight A).PosSemidef := posSemidef_partialTraceRight hA
  have hdnn : ∀ a, 0 ≤ d a := fun a => re_diag_nonneg hρpsd a
  have hNnn : ∀ a, 0 ≤ N a := fun a => Finset.sum_nonneg fun i _ => sq_nonneg _
  -- the trace term
  have hT : (matSesq ((partialTraceRight A) ⊗ₖ (1 : Matrix β β ℂ)) φ φ).re = ∑ a, d a * N a := by
    rw [matSesq_kron_one]
    have hstep : ∀ a : α, (∑ i, ∑ b, (starRingEnd ℂ) (φ (a, i)) * (partialTraceRight A) a b
        * φ (b, i)) = ((N a : ℝ) : ℂ) * (partialTraceRight A) a a := by
      intro a
      have hb : ∀ i : β, (∑ b, (starRingEnd ℂ) (φ (a, i)) * (partialTraceRight A) a b * φ (b, i))
          = ((‖φ (a, i)‖ ^ 2 : ℝ) : ℂ) * (partialTraceRight A) a a := by
        intro i
        rw [Finset.sum_eq_single a]
        · rw [← conj_mul_self]; ring
        · intro b _ hb'; rw [hdiag a b (Ne.symm hb')]; ring
        · intro h; exact absurd (Finset.mem_univ a) h
      rw [Finset.sum_congr rfl fun i _ => hb i, ← Finset.sum_mul, hNdef]
      congr 1
      push_cast
      rfl
    rw [Finset.sum_congr rfl fun a _ => hstep a, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_ofReal_mul, hddef]
    ring
  -- each row slice
  have hrow : ∀ a, (matSesq A (rowSlice φ a) (rowSlice φ a)).re ≤ d a * N a := by
    intro a
    set g : β → ℝ := fun m => ‖φ (a, m)‖ * Real.sqrt ((A (a, m) (a, m)).re) with hgdef
    have hddn : ∀ m : β, 0 ≤ (A (a, m) (a, m)).re := fun m => re_diag_nonneg hA (a, m)
    have hstep : (matSesq A (rowSlice φ a) (rowSlice φ a)).re ≤ (∑ m, g m) ^ 2 := by
      rw [← sum_cellSlice φ a]
      refine matSesq_self_re_le_sq_sum hA Finset.univ (fun m => cellSlice φ (a, m)) g
        (fun m _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (fun m _ => ?_)
      rw [matSesq_cellSlice]
      have : (starRingEnd ℂ) (φ (a, m)) * A (a, m) (a, m) * φ (a, m)
          = ((‖φ (a, m)‖ ^ 2 : ℝ) : ℂ) * A (a, m) (a, m) := by
        rw [← conj_mul_self]; ring
      rw [this]
      have hsq : (g m) ^ 2 = ‖φ (a, m)‖ ^ 2 * (A (a, m) (a, m)).re := by
        rw [hgdef, mul_pow, Real.sq_sqrt (hddn m)]
      rw [hsq, Complex.re_ofReal_mul]
    refine hstep.trans ?_
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset β)
      (fun m => ‖φ (a, m)‖) (fun m => Real.sqrt ((A (a, m) (a, m)).re))
    have hd' : ∑ m, (Real.sqrt ((A (a, m) (a, m)).re)) ^ 2 = d a := by
      rw [Finset.sum_congr rfl fun m _ => Real.sq_sqrt (hddn m)]
      simp only [hddef, partialTraceRight, Complex.re_sum]
    rw [hd'] at hcs
    calc (∑ m, g m) ^ 2 ≤ (∑ m, ‖φ (a, m)‖ ^ 2) * d a := hcs
      _ = d a * N a := by rw [hNdef]; ring
  have hmaster : (matSesq A φ φ).re
      ≤ (Fintype.card α : ℝ) * ∑ a, (matSesq A (rowSlice φ a) (rowSlice φ a)).re := by
    have h := matSesq_self_re_le_card_mul hA (Finset.univ : Finset α) (rowSlice φ)
    rw [sum_rowSlice] at h
    simpa [Finset.card_univ] using h
  have hsum : ∑ a, (matSesq A (rowSlice φ a) (rowSlice φ a)).re ≤ ∑ a, d a * N a :=
    Finset.sum_le_sum fun a _ => hrow a
  have hTnn : (0 : ℝ) ≤ ∑ a, d a * N a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hdnn a) (hNnn a)
  have hcnn : (0 : ℝ) ≤ c := le_trans (Nat.cast_nonneg _) hc
  have hcard_nn : (0 : ℝ) ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
  rw [hT]
  nlinarith [hmaster, hsum, mul_le_mul_of_nonneg_right hc hTnn]

/-- **Amplification half of the threshold.**  Coefficient at least the amplification depth always
works, at every aperture.  The partial trace is diagonalized first by an ancilla rotation. -/
theorem redPencil_posSemidef_of_card_left_le {c : ℝ} {A : Matrix (α × β) (α × β) ℂ}
    (hA : A.PosSemidef) (hc : (Fintype.card α : ℝ) ≤ c) : (redPencil c A).PosSemidef := by
  classical
  have hρH : (partialTraceRight A).IsHermitian := (posSemidef_partialTraceRight hA).isHermitian
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix α α ℂ, U = (hρH.eigenvectorUnitary : Matrix α α ℂ) := ⟨_, rfl⟩
  have hU1 : Uᴴ * U = 1 := by
    have h := Matrix.UnitaryGroup.star_mul_self hρH.eigenvectorUnitary
    simpa [hUdef, Matrix.star_eq_conjTranspose] using h
  have hU2 : U * Uᴴ = 1 := mul_eq_one_comm.mp hU1
  obtain ⟨W, hWdef⟩ : ∃ W : Matrix (α × β) (α × β) ℂ, W = U ⊗ₖ (1 : Matrix β β ℂ) := ⟨_, rfl⟩
  have hWH : Wᴴ = Uᴴ ⊗ₖ (1 : Matrix β β ℂ) := by
    rw [hWdef, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  have hW2 : W * Wᴴ = 1 := by
    rw [hWH, hWdef, ← Matrix.mul_kronecker_mul, hU2, Matrix.one_mul, Matrix.one_kronecker_one]
  have hA' : (Wᴴ * A * W).PosSemidef := hA.conjTranspose_mul_mul_same W
  have hptr : partialTraceRight (Wᴴ * A * W) = Uᴴ * (partialTraceRight A) * U := by
    rw [hWH, hWdef, partialTraceRight_kron_conj]
  have hdiagonal : Uᴴ * (partialTraceRight A) * U
      = Matrix.diagonal (RCLike.ofReal ∘ hρH.eigenvalues) := by
    have h := hρH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [hUdef, Matrix.star_eq_conjTranspose] using h
  have hdiag : ∀ a b, a ≠ b → partialTraceRight (Wᴴ * A * W) a b = 0 := by
    intro a b hab
    rw [hptr, hdiagonal, Matrix.diagonal_apply_ne _ hab]
  have hkey := redPencil_posSemidef_of_card_left_le_of_diagonal hA' hdiag hc
  have hconj : W * ((Uᴴ * partialTraceRight A * U) ⊗ₖ (1 : Matrix β β ℂ)) * Wᴴ
      = (partialTraceRight A) ⊗ₖ (1 : Matrix β β ℂ) := by
    rw [hWH, hWdef, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    congr 1
    · rw [show U * (Uᴴ * partialTraceRight A * U) * Uᴴ
          = (U * Uᴴ) * partialTraceRight A * (U * Uᴴ) by simp [Matrix.mul_assoc], hU2,
        Matrix.one_mul, Matrix.mul_one]
    all_goals simp
  have hconj2 : W * (Wᴴ * A * W) * Wᴴ = A := by
    rw [show W * (Wᴴ * A * W) * Wᴴ = (W * Wᴴ) * A * (W * Wᴴ) by simp [Matrix.mul_assoc], hW2,
      Matrix.one_mul, Matrix.mul_one]
  have heq : W * (redPencil c (Wᴴ * A * W)) * Wᴴ = redPencil c A := by
    unfold redPencil
    rw [hptr, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hconj, hconj2]
  rw [← heq]
  exact hkey.mul_mul_conjTranspose_same W

/-- **Sufficiency, both halves.** -/
theorem redPencil_posSemidef_of_min_le {c : ℝ} {A : Matrix (α × β) (α × β) ℂ}
    (hA : A.PosSemidef) (hc : ((min (Fintype.card α) (Fintype.card β) : ℕ) : ℝ) ≤ c) :
    (redPencil c A).PosSemidef := by
  rw [Nat.cast_min, min_le_iff] at hc
  rcases hc with h | h
  · exact redPencil_posSemidef_of_card_left_le hA h
  · exact redPencil_posSemidef_of_card_right_le hA h

/-! ## Necessity: the maximally entangled witness -/

private theorem sum4_swap {ι₁ ι₂ ι₃ ι₄ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → ℂ) :
    (∑ a, ∑ i, ∑ t, ∑ s, F a i t s) = ∑ t, ∑ s, ∑ a, ∑ i, F a i t s := by
  have h1 : ∀ a, (∑ i, ∑ t, ∑ s, F a i t s) = ∑ t, ∑ s, ∑ i, F a i t s := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_comm

/-- The maximally entangled vector of an orthonormal pair family. -/
def entangledVec {ι : Type*} [Fintype ι] (u : ι → α → ℂ) (v : ι → β → ℂ) : α × β → ℂ :=
  fun z => ∑ t, u t z.1 * v t z.2

/-- The rank-one positive matrix of the maximally entangled vector. -/
def entangledMat {ι : Type*} [Fintype ι] (u : ι → α → ℂ) (v : ι → β → ℂ) :
    Matrix (α × β) (α × β) ℂ :=
  fun x y => entangledVec u v x * (starRingEnd ℂ) (entangledVec u v y)

theorem entangledMat_posSemidef {ι : Type*} [Fintype ι] (u : ι → α → ℂ) (v : ι → β → ℂ) :
    (entangledMat u v).PosSemidef := by
  classical
  have h : entangledMat u v
      = (Matrix.replicateRow Unit (fun z => (starRingEnd ℂ) (entangledVec u v z)))ᴴ
        * (Matrix.replicateRow Unit (fun z => (starRingEnd ℂ) (entangledVec u v z))) := by
    ext x y
    simp [entangledMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.replicateRow]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Necessity of the threshold.**  A maximally entangled vector of Schmidt rank `card ι` rejects
every coefficient below `card ι`. -/
theorem exists_posSemidef_not_redPencil_posSemidef {c : ℝ} [Nonempty ι]
    (u : ι → α → ℂ) (v : ι → β → ℂ)
    (hu : ∀ t s, ∑ a, (starRingEnd ℂ) (u t a) * u s a = if t = s then 1 else 0)
    (hv : ∀ t s, ∑ i, (starRingEnd ℂ) (v t i) * v s i = if t = s then 1 else 0)
    (hc : c < Fintype.card ι) :
    ∃ A : Matrix (α × β) (α × β) ℂ, A.PosSemidef ∧ ¬ (redPencil c A).PosSemidef := by
  classical
  set Ψ := entangledVec u v with hΨ
  set A := entangledMat u v with hAdef
  refine ⟨A, entangledMat_posSemidef u v, ?_⟩
  intro hpos
  -- the aperture sum of `Ψ` over one ancilla index
  have hinner : ∀ a : α, (∑ i, (starRingEnd ℂ) (Ψ (a, i)) * Ψ (a, i))
      = ∑ t, (starRingEnd ℂ) (u t a) * u t a := by
    intro a
    have hstep : ∀ i : β, (starRingEnd ℂ) (Ψ (a, i)) * Ψ (a, i)
        = ∑ t, ∑ s, ((starRingEnd ℂ) (u t a) * u s a) * ((starRingEnd ℂ) (v t i) * v s i) := by
      intro i
      simp only [hΨ, entangledVec, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    rw [Finset.sum_congr rfl fun i _ => hstep i]
    rw [(sum3_rot (fun t s i => ((starRingEnd ℂ) (u t a) * u s a)
      * ((starRingEnd ℂ) (v t i) * v s i))).symm]
    have hcollapse : ∀ t s : ι, (∑ i, ((starRingEnd ℂ) (u t a) * u s a)
        * ((starRingEnd ℂ) (v t i) * v s i))
        = ((starRingEnd ℂ) (u t a) * u s a) * (if t = s then 1 else 0) := by
      intro t s
      rw [← Finset.mul_sum, hv t s]
    rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => hcollapse t s]
    exact Finset.sum_congr rfl fun t _ => by simp
  have hM : (∑ a, ∑ i, (starRingEnd ℂ) (Ψ (a, i)) * Ψ (a, i)) = (Fintype.card ι : ℂ) := by
    rw [Finset.sum_congr rfl fun a _ => hinner a, Finset.sum_comm,
      Finset.sum_congr rfl fun t _ => hu t t]
    simp
  have hM2 : ∑ z : α × β, (starRingEnd ℂ) (Ψ z) * Ψ z = (Fintype.card ι : ℂ) := by
    rw [Fintype.sum_prod_type]; exact hM
  -- the partial trace acts as the identity on the entangled vector
  have hρ : ∀ a b, (partialTraceRight A) a b = ∑ t, u t a * (starRingEnd ℂ) (u t b) := by
    intro a b
    simp only [partialTraceRight, hAdef, entangledMat, hΨ, entangledVec, map_sum, map_mul]
    have hstep : ∀ l : β, (∑ t, u t a * v t l) * (∑ s, (starRingEnd ℂ) (u s b)
        * (starRingEnd ℂ) (v s l))
        = ∑ t, ∑ s, (u t a * (starRingEnd ℂ) (u s b)) * (v t l * (starRingEnd ℂ) (v s l)) := by
      intro l
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    rw [Finset.sum_congr rfl fun l _ => hstep l]
    rw [(sum3_rot (fun t s l => (u t a * (starRingEnd ℂ) (u s b))
      * (v t l * (starRingEnd ℂ) (v s l)))).symm]
    have hcollapse : ∀ t s : ι, (∑ l, (u t a * (starRingEnd ℂ) (u s b))
        * (v t l * (starRingEnd ℂ) (v s l)))
        = (u t a * (starRingEnd ℂ) (u s b)) * (if t = s then 1 else 0) := by
      intro t s
      rw [← Finset.mul_sum]
      congr 1
      have hconjsum : ∑ l, v t l * (starRingEnd ℂ) (v s l)
          = (starRingEnd ℂ) (∑ l, (starRingEnd ℂ) (v t l) * v s l) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun l _ => by simp
      rw [hconjsum, hv t s]
      by_cases hts : t = s <;> simp [hts]
    rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => hcollapse t s]
    exact Finset.sum_congr rfl fun t _ => by simp
  have hact : ∀ a i, (∑ b, (partialTraceRight A) a b * Ψ (b, i)) = Ψ (a, i) := by
    intro a i
    have hstep : ∀ b : α, (partialTraceRight A) a b * Ψ (b, i)
        = ∑ t, ∑ s, (u t a * v s i) * ((starRingEnd ℂ) (u t b) * u s b) := by
      intro b
      rw [hρ a b]
      simp only [hΨ, entangledVec]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    rw [Finset.sum_congr rfl fun b _ => hstep b]
    rw [(sum3_rot (fun t s b => (u t a * v s i)
      * ((starRingEnd ℂ) (u t b) * u s b))).symm]
    have hcollapse : ∀ t s : ι, (∑ b, (u t a * v s i) * ((starRingEnd ℂ) (u t b) * u s b))
        = (u t a * v s i) * (if t = s then 1 else 0) := by
      intro t s
      rw [← Finset.mul_sum, hu t s]
    rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => hcollapse t s]
    simp [hΨ, entangledVec]
  -- the two quadratic forms
  have hAform : matSesq A Ψ Ψ = (Fintype.card ι : ℂ) ^ 2 := by
    have : matSesq A Ψ Ψ = (∑ i, (starRingEnd ℂ) (Ψ i) * Ψ i)
        * ∑ j, (starRingEnd ℂ) (Ψ j) * Ψ j := by
      rw [Finset.sum_mul_sum]
      simp only [matSesq, hAdef, entangledMat]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, hM2, sq]
  have hTform : matSesq ((partialTraceRight A) ⊗ₖ (1 : Matrix β β ℂ)) Ψ Ψ
      = (Fintype.card ι : ℂ) := by
    rw [matSesq_kron_one]
    have hstep : ∀ (a : α) (i : β), (∑ b, (starRingEnd ℂ) (Ψ (a, i)) * (partialTraceRight A) a b
        * Ψ (b, i)) = (starRingEnd ℂ) (Ψ (a, i)) * Ψ (a, i) := by
      intro a i
      rw [show (∑ b, (starRingEnd ℂ) (Ψ (a, i)) * (partialTraceRight A) a b * Ψ (b, i))
          = (starRingEnd ℂ) (Ψ (a, i)) * ∑ b, (partialTraceRight A) a b * Ψ (b, i) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring]
      rw [hact a i]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => hstep a i, hM]
  -- contradiction
  have hval := matSesq_self_re_nonneg hpos Ψ
  rw [matSesq_redPencil, hAform, hTform] at hval
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hre : ((c : ℂ) * (Fintype.card ι : ℂ) - (Fintype.card ι : ℂ) ^ 2).re
      = c * (Fintype.card ι : ℝ) - (Fintype.card ι : ℝ) ^ 2 := by
    simp [Complex.sub_re, Complex.mul_re, sq]
  rw [hre] at hval
  nlinarith [hval, hcard, hc]

/-- **Theorem 2.1.**  The exact `k`-positivity threshold of the reduction pencil. -/
theorem redPencil_posSemidef_forall_iff [Nonempty α] [Nonempty β] (c : ℝ) :
    (∀ A : Matrix (α × β) (α × β) ℂ, A.PosSemidef → (redPencil c A).PosSemidef)
      ↔ ((min (Fintype.card α) (Fintype.card β) : ℕ) : ℝ) ≤ c := by
  classical
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨e⟩ : Nonempty (Fin (min (Fintype.card α) (Fintype.card β)) ↪ α) :=
      Function.Embedding.nonempty_of_card_le (by simp [Fintype.card_fin])
    obtain ⟨f⟩ : Nonempty (Fin (min (Fintype.card α) (Fintype.card β)) ↪ β) :=
      Function.Embedding.nonempty_of_card_le (by simp [Fintype.card_fin])
    have hpos : 0 < min (Fintype.card α) (Fintype.card β) :=
      lt_min Fintype.card_pos Fintype.card_pos
    have : Nonempty (Fin (min (Fintype.card α) (Fintype.card β))) := ⟨⟨0, hpos⟩⟩
    obtain ⟨A, hA, hnA⟩ := exists_posSemidef_not_redPencil_posSemidef (c := c)
      (fun t a => if a = e t then (1 : ℂ) else 0) (fun t i => if i = f t then (1 : ℂ) else 0)
      (fun t s => by
        classical
        rw [Finset.sum_eq_single (e t)]
        · simp [EmbeddingLike.apply_eq_iff_eq]
        · intro a _ ha; simp [ha]
        · intro hmem; exact absurd (Finset.mem_univ (e t)) hmem)
      (fun t s => by
        classical
        rw [Finset.sum_eq_single (f t)]
        · simp [EmbeddingLike.apply_eq_iff_eq]
        · intro a _ ha; simp [ha]
        · intro hmem; exact absurd (Finset.mem_univ (f t)) hmem)
      (by simpa [Fintype.card_fin] using hlt)
    exact hnA (h A hA)
  · intro hc A hA
    exact redPencil_posSemidef_of_min_le hA hc

end Bipartite

end GaloisForLFunctions.HTGeometry
