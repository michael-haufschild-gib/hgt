import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite weighted monomial frames and exact leverage conservation

A finite positive packet with at least `n` distinct nodes gives a strict weighted monomial Gram
matrix in dimension `n`.  Its inverse supplies a canonical redundant dual, including exact complex
monomial reconstruction.  At real targets the dual energy is exactly the Christoffel kernel, while
the packet's total nodal leverage is exactly `n`.  Thus oversampling redistributes a fixed
dimension budget rather than inheriting square interpolation's condition number.
-/

open Matrix
open scoped BigOperators ComplexConjugate

namespace HTGeometry

noncomputable section

/-- Monomial feature vector through degree strictly below `n`. -/
def monomialEvaluationVector (n : ℕ) (t : ℝ) : Fin n → ℝ :=
  fun j => t ^ (j : ℕ)

/-- Weighted monomial Gram matrix of a finite, possibly redundant, real packet. -/
def weightedMonomialGram {N : ℕ} (x : Fin N → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ r : Fin N, x r * x r ^ ((i : ℕ) + (j : ℕ))

theorem weightedMonomialGram_isHermitian {N : ℕ} (x : Fin N → ℝ) (n : ℕ) :
    (weightedMonomialGram x n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [weightedMonomialGram, star_trivial]
  congr 1
  funext r
  rw [add_comm]

/-- Gram quadratic form equals weighted nodal polynomial energy. -/
theorem dotProduct_mulVec_weightedMonomialGram
    {N n : ℕ} (x : Fin N → ℝ) (a : Fin n → ℝ) :
    a ⬝ᵥ (weightedMonomialGram x n).mulVec a =
      ∑ r : Fin N, x r * Polynomial.eval (x r) (Polynomial.ofFn n a) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, weightedMonomialGram]
  calc
    ∑ i : Fin n, a i * ∑ j : Fin n,
        (∑ r : Fin N, x r * x r ^ ((i : ℕ) + (j : ℕ))) * a j =
        ∑ i : Fin n, ∑ j : Fin n, ∑ r : Fin N,
          x r * (a i * x r ^ (i : ℕ)) * (a j * x r ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_add]
      ring
    _ = ∑ i : Fin n, ∑ r : Fin N, ∑ j : Fin n,
          x r * (a i * x r ^ (i : ℕ)) * (a j * x r ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ r : Fin N, ∑ i : Fin n, ∑ j : Fin n,
          x r * (a i * x r ^ (i : ℕ)) * (a j * x r ^ (j : ℕ)) :=
      Finset.sum_comm
    _ = ∑ r : Fin N, x r * (∑ i : Fin n, a i * x r ^ (i : ℕ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ r : Fin N, x r * Polynomial.eval (x r) (Polynomial.ofFn n a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_monomial]

/-- Positive weights and enough distinct nodes make the redundant monomial Gram matrix strict. -/
theorem weightedMonomialGram_posDef
    {N n : ℕ} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card) :
    (weightedMonomialGram x n).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨weightedMonomialGram_isHermitian x n, ?_⟩
  intro a ha
  rw [star_trivial, dotProduct_mulVec_weightedMonomialGram]
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact ha (Subsingleton.elim _ _)
  let p : Polynomial ℝ := Polynomial.ofFn n a
  have hp : p ≠ 0 := by
    intro hp0
    apply ha
    apply Polynomial.injective_ofFn n
    simpa [p] using hp0
  have hnonneg : 0 ≤ ∑ r : Fin N, x r * Polynomial.eval (x r) p ^ 2 := by
    apply Finset.sum_nonneg
    intro r _
    exact mul_nonneg (hx r).le (sq_nonneg _)
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have heach : ∀ r : Fin N, Polynomial.eval (x r) p = 0 := by
    intro r
    have hr := (Finset.sum_eq_zero_iff_of_nonneg fun s (_ : s ∈
        (Finset.univ : Finset (Fin N))) =>
      mul_nonneg (hx s).le (sq_nonneg (Polynomial.eval (x s) p))).mp
        (by simpa only [p] using hzero.symm) r (Finset.mem_univ r)
    rcases mul_eq_zero.mp hr with hxr | hsquare
    · exact False.elim ((hx r).ne' hxr)
    · exact sq_eq_zero_iff.mp hsquare
  let T : Finset ℝ := (Finset.univ : Finset (Fin N)).image x
  have heval : ∀ t : T, Polynomial.eval (t : ℝ) p = 0 := by
    intro t
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp t.property
    simpa only [hr] using heach r
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    p (f := fun t : T => (t : ℝ)) Subtype.val_injective heval
  exact (Polynomial.ofFn_natDegree_lt hn a).trans_le (by simpa [T] using hcard)

/-- Canonical nodal leverage of a weighted redundant monomial packet. -/
def weightedMonomialLeverage {N : ℕ} (x : Fin N → ℝ) (n : ℕ) (r : Fin N) : ℝ :=
  x r * ∑ i : Fin n, ∑ j : Fin n,
    x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j * x r ^ (j : ℕ)

/-- Entrywise `ℓ¹` size of the inverse weighted monomial Gram matrix. -/
def weightedMonomialInverseEntryL1 {N : ℕ} (x : Fin N → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, |(weightedMonomialGram x n)⁻¹ i j|

/-- A positive target packet inside `[0,1]` has relative Hankel trace at most inverse-Gram
entrywise size times its total first mass. -/
theorem trace_inv_mul_positiveWeightedMonomialGram_le_inverseEntryL1_mul_mass
    {N M n : ℕ} (x : Fin N → ℝ) (t : Fin M → ℝ)
    (ht0 : ∀ q, 0 ≤ t q) (ht1 : ∀ q, t q ≤ 1) :
    Matrix.trace ((weightedMonomialGram x n)⁻¹ * weightedMonomialGram t n) ≤
      weightedMonomialInverseEntryL1 x n * ∑ q : Fin M, t q := by
  change (∑ i : Fin n, ∑ j : Fin n,
      (weightedMonomialGram x n)⁻¹ i j *
        (∑ q : Fin M, t q * t q ^ ((j : ℕ) + (i : ℕ)))) ≤
    (∑ i : Fin n, ∑ j : Fin n, |(weightedMonomialGram x n)⁻¹ i j|) *
      ∑ q : Fin M, t q
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hmom0 : 0 ≤ ∑ q : Fin M, t q * t q ^ ((j : ℕ) + (i : ℕ)) := by
    apply Finset.sum_nonneg
    intro q _
    exact mul_nonneg (ht0 q) (pow_nonneg (ht0 q) _)
  have hmom_le : (∑ q : Fin M, t q * t q ^ ((j : ℕ) + (i : ℕ))) ≤
      ∑ q : Fin M, t q := by
    apply Finset.sum_le_sum
    intro q _
    have hp : t q ^ ((j : ℕ) + (i : ℕ)) ≤ 1 :=
      pow_le_one₀ (ht0 q) (ht1 q)
    exact mul_le_of_le_one_right (ht0 q) hp
  exact (mul_le_mul_of_nonneg_right (le_abs_self _) hmom0).trans
    (mul_le_mul_of_nonneg_left hmom_le (abs_nonneg _))

/-- Exact finite-frame leverage conservation: total leverage is feature-space dimension. -/
theorem sum_weightedMonomialLeverage_eq_dimension
    {N n : ℕ} (x : Fin N → ℝ)
    (hunit : IsUnit (weightedMonomialGram x n).det) :
    ∑ r : Fin N, weightedMonomialLeverage x n r = n := by
  have hinv : (weightedMonomialGram x n)⁻¹ * weightedMonomialGram x n = 1 :=
    Matrix.nonsing_inv_mul _ hunit
  calc
    ∑ r : Fin N, weightedMonomialLeverage x n r =
        Matrix.trace ((weightedMonomialGram x n)⁻¹ * weightedMonomialGram x n) := by
      change (∑ r : Fin N, x r * ∑ i : Fin n, ∑ j : Fin n,
          x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j * x r ^ (j : ℕ)) =
        ∑ i : Fin n, ∑ j : Fin n,
          (weightedMonomialGram x n)⁻¹ i j *
            (∑ r : Fin N, x r * x r ^ ((j : ℕ) + (i : ℕ)))
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) := congrArg Matrix.trace hinv
    _ = n := by simp

/-- `j`th canonical dual coordinate at sample `r`. -/
def weightedMonomialDual {N : ℕ} (x : Fin N → ℝ) (n : ℕ)
    (j : Fin n) (r : Fin N) : ℝ :=
  x r * ∑ i : Fin n, x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j

/-- Finite weighted Christoffel kernel. -/
def weightedMonomialKernel {N : ℕ} (x : Fin N → ℝ) (n : ℕ) (s t : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    s ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j * t ^ (j : ℕ)

@[simp] theorem weightedMonomialLeverage_eq_mul_kernel
    {N n : ℕ} (x : Fin N → ℝ) (r : Fin N) :
    weightedMonomialLeverage x n r =
      x r * weightedMonomialKernel x n (x r) (x r) := rfl

/-- Inverse-Gram dual coordinates isolate monomials exactly. -/
theorem weightedMonomialDual_reproduces_monomial
    {N n : ℕ} (x : Fin N → ℝ)
    (hunit : IsUnit (weightedMonomialGram x n).det) (k j : Fin n) :
    ∑ r : Fin N, weightedMonomialDual x n j r * x r ^ (k : ℕ) =
      if k = j then 1 else 0 := by
  have hinv : weightedMonomialGram x n * (weightedMonomialGram x n)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hunit
  calc
    ∑ r : Fin N, weightedMonomialDual x n j r * x r ^ (k : ℕ) =
        ∑ r : Fin N, ∑ i : Fin n,
          x r * (x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j) *
            x r ^ (k : ℕ) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [weightedMonomialDual]
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : Fin n, ∑ r : Fin N,
          x r * (x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j) *
            x r ^ (k : ℕ) := Finset.sum_comm
    _ = ∑ i : Fin n, weightedMonomialGram x n k i *
          (weightedMonomialGram x n)⁻¹ i j := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [weightedMonomialGram]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_add]
      ring
    _ = if k = j then 1 else 0 := by
      have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M k j) hinv
      simpa [Matrix.mul_apply, Matrix.one_apply] using hentry

/-- Canonical dual vectors have inverse-Gram weighted pair energy. -/
theorem weightedMonomialDual_energy_pair
    {N n : ℕ} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hunit : IsUnit (weightedMonomialGram x n).det) (j k : Fin n) :
    ∑ r : Fin N, weightedMonomialDual x n j r * weightedMonomialDual x n k r / x r =
      (weightedMonomialGram x n)⁻¹ j k := by
  calc
    ∑ r : Fin N, weightedMonomialDual x n j r * weightedMonomialDual x n k r / x r =
        ∑ r : Fin N, weightedMonomialDual x n j r *
          (∑ i : Fin n, x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i k) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [weightedMonomialDual]
      field_simp [(hx r).ne']
    _ = ∑ r : Fin N, ∑ i : Fin n,
          weightedMonomialDual x n j r *
            (x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i k) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ r : Fin N,
          weightedMonomialDual x n j r *
            (x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i k) :=
      Finset.sum_comm
    _ = ∑ i : Fin n,
          (∑ r : Fin N, weightedMonomialDual x n j r * x r ^ (i : ℕ)) *
            (weightedMonomialGram x n)⁻¹ i k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ i : Fin n, (if i = j then 1 else 0) *
          (weightedMonomialGram x n)⁻¹ i k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [weightedMonomialDual_reproduces_monomial x hunit i j]
    _ = (weightedMonomialGram x n)⁻¹ j k := by simp

/-- Canonical complex reconstruction coefficients supplied by inverse-Gram duality. -/
def canonicalMonomialReconstruction {N : ℕ} (x : Fin N → ℝ) (n : ℕ)
    (z : ℂ) (r : Fin N) : ℂ :=
  ∑ j : Fin n, (weightedMonomialDual x n j r : ℂ) * z ^ (j : ℕ)

/-- Hermitian inverse-Gram kernel diagonal at a complex target. -/
def complexWeightedMonomialKernelDiagonal {N : ℕ}
    (x : Fin N → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j : Fin n, ∑ k : Fin n,
    conj (z ^ (j : ℕ)) * ((weightedMonomialGram x n)⁻¹ j k : ℂ) * z ^ (k : ℕ)

/-- Complex target moment matrix, oriented so inverse-Gram multiplication traces kernel mass. -/
def complexTargetMonomialMomentMatrix {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (b : ι → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => ∑ q : ι, (b q : ℂ) * conj (z q ^ (k : ℕ)) * z q ^ (j : ℕ)

/-- Positive real targets give exactly the complexified weighted Hankel Gram matrix. -/
theorem complexTargetMonomialMomentMatrix_ofReal_pos
    {M n : ℕ} (t : Fin M → ℝ) (ht : ∀ q, 0 < t q) :
    complexTargetMonomialMomentMatrix (fun q => (t q : ℂ))
        (fun q => ‖(t q : ℂ)‖) n =
      (weightedMonomialGram t n).map (algebraMap ℝ ℂ) := by
  ext j k
  simp only [complexTargetMonomialMomentMatrix, weightedMonomialGram, Matrix.map_apply,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ht _)]
  push_cast
  apply Finset.sum_congr rfl
  intro q _
  simp only [map_pow, Complex.conj_ofReal]
  rw [pow_add]
  ac_rfl

/-- Real specialization of canonical reconstruction. -/
def canonicalMonomialReconstructionReal {N : ℕ} (x : Fin N → ℝ) (n : ℕ)
    (t : ℝ) (r : Fin N) : ℝ :=
  ∑ j : Fin n, weightedMonomialDual x n j r * t ^ (j : ℕ)

theorem canonicalMonomialReconstruction_ofReal
    {N n : ℕ} (x : Fin N → ℝ) (t : ℝ) (r : Fin N) :
    canonicalMonomialReconstruction x n (t : ℂ) r =
      (canonicalMonomialReconstructionReal x n t r : ℂ) := by
  simp only [canonicalMonomialReconstruction, canonicalMonomialReconstructionReal]
  push_cast
  rfl

theorem canonicalMonomialReconstructionReal_eq_mul_kernel
    {N n : ℕ} (x : Fin N → ℝ) (t : ℝ) (r : Fin N) :
    canonicalMonomialReconstructionReal x n t r =
      x r * weightedMonomialKernel x n (x r) t := by
  simp only [canonicalMonomialReconstructionReal, weightedMonomialDual,
    weightedMonomialKernel]
  calc
    ∑ j : Fin n, (x r * ∑ i : Fin n,
        x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j) * t ^ (j : ℕ) =
        ∑ j : Fin n, ∑ i : Fin n,
          x r * (x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j) *
            t ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : Fin n, ∑ j : Fin n,
          x r * (x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j) *
            t ^ (j : ℕ) := Finset.sum_comm
    _ = x r * ∑ i : Fin n, ∑ j : Fin n,
          x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j * t ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem canonicalMonomialReconstructionReal_reproduces_monomial
    {N n : ℕ} (x : Fin N → ℝ)
    (hunit : IsUnit (weightedMonomialGram x n).det) (t : ℝ) (k : Fin n) :
    ∑ r : Fin N, canonicalMonomialReconstructionReal x n t r * x r ^ (k : ℕ) =
      t ^ (k : ℕ) := by
  calc
    ∑ r : Fin N, canonicalMonomialReconstructionReal x n t r * x r ^ (k : ℕ) =
        ∑ r : Fin N, ∑ j : Fin n,
          (weightedMonomialDual x n j r * t ^ (j : ℕ)) * x r ^ (k : ℕ) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [canonicalMonomialReconstructionReal]
      rw [Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ r : Fin N,
          (weightedMonomialDual x n j r * t ^ (j : ℕ)) * x r ^ (k : ℕ) :=
      Finset.sum_comm
    _ = ∑ j : Fin n,
          (∑ r : Fin N, weightedMonomialDual x n j r * x r ^ (k : ℕ)) *
            t ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ j : Fin n, (if k = j then 1 else 0) * t ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [weightedMonomialDual_reproduces_monomial x hunit k j]
    _ = t ^ (k : ℕ) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp

/-- At real targets, canonical dual weighted energy is exactly the Christoffel kernel diagonal. -/
theorem canonicalMonomialReconstructionReal_energy_eq_kernel
    {N n : ℕ} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hunit : IsUnit (weightedMonomialGram x n).det) (t : ℝ) :
    ∑ r : Fin N, canonicalMonomialReconstructionReal x n t r ^ 2 / x r =
      weightedMonomialKernel x n t t := by
  calc
    ∑ r : Fin N, canonicalMonomialReconstructionReal x n t r ^ 2 / x r =
        ∑ r : Fin N, canonicalMonomialReconstructionReal x n t r *
          weightedMonomialKernel x n (x r) t := by
      apply Finset.sum_congr rfl
      intro r _
      rw [canonicalMonomialReconstructionReal_eq_mul_kernel]
      field_simp [(hx r).ne']
    _ = ∑ r : Fin N, ∑ i : Fin n, ∑ j : Fin n,
          canonicalMonomialReconstructionReal x n t r *
            (x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j * t ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [weightedMonomialKernel]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ r : Fin N, ∑ j : Fin n,
          canonicalMonomialReconstructionReal x n t r *
            (x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j * t ^ (j : ℕ)) :=
      Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ r : Fin N,
          canonicalMonomialReconstructionReal x n t r *
            (x r ^ (i : ℕ) * (weightedMonomialGram x n)⁻¹ i j * t ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n,
          (∑ r : Fin N, canonicalMonomialReconstructionReal x n t r *
            x r ^ (i : ℕ)) * (weightedMonomialGram x n)⁻¹ i j * t ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = weightedMonomialKernel x n t t := by
      simp only [weightedMonomialKernel]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [canonicalMonomialReconstructionReal_reproduces_monomial x hunit t i]

/-- Canonical inverse-Gram coefficients reconstruct every complex target monomial. -/
theorem canonicalMonomialReconstruction_reproduces_monomial
    {N n : ℕ} (x : Fin N → ℝ)
    (hunit : IsUnit (weightedMonomialGram x n).det) (z : ℂ) (k : Fin n) :
    ∑ r : Fin N, canonicalMonomialReconstruction x n z r * (x r : ℂ) ^ (k : ℕ) =
      z ^ (k : ℕ) := by
  calc
    ∑ r : Fin N, canonicalMonomialReconstruction x n z r * (x r : ℂ) ^ (k : ℕ) =
        ∑ r : Fin N, ∑ j : Fin n,
          ((weightedMonomialDual x n j r : ℂ) * z ^ (j : ℕ)) *
            (x r : ℂ) ^ (k : ℕ) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [canonicalMonomialReconstruction]
      rw [Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ r : Fin N,
          ((weightedMonomialDual x n j r : ℂ) * z ^ (j : ℕ)) *
            (x r : ℂ) ^ (k : ℕ) := Finset.sum_comm
    _ = ∑ j : Fin n,
          ((∑ r : Fin N, weightedMonomialDual x n j r * x r ^ (k : ℕ) : ℝ) : ℂ) *
            z ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ j : Fin n, ((if k = j then 1 else 0 : ℝ) : ℂ) * z ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [weightedMonomialDual_reproduces_monomial x hunit k j]
    _ = z ^ (k : ℕ) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp

/-- Canonical complex reconstruction energy is exactly the Hermitian inverse-Gram kernel. -/
theorem canonicalMonomialReconstruction_energy_eq_complexKernelDiagonal
    {N n : ℕ} (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hunit : IsUnit (weightedMonomialGram x n).det) (z : ℂ) :
    ((∑ r : Fin N, ‖canonicalMonomialReconstruction x n z r‖ ^ 2 / x r : ℝ) : ℂ) =
      complexWeightedMonomialKernelDiagonal x n z := by
  calc
    ((∑ r : Fin N, ‖canonicalMonomialReconstruction x n z r‖ ^ 2 / x r : ℝ) : ℂ) =
        ∑ r : Fin N,
          ((‖canonicalMonomialReconstruction x n z r‖ ^ 2 : ℝ) : ℂ) / (x r : ℂ) := by
      push_cast
      rfl
    _ = ∑ r : Fin N,
        ((starRingEnd ℂ) (canonicalMonomialReconstruction x n z r) *
          canonicalMonomialReconstruction x n z r) / (x r : ℂ) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    _ = ∑ r : Fin N, ∑ j : Fin n, ∑ k : Fin n,
          ((weightedMonomialDual x n j r : ℂ) * (starRingEnd ℂ) (z ^ (j : ℕ))) *
            ((weightedMonomialDual x n k r : ℂ) * z ^ (k : ℕ)) / (x r : ℂ) := by
      simp only [canonicalMonomialReconstruction]
      apply Finset.sum_congr rfl
      intro r _
      rw [map_sum, div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp only [map_mul, Complex.conj_ofReal]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ r : Fin N,
          ((weightedMonomialDual x n j r : ℂ) * (starRingEnd ℂ) (z ^ (j : ℕ))) *
            ((weightedMonomialDual x n k r : ℂ) * z ^ (k : ℕ)) / (x r : ℂ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ j : Fin n, ∑ k : Fin n,
          ((∑ r : Fin N, weightedMonomialDual x n j r *
            weightedMonomialDual x n k r / x r : ℝ) : ℂ) *
            (starRingEnd ℂ) (z ^ (j : ℕ)) * z ^ (k : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      field_simp [(hx r).ne']
    _ = ∑ j : Fin n, ∑ k : Fin n,
          (starRingEnd ℂ) (z ^ (j : ℕ)) *
            ((weightedMonomialGram x n)⁻¹ j k : ℂ) * z ^ (k : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [weightedMonomialDual_energy_pair x hx hunit j k]
      ring
    _ = complexWeightedMonomialKernelDiagonal x n z := rfl

/-- Finite target superposition is exactly a relative moment-matrix trace. -/
theorem sum_mul_complexKernelDiagonal_eq_trace
    {N n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Fin N → ℝ) (z : ι → ℂ) (b : ι → ℝ) :
    ∑ q : ι, (b q : ℂ) * complexWeightedMonomialKernelDiagonal x n (z q) =
      Matrix.trace
        (((weightedMonomialGram x n)⁻¹.map (algebraMap ℝ ℂ)) *
          complexTargetMonomialMomentMatrix z b n) := by
  simp only [complexWeightedMonomialKernelDiagonal, Matrix.trace]
  calc
    ∑ q : ι, (b q : ℂ) * ∑ j : Fin n, ∑ k : Fin n,
        conj (z q ^ (j : ℕ)) * ((weightedMonomialGram x n)⁻¹ j k : ℂ) *
          z q ^ (k : ℕ) =
        ∑ q : ι, ∑ j : Fin n, ∑ k : Fin n,
          (b q : ℂ) * (conj (z q ^ (j : ℕ)) *
            ((weightedMonomialGram x n)⁻¹ j k : ℂ) * z q ^ (k : ℕ)) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ q : ι, ∑ k : Fin n,
          (b q : ℂ) * (conj (z q ^ (j : ℕ)) *
            ((weightedMonomialGram x n)⁻¹ j k : ℂ) * z q ^ (k : ℕ)) :=
      Finset.sum_comm
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ q : ι,
          (b q : ℂ) * (conj (z q ^ (j : ℕ)) *
            ((weightedMonomialGram x n)⁻¹ j k : ℂ) * z q ^ (k : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ j : Fin n, ∑ k : Fin n,
          ((weightedMonomialGram x n)⁻¹ j k : ℂ) *
            ∑ q : ι, (b q : ℂ) * conj (z q ^ (j : ℕ)) * z q ^ (k : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = ∑ j : Fin n, ∑ k : Fin n,
          ((weightedMonomialGram x n)⁻¹ j k : ℂ) *
            ∑ q : ι, (b q : ℂ) * conj (z q ^ (j : ℕ)) * z q ^ (k : ℕ) := rfl

end

end HTGeometry
