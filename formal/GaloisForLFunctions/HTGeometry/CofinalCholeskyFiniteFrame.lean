import Mathlib

/-!
# Finite Cayley coordinates and inverse-Cholesky frame algebra

This module formalizes the finite algebraic core of the cofinal Cholesky carrier-selection law.
The Cayley powers form a lower-triangular coordinate transform with diagonal
`(-2 * i) ^ n`, hence equality of every row through level `N` is equivalent to equality of the
reciprocal-power data through level `N`. Independently, an inverse-Cholesky identity
`C * G * Cᴴ = 1` determines both `G⁻¹` and `G` from the frame matrix `C`.

The measure-theoretic moment and Cauchy-derivative bridges are intentionally not hidden in these
finite lemmas; they are formalized in the subsequent carrier modules.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix
open scoped ComplexOrder

noncomputable section

/-- The finite lower-triangular change of coordinates induced by the Cayley transform. -/
def cayleyTriangularTransform (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (n + 1),
    (-2 * I) ^ r * b r * (n.choose r : ℂ)

/-- The Cayley transform is `1 - 2i/(x+i)` away from its pole. -/
theorem cayley_eq_one_add_reciprocal {x : ℂ} (h : x + I ≠ 0) :
    (x - I) / (x + I) = 1 + (-2 * I) * (x + I)⁻¹ := by
  field_simp
  ring

/-- Every Cayley power is the explicit triangular binomial combination of reciprocal powers. -/
theorem cayley_pow_expansion {x : ℂ} (h : x + I ≠ 0) (n : ℕ) :
    ((x - I) / (x + I)) ^ n =
      cayleyTriangularTransform (fun r => (x + I)⁻¹ ^ r) n := by
  have hreorder : (x - I) / (x + I) = (-2 * I) * (x + I)⁻¹ + 1 := by
    rw [cayley_eq_one_add_reciprocal h]
    ring
  rw [hreorder, add_pow]
  unfold cayleyTriangularTransform
  apply Finset.sum_congr rfl
  intro r hr
  simp only [one_pow, mul_one]
  ring

/-- The Cayley triangular transform is injective on every finite prefix. -/
theorem cayleyTriangularTransform_injective_on_prefix
    {b₁ b₂ : ℕ → ℂ} {N : ℕ}
    (h : ∀ n ≤ N,
      cayleyTriangularTransform b₁ n = cayleyTriangularTransform b₂ n) :
    ∀ n ≤ N, b₁ n = b₂ n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hrow := h n hn
      unfold cayleyTriangularTransform at hrow
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at hrow
      have hprefix :
          (∑ r ∈ Finset.range n, (-2 * I) ^ r * b₁ r * (n.choose r : ℂ)) =
            ∑ r ∈ Finset.range n, (-2 * I) ^ r * b₂ r * (n.choose r : ℂ) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [ih r (Finset.mem_range.mp hr)
          ((Nat.le_of_lt (Finset.mem_range.mp hr)).trans hn)]
      rw [hprefix] at hrow
      simp only [Nat.choose_self, Nat.cast_one, mul_one] at hrow
      exact mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-2 * I : ℂ) ≠ 0))
        (add_left_cancel hrow)

/-- On every finite prefix, equality after the Cayley transform is equivalent to equality before
the transform. -/
theorem cayleyTriangularTransform_prefix_iff
    {b₁ b₂ : ℕ → ℂ} {N : ℕ} :
    (∀ n ≤ N, cayleyTriangularTransform b₁ n = cayleyTriangularTransform b₂ n) ↔
      ∀ n ≤ N, b₁ n = b₂ n := by
  constructor
  · exact cayleyTriangularTransform_injective_on_prefix
  · intro h n hn
    unfold cayleyTriangularTransform
    apply Finset.sum_congr rfl
    intro r hr
    rw [h r ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)).trans hn)]

/-- The Toeplitz Gram matrix cut out by a two-sided circle-moment sequence through level `N`. -/
def circleToeplitzGram (N : ℕ) (c : ℤ → ℂ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := fun j k =>
  c (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ))

/-- Equality of two level-`N` Toeplitz Gram matrices forces equality of all nonnegative moments
through level `N`. -/
theorem positiveMoment_eq_of_circleToeplitzGram_eq
    {N : ℕ} {c₁ c₂ : ℤ → ℂ}
    (h : circleToeplitzGram N c₁ = circleToeplitzGram N c₂) :
    ∀ r ≤ N, c₁ r = c₂ r := by
  intro r hr
  have hentry := congrFun (congrFun h ⟨r, Nat.lt_succ_iff.mpr hr⟩)
    ⟨0, Nat.zero_lt_succ N⟩
  simpa [circleToeplitzGram] using hentry

/-- Equality of all moments in the two-sided window `[-N,N]` gives equality of the corresponding
Toeplitz Gram matrices. -/
theorem circleToeplitzGram_eq_of_moment_eq
    {N : ℕ} {c₁ c₂ : ℤ → ℂ}
    (h : ∀ q : ℤ, -(N : ℤ) ≤ q → q ≤ N → c₁ q = c₂ q) :
    circleToeplitzGram N c₁ = circleToeplitzGram N c₂ := by
  ext j k
  apply h
  · have hj : (j : ℕ) ≤ N := Nat.le_of_lt_succ j.isLt
    have hk : (k : ℕ) ≤ N := Nat.le_of_lt_succ k.isLt
    omega
  · have hj : (j : ℕ) ≤ N := Nat.le_of_lt_succ j.isLt
    have hk : (k : ℕ) ≤ N := Nat.le_of_lt_succ k.isLt
    omega

/-- Hermitian symmetry of a two-sided moment sequence. Circle moments of a positive measure have
this symmetry because negative monomials are complex conjugates of positive monomials. -/
def IsHermitianMoment (c : ℤ → ℂ) : Prop :=
  ∀ r : ℕ, c (-(r : ℤ)) = star (c r)

/-- For Hermitian moment sequences, equality of level-`N` Toeplitz Gram matrices is exactly
equality of their nonnegative moments through level `N`. -/
theorem circleToeplitzGram_eq_iff_positiveMoment_eq
    {N : ℕ} {c₁ c₂ : ℤ → ℂ}
    (h₁ : IsHermitianMoment c₁) (h₂ : IsHermitianMoment c₂) :
    circleToeplitzGram N c₁ = circleToeplitzGram N c₂ ↔
      ∀ r ≤ N, c₁ r = c₂ r := by
  constructor
  · exact positiveMoment_eq_of_circleToeplitzGram_eq
  · intro hpos
    apply circleToeplitzGram_eq_of_moment_eq
    intro q hqleft hqright
    cases q with
    | ofNat r =>
        apply hpos r
        exact Int.ofNat_le.mp hqright
    | negSucc r =>
        have hr : r + 1 ≤ N := by omega
        rw [show Int.negSucc r = -((r + 1 : ℕ) : ℤ) by omega,
          h₁ (r + 1), h₂ (r + 1), hpos (r + 1) hr]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix `C` is an inverse-Cholesky frame for `G` when it orthonormalizes the Gram matrix by
congruence. Triangularity and positive diagonal, which make the frame canonical, are imposed by
the later Cholesky construction. -/
def IsInverseCholeskyFrame (C G : Matrix n n ℂ) : Prop :=
  C * G * Cᴴ = 1

/-- Every finite positive-definite complex Gram matrix admits an inverse frame. The construction is
normalized Gram--Schmidt in the inner product induced by `G`. The subsequent canonical Cholesky
theorem strengthens this frame with lower triangularity and positive diagonal. -/
theorem exists_inverseCholeskyFrame_of_posDef
    {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) :
    ∃ C : Matrix (Fin N) (Fin N) ℂ, IsInverseCholeskyFrame C G := by
  let normInst := Matrix.toNormedAddCommGroup G hG
  letI : NormedAddCommGroup (Fin N → ℂ) := normInst
  letI : SeminormedAddCommGroup (Fin N → ℂ) := normInst.toSeminormedAddCommGroup
  letI := Matrix.toInnerProductSpace G hG.posSemidef
  let b : Module.Basis (Fin N) ℂ (Fin N → ℂ) := Pi.basisFun ℂ (Fin N)
  let q : Fin N → (Fin N → ℂ) := InnerProductSpace.gramSchmidtNormed ℂ b
  let C : Matrix (Fin N) (Fin N) ℂ := fun j k => star (q j k)
  refine ⟨C, ?_⟩
  unfold IsInverseCholeskyFrame
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.mul_apply, C, Matrix.conjTranspose_apply, star_star]
  have horth : Orthonormal ℂ q :=
    InnerProductSpace.gramSchmidtNormed_orthonormal b.linearIndependent
  have hinner := orthonormal_iff_ite.mp horth j k
  change (G *ᵥ q k) ⬝ᵥ star (q j) = (if j = k then 1 else 0) at hinner
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply] at hinner
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  convert hinner using 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- An inverse-Cholesky frame satisfies the exact inverse Gram identity `G⁻¹ = Cᴴ C`. -/
theorem inverse_eq_conjTranspose_mul_of_inverseCholesky
    (C G : Matrix n n ℂ) (h : IsInverseCholeskyFrame C G) :
    G⁻¹ = Cᴴ * C := by
  have hCright : C * (G * Cᴴ) = 1 := by
    simpa [IsInverseCholeskyFrame, mul_assoc] using h
  have hCdet : IsUnit C.det := Matrix.isUnit_det_of_right_inverse hCright
  have hGC : G * Cᴴ = C⁻¹ := (Matrix.inv_eq_right_inv hCright).symm
  apply Matrix.inv_eq_right_inv
  calc
    G * (Cᴴ * C) = (G * Cᴴ) * C := by rw [mul_assoc]
    _ = C⁻¹ * C := by rw [hGC]
    _ = 1 := Matrix.nonsing_inv_mul C hCdet

/-- One inverse-Cholesky frame matrix cannot orthonormalize two different Gram matrices. -/
theorem gram_eq_of_same_inverseCholesky
    (C G₁ G₂ : Matrix n n ℂ)
    (h₁ : IsInverseCholeskyFrame C G₁) (h₂ : IsInverseCholeskyFrame C G₂) :
    G₁ = G₂ := by
  have hCright : C * (G₁ * Cᴴ) = 1 := by
    simpa [IsInverseCholeskyFrame, mul_assoc] using h₁
  have hCdet : IsUnit C.det := Matrix.isUnit_det_of_right_inverse hCright
  have hCtdet : IsUnit (Cᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hCdet.star
  have hEq : C * G₁ * Cᴴ = C * G₂ * Cᴴ := h₁.trans h₂.symm
  calc
    G₁ = C⁻¹ * (C * G₁ * Cᴴ) * (Cᴴ)⁻¹ := by
      symm
      calc
        C⁻¹ * (C * G₁ * Cᴴ) * (Cᴴ)⁻¹ =
            (C⁻¹ * C) * G₁ * (Cᴴ * (Cᴴ)⁻¹) := by simp only [mul_assoc]
        _ = G₁ := by
          rw [Matrix.nonsing_inv_mul C hCdet,
            Matrix.mul_nonsing_inv Cᴴ hCtdet]
          simp
    _ = C⁻¹ * (C * G₂ * Cᴴ) * (Cᴴ)⁻¹ := by rw [hEq]
    _ = G₂ := by
      calc
        C⁻¹ * (C * G₂ * Cᴴ) * (Cᴴ)⁻¹ =
            (C⁻¹ * C) * G₂ * (Cᴴ * (Cᴴ)⁻¹) := by simp only [mul_assoc]
        _ = G₂ := by
          rw [Matrix.nonsing_inv_mul C hCdet,
            Matrix.mul_nonsing_inv Cᴴ hCtdet]
          simp

end

end GaloisForLFunctions.HTGeometry
