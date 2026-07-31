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

/-- Canonical innovation amplitude of the unit response packet in one inverse-Cholesky row. -/
def inverseCholeskyUnitAmplitude {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℂ :=
  ∑ j, C i j

/-- Squared energy of the unit response packet in inverse-Cholesky coordinates. -/
def inverseCholeskyUnitCapacity {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ i, ‖inverseCholeskyUnitAmplitude C i‖ ^ 2

/-- The new unit-packet amplitude at level `N` of a coherent inverse-Cholesky tower. -/
def coherentClockInnovation
    (C : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (N : ℕ) : ℂ :=
  inverseCholeskyUnitAmplitude (C N) (Fin.last N)

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

/-- The canonical inverse frame obtained by normalized Gram--Schmidt in the inner product induced
by a positive-definite Gram matrix. -/
def gramSchmidtInverseFrame
    {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) :
    Matrix (Fin N) (Fin N) ℂ := by
  let normInst := Matrix.toNormedAddCommGroup G hG
  letI : NormedAddCommGroup (Fin N → ℂ) := normInst
  letI : SeminormedAddCommGroup (Fin N → ℂ) := normInst.toSeminormedAddCommGroup
  letI := Matrix.toInnerProductSpace G hG.posSemidef
  letI := FiniteDimensional.complete ℂ (Fin N → ℂ)
  let b : Module.Basis (Fin N) ℂ (Fin N → ℂ) := Pi.basisFun ℂ (Fin N)
  exact fun j k => star (InnerProductSpace.gramSchmidtNormed ℂ b j k)

/-- The normalized Gram--Schmidt matrix orthonormalizes the original Gram matrix. -/
theorem gramSchmidtInverseFrame_isInverseCholeskyFrame
    {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) :
    IsInverseCholeskyFrame (gramSchmidtInverseFrame G hG) G := by
  let normInst := Matrix.toNormedAddCommGroup G hG
  letI : NormedAddCommGroup (Fin N → ℂ) := normInst
  letI : SeminormedAddCommGroup (Fin N → ℂ) := normInst.toSeminormedAddCommGroup
  letI := Matrix.toInnerProductSpace G hG.posSemidef
  letI := FiniteDimensional.complete ℂ (Fin N → ℂ)
  let b : Module.Basis (Fin N) ℂ (Fin N → ℂ) := Pi.basisFun ℂ (Fin N)
  unfold IsInverseCholeskyFrame
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.mul_apply, gramSchmidtInverseFrame,
    Matrix.conjTranspose_apply, star_star]
  have horth : Orthonormal ℂ (InnerProductSpace.gramSchmidtNormed ℂ b) :=
    InnerProductSpace.gramSchmidtNormed_orthonormal b.linearIndependent
  have hinner := orthonormal_iff_ite.mp horth j k
  change (G *ᵥ InnerProductSpace.gramSchmidtNormed ℂ b k) ⬝ᵥ
      star (InnerProductSpace.gramSchmidtNormed ℂ b j) =
        (if j = k then 1 else 0) at hinner
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

/-- The canonical inverse frame is lower triangular. -/
theorem gramSchmidtInverseFrame_lowerTriangular
    {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) :
    (gramSchmidtInverseFrame G hG).BlockTriangular
      (fun i : Fin N => OrderDual.toDual i) := by
  let normInst := Matrix.toNormedAddCommGroup G hG
  letI : NormedAddCommGroup (Fin N → ℂ) := normInst
  letI : SeminormedAddCommGroup (Fin N → ℂ) := normInst.toSeminormedAddCommGroup
  letI := Matrix.toInnerProductSpace G hG.posSemidef
  letI := FiniteDimensional.complete ℂ (Fin N → ℂ)
  let b : Module.Basis (Fin N) ℂ (Fin N → ℂ) := Pi.basisFun ℂ (Fin N)
  intro i j hij
  change star (InnerProductSpace.gramSchmidtNormed ℂ b i j) = 0
  rw [star_eq_zero]
  have htri := InnerProductSpace.gramSchmidt_triangular
    (OrderDual.toDual_lt_toDual.mp hij) b
  rw [Pi.basisFun_repr] at htri
  simp [InnerProductSpace.gramSchmidtNormed, htri]

/-- Every diagonal entry of the canonical inverse frame is a positive real number. -/
theorem gramSchmidtInverseFrame_diag_pos
    {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) (i : Fin N) :
    0 < (gramSchmidtInverseFrame G hG i i).re := by
  let normInst := Matrix.toNormedAddCommGroup G hG
  letI : NormedAddCommGroup (Fin N → ℂ) := normInst
  letI : SeminormedAddCommGroup (Fin N → ℂ) := normInst.toSeminormedAddCommGroup
  letI := Matrix.toInnerProductSpace G hG.posSemidef
  letI := FiniteDimensional.complete ℂ (Fin N → ℂ)
  let b : Module.Basis (Fin N) ℂ (Fin N → ℂ) := Pi.basisFun ℂ (Fin N)
  change 0 < (star (InnerProductSpace.gramSchmidtNormed ℂ b i i)).re
  have hdiag : InnerProductSpace.gramSchmidt ℂ b i i = 1 := by
    have hdef := congrFun (InnerProductSpace.gramSchmidt_def'' ℂ b i) i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hdef
    have hzero : ∀ k ∈ Finset.Iio i,
        InnerProductSpace.gramSchmidt ℂ b k i = 0 := by
      intro k hk
      have htri := InnerProductSpace.gramSchmidt_triangular (Finset.mem_Iio.mp hk) b
      rw [Pi.basisFun_repr] at htri
      exact htri
    rw [Finset.sum_eq_zero (fun k hk => by rw [hzero k hk, mul_zero]), add_zero] at hdef
    simpa [b, Pi.basisFun_apply] using hdef.symm
  have hne : InnerProductSpace.gramSchmidt ℂ b i ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero i b.linearIndependent
  rw [InnerProductSpace.gramSchmidtNormed, Pi.smul_apply, hdiag, smul_eq_mul, mul_one,
    RCLike.star_def]
  have hnorm : 0 < @norm (Fin N → ℂ) normInst.toNorm
      (InnerProductSpace.gramSchmidt ℂ b i) := by
    exact (@norm_pos_iff (Fin N → ℂ) normInst.toNormedAddGroup _).mpr hne
  rw [Complex.conj_re, Complex.inv_re]
  norm_num [Complex.normSq_apply]
  exact hnorm

/-- Every diagonal entry of the canonical inverse frame is real. Together with
`gramSchmidtInverseFrame_diag_pos`, this is the positive-diagonal Cholesky normalization. -/
theorem gramSchmidtInverseFrame_diag_im_zero
    {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) (i : Fin N) :
    (gramSchmidtInverseFrame G hG i i).im = 0 := by
  let normInst := Matrix.toNormedAddCommGroup G hG
  letI : NormedAddCommGroup (Fin N → ℂ) := normInst
  letI : SeminormedAddCommGroup (Fin N → ℂ) := normInst.toSeminormedAddCommGroup
  letI := Matrix.toInnerProductSpace G hG.posSemidef
  letI := FiniteDimensional.complete ℂ (Fin N → ℂ)
  let b : Module.Basis (Fin N) ℂ (Fin N → ℂ) := Pi.basisFun ℂ (Fin N)
  change (star (InnerProductSpace.gramSchmidtNormed ℂ b i i)).im = 0
  have hdiag : InnerProductSpace.gramSchmidt ℂ b i i = 1 := by
    have hdef := congrFun (InnerProductSpace.gramSchmidt_def'' ℂ b i) i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hdef
    have hzero : ∀ k ∈ Finset.Iio i,
        InnerProductSpace.gramSchmidt ℂ b k i = 0 := by
      intro k hk
      have htri := InnerProductSpace.gramSchmidt_triangular (Finset.mem_Iio.mp hk) b
      rw [Pi.basisFun_repr] at htri
      exact htri
    rw [Finset.sum_eq_zero (fun k hk => by rw [hzero k hk, mul_zero]), add_zero] at hdef
    simpa [b, Pi.basisFun_apply] using hdef.symm
  rw [InnerProductSpace.gramSchmidtNormed, Pi.smul_apply, hdiag, smul_eq_mul, mul_one,
    RCLike.star_def, Complex.conj_im, Complex.inv_im]
  norm_num [Complex.normSq_apply]

/-- Structural predicate for a canonical inverse-Cholesky frame: inverse Gram orthonormalization,
lower triangularity, and positive real diagonal. -/
def IsCanonicalInverseCholeskyFrame
    {N : ℕ} (C G : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsInverseCholeskyFrame C G ∧
    C.BlockTriangular (fun i : Fin N => OrderDual.toDual i) ∧
      ∀ i, (C i i).im = 0 ∧ 0 < (C i i).re

/-- The normalized Gram--Schmidt construction is a canonical inverse-Cholesky frame. -/
theorem gramSchmidtInverseFrame_isCanonical
    {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) :
    IsCanonicalInverseCholeskyFrame (gramSchmidtInverseFrame G hG) G := by
  exact ⟨gramSchmidtInverseFrame_isInverseCholeskyFrame G hG,
    gramSchmidtInverseFrame_lowerTriangular G hG,
    fun i => ⟨gramSchmidtInverseFrame_diag_im_zero G hG i,
      gramSchmidtInverseFrame_diag_pos G hG i⟩⟩

/-- Every positive-definite finite complex Gram matrix admits a canonical inverse-Cholesky frame. -/
theorem exists_canonicalInverseCholeskyFrame_of_posDef
    {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) :
    ∃ C : Matrix (Fin N) (Fin N) ℂ, IsCanonicalInverseCholeskyFrame C G :=
  ⟨gramSchmidtInverseFrame G hG, gramSchmidtInverseFrame_isCanonical G hG⟩

/-- Every finite positive-definite complex Gram matrix admits a lower-triangular inverse frame with
positive real diagonal. -/
theorem exists_inverseCholeskyFrame_of_posDef
    {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) :
    ∃ C : Matrix (Fin N) (Fin N) ℂ, IsInverseCholeskyFrame C G := by
  exact ⟨gramSchmidtInverseFrame G hG,
    gramSchmidtInverseFrame_isInverseCholeskyFrame G hG⟩

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

/-- A lower-triangular unitary matrix with positive real diagonal is the identity. -/
theorem lowerTriangular_unitary_pos_diag_eq_one
    {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (htri : U.BlockTriangular (fun i : Fin N => OrderDual.toDual i))
    (hunit : U * Uᴴ = 1)
    (hdiag : ∀ i, (U i i).im = 0 ∧ 0 < (U i i).re) :
    U = 1 := by
  have hcol_nat : ∀ n : ℕ, (hn : n < N) → ∀ j : Fin N,
      U j ⟨n, hn⟩ = if j.val = n then 1 else 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn j
        let i : Fin N := ⟨n, hn⟩
        have hrowzero : ∀ k : Fin N, k ≠ i → U i k = 0 := by
          intro k hki
          rcases lt_or_gt_of_ne hki with hlt | hgt
          · have hk := ih k.val hlt k.isLt i
            have hnk : n ≠ k.val := (Fin.mk_lt_mk.mp hlt).ne'
            simpa [i, hnk] using hk
          · exact htri (by simpa [i] using hgt)
        have hiiEntry := congrFun (congrFun hunit i) i
        simp only [Matrix.mul_apply, Matrix.one_apply, if_pos] at hiiEntry
        have hiiProd : U i i * star (U i i) = 1 := by
          rw [Finset.sum_eq_single i] at hiiEntry
          · simpa using hiiEntry
          · intro k hk hki
            rw [hrowzero k hki, zero_mul]
          · intro hi
            simp at hi
        have hii : U i i = 1 := by
          apply Complex.ext
          · have hre := congrArg Complex.re hiiProd
            have hz := (hdiag i).1
            have hp := (hdiag i).2
            simp [Complex.mul_re, RCLike.star_def, hz] at hre
            change (U i i).re = 1
            nlinarith
          · simpa using (hdiag i).1
        by_cases hji : j = i
        · subst j
          rw [hii, if_pos rfl]
        · have hvalne : j.val ≠ n := by simpa [i, Fin.ext_iff] using hji
          rw [if_neg hvalne]
          rcases lt_or_gt_of_ne hji with hjlt | hjgt
          · exact htri (by simpa [i] using hjlt)
          · have hjiEntry := congrFun (congrFun hunit j) i
            rw [Matrix.mul_apply, Matrix.one_apply, if_neg hji] at hjiEntry
            rw [Finset.sum_eq_single i] at hjiEntry
            · simpa [hii] using hjiEntry
            · intro k hk hki
              rw [Matrix.conjTranspose_apply, hrowzero k hki, star_zero, mul_zero]
            · intro hi
              simp at hi
  ext j i
  have h := hcol_nat i.val i.isLt j
  simpa [Matrix.one_apply, Fin.ext_iff] using h

/-- The diagonal of a product of two lower-triangular matrices is the product of their
diagonals. -/
theorem lowerTriangular_mul_apply_diag
    {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.BlockTriangular (fun i : Fin N => OrderDual.toDual i))
    (hB : B.BlockTriangular (fun i : Fin N => OrderDual.toDual i)) (i : Fin N) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k hk hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hB (by simpa using hlt), mul_zero]
    · rw [hA (by simpa using hgt), zero_mul]
  · intro hi
    simp at hi

/-- Canonical inverse-Cholesky frames are structurally unique: any two lower-triangular
positive-real-diagonal matrices orthonormalizing the same Gram matrix coincide. -/
theorem canonicalInverseCholeskyFrame_unique
    {N : ℕ} (G C₁ C₂ : Matrix (Fin N) (Fin N) ℂ)
    (h₁ : IsCanonicalInverseCholeskyFrame C₁ G)
    (h₂ : IsCanonicalInverseCholeskyFrame C₂ G) :
    C₁ = C₂ := by
  have hC₁right : C₁ * (G * C₁ᴴ) = 1 := by
    simpa [IsInverseCholeskyFrame, mul_assoc] using h₁.1
  have hC₁det : IsUnit C₁.det := Matrix.isUnit_det_of_right_inverse hC₁right
  letI : Invertible C₁ := Matrix.invertibleOfIsUnitDet C₁ hC₁det
  let U : Matrix (Fin N) (Fin N) ℂ := C₂ * C₁⁻¹
  have htriInv : C₁⁻¹.BlockTriangular (fun i : Fin N => OrderDual.toDual i) :=
    Matrix.blockTriangular_inv_of_blockTriangular h₁.2.1
  have htriU : U.BlockTriangular (fun i : Fin N => OrderDual.toDual i) :=
    h₂.2.1.mul htriInv
  have hUC : U * C₁ = C₂ := by
    unfold U
    calc
      (C₂ * C₁⁻¹) * C₁ = C₂ * (C₁⁻¹ * C₁) := by rw [mul_assoc]
      _ = C₂ := by rw [Matrix.inv_mul_of_invertible]; simp
  have hstar : (U * C₁)ᴴ = C₁ᴴ * Uᴴ := Matrix.conjTranspose_mul U C₁
  have hunit : U * Uᴴ = 1 := by
    calc
      U * Uᴴ = U * 1 * Uᴴ := by simp
      _ = U * (C₁ * G * C₁ᴴ) * Uᴴ := by rw [h₁.1]
      _ = (U * C₁) * G * (U * C₁)ᴴ := by
        rw [hstar]
        simp only [mul_assoc]
      _ = C₂ * G * C₂ᴴ := by rw [hUC]
      _ = 1 := h₂.1
  have hdiagU : ∀ i, (U i i).im = 0 ∧ 0 < (U i i).re := by
    intro i
    have hdiagEq : U i i * C₁ i i = C₂ i i := by
      rw [← lowerTriangular_mul_apply_diag htriU h₁.2.1 i, hUC]
    have hImEq := congrArg Complex.im hdiagEq
    have hReEq := congrArg Complex.re hdiagEq
    rcases h₁.2.2 i with ⟨h₁im, h₁pos⟩
    rcases h₂.2.2 i with ⟨h₂im, h₂pos⟩
    constructor
    · simp [Complex.mul_im, h₁im, h₂im] at hImEq
      exact hImEq.resolve_right (ne_of_gt h₁pos)
    · simp [Complex.mul_re, h₁im] at hReEq
      nlinarith
  have hU : U = 1 := lowerTriangular_unitary_pos_diag_eq_one U htriU hunit hdiagU
  have h := hUC
  rw [hU, one_mul] at h
  exact h

/-- Determinant form of inverse-Cholesky orthonormalization. This is the algebraic source of the
finite determinant repair law. -/
theorem det_identity_of_inverseCholesky (C G : Matrix n n ℂ)
    (h : IsInverseCholeskyFrame C G) :
    C.det * G.det * star C.det = 1 := by
  have hdet := congrArg Matrix.det h
  simpa [Matrix.det_mul, Matrix.det_conjTranspose] using hdet

/-- A canonical lower-triangular inverse-Cholesky frame has positive real determinant. -/
theorem canonicalInverseCholesky_det_pos
    {N : ℕ} (C G : Matrix (Fin N) (Fin N) ℂ)
    (h : IsCanonicalInverseCholeskyFrame C G) :
    0 < C.det.re ∧ C.det.im = 0 := by
  rw [Matrix.det_of_lowerTriangular C h.2.1]
  have hdiag (i : Fin N) : C i i = ((C i i).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using (h.2.2 i).1
  have hprod : (∏ i, C i i) = ((∏ i, (C i i).re : ℝ) : ℂ) := by
    calc
      (∏ i, C i i) = ∏ i, ((C i i).re : ℂ) :=
        Finset.prod_congr rfl fun i _ => hdiag i
      _ = ((∏ i, (C i i).re : ℝ) : ℂ) := by norm_cast
  rw [hprod]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.prod_pos fun i _ => (h.2.2 i).2, trivial⟩

/-- For the canonical normalization, the determinant identity is exactly
`det G * (det C)^2 = 1`. -/
theorem canonicalInverseCholesky_det_square_mul
    {N : ℕ} (C G : Matrix (Fin N) (Fin N) ℂ)
    (h : IsCanonicalInverseCholeskyFrame C G) :
    G.det * C.det ^ 2 = 1 := by
  have hid := det_identity_of_inverseCholesky C G h.1
  have hreal := (canonicalInverseCholesky_det_pos C G h).2
  have hstar : star C.det = C.det := by
    apply Complex.ext
    · simp
    · simp [hreal]
  rw [hstar, mul_comm C.det G.det] at hid
  calc
    G.det * C.det ^ 2 = G.det * C.det * C.det := by ring
    _ = 1 := hid

/-- Exact positive-root form of the inverse-Cholesky determinant law:
`det C = (det G)⁻¹ᐟ²`. Since both determinants are real and positive, the statement is expressed
on real parts. -/
theorem canonicalInverseCholesky_det_eq_inv_sqrt
    {N : ℕ} (C G : Matrix (Fin N) (Fin N) ℂ)
    (hG : G.PosDef) (h : IsCanonicalInverseCholeskyFrame C G) :
    C.det.re = (G.det.re)⁻¹.sqrt := by
  have hgpos := hG.det_pos
  simp only [Complex.lt_def, Complex.zero_re, Complex.zero_im] at hgpos
  have hgim : G.det.im = 0 := hgpos.2.symm
  have hc := canonicalInverseCholesky_det_pos C G h
  have hid := canonicalInverseCholesky_det_square_mul C G h
  have hre := congrArg Complex.re hid
  rw [pow_two] at hre
  simp [Complex.mul_re, hgim, hc.2] at hre
  have hsqrt_nonneg : 0 ≤ (G.det.re)⁻¹.sqrt := Real.sqrt_nonneg _
  have hsqrt_sq : (G.det.re)⁻¹.sqrt ^ 2 = (G.det.re)⁻¹ := by
    rw [Real.sq_sqrt]
    exact inv_nonneg.mpr hgpos.1.le
  have hg_ne : G.det.re ≠ 0 := ne_of_gt hgpos.1
  apply (sq_eq_sq₀ (le_of_lt hc.1) hsqrt_nonneg).mp
  rw [hsqrt_sq, inv_eq_one_div]
  apply (eq_div_iff hg_ne).2
  nlinarith

/-- Leading principal restriction from level `N+1` to level `N`. -/
def leadingPrincipalSubmatrix {N : ℕ}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  M.submatrix Fin.castSucc Fin.castSucc

/-- The leading principal restriction of a canonical inverse-Cholesky frame remains canonical for
the leading principal Gram block. -/
theorem leadingPrincipalSubmatrix_isCanonical
    {N : ℕ} (C G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (h : IsCanonicalInverseCholeskyFrame C G) :
    IsCanonicalInverseCholeskyFrame
      (leadingPrincipalSubmatrix C) (leadingPrincipalSubmatrix G) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsInverseCholeskyFrame leadingPrincipalSubmatrix
    ext i j
    have hbig := congrFun (congrFun h.1 i.castSucc) j.castSucc
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Matrix.submatrix_apply, Fin.castSucc_inj] at hbig ⊢
    rw [Fin.sum_univ_castSucc] at hbig
    simp_rw [Fin.sum_univ_castSucc] at hbig
    have hiLast : C i.castSucc (Fin.last N) = 0 := by
      apply h.2.1
      simp
    have hjLast : C j.castSucc (Fin.last N) = 0 := by
      apply h.2.1
      simp
    simp [hiLast, hjLast] at hbig
    exact hbig
  · intro i j hij
    exact h.2.1 hij
  · intro i
    exact h.2.2 i.castSucc

/-- Normalized Gram--Schmidt inverse-Cholesky frames are compatible under leading-principal
restriction. Thus the canonical finite frames form a coherent tower. -/
theorem gramSchmidtInverseFrame_leadingPrincipal
    {N : ℕ} (G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (hG : G.PosDef) :
    leadingPrincipalSubmatrix (gramSchmidtInverseFrame G hG) =
      gramSchmidtInverseFrame (leadingPrincipalSubmatrix G)
        (hG.submatrix (Fin.castSucc_injective N)) := by
  apply canonicalInverseCholeskyFrame_unique (leadingPrincipalSubmatrix G)
  · exact leadingPrincipalSubmatrix_isCanonical _ _
      (gramSchmidtInverseFrame_isCanonical G hG)
  · exact gramSchmidtInverseFrame_isCanonical _ _

/-- For the canonical normalized Gram--Schmidt construction, equality of inverse-Cholesky frames
is equivalent to equality of the underlying positive-definite Gram matrices. -/
theorem gramSchmidtInverseFrame_eq_iff_gram_eq
    {N : ℕ} (G₁ G₂ : Matrix (Fin N) (Fin N) ℂ)
    (h₁ : G₁.PosDef) (h₂ : G₂.PosDef) :
    gramSchmidtInverseFrame G₁ h₁ = gramSchmidtInverseFrame G₂ h₂ ↔ G₁ = G₂ := by
  constructor
  · intro hC
    have hframe₁ := gramSchmidtInverseFrame_isInverseCholeskyFrame G₁ h₁
    have hframe₂ := gramSchmidtInverseFrame_isInverseCholeskyFrame G₂ h₂
    rw [← hC] at hframe₂
    exact gram_eq_of_same_inverseCholesky _ G₁ G₂ hframe₁ hframe₂
  · intro hG
    subst G₂
    rfl

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix
open scoped ComplexOrder

noncomputable section

/-!
## Complete scalar capacity realization, including zero increments

The diagonal realization later in this module requires every innovation to be strictly positive.  The following
lower-triangular frame keeps a positive diagonal while allowing arbitrary later row sums.  It
therefore realizes every positive monotone capacity profile, including profiles with flat steps.
-/

/-- The positive Gram matrix induced by an invertible inverse-Cholesky frame. -/
def gramOfInvertibleFrame {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) : Matrix n n ℂ :=
  C⁻¹ * (C⁻¹)ᴴ

theorem gramOfInvertibleFrame_posDef {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (hC : IsUnit C) :
    (gramOfInvertibleFrame C).PosDef := by
  have hInv : IsUnit C⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hC
  simpa [gramOfInvertibleFrame] using
    (Matrix.PosDef.one.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit hInv))

theorem frame_isInverseCholesky_gramOfInvertibleFrame
    {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℂ) (hC : IsUnit C) :
    IsInverseCholeskyFrame C (gramOfInvertibleFrame C) := by
  have hdet : IsUnit C.det := C.isUnit_iff_isUnit_det.mp hC
  unfold IsInverseCholeskyFrame gramOfInvertibleFrame
  calc
    C * (C⁻¹ * (C⁻¹)ᴴ) * Cᴴ = (C * C⁻¹) * (C⁻¹)ᴴ * Cᴴ := by
      simp only [Matrix.mul_assoc]
    _ = (C⁻¹)ᴴ * Cᴴ := by rw [C.mul_nonsing_inv hdet, Matrix.one_mul]
    _ = (C * C⁻¹)ᴴ := by rw [Matrix.conjTranspose_mul]
    _ = 1 := by rw [C.mul_nonsing_inv hdet, Matrix.conjTranspose_one]

/-- A lower-triangular frame whose row sums are an arbitrary real packet.  Its diagonal stays
positive when the zeroth packet entry is positive, even if any later row sum vanishes. -/
def arbitraryInnovationFrame {N : ℕ} (eta : Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j => (if i = j then 1 else 0) +
    if j = 0 then ((eta i - 1 : ℝ) : ℂ) else 0

theorem arbitraryInnovationFrame_lowerTriangular {N : ℕ}
    (eta : Fin (N + 1) → ℝ) :
    (arbitraryInnovationFrame eta).BlockTriangular
      (fun i : Fin (N + 1) => OrderDual.toDual i) := by
  intro i j hij
  have hij' : i < j := hij
  have hji : j ≠ i := ne_of_gt hij'
  have hj0 : j ≠ 0 := by
    intro hj
    subst j
    exact (Fin.not_lt_zero i) hij'
  simp only [arbitraryInnovationFrame]
  simp [Ne.symm hji, hj0]

theorem arbitraryInnovationFrame_diag_pos {N : ℕ}
    (eta : Fin (N + 1) → ℝ) (heta0 : 0 < eta 0) (i : Fin (N + 1)) :
    (arbitraryInnovationFrame eta i i).im = 0 ∧
      0 < (arbitraryInnovationFrame eta i i).re := by
  by_cases hi : i = 0
  · subst i
    simp [arbitraryInnovationFrame, heta0]
  · simp [arbitraryInnovationFrame, hi]

theorem arbitraryInnovationFrame_isUnit {N : ℕ}
    (eta : Fin (N + 1) → ℝ) (heta0 : 0 < eta 0) :
    IsUnit (arbitraryInnovationFrame eta) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [Matrix.det_of_lowerTriangular _
    (arbitraryInnovationFrame_lowerTriangular eta)]
  rw [isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    Complex.ne_zero_of_re_pos (arbitraryInnovationFrame_diag_pos eta heta0 i).2

theorem arbitraryInnovationFrame_isCanonical {N : ℕ}
    (eta : Fin (N + 1) → ℝ) (heta0 : 0 < eta 0) :
    IsCanonicalInverseCholeskyFrame
      (arbitraryInnovationFrame eta)
      (gramOfInvertibleFrame (arbitraryInnovationFrame eta)) := by
  refine ⟨frame_isInverseCholesky_gramOfInvertibleFrame _
    (arbitraryInnovationFrame_isUnit eta heta0),
    arbitraryInnovationFrame_lowerTriangular eta, ?_⟩
  intro i
  exact arbitraryInnovationFrame_diag_pos eta heta0 i

theorem arbitraryInnovationFrame_amplitude {N : ℕ}
    (eta : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    inverseCholeskyUnitAmplitude (arbitraryInnovationFrame eta) i = eta i := by
  classical
  simp [inverseCholeskyUnitAmplitude, arbitraryInnovationFrame,
    Finset.sum_add_distrib]

theorem arbitraryInnovationFrame_capacity {N : ℕ}
    (eta : Fin (N + 1) → ℝ) :
    inverseCholeskyUnitCapacity (arbitraryInnovationFrame eta) =
      ∑ i, eta i ^ 2 := by
  unfold inverseCholeskyUnitCapacity
  apply Finset.sum_congr rfl
  intro i hi
  rw [arbitraryInnovationFrame_amplitude]
  simp [Real.norm_eq_abs, sq_abs]

/-- Coherent inverse-Cholesky frames with an arbitrary prescribed real innovation sequence. -/
def arbitraryInnovationTower (eta : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  arbitraryInnovationFrame fun i => eta i

/-- The positive Gram tower induced by `arbitraryInnovationTower`. -/
def arbitraryInnovationGramTower (eta : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  gramOfInvertibleFrame (arbitraryInnovationTower eta N)

theorem arbitraryInnovationTower_coherent (eta : ℕ → ℝ) (N : ℕ) :
    leadingPrincipalSubmatrix (arbitraryInnovationTower eta (N + 1)) =
      arbitraryInnovationTower eta N := by
  ext i j
  simp [leadingPrincipalSubmatrix, arbitraryInnovationTower,
    arbitraryInnovationFrame]

theorem arbitraryInnovationGramTower_posDef (eta : ℕ → ℝ)
    (heta0 : 0 < eta 0) (N : ℕ) :
    (arbitraryInnovationGramTower eta N).PosDef :=
  gramOfInvertibleFrame_posDef _
    (arbitraryInnovationFrame_isUnit (fun i : Fin (N + 1) => eta i) heta0)

theorem arbitraryInnovationTower_isCanonical (eta : ℕ → ℝ)
    (heta0 : 0 < eta 0) (N : ℕ) :
    IsCanonicalInverseCholeskyFrame
      (arbitraryInnovationTower eta N) (arbitraryInnovationGramTower eta N) :=
  arbitraryInnovationFrame_isCanonical _ heta0

theorem arbitraryInnovationGramTower_coherent (eta : ℕ → ℝ)
    (heta0 : 0 < eta 0) (N : ℕ) :
    leadingPrincipalSubmatrix (arbitraryInnovationGramTower eta (N + 1)) =
      arbitraryInnovationGramTower eta N := by
  apply gram_eq_of_same_inverseCholesky (arbitraryInnovationTower eta N)
  · rw [← arbitraryInnovationTower_coherent eta N]
    exact (leadingPrincipalSubmatrix_isCanonical _ _
      (arbitraryInnovationTower_isCanonical eta heta0 (N + 1))).1
  · exact (arbitraryInnovationTower_isCanonical eta heta0 N).1

theorem arbitraryInnovationTower_innovation (eta : ℕ → ℝ) (N : ℕ) :
    coherentClockInnovation (arbitraryInnovationTower eta) N = eta N :=
  arbitraryInnovationFrame_amplitude _ (Fin.last N)

theorem arbitraryInnovationTower_capacity (eta : ℕ → ℝ) (N : ℕ) :
    inverseCholeskyUnitCapacity (arbitraryInnovationTower eta N) =
      ∑ i : Fin (N + 1), eta i ^ 2 :=
  arbitraryInnovationFrame_capacity _

/-- Innovation sequence whose cumulative squared mass is a prescribed monotone capacity. -/
def monotoneCapacityInnovation (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => Real.sqrt (q 0)
  | n + 1 => Real.sqrt (q (n + 1) - q n)

theorem monotoneCapacityInnovation_zero_pos (q : ℕ → ℝ) (hq0 : 0 < q 0) :
    0 < monotoneCapacityInnovation q 0 := by
  simpa [monotoneCapacityInnovation] using Real.sqrt_pos.2 hq0

theorem sum_monotoneCapacityInnovation_sq (q : ℕ → ℝ)
    (hq0 : 0 < q 0) (hq : Monotone q) (N : ℕ) :
    ∑ i : Fin (N + 1), monotoneCapacityInnovation q i ^ 2 = q N := by
  induction N with
  | zero =>
      simp [monotoneCapacityInnovation, Real.sq_sqrt hq0.le]
  | succ N ih =>
      rw [Fin.sum_univ_castSucc]
      have hprefix :
          (∑ i : Fin (N + 1), monotoneCapacityInnovation q i.castSucc ^ 2) = q N := by
        simpa using ih
      rw [hprefix]
      simp [monotoneCapacityInnovation,
        Real.sq_sqrt (sub_nonneg.mpr (hq (Nat.le_succ N)))]

/-- **Complete scalar capacity realization.**  Every positive monotone capacity profile is the
exact capacity path of a coherent positive Gram clock, including profiles with zero increments. -/
theorem monotoneCapacity_realized (q : ℕ → ℝ)
    (hq0 : 0 < q 0) (hq : Monotone q) (N : ℕ) :
    inverseCholeskyUnitCapacity
        (arbitraryInnovationTower (monotoneCapacityInnovation q) N) = q N := by
  rw [arbitraryInnovationTower_capacity,
    sum_monotoneCapacityInnovation_sq q hq0 hq N]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix
open scoped ComplexOrder

noncomputable section

/-- **Clock-capacity increment law.**  For a lower-triangular inverse frame, adjoining one clock
constraint adds exactly the squared norm of the new row's unit-packet amplitude. -/
theorem inverseCholeskyUnitCapacity_succ
    {N : ℕ} (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (htri : C.BlockTriangular (fun i : Fin (N + 1) => OrderDual.toDual i)) :
    inverseCholeskyUnitCapacity C =
      inverseCholeskyUnitCapacity (leadingPrincipalSubmatrix C) +
        ‖inverseCholeskyUnitAmplitude C (Fin.last N)‖ ^ 2 := by
  unfold inverseCholeskyUnitCapacity
  rw [Fin.sum_univ_castSucc]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  unfold inverseCholeskyUnitAmplitude leadingPrincipalSubmatrix
  rw [Fin.sum_univ_castSucc]
  have hzero : C i.castSucc (Fin.last N) = 0 := by
    apply htri
    simp
  simp [hzero]

/-- The canonical positive inverse-Cholesky tower obeys the exact clock-capacity increment law. -/
theorem gramSchmidtInverseFrame_unitCapacity_succ
    {N : ℕ} (G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (hG : G.PosDef) :
    inverseCholeskyUnitCapacity (gramSchmidtInverseFrame G hG) =
      inverseCholeskyUnitCapacity
        (gramSchmidtInverseFrame (leadingPrincipalSubmatrix G)
          (hG.submatrix (Fin.castSucc_injective N))) +
      ‖inverseCholeskyUnitAmplitude (gramSchmidtInverseFrame G hG) (Fin.last N)‖ ^ 2 := by
  rw [← gramSchmidtInverseFrame_leadingPrincipal G hG]
  exact inverseCholeskyUnitCapacity_succ _
    (gramSchmidtInverseFrame_lowerTriangular G hG)

/-- New clock capacity is monotone under leading-principal extension. -/
theorem inverseCholeskyUnitCapacity_le_succ
    {N : ℕ} (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (htri : C.BlockTriangular (fun i : Fin (N + 1) => OrderDual.toDual i)) :
    inverseCholeskyUnitCapacity (leadingPrincipalSubmatrix C) ≤
      inverseCholeskyUnitCapacity C := by
  rw [inverseCholeskyUnitCapacity_succ C htri]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- **Clock-capacity decomposition.**  In every coherent lower-triangular frame tower, the finite
unit-boundary capacity is exactly the cumulative squared innovation amplitude. -/
theorem coherentClockUnitCapacity_eq_sum_innovations
    (C : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (htri : ∀ N, (C N).BlockTriangular
      (fun i : Fin (N + 1) => OrderDual.toDual i))
    (hcoh : ∀ N, leadingPrincipalSubmatrix (C (N + 1)) = C N) :
    ∀ N, inverseCholeskyUnitCapacity (C N) =
      ∑ n ∈ Finset.range (N + 1), ‖coherentClockInnovation C n‖ ^ 2 := by
  intro N
  induction N with
  | zero =>
      simp [inverseCholeskyUnitCapacity, inverseCholeskyUnitAmplitude,
        coherentClockInnovation]
  | succ N ih =>
      rw [inverseCholeskyUnitCapacity_succ (C (N + 1)) (htri (N + 1))]
      rw [hcoh N, ih, Finset.sum_range_succ]
      simp [Finset.sum_range_succ, coherentClockInnovation, add_assoc]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix

noncomputable section

section UnitBoundaryCapacity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The finite inverse-frame vector obtained from one row of `C` and the original clock modes. -/
def inverseCholeskyFrameVector {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (u : Fin N → E) (i : Fin N) : E :=
  ∑ j, C i j • u j

/-- Unit response against the original clock packet becomes the conjugate canonical innovation
amplitude against its inverse-Cholesky frame. -/
theorem inner_inverseCholeskyFrameVector_unitResponse
    {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (u : Fin N → E) (y : E)
    (hy : ∀ j, inner ℂ (u j) y = 1) (i : Fin N) :
    inner ℂ (inverseCholeskyFrameVector C u i) y =
      star (inverseCholeskyUnitAmplitude C i) := by
  simp [inverseCholeskyFrameVector, inverseCholeskyUnitAmplitude, hy]

/-- **Normal-boundary capacity bound.**  If the inverse-Cholesky clock modes are orthonormal, every
normal vector realizing the finite unit response packet bounds the canonical clock capacity by its
squared norm.  Hence one global normal boundary uniformly bounds the entire coherent capacity
tower. -/
theorem inverseCholeskyUnitCapacity_le_norm_sq_of_orthonormal_unitResponse
    {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (u : Fin N → E) (y : E)
    (horth : Orthonormal ℂ (inverseCholeskyFrameVector C u))
    (hy : ∀ j, inner ℂ (u j) y = 1) :
    inverseCholeskyUnitCapacity C ≤ ‖y‖ ^ 2 := by
  have hbound := horth.sum_inner_products_le y (s := Finset.univ)
  simpa [inverseCholeskyUnitCapacity,
    inner_inverseCholeskyFrameVector_unitResponse C u y hy] using hbound

end UnitBoundaryCapacity

section CapacityRealization

open scoped ComplexOrder

/-- Canonical diagonal inverse frame realizing a prescribed positive innovation packet. -/
def prescribedPositiveInnovationFrame {N : ℕ} (eta : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal fun i => (eta i : ℂ)

/-- Positive diagonal Gram matrix paired with the prescribed innovation frame. -/
def prescribedPositiveInnovationGram {N : ℕ} (eta : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => (((eta i)⁻¹ ^ 2 : ℝ) : ℂ)

/-- Every strictly positive innovation packet defines a positive-definite Gram clock. -/
theorem prescribedPositiveInnovationGram_posDef {N : ℕ} (eta : Fin N → ℝ)
    (heta : ∀ i, 0 < eta i) :
    (prescribedPositiveInnovationGram eta).PosDef := by
  rw [prescribedPositiveInnovationGram, Matrix.posDef_diagonal_iff]
  intro i
  rw [Complex.zero_lt_real]
  exact sq_pos_of_pos (inv_pos.mpr (heta i))

/-- The prescribed positive diagonal frame is the canonical inverse-Cholesky frame of its Gram
clock. -/
theorem prescribedPositiveInnovationFrame_isCanonical {N : ℕ} (eta : Fin N → ℝ)
    (heta : ∀ i, 0 < eta i) :
    IsCanonicalInverseCholeskyFrame
      (prescribedPositiveInnovationFrame eta)
      (prescribedPositiveInnovationGram eta) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsInverseCholeskyFrame prescribedPositiveInnovationFrame
      prescribedPositiveInnovationGram
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hne : (eta i : ℂ) ≠ 0 := by exact_mod_cast (heta i).ne'
    rw [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    change (eta i : ℂ) * (((eta i)⁻¹ ^ 2 : ℝ) : ℂ) * (eta i : ℂ) = 1
    norm_cast
    field_simp [(heta i).ne']
  · intro i j hij
    have hne : i ≠ j := by
      intro h
      subst j
      exact (lt_irrefl _ hij)
    simp [prescribedPositiveInnovationFrame, Matrix.diagonal, hne]
  · intro i
    simp [prescribedPositiveInnovationFrame, heta i]

/-- The normalized Gram--Schmidt construction recovers the prescribed innovation frame exactly. -/
theorem gramSchmidtInverseFrame_prescribedPositiveInnovation {N : ℕ}
    (eta : Fin N → ℝ) (heta : ∀ i, 0 < eta i) :
    gramSchmidtInverseFrame (prescribedPositiveInnovationGram eta)
        (prescribedPositiveInnovationGram_posDef eta heta) =
      prescribedPositiveInnovationFrame eta := by
  apply canonicalInverseCholeskyFrame_unique (prescribedPositiveInnovationGram eta)
  · exact gramSchmidtInverseFrame_isCanonical _ _
  · exact prescribedPositiveInnovationFrame_isCanonical eta heta

/-- The unit-packet innovation of the prescribed frame is exactly the requested value. -/
theorem prescribedPositiveInnovationFrame_amplitude {N : ℕ} (eta : Fin N → ℝ)
    (i : Fin N) :
    inverseCholeskyUnitAmplitude (prescribedPositiveInnovationFrame eta) i = eta i := by
  classical
  unfold inverseCholeskyUnitAmplitude prescribedPositiveInnovationFrame
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Matrix.diagonal, Ne.symm hbi]
  · simp

/-- The capacity of a prescribed positive innovation packet is its exact squared `ℓ²` mass. -/
theorem prescribedPositiveInnovationFrame_capacity {N : ℕ} (eta : Fin N → ℝ)
    (heta : ∀ i, 0 < eta i) :
    inverseCholeskyUnitCapacity (prescribedPositiveInnovationFrame eta) =
      ∑ i, eta i ^ 2 := by
  unfold inverseCholeskyUnitCapacity
  apply Finset.sum_congr rfl
  intro i hi
  rw [prescribedPositiveInnovationFrame_amplitude]
  simp [Real.norm_eq_abs, abs_of_pos (heta i)]

/-- Coherent diagonal clock tower with an arbitrary prescribed positive innovation sequence. -/
def prescribedPositiveInnovationTower (eta : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  prescribedPositiveInnovationFrame fun i => eta i

/-- Every level of the prescribed tower is lower triangular. -/
theorem prescribedPositiveInnovationTower_lowerTriangular
    (eta : ℕ → ℝ) (heta : ∀ n, 0 < eta n) (N : ℕ) :
    (prescribedPositiveInnovationTower eta N).BlockTriangular
      (fun i : Fin (N + 1) => OrderDual.toDual i) :=
  (prescribedPositiveInnovationFrame_isCanonical
    (fun i : Fin (N + 1) => eta i) (fun i => heta i)).2.1

/-- The prescribed positive innovation tower is coherent under leading-principal restriction. -/
theorem prescribedPositiveInnovationTower_coherent (eta : ℕ → ℝ) (N : ℕ) :
    leadingPrincipalSubmatrix (prescribedPositiveInnovationTower eta (N + 1)) =
      prescribedPositiveInnovationTower eta N := by
  ext i j
  simp [leadingPrincipalSubmatrix, prescribedPositiveInnovationTower,
    prescribedPositiveInnovationFrame, Matrix.diagonal]

/-- **Positive clock realization theorem.**  Every strictly positive sequence occurs exactly as
the canonical unit-boundary innovation sequence of a coherent positive Gram clock. -/
theorem prescribedPositiveInnovationTower_innovation
    (eta : ℕ → ℝ) (N : ℕ) :
    coherentClockInnovation (prescribedPositiveInnovationTower eta) N = eta N := by
  exact prescribedPositiveInnovationFrame_amplitude
    (fun i : Fin (N + 1) => eta i) (Fin.last N)

end CapacityRealization

section RealizationInvariantCapacity

open Asymptotics

variable {𝕜 E F T : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Bounded-realization capacity comparison.**  Suppose two normed realizations have response
maps intertwined by a continuous linear equivalence.  Then their minimum-norm representers of
every response packet differ by at most the two operator norms of that equivalence. -/
theorem minimumResponseNorm_boundedComparison
    (e : E ≃L[𝕜] F) (A : E → T) (B : F → T)
    (hresp : ∀ x, B (e x) = A x)
    (mE : T → E) (mF : T → F)
    (hEresp : ∀ t, A (mE t) = t)
    (hFresp : ∀ t, B (mF t) = t)
    (hEmin : ∀ t x, A x = t → ‖mE t‖ ≤ ‖x‖)
    (hFmin : ∀ t x, B x = t → ‖mF t‖ ≤ ‖x‖)
    (t : T) :
    ‖mF t‖ ≤ ‖(e : E →L[𝕜] F)‖ * ‖mE t‖ ∧
      ‖mE t‖ ≤ ‖(e.symm : F →L[𝕜] E)‖ * ‖mF t‖ := by
  constructor
  · exact (hFmin t (e (mE t)) ((hresp (mE t)).trans (hEresp t))).trans
      ((e : E →L[𝕜] F).le_opNorm (mE t))
  · have hinv : A (e.symm (mF t)) = t := by
      rw [← hresp (e.symm (mF t)), e.apply_symm_apply, hFresp]
    exact (hEmin t (e.symm (mF t)) hinv).trans
      ((e.symm : F →L[𝕜] E).le_opNorm (mF t))

/-- Uniform finiteness of an entire minimum-response capacity profile is invariant under bounded
realization equivalence. -/
theorem minimumResponseNorm_uniformlyBounded_iff
    (e : E ≃L[𝕜] F) (A : E → T) (B : F → T)
    (hresp : ∀ x, B (e x) = A x)
    (mE : T → E) (mF : T → F)
    (hEresp : ∀ t, A (mE t) = t)
    (hFresp : ∀ t, B (mF t) = t)
    (hEmin : ∀ t x, A x = t → ‖mE t‖ ≤ ‖x‖)
    (hFmin : ∀ t x, B x = t → ‖mF t‖ ≤ ‖x‖) :
    (∃ C : ℝ, ∀ t, ‖mE t‖ ≤ C) ↔
      ∃ C : ℝ, ∀ t, ‖mF t‖ ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖(e : E →L[𝕜] F)‖ * C, fun t => ?_⟩
    exact (minimumResponseNorm_boundedComparison e A B hresp mE mF hEresp hFresp
      hEmin hFmin t).1.trans
      (mul_le_mul_of_nonneg_left (hC t) (norm_nonneg (e : E →L[𝕜] F)))
  · rintro ⟨C, hC⟩
    refine ⟨‖(e.symm : F →L[𝕜] E)‖ * C, fun t => ?_⟩
    exact (minimumResponseNorm_boundedComparison e A B hresp mE mF hEresp hFresp
      hEmin hFmin t).2.trans
      (mul_le_mul_of_nonneg_left (hC t) (norm_nonneg (e.symm : F →L[𝕜] E)))

/-- **Clock-capacity growth invariance.**  The whole asymptotic growth class of the minimum-response
profile, not only its bounded/unbounded phase, is invariant under bounded realization equivalence. -/
theorem minimumResponseNorm_isTheta
    (e : E ≃L[𝕜] F) (A : E → T) (B : F → T)
    (hresp : ∀ x, B (e x) = A x)
    (mE : T → E) (mF : T → F)
    (hEresp : ∀ t, A (mE t) = t)
    (hFresp : ∀ t, B (mF t) = t)
    (hEmin : ∀ t x, A x = t → ‖mE t‖ ≤ ‖x‖)
    (hFmin : ∀ t x, B x = t → ‖mF t‖ ≤ ‖x‖)
    (l : Filter T) :
    (fun t => ‖mE t‖) =Θ[l] (fun t => ‖mF t‖) := by
  constructor
  · apply IsBigO.of_bound ‖(e.symm : F →L[𝕜] E)‖
    exact Filter.Eventually.of_forall fun t => by
      simpa only [norm_norm] using
        (minimumResponseNorm_boundedComparison e A B hresp mE mF hEresp hFresp
          hEmin hFmin t).2
  · apply IsBigO.of_bound ‖(e : E →L[𝕜] F)‖
    exact Filter.Eventually.of_forall fun t => by
      simpa only [norm_norm] using
        (minimumResponseNorm_boundedComparison e A B hresp mE mF hEresp hFresp
          hEmin hFmin t).1

/-- Squared minimum-response energies, hence scalar clock capacities, have the same asymptotic
growth class under bounded realization equivalence. -/
theorem minimumResponseEnergy_isTheta
    (e : E ≃L[𝕜] F) (A : E → T) (B : F → T)
    (hresp : ∀ x, B (e x) = A x)
    (mE : T → E) (mF : T → F)
    (hEresp : ∀ t, A (mE t) = t)
    (hFresp : ∀ t, B (mF t) = t)
    (hEmin : ∀ t x, A x = t → ‖mE t‖ ≤ ‖x‖)
    (hFmin : ∀ t x, B x = t → ‖mF t‖ ≤ ‖x‖)
    (l : Filter T) :
    (fun t => ‖mE t‖ ^ 2) =Θ[l] (fun t => ‖mF t‖ ^ 2) := by
  exact (minimumResponseNorm_isTheta e A B hresp mE mF hEresp hFresp
    hEmin hFmin l).pow 2

end RealizationInvariantCapacity

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix
open scoped ComplexOrder

noncomputable section

/-- One inverse-Cholesky innovation row for an `r`-packet of target clock responses. -/
def inverseCholeskyPacketAmplitude {N r : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (target : Fin N → Fin r → ℂ)
    (i : Fin N) (a : Fin r) : ℂ :=
  ∑ j, C i j * target j a

/-- Positive matrix capacity of a finite packet of target clock responses. -/
def inverseCholeskyPacketCapacity {N r : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (target : Fin N → Fin r → ℂ) :
    Matrix (Fin r) (Fin r) ℂ := fun a b =>
  ∑ i, star (inverseCholeskyPacketAmplitude C target i a) *
    inverseCholeskyPacketAmplitude C target i b

/-- Rank-one positive capacity increment contributed by one innovation row. -/
def packetInnovationOuter {r : ℕ} (eta : Fin r → ℂ) :
    Matrix (Fin r) (Fin r) ℂ := fun a b => star (eta a) * eta b

/-- Every packet innovation outer product is positive semidefinite. -/
theorem packetInnovationOuter_posSemidef {r : ℕ} (eta : Fin r → ℂ) :
    (packetInnovationOuter eta).PosSemidef := by
  let B : Matrix (Fin 1) (Fin r) ℂ := fun _ a => eta a
  have hpos : (Bᴴ * (1 : Matrix (Fin 1) (Fin 1) ℂ) * B).PosSemidef :=
    Matrix.PosSemidef.one.conjTranspose_mul_mul_same B
  have heq : Bᴴ * B = packetInnovationOuter eta := by
    ext a b
    simp [packetInnovationOuter, B, Matrix.mul_apply]
  simpa [heq] using hpos

/-- **Matrix clock-capacity increment law.**  Adjoining one clock constraint adds exactly the
rank-one positive outer product of its packet innovation. -/
theorem inverseCholeskyPacketCapacity_succ
    {N r : ℕ} (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (target : Fin (N + 1) → Fin r → ℂ)
    (htri : C.BlockTriangular (fun i : Fin (N + 1) => OrderDual.toDual i)) :
    inverseCholeskyPacketCapacity C target =
      inverseCholeskyPacketCapacity (leadingPrincipalSubmatrix C)
        (fun j => target j.castSucc) +
      packetInnovationOuter
        (inverseCholeskyPacketAmplitude C target (Fin.last N)) := by
  ext a b
  unfold inverseCholeskyPacketCapacity packetInnovationOuter
  rw [Fin.sum_univ_castSucc, Matrix.add_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hamp : ∀ q : Fin r,
      inverseCholeskyPacketAmplitude C target i.castSucc q =
        inverseCholeskyPacketAmplitude (leadingPrincipalSubmatrix C)
          (fun j => target j.castSucc) i q := by
    intro q
    unfold inverseCholeskyPacketAmplitude leadingPrincipalSubmatrix
    rw [Fin.sum_univ_castSucc]
    have hzero : C i.castSucc (Fin.last N) = 0 := by
      apply htri
      simp
    simp [hzero]
  rw [hamp a, hamp b]

/-- Packet innovation at level `N` of a coherent inverse-Cholesky tower. -/
def coherentClockPacketInnovation {r : ℕ}
    (C : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (target : ℕ → Fin r → ℂ) (N : ℕ) : Fin r → ℂ :=
  inverseCholeskyPacketAmplitude (C N) (fun j => target (j : ℕ)) (Fin.last N)

/-- **Matrix clock-capacity decomposition.**  A coherent `r`-packet capacity is the cumulative
sum of the rank-one positive outer products of its canonical innovations. -/
theorem coherentClockPacketCapacity_eq_sum_innovations {r : ℕ}
    (C : ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (target : ℕ → Fin r → ℂ)
    (htri : ∀ N, (C N).BlockTriangular
      (fun i : Fin (N + 1) => OrderDual.toDual i))
    (hcoh : ∀ N, leadingPrincipalSubmatrix (C (N + 1)) = C N) :
    ∀ N, inverseCholeskyPacketCapacity (C N) (fun j => target (j : ℕ)) =
      ∑ n ∈ Finset.range (N + 1),
        packetInnovationOuter (coherentClockPacketInnovation C target n) := by
  intro N
  induction N with
  | zero =>
      ext a b
      simp [inverseCholeskyPacketCapacity, inverseCholeskyPacketAmplitude,
        packetInnovationOuter, coherentClockPacketInnovation]
  | succ N ih =>
      rw [inverseCholeskyPacketCapacity_succ (C (N + 1))
        (fun j => target (j : ℕ)) (htri (N + 1))]
      rw [hcoh N]
      have htarget : (fun j : Fin (N + 1) => target (j.castSucc : ℕ)) =
          (fun j : Fin (N + 1) => target (j : ℕ)) := by rfl
      rw [htarget, ih, Finset.sum_range_succ]
      simp [Finset.sum_range_succ, coherentClockPacketInnovation, add_assoc]

/-- Change of coordinates in a finite packet of clock responses. -/
def clockPacketCoordinateChange {N r s : ℕ}
    (target : Fin N → Fin r → ℂ) (R : Matrix (Fin r) (Fin s) ℂ) :
    Fin N → Fin s → ℂ := fun j a => ∑ b, target j b * R b a

/-- Innovation rows transform covariantly under a change of packet coordinates. -/
theorem inverseCholeskyPacketAmplitude_coordinateChange {N r s : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (target : Fin N → Fin r → ℂ)
    (R : Matrix (Fin r) (Fin s) ℂ) (i : Fin N) (a : Fin s) :
    inverseCholeskyPacketAmplitude C (clockPacketCoordinateChange target R) i a =
      ∑ b, inverseCholeskyPacketAmplitude C target i b * R b a := by
  simp only [inverseCholeskyPacketAmplitude, clockPacketCoordinateChange]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Matrix of innovation rows for a finite response packet. -/
def inverseCholeskyPacketAmplitudeMatrix {N r : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (target : Fin N → Fin r → ℂ) :
    Matrix (Fin N) (Fin r) ℂ := fun i a =>
  inverseCholeskyPacketAmplitude C target i a

/-- The innovation matrix transforms by right multiplication in packet coordinates. -/
theorem inverseCholeskyPacketAmplitudeMatrix_coordinateChange {N r s : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (target : Fin N → Fin r → ℂ)
    (R : Matrix (Fin r) (Fin s) ℂ) :
    inverseCholeskyPacketAmplitudeMatrix C (clockPacketCoordinateChange target R) =
      inverseCholeskyPacketAmplitudeMatrix C target * R := by
  ext i a
  exact inverseCholeskyPacketAmplitude_coordinateChange C target R i a

/-- Packet capacity is the Hermitian Gram form of its innovation matrix. -/
theorem inverseCholeskyPacketCapacity_eq_conjTranspose_mul {N r : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (target : Fin N → Fin r → ℂ) :
    inverseCholeskyPacketCapacity C target =
      (inverseCholeskyPacketAmplitudeMatrix C target)ᴴ *
        inverseCholeskyPacketAmplitudeMatrix C target := by
  ext a b
  rfl

/-- **Capacity-form covariance.**  Matrix clock capacity is not a coordinatewise scalar invariant:
it is a covariant Hermitian form on the response packet.  Every packet-coordinate change acts by
the exact congruence law `K ↦ Rᴴ K R`. -/
theorem inverseCholeskyPacketCapacity_coordinateChange {N r s : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (target : Fin N → Fin r → ℂ)
    (R : Matrix (Fin r) (Fin s) ℂ) :
    inverseCholeskyPacketCapacity C (clockPacketCoordinateChange target R) =
      Rᴴ * inverseCholeskyPacketCapacity C target * R := by
  rw [inverseCholeskyPacketCapacity_eq_conjTranspose_mul,
    inverseCholeskyPacketAmplitudeMatrix_coordinateChange,
    inverseCholeskyPacketCapacity_eq_conjTranspose_mul,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end

end GaloisForLFunctions.HTGeometry
