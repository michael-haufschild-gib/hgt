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
