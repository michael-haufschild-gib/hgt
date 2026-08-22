/-
# The SPD split update (Section 5.1.3, Equation (13))

On the manifold `S⁺⁺(n)` of symmetric positive definite matrices with the affine-invariant
metric, the Riemannian exponential is

```
exp_X(S) = X^{1/2} exp( X^{-1/2} S X^{-1/2} ) X^{1/2} .
```

`spdExp_congr` proves the *congruence invariance* that makes the Busemann layer computable:
for every invertible `A`,

```
exp_{A Aᵀ}(A S Aᵀ) = A (exp S) Aᵀ .
```

Applied to `A = U L`, where `Uᵀ X U = L Lᵀ` is a Cholesky factorisation and the negative
gradient direction of `V = φ(λ b_{U,d} + β)` is `s · U L D Lᵀ Uᵀ` with `D = diag(d)`, this gives
exactly Equation (13) of the source:

```
exp_X(-τ grad V(X)) = (U L exp((s/2) D)) (U L exp((s/2) D))ᵀ ,
```

i.e. the Cholesky factor is updated by right multiplication with `exp((s/2)D)`
(`spd_split_update`).  This is what makes the split SPD denoiser cheap: no matrix square root
of `X` is ever formed.
-/
import GaloisForLFunctions.HTGeometry.ConstitutivePositiveConeMidpointRecovery

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Matrix
open scoped Matrix MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For an invertible real matrix `A`, the Gram matrix `A Aᵀ` is positive definite. -/
theorem posDef_mul_transpose_self (A : Matrix n n ℝ) (hA : IsUnit A.det) : (A * Aᵀ).PosDef := by
  have hvec : Function.Injective A.vecMul := by
    have hinv : Function.LeftInverse (fun v : n → ℝ => v ᵥ* A⁻¹) A.vecMul := by
      intro x
      show (x ᵥ* A) ᵥ* A⁻¹ = x
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hA, Matrix.vecMul_one]
    exact hinv.injective
  have h := Matrix.PosDef.mul_conjTranspose_self A hvec
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The affine-invariant Riemannian exponential map at a symmetric positive definite `X`. -/
noncomputable def spdExp (X S : Matrix n n ℝ) : Matrix n n ℝ :=
  CFC.sqrt X * NormedSpace.exp ((CFC.sqrt X)⁻¹ * S * (CFC.sqrt X)⁻¹) * CFC.sqrt X

/-- **Congruence invariance of the affine-invariant exponential.**  The exponential at a Gram
matrix `A Aᵀ` in a congruent direction is the congruence of the matrix exponential. -/
theorem spdExp_congr (A S : Matrix n n ℝ) (hA : IsUnit A.det) :
    spdExp (A * Aᵀ) (A * S * Aᵀ) = A * NormedSpace.exp S * Aᵀ := by
  have hAAT : (A * Aᵀ).PosDef := posDef_mul_transpose_self A hA
  set W : Matrix n n ℝ := CFC.sqrt (A * Aᵀ) with hWdef
  have hW : W.PosDef := positiveMatrixSqrt_posDef hAAT
  have hWsq : W * W = A * Aᵀ := positiveMatrixSqrt_mul_self hAAT
  have hWdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).mp hW.isUnit
  have hWsymm : Wᵀ = W := by
    have := hW.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hWinvsymm : (W⁻¹)ᵀ = W⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hWsymm]
  set O : Matrix n n ℝ := W⁻¹ * A with hOdef
  have hOT : Oᵀ = Aᵀ * W⁻¹ := by rw [hOdef, Matrix.transpose_mul, hWinvsymm]
  have hOOT : O * Oᵀ = 1 := by
    rw [hOdef, hOT]
    calc W⁻¹ * A * (Aᵀ * W⁻¹) = W⁻¹ * (A * Aᵀ) * W⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = W⁻¹ * (W * W) * W⁻¹ := by rw [hWsq]
      _ = 1 := by
          rw [← Matrix.mul_assoc W⁻¹ W W, Matrix.nonsing_inv_mul W hWdet, Matrix.one_mul,
            Matrix.mul_nonsing_inv W hWdet]
  have hOdet : IsUnit O.det := by
    have hdet : O.det * Oᵀ.det = 1 := by
      rw [← Matrix.det_mul, hOOT, Matrix.det_one]
    have hne : O.det ≠ 0 := by
      intro h
      rw [h, zero_mul] at hdet
      exact one_ne_zero hdet.symm
    exact isUnit_iff_ne_zero.mpr hne
  have hOunit : IsUnit O := (Matrix.isUnit_iff_isUnit_det O).mpr hOdet
  have hOinv : O⁻¹ = Oᵀ := Matrix.inv_eq_right_inv hOOT
  -- the conjugated direction
  have hdir : W⁻¹ * (A * S * Aᵀ) * W⁻¹ = O * S * O⁻¹ := by
    rw [hOinv, hOdef, hOT]
    simp only [Matrix.mul_assoc]
  -- assemble
  have hWO : W * O = A := by
    rw [hOdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv W hWdet, Matrix.one_mul]
  have hOTW : Oᵀ * W = Aᵀ := by
    rw [hOT, Matrix.mul_assoc, Matrix.nonsing_inv_mul W hWdet, Matrix.mul_one]
  rw [spdExp, ← hWdef, hdir, Matrix.exp_conj O S hOunit, hOinv]
  calc W * (O * NormedSpace.exp S * Oᵀ) * W
      = (W * O) * NormedSpace.exp S * (Oᵀ * W) := by simp only [Matrix.mul_assoc]
    _ = A * NormedSpace.exp S * Aᵀ := by rw [hWO, hOTW]

/-- The scalar version: `exp_{A Aᵀ}(s · A D Aᵀ) = A exp(s D) Aᵀ`. -/
theorem spdExp_congr_smul (A D : Matrix n n ℝ) (hA : IsUnit A.det) (s : ℝ) :
    spdExp (A * Aᵀ) (s • (A * D * Aᵀ)) = A * NormedSpace.exp (s • D) * Aᵀ := by
  have hsm : s • (A * D * Aᵀ) = A * (s • D) * Aᵀ := by
    simp
  rw [hsm, spdExp_congr A (s • D) hA]

/-- Half-step splitting of a symmetric direction. -/
theorem exp_smul_split (D : Matrix n n ℝ) (hD : Dᵀ = D) (s : ℝ) :
    NormedSpace.exp (s • D)
      = NormedSpace.exp ((s / 2) • D) * (NormedSpace.exp ((s / 2) • D))ᵀ := by
  have hT : (NormedSpace.exp ((s / 2) • D))ᵀ = NormedSpace.exp ((s / 2) • D) := by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul, hD]
  rw [hT, ← Matrix.exp_add_of_commute _ _ (Commute.refl _)]
  congr 1
  rw [← add_smul]
  congr 1
  ring

/-- **Equation (13).**  With `X = (U L)(U L)ᵀ` and negative-gradient direction
`s · (U L) D (U L)ᵀ`, the affine-invariant step updates the Cholesky-type factor by right
multiplication with `exp((s/2) D)`. -/
theorem spd_split_update (A D : Matrix n n ℝ) (hA : IsUnit A.det) (hD : Dᵀ = D) (s : ℝ) :
    spdExp (A * Aᵀ) (s • (A * D * Aᵀ))
      = (A * NormedSpace.exp ((s / 2) • D)) * (A * NormedSpace.exp ((s / 2) • D))ᵀ := by
  rw [spdExp_congr_smul A D hA s, exp_smul_split D hD s]
  rw [Matrix.transpose_mul]
  have hT : (NormedSpace.exp ((s / 2) • D))ᵀ = NormedSpace.exp ((s / 2) • D) := by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul, hD]
  rw [hT]
  simp only [Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The base point of the split update, written as in the source: `X = U (L Lᵀ) Uᵀ`. -/
theorem spd_basepoint (U L : Matrix n n ℝ) : (U * L) * (U * L)ᵀ = U * (L * Lᵀ) * Uᵀ := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The direction of the split update, written as in the source. -/
theorem spd_direction (U L D : Matrix n n ℝ) (s : ℝ) :
    s • ((U * L) * D * (U * L)ᵀ) = s • (U * (L * D * Lᵀ) * Uᵀ) := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- The Cholesky-form Busemann function `b_{U,d}(X) = -2 Σ dᵢ log Lᵢᵢ` of the source, as a
function of the Cholesky factor. -/
noncomputable def spdBusemannOfFactor (d : n → ℝ) (L : Matrix n n ℝ) : ℝ :=
  -2 * ∑ i, d i * Real.log (L i i)

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
