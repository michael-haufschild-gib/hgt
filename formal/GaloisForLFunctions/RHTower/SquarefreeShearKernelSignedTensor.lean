import GaloisForLFunctions.RHTower.CommonProfileBooleanAnchorCurvature

/-!
# Signed tensor factorization of the squarefree shear kernel

This file gives the Fourier-side spectral normal form of the weighted common-profile Boolean
anchor curvature proved in `CommonProfileBooleanAnchorCurvature`.  It isolates the finite algebra
behind the CRT shear symbol

`q * 1_(i = o) + q * 1_(j = o) - 1`.

The local matrix is a positive rank-one outer product minus a negative rank-one outer product.  A
finite product of such local factors therefore expands into branch outer products with sign given
exactly by branch parity.  This is the pointwise spectral core of weighted `(CG7)`; the final
theorem records the corresponding scalar alternating-square identity.

This is finite structural algebra.  It does not estimate the physical `FCRJ` response correlation.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

section LocalShearKernel

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- The local arithmetic shear kernel with distinguished zero coordinate `o`. -/
def localShearKernel (q : R) (o : ι) : Matrix ι ι R :=
  fun i j =>
    q * (if i = o then 1 else 0) + q * (if j = o then 1 else 0) - 1

/-- Positive local branch, supported at the distinguished coordinate. -/
def localShearPositiveBranch (q : R) (o : ι) : ι → R :=
  fun i => q * (if i = o then 1 else 0)

/-- Complementary local branch. -/
def localShearNegativeBranch (q : R) (o : ι) : ι → R :=
  fun i => 1 - localShearPositiveBranch q o i

/-- **Local signed-rank-one factorization.**  The shear kernel is the outer square of the
distinguished branch minus the outer square of its complement. -/
theorem localShearKernel_eq_rankOne_sub_rankOne (q : R) (o : ι) :
    localShearKernel q o =
      Matrix.vecMulVec (localShearPositiveBranch q o) (localShearPositiveBranch q o) -
        Matrix.vecMulVec (localShearNegativeBranch q o) (localShearNegativeBranch q o) := by
  ext i j
  simp only [localShearKernel, localShearPositiveBranch, localShearNegativeBranch,
    Matrix.vecMulVec_apply, Matrix.sub_apply]
  ring

end LocalShearKernel

section SignedTensorExpansion

variable {κ ι R : Type*} [DecidableEq ι] [CommRing R]

/-- One branch amplitude: use `negative` on `t` and `positive` on its complement in `s`. -/
def signedTensorBranch (s t : Finset ι) (positive negative : ι → κ → R) (x : κ) : R :=
  (∏ i ∈ s \ t, positive i x) * ∏ i ∈ t, negative i x

/-- Product of the local signed outer-product kernels. -/
def productDifferenceKernel
    (s : Finset ι) (positive negative : ι → κ → R) (x y : κ) : R :=
  ∏ i ∈ s, (positive i x * positive i y - negative i x * negative i y)

/-- **Finite signed tensor expansion.**  A product of local differences of outer products is the
alternating sum of the global branch outer products. -/
theorem productDifferenceKernel_signedBranchExpansion
    (s : Finset ι) (positive negative : ι → κ → R) (x y : κ) :
    productDifferenceKernel s positive negative x y =
      ∑ t ∈ s.powerset,
        (-1 : R) ^ t.card *
          signedTensorBranch s t positive negative x *
            signedTensorBranch s t positive negative y := by
  rw [productDifferenceKernel, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t _ht
  simp only [signedTensorBranch, Finset.prod_mul_distrib]
  ring

/-- Scalar branch amplitude for a choice of negative coordinates `t`. -/
def signedScalarBranch (s t : Finset ι) (positive negative : ι → R) : R :=
  (∏ i ∈ s \ t, positive i) * ∏ i ∈ t, negative i

/-- **Alternating-square action.**  The product of local differences of squares is the parity
signed sum of the squares of all global branch amplitudes. -/
theorem prod_sq_sub_sq_eq_signedBranchSquareSum
    (s : Finset ι) (positive negative : ι → R) :
    (∏ i ∈ s, ((positive i) ^ (2 : ℕ) - (negative i) ^ (2 : ℕ))) =
      ∑ t ∈ s.powerset,
        (-1 : R) ^ t.card * (signedScalarBranch s t positive negative) ^ (2 : ℕ) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t _ht
  simp only [signedScalarBranch, Finset.prod_pow]
  ring

end SignedTensorExpansion

end

end RHTower
