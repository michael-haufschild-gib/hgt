import GaloisForLFunctions.Core

/-!
# Signed-transpose polarization of reflected two-point kernels

A reflected two-point kernel has one of two universal covariance signs:

`K (τ a) i j = K a j i` or `K (τ a) i j = -K a j i`.

The sign decides which reflection sector is symmetric in the two source labels.  With positive
transpose covariance the reflection-even sector is symmetric and the odd sector is skew.  With
negative transpose covariance the roles reverse: the even sector is skew and the odd sector is
symmetric.  At a reflection-fixed parameter, every negatively covariant kernel is skew, has zero
diagonal, and every odd-dimensional finite packet is singular.

This is the algebraic incidence law behind diagonal reflection blindness and completed Xi seam
polarization.  No topology, positivity, spectral model, or arithmetic input is used.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A I R : Type*}

/-- Reflection-even part of a two-point kernel. -/
def reflectionEvenKernel [Add R] (τ : A → A) (K : A → I → I → R)
    (a : A) (i j : I) : R :=
  K a i j + K (τ a) i j

/-- Reflection-odd part of a two-point kernel. -/
def reflectionOddKernel [AddGroup R] (τ : A → A) (K : A → I → I → R)
    (a : A) (i j : I) : R :=
  K a i j - K (τ a) i j

theorem reflectionEvenKernel_eq_add_swap_of_reflect_eq_swap [Add R]
    (τ : A → A) (K : A → I → I → R)
    (hK : ∀ a i j, K (τ a) i j = K a j i) (a : A) (i j : I) :
    reflectionEvenKernel τ K a i j = K a i j + K a j i := by
  rw [reflectionEvenKernel, hK]

theorem reflectionOddKernel_eq_sub_swap_of_reflect_eq_swap [AddGroup R]
    (τ : A → A) (K : A → I → I → R)
    (hK : ∀ a i j, K (τ a) i j = K a j i) (a : A) (i j : I) :
    reflectionOddKernel τ K a i j = K a i j - K a j i := by
  rw [reflectionOddKernel, hK]

theorem reflectionEvenKernel_swap_of_reflect_eq_swap [AddCommSemigroup R]
    (τ : A → A) (K : A → I → I → R)
    (hK : ∀ a i j, K (τ a) i j = K a j i) (a : A) (i j : I) :
    reflectionEvenKernel τ K a j i = reflectionEvenKernel τ K a i j := by
  rw [reflectionEvenKernel_eq_add_swap_of_reflect_eq_swap τ K hK,
    reflectionEvenKernel_eq_add_swap_of_reflect_eq_swap τ K hK]
  exact add_comm _ _

theorem reflectionOddKernel_swap_neg_of_reflect_eq_swap [AddCommGroup R]
    (τ : A → A) (K : A → I → I → R)
    (hK : ∀ a i j, K (τ a) i j = K a j i) (a : A) (i j : I) :
    reflectionOddKernel τ K a j i = -reflectionOddKernel τ K a i j := by
  rw [reflectionOddKernel_eq_sub_swap_of_reflect_eq_swap τ K hK,
    reflectionOddKernel_eq_sub_swap_of_reflect_eq_swap τ K hK]
  abel

theorem reflectionEvenKernel_eq_sub_swap_of_reflect_eq_neg_swap [AddGroup R]
    (τ : A → A) (K : A → I → I → R)
    (hK : ∀ a i j, K (τ a) i j = -K a j i) (a : A) (i j : I) :
    reflectionEvenKernel τ K a i j = K a i j - K a j i := by
  rw [reflectionEvenKernel, hK, sub_eq_add_neg]

theorem reflectionOddKernel_eq_add_swap_of_reflect_eq_neg_swap [AddCommGroup R]
    (τ : A → A) (K : A → I → I → R)
    (hK : ∀ a i j, K (τ a) i j = -K a j i) (a : A) (i j : I) :
    reflectionOddKernel τ K a i j = K a i j + K a j i := by
  rw [reflectionOddKernel, hK, sub_neg_eq_add]

theorem reflectionEvenKernel_swap_neg_of_reflect_eq_neg_swap [AddCommGroup R]
    (τ : A → A) (K : A → I → I → R)
    (hK : ∀ a i j, K (τ a) i j = -K a j i) (a : A) (i j : I) :
    reflectionEvenKernel τ K a j i = -reflectionEvenKernel τ K a i j := by
  rw [reflectionEvenKernel_eq_sub_swap_of_reflect_eq_neg_swap τ K hK,
    reflectionEvenKernel_eq_sub_swap_of_reflect_eq_neg_swap τ K hK]
  abel

theorem reflectionOddKernel_swap_of_reflect_eq_neg_swap [AddCommGroup R]
    (τ : A → A) (K : A → I → I → R)
    (hK : ∀ a i j, K (τ a) i j = -K a j i) (a : A) (i j : I) :
    reflectionOddKernel τ K a j i = reflectionOddKernel τ K a i j := by
  rw [reflectionOddKernel_eq_add_swap_of_reflect_eq_neg_swap τ K hK,
    reflectionOddKernel_eq_add_swap_of_reflect_eq_neg_swap τ K hK]
  exact add_comm _ _

/-- A negatively transpose-covariant complex kernel has zero diagonal at every fixed parameter. -/
theorem kernel_diagonal_eq_zero_of_fixed_reflect_eq_neg_swap
    (τ : A → A) (K : A → I → I → ℂ)
    (hK : ∀ a i j, K (τ a) i j = -K a j i)
    {a : A} (ha : τ a = a) (i : I) :
    K a i i = 0 := by
  have h := hK a i i
  rw [ha] at h
  linear_combination h / 2

/-- Finite matrix packet sampled from a reflected two-point kernel. -/
def reflectedKernelMatrix [Fintype I] (K : A → I → I → ℂ) (a : A) : Matrix I I ℂ :=
  fun i j => K a i j

theorem reflectedKernelMatrix_transpose_eq_neg_of_fixed
    [Fintype I] (τ : A → A) (K : A → I → I → ℂ)
    (hK : ∀ a i j, K (τ a) i j = -K a j i)
    {a : A} (ha : τ a = a) :
    (reflectedKernelMatrix K a).transpose = -reflectedKernelMatrix K a := by
  ext i j
  change K a j i = -K a i j
  have h := hK a j i
  rwa [ha] at h

/-- Every odd-dimensional packet of a negatively transpose-covariant kernel is singular at a
reflection-fixed parameter. -/
theorem reflectedKernelMatrix_det_eq_zero_of_fixed_of_odd
    [Fintype I] [DecidableEq I] (τ : A → A) (K : A → I → I → ℂ)
    (hK : ∀ a i j, K (τ a) i j = -K a j i)
    {a : A} (ha : τ a = a) (hodd : Odd (Fintype.card I)) :
    (reflectedKernelMatrix K a).det = 0 := by
  have htranspose := reflectedKernelMatrix_transpose_eq_neg_of_fixed τ K hK ha
  have hdet := congrArg Matrix.det htranspose
  rw [Matrix.det_transpose, Matrix.det_neg, hodd.neg_one_pow, neg_one_mul] at hdet
  linear_combination hdet / 2

end

end GaloisForLFunctions.HTGeometry
