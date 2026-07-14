import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaProduct

/-!
# Parity-correct inversion for the all-order multiple elliptic gamma

The elliptic-gamma inversion used as unitarity in solvable lattice models extends directly to the
finite-nome hierarchy already constructed in HTGeometry.  In the uncentered additive convention,
reflection through the sum of the structural parameters realizes

`x ↦ (∏ i, p i) / x`.

This exchanges every forward and backward product atom.  The genuine multiple elliptic gamma is a
quotient in even rank and a product in odd rank, so reflection inverts it in even rank and fixes it
in odd rank.  At logarithmic-derivative level the uniform law is multiplication by `(-1)^rank`.
As in the two-nome result, regularity at the reflected point is discharged from the original pair
of nonvanishing hypotheses.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι]

/-- The uncentered multiple-gamma coordinate realizes reflection through the sum of the additive
nome parameters as `x ↦ (∏ i, p i) / x`. -/
theorem multipleEllipticGammaCoordinate_reflection (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaCoordinate ((∑ i, τ i) - z) =
      (∏ i, ellipticNome (τ i)) / multipleEllipticGammaCoordinate z := by
  simp only [multipleEllipticGammaCoordinate, ellipticNome, div_eq_mul_inv]
  rw [show 2 * Real.pi * I * ((∑ i, τ i) - z) =
      (∑ i, 2 * Real.pi * I * τ i) + -(2 * Real.pi * I * z) by
        rw [mul_sub, Finset.mul_sum]
        ring,
    Complex.exp_add, Complex.exp_neg, Complex.exp_sum]

/-- Reflection exchanges an all-order forward argument with its backward partner. -/
theorem multipleEllipticGammaForwardArgument_reflection
    {p : ι → ℂ} {x : ℂ} (hp : ∀ i, p i ≠ 0) (hx : x ≠ 0) (n : ι → ℕ) :
    multipleEllipticGammaForwardArgument p ((∏ i, p i) / x) n =
      multipleEllipticGammaBackwardArgument p x n := by
  have hpProd : (∏ i, p i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hp i
  have hpow : (∏ i, p i ^ (n i + 1)) =
      (∏ i, p i ^ n i) * ∏ i, p i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [pow_succ]
  rw [multipleEllipticGammaForwardArgument,
    multipleEllipticGammaBackwardArgument, hpow]
  field_simp [hpProd, hx]

/-- Reflection exchanges an all-order backward argument with its forward partner. -/
theorem multipleEllipticGammaBackwardArgument_reflection
    (p : ι → ℂ) (x : ℂ) (n : ι → ℕ) :
    multipleEllipticGammaBackwardArgument p ((∏ i, p i) / x) n =
      multipleEllipticGammaForwardArgument p x n := by
  have hpow : (∏ i, p i ^ (n i + 1)) =
      (∏ i, p i ^ n i) * ∏ i, p i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [pow_succ]
  rw [multipleEllipticGammaForwardArgument,
    multipleEllipticGammaBackwardArgument, hpow, div_eq_mul_inv]
  ring

/-- Reflection multiplies each all-order logarithmic summand by the rank-parity sign. -/
theorem multipleEllipticGammaLogSummand_reflection
    {p : ι → ℂ} {x : ℂ} (hp : ∀ i, p i ≠ 0) (hx : x ≠ 0) (n : ι → ℕ) :
    multipleEllipticGammaLogSummand p ((∏ i, p i) / x) n =
      multipleEllipticGammaLogSign ι * multipleEllipticGammaLogSummand p x n := by
  rw [multipleEllipticGammaLogSummand, multipleEllipticGammaLogSummand,
    multipleEllipticGammaForwardArgument_reflection hp hx,
    multipleEllipticGammaBackwardArgument_reflection]
  by_cases hcard : Even (Fintype.card ι)
  · simp only [multipleEllipticGammaLogSign, neg_one_pow_eq_ite, hcard, if_true,
      one_mul]
    ring
  · simp only [multipleEllipticGammaLogSign, neg_one_pow_eq_ite, hcard, if_false,
      neg_mul, one_mul]
    ring

/-- Uniform all-order kernel reflection law.  Even rank is invariant and odd rank is
anti-invariant. -/
theorem multipleEllipticGammaLogKernel_reflection
    {p : ι → ℂ} {x : ℂ} (hp : ∀ i, p i ≠ 0) (hx : x ≠ 0) :
    multipleEllipticGammaLogKernel p ((∏ i, p i) / x) =
      multipleEllipticGammaLogSign ι * multipleEllipticGammaLogKernel p x := by
  rw [multipleEllipticGammaLogKernel, multipleEllipticGammaLogKernel,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  exact multipleEllipticGammaLogSummand_reflection hp hx n

/-- Additive signed reflection law for the all-order logarithmic kernel. -/
theorem multipleEllipticGammaAdditiveLogKernel_reflection
    (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaAdditiveLogKernel τ ((∑ i, τ i) - z) =
      multipleEllipticGammaLogSign ι *
        multipleEllipticGammaAdditiveLogKernel τ z := by
  rw [multipleEllipticGammaAdditiveLogKernel,
    multipleEllipticGammaAdditiveLogKernel,
    multipleEllipticGammaCoordinate_reflection,
    multipleEllipticGammaLogKernel_reflection
      (fun i => ellipticNome_ne_zero (τ i))
      (multipleEllipticGammaCoordinate_ne_zero z)]
  ring

/-- Reflection exchanges each all-order forward factor with its backward partner. -/
theorem multipleEllipticGammaForwardFactor_reflection
    (τ : ι → ℂ) (n : ι → ℕ) (z : ℂ) :
    multipleEllipticGammaForwardFactor τ n ((∑ i, τ i) - z) =
      multipleEllipticGammaBackwardFactor τ n z := by
  rw [multipleEllipticGammaForwardFactor,
    multipleEllipticGammaBackwardFactor,
    multipleEllipticGammaCoordinate_reflection,
    multipleEllipticGammaForwardArgument_reflection
      (fun i => ellipticNome_ne_zero (τ i))
      (multipleEllipticGammaCoordinate_ne_zero z)]

/-- Reflection exchanges each all-order backward factor with its forward partner. -/
theorem multipleEllipticGammaBackwardFactor_reflection
    (τ : ι → ℂ) (n : ι → ℕ) (z : ℂ) :
    multipleEllipticGammaBackwardFactor τ n ((∑ i, τ i) - z) =
      multipleEllipticGammaForwardFactor τ n z := by
  rw [multipleEllipticGammaBackwardFactor,
    multipleEllipticGammaForwardFactor,
    multipleEllipticGammaCoordinate_reflection,
    multipleEllipticGammaBackwardArgument_reflection]

/-- Reflection exchanges the all-order forward and backward entire products. -/
theorem multipleEllipticGammaForwardProduct_reflection
    (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaForwardProduct τ ((∑ i, τ i) - z) =
      multipleEllipticGammaBackwardProduct τ z := by
  rw [multipleEllipticGammaForwardProduct,
    multipleEllipticGammaBackwardProduct]
  apply tprod_congr
  intro n
  exact multipleEllipticGammaForwardFactor_reflection τ n z

/-- Reflection exchanges the all-order backward and forward entire products. -/
theorem multipleEllipticGammaBackwardProduct_reflection
    (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaBackwardProduct τ ((∑ i, τ i) - z) =
      multipleEllipticGammaForwardProduct τ z := by
  rw [multipleEllipticGammaBackwardProduct,
    multipleEllipticGammaForwardProduct]
  apply tprod_congr
  intro n
  exact multipleEllipticGammaBackwardFactor_reflection τ n z

/-- Parity-correct reflection of the genuine multiple elliptic gamma: even rank gives the reciprocal
and odd rank gives the original value. -/
theorem multipleEllipticGammaProduct_reflection (τ : ι → ℂ) (z : ℂ) :
    multipleEllipticGammaProduct τ ((∑ i, τ i) - z) =
      if Even (Fintype.card ι) then (multipleEllipticGammaProduct τ z)⁻¹
      else multipleEllipticGammaProduct τ z := by
  by_cases hcard : Even (Fintype.card ι)
  · simp only [multipleEllipticGammaProduct, hcard, if_true,
      multipleEllipticGammaForwardProduct_reflection,
      multipleEllipticGammaBackwardProduct_reflection, inv_div]
  · simp only [multipleEllipticGammaProduct, hcard, if_false,
      multipleEllipticGammaForwardProduct_reflection,
      multipleEllipticGammaBackwardProduct_reflection]
    ring

/-- Original regularity transports to the reflected all-order products. -/
theorem multipleEllipticGammaProducts_reflection_ne_zero
    {τ : ι → ℂ} {z : ℂ}
    (hzF : multipleEllipticGammaForwardProduct τ z ≠ 0)
    (hzB : multipleEllipticGammaBackwardProduct τ z ≠ 0) :
    multipleEllipticGammaForwardProduct τ ((∑ i, τ i) - z) ≠ 0 ∧
      multipleEllipticGammaBackwardProduct τ ((∑ i, τ i) - z) ≠ 0 := by
  rw [multipleEllipticGammaForwardProduct_reflection,
    multipleEllipticGammaBackwardProduct_reflection]
  exact ⟨hzB, hzF⟩

/-- Even-rank regular-locus unitarity in product-one form. -/
theorem multipleEllipticGammaProduct_mul_reflection_of_even
    {τ : ι → ℂ} {z : ℂ} (hcard : Even (Fintype.card ι))
    (hzF : multipleEllipticGammaForwardProduct τ z ≠ 0)
    (hzB : multipleEllipticGammaBackwardProduct τ z ≠ 0) :
    multipleEllipticGammaProduct τ z *
      multipleEllipticGammaProduct τ ((∑ i, τ i) - z) = 1 := by
  rw [multipleEllipticGammaProduct_reflection]
  simp only [hcard, if_true]
  apply mul_inv_cancel₀
  simp only [multipleEllipticGammaProduct, hcard, if_true]
  exact div_ne_zero hzF hzB

/-- Direct application to the existing all-order analytic product bridge: reflected-point
regularity is discharged, and reflection acts on the logarithmic derivative by `(-1)^rank`. -/
theorem logDeriv_multipleEllipticGammaProduct_reflection
    {τ : ι → ℂ} {z : ℂ} (hτ : ∀ i, 0 < (τ i).im)
    (hzF : multipleEllipticGammaForwardProduct τ z ≠ 0)
    (hzB : multipleEllipticGammaBackwardProduct τ z ≠ 0) :
    logDeriv (multipleEllipticGammaProduct τ) ((∑ i, τ i) - z) =
      multipleEllipticGammaLogSign ι *
        logDeriv (multipleEllipticGammaProduct τ) z := by
  obtain ⟨hrF, hrB⟩ :=
    multipleEllipticGammaProducts_reflection_ne_zero hzF hzB
  rw [logDeriv_multipleEllipticGammaProduct_eq_additiveKernel hτ hrF hrB,
    logDeriv_multipleEllipticGammaProduct_eq_additiveKernel hτ hzF hzB,
    multipleEllipticGammaAdditiveLogKernel_reflection]

end

end GaloisForLFunctions
