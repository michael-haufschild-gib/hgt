import GaloisForLFunctions.HTGeometry.ChebyshevMomentTrace
import Mathlib.Algebra.Polynomial.Sequence

/-!
# Triangularity of Chebyshev traces: moments are recoverable

The shifted Chebyshev kernels `T_n(1 - 2X)` have exact degree `n` and leading coefficient
`2^(n-1) (-2)^n ≠ 0`, so they form a triangular basis of `ℝ[X]` whose first `n + 1` members span the
polynomials of degree at most `n`. Consequently a moment sequence is determined by its shifted
Chebyshev traces, and the positive moments `s_(k+1)` are determined by the Chebyshev traces
`L_s(X T_n(1 - 2X))`: passing from moments to Chebyshev traces loses no information.

## Main results

- `chebyshevTraceKernelPolynomial_natDegree`, `chebyshevTracePolynomial_natDegree`: the kernel and the
  trace polynomial have degrees `n` and `n + 1`.
- `chebyshevTracePolynomial_leadingCoeff`: the leading coefficient of `X T_n(1 - 2X)` is
  `2^(n-1) (-2)^n`.
- `chebyshevKernelBasis`: the kernels `T_n(1 - 2X)` form a basis of `ℝ[X]`.
- `chebyshevKernel_span_degreeLE`: the kernels of index at most `n` span the polynomials of degree at
  most `n`.
- `chebyshevShiftedMomentTrace_injective`: a real sequence is determined by its shifted Chebyshev traces.
- `chebyshevMomentTrace_lossless`: equal Chebyshev traces force `s_(k+1) = t_(k+1)` for all `k`.

## Hypotheses

Unconditional; no positivity or moment-problem hypothesis is used.
-/

open Polynomial
open Module

namespace HTGeometry

private theorem chebyshevAffine_eq_linear :
    (1 - 2 * X : Polynomial ℝ) = C (-2) * X + C 1 := by
  simp only [C_neg, C_ofNat, C_1]
  ring

private theorem chebyshevAffine_natDegree :
    (1 - 2 * X : Polynomial ℝ).natDegree = 1 := by
  rw [chebyshevAffine_eq_linear, natDegree_linear]
  norm_num

private theorem chebyshevAffine_leadingCoeff :
    (1 - 2 * X : Polynomial ℝ).leadingCoeff = -2 := by
  rw [chebyshevAffine_eq_linear, leadingCoeff_linear]
  norm_num

/-- The shifted Chebyshev kernel `T_n(1 - 2X)` has degree exactly `n`. -/
theorem chebyshevTraceKernelPolynomial_natDegree (n : ℕ) :
    (chebyshevTraceKernelPolynomial n).natDegree = n := by
  rw [chebyshevTraceKernelPolynomial, natDegree_comp,
    Chebyshev.natDegree_T, chebyshevAffine_natDegree]
  simp

/-- The Chebyshev trace polynomial `X T_n(1 - 2X)` has degree exactly `n + 1`. -/
theorem chebyshevTracePolynomial_natDegree (n : ℕ) :
    (chebyshevTracePolynomial n).natDegree = n + 1 := by
  rw [chebyshevTracePolynomial, natDegree_X_mul]
  · rw [chebyshevTraceKernelPolynomial_natDegree]
  · intro hzero
    have := chebyshevTraceKernelPolynomial_natDegree n
    rw [hzero, natDegree_zero] at this
    cases n with
    | zero =>
        rw [chebyshevTraceKernelPolynomial_zero] at hzero
        exact one_ne_zero hzero
    | succ n => omega

/-- The leading coefficient of `X T_n(1 - 2X)` is `2^(n-1) (-2)^n`. -/
theorem chebyshevTracePolynomial_leadingCoeff (n : ℕ) :
    (chebyshevTracePolynomial n).leadingCoeff =
      2 ^ (n - 1) * (-2) ^ n := by
  rw [chebyshevTracePolynomial, mul_comm, leadingCoeff_mul_X,
    chebyshevTraceKernelPolynomial, leadingCoeff_comp]
  · rw [Chebyshev.leadingCoeff_T, chebyshevAffine_leadingCoeff]
    simp
  · rw [chebyshevAffine_natDegree]
    norm_num

/-- The top coefficient (of `X^(n+1)`) of `X T_n(1 - 2X)` is nonzero. -/
theorem chebyshevTracePolynomial_topCoeff_ne_zero (n : ℕ) :
    (chebyshevTracePolynomial n).coeff (n + 1) ≠ 0 := by
  rw [← chebyshevTracePolynomial_natDegree n,
    coeff_natDegree, chebyshevTracePolynomial_leadingCoeff]
  positivity

/-- The leading coefficient of `T_n(1 - 2X)` is `2^(n-1) (-2)^n`. -/
theorem chebyshevTraceKernelPolynomial_leadingCoeff (n : ℕ) :
    (chebyshevTraceKernelPolynomial n).leadingCoeff =
      2 ^ (n - 1) * (-2) ^ n := by
  rw [chebyshevTraceKernelPolynomial, leadingCoeff_comp]
  · rw [Chebyshev.leadingCoeff_T, chebyshevAffine_leadingCoeff]
    simp
  · rw [chebyshevAffine_natDegree]
    norm_num

private theorem chebyshevTraceKernelPolynomial_ne_zero (n : ℕ) :
    chebyshevTraceKernelPolynomial n ≠ 0 := by
  intro h
  have hcoeff := chebyshevTraceKernelPolynomial_leadingCoeff n
  rw [h, leadingCoeff_zero] at hcoeff
  have hnonzero : 2 ^ (n - 1) * (-2 : ℝ) ^ n ≠ 0 := by positivity
  exact hnonzero hcoeff.symm

/-- The shifted Chebyshev kernels as a polynomial sequence with `deg T_n(1 - 2X) = n`. -/
noncomputable def chebyshevKernelSequence : Polynomial.Sequence ℝ where
  elems' := chebyshevTraceKernelPolynomial
  degree_eq' n := by
    rw [degree_eq_natDegree (chebyshevTraceKernelPolynomial_ne_zero n)]
    exact_mod_cast chebyshevTraceKernelPolynomial_natDegree n

private theorem chebyshevKernelSequence_leadingCoeff_isUnit (n : ℕ) :
    IsUnit (chebyshevKernelSequence n).leadingCoeff := by
  change IsUnit (chebyshevTraceKernelPolynomial n).leadingCoeff
  rw [chebyshevTraceKernelPolynomial_leadingCoeff]
  exact isUnit_iff_ne_zero.mpr (by positivity)

/-- The shifted Chebyshev kernels form a basis of `ℝ[X]`, since their leading coefficients are units. -/
noncomputable def chebyshevKernelBasis : Basis ℕ ℝ (Polynomial ℝ) :=
  chebyshevKernelSequence.basis chebyshevKernelSequence_leadingCoeff_isUnit

theorem chebyshevKernelBasis_eq (n : ℕ) :
    chebyshevKernelBasis n = chebyshevTraceKernelPolynomial n := by
  exact chebyshevKernelSequence.basis_eq_self chebyshevKernelSequence_leadingCoeff_isUnit n

/-- The kernels `T_m(1 - 2X)` with `m ≤ n` span exactly the polynomials of degree at most `n`. -/
theorem chebyshevKernel_span_degreeLE (n : ℕ) :
    Submodule.span ℝ (chebyshevTraceKernelPolynomial '' Set.Iic n) =
      Polynomial.degreeLE ℝ n := by
  exact chebyshevKernelSequence.span_degreeLE
    (fun i hi => chebyshevKernelSequence_leadingCoeff_isUnit i)

/-- The moment functional `L_s` as a linear map `ℝ[X] → ℝ`. -/
noncomputable def momentFunctionalLinearMap (s : ℕ → ℝ) :
    Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun := momentFunctional s
  map_add' := momentFunctional_add s
  map_smul' := by
    intro c p
    exact momentFunctional_smul s c p

/-- A real sequence is determined by its shifted Chebyshev traces `L_s(T_n(1 - 2X))`, `n ≥ 0`. -/
theorem chebyshevShiftedMomentTrace_injective :
    Function.Injective (fun s : ℕ → ℝ => chebyshevShiftedMomentTrace s) := by
  intro s t h
  have hlinear : momentFunctionalLinearMap s = momentFunctionalLinearMap t := by
    apply chebyshevKernelBasis.ext
    intro n
    simpa [chebyshevKernelBasis_eq, momentFunctionalLinearMap,
      chebyshevShiftedMomentTrace] using congrFun h n
  funext k
  have hk := congrArg (fun f : Polynomial ℝ →ₗ[ℝ] ℝ => f (X ^ k)) hlinear
  simpa [momentFunctionalLinearMap, momentFunctional_X_pow] using hk

/-- The shifted moment functional `p ↦ L_s(X p)` as a linear map. -/
noncomputable def positiveMomentFunctionalLinearMap (s : ℕ → ℝ) :
    Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := momentFunctional s (X * p)
  map_add' p q := by
    rw [mul_add, momentFunctional_add]
  map_smul' c p := by
    rw [mul_smul_comm, momentFunctional_smul]
    rfl

/-- Lossless Chebyshev traces: if `L_s(X T_n(1 - 2X)) = L_t(X T_n(1 - 2X))` for all `n`, then
`s_(k+1) = t_(k+1)` for all `k`. -/
theorem chebyshevMomentTrace_lossless {s t : ℕ → ℝ}
    (h : ∀ n, chebyshevMomentTrace s n = chebyshevMomentTrace t n) :
    ∀ k, s (k + 1) = t (k + 1) := by
  have hlinear : positiveMomentFunctionalLinearMap s =
      positiveMomentFunctionalLinearMap t := by
    apply chebyshevKernelBasis.ext
    intro n
    simpa [positiveMomentFunctionalLinearMap, chebyshevKernelBasis_eq,
      chebyshevMomentTrace, chebyshevTracePolynomial] using h n
  intro k
  have hk := congrArg (fun f : Polynomial ℝ →ₗ[ℝ] ℝ => f (X ^ k)) hlinear
  change momentFunctional s (X * X ^ k) = momentFunctional t (X * X ^ k) at hk
  rw [mul_comm X (X ^ k), ← pow_succ, momentFunctional_X_pow,
    momentFunctional_X_pow] at hk
  exact hk

end HTGeometry
