import Mathlib

/-!
# Signed power-sum moment separation of Gamma Laurent monomials

For distinct scales `λ : Fin r → ℂ`, the signed power-sum moment map
`e ↦ (M_0(e), …, M_{r-1}(e))`, with `M_k(e) = ∑ᵢ eᵢ λᵢᵏ`, is injective.  This is the exact
Vandermonde separator behind the finite value-relation ledger of the prime-log Gamma cocycle:
distinct Gamma Laurent monomials `∏ᵢ Γ(s + λᵢ)^{eᵢ}` have distinct complete formal Stirling
signatures, because the coefficient of each inverse power of `s` in the Stirling expansion is a
Bernoulli polynomial in the `λᵢ` whose top term is `λᵢᵏ`, and the triangular Bernoulli-to-power
change of coordinates turns equality of complete signatures into equality of the moments.  The kernel
is mathlib's `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` (invertibility of the Vandermonde
matrix for distinct nodes).
-/

open Finset

namespace GaloisForLFunctions

/-- Signed power-sum moment of order `k` of an exponent vector `e` against scales `lam`. -/
noncomputable def signedMoment {r : ℕ} (lam : Fin r → ℂ) (e : Fin r → ℂ) (k : ℕ) : ℂ :=
  ∑ i, e i * lam i ^ k

/-- **Moment separation.**  For distinct scales `lam`, the first `r` signed moments determine the
exponent vector: the moment map `e ↦ (k ↦ M_k(e))` on `Fin r → ℂ` is injective. -/
theorem signedMoment_injective {r : ℕ} {lam : Fin r → ℂ} (hlam : Function.Injective lam) :
    Function.Injective (fun e : Fin r → ℂ => fun k : Fin r => signedMoment lam e (k : ℕ)) := by
  intro e e' h
  have hker : ∀ k : Fin r, ∑ i, (e i - e' i) * lam i ^ (k : ℕ) = 0 := by
    intro k
    have hk := congrFun h k
    simp only [signedMoment] at hk
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hk
    rw [← hk]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hzero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hlam hker
  funext i
  have hi := congrFun hzero i
  simp only [Pi.zero_apply, sub_eq_zero] at hi
  exact hi

/-- **Finite Stirling-signature separation (integer exponents).**  Two integer exponent vectors
with equal signed power-sum moments `M_k(e) = ∑ᵢ eᵢ λᵢᵏ` for `0 ≤ k < r` against distinct scales
`λ` are equal.  Hence distinct Gamma Laurent monomials `∏ᵢ Γ(s+λᵢ)^{eᵢ}` have distinct complete
formal Stirling signatures. -/
theorem signedMoment_intExponent_injective {r : ℕ} {lam : Fin r → ℂ}
    (hlam : Function.Injective lam) {e e' : Fin r → ℤ}
    (h : ∀ k : Fin r, signedMoment lam (fun i => (e i : ℂ)) (k : ℕ)
        = signedMoment lam (fun i => (e' i : ℂ)) (k : ℕ)) :
    e = e' := by
  have hc : (fun i => (e i : ℂ)) = (fun i => (e' i : ℂ)) :=
    signedMoment_injective hlam (funext h)
  funext i
  have := congrFun hc i
  exact_mod_cast this

end GaloisForLFunctions
