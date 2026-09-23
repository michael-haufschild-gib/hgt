import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic

/-!
# The Chebyshev–Laurent plethysm identity (Tier A)

This file formalizes the algebraic core of branch B30 §7,
`docs/drafts/spectral-functoriality-operations-calculus.md`: the `Symᵏ`
plethysm `p_m(Symᵏπ) = U_k(p_m/2)`.

For a `GL₂` Satake parameter `z` (with contragredient `z⁻¹`), the degree-`k`
symmetric-power power sum is the **Dirichlet kernel** `Σ_{j=0}^k z^{k-2j}`, which
is the Chebyshev polynomial `S_k` (the rescaled `U_k`, `S_eq_U_comp_half_mul_X`)
evaluated at `z + z⁻¹`. Cleared of negative powers this is the finite geometric
series. We prove, by two-step induction on the Chebyshev recurrence
`S_add_two`, the edge-case-free identity

  `z^k · S_k(z + z⁻¹) = Σ_{i=0}^{k} (z²)^i`     (for `z ≠ 0`).

This is the prime/Satake-side λ-ring identity only. The zero-side realization
(the secular moments of `Symᵏπ` as functions of those of `π`) is the
explicit-formula / period-comparison wall and is **not** formalized here.
-/

open scoped BigOperators
open Polynomial

namespace GaloisForLFunctions

noncomputable section

/-- **B30 §7 (Chebyshev–Laurent plethysm core).** For `z ≠ 0`, the Chebyshev
polynomial `S_k` evaluated at `z + z⁻¹`, cleared of negative powers by `z^k`, is
the finite geometric series `Σ_{i=0}^{k} (z²)^i`. Equivalently the `Symᵏ` power
sum `Σ_{j=0}^k z^{k-2j}` is the Dirichlet kernel `S_k(z + z⁻¹) = U_k((z+z⁻¹)/2)`.
Proved by two-step induction on the recurrence `S_{k+2} = X·S_{k+1} − S_k`. -/
@[aesop safe]
theorem chebyshevS_eval_add_inv (z : ℂ) (hz : z ≠ 0) (k : ℕ) :
    z ^ k * (Chebyshev.S ℂ (k : ℤ)).eval (z + z⁻¹)
      = ∑ i ∈ Finset.range (k + 1), (z ^ (2 : ℕ)) ^ i := by
  induction k using Nat.twoStepInduction with
  | zero => simp [Chebyshev.S_zero]
  | one =>
      simp only [Nat.cast_one, Chebyshev.S_one, Polynomial.eval_X, pow_one,
        Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
      field_simp
      ring
  | more n ih1 ih2 =>
      have e1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      have e2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
      rw [e1] at ih2
      rw [e2, Chebyshev.S_add_two, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_X]
      set A := (Chebyshev.S ℂ (n : ℤ)).eval (z + z⁻¹) with hA
      set B := (Chebyshev.S ℂ ((n : ℤ) + 1)).eval (z + z⁻¹) with hB
      -- ih1 : z ^ n * A = ∑ i ∈ range (n+1), (z^(2 : ℕ))^i
      -- ih2 : z ^ (n+1) * B = ∑ i ∈ range (n+2), (z^(2 : ℕ))^i
      -- goal : z ^ (n+2) * ((z + z⁻¹) * B - A) = ∑ i ∈ range (n+3), (z^(2 : ℕ))^i
      have step : z ^ (n + 2) * ((z + z⁻¹) * B - A)
          = (z ^ (2 : ℕ) + 1) * (z ^ (n + 1) * B) - z ^ (2 : ℕ) * (z ^ n * A) := by
        field_simp
        ring
      have g1 : ∑ i ∈ Finset.range (n + 2), (z ^ (2 : ℕ)) ^ i
          = (∑ i ∈ Finset.range (n + 1), (z ^ (2 : ℕ)) ^ i) + (z ^ (2 : ℕ)) ^ (n + 1) :=
        Finset.sum_range_succ _ _
      have g2 : ∑ i ∈ Finset.range (n + 3), (z ^ (2 : ℕ)) ^ i
          = (∑ i ∈ Finset.range (n + 2), (z ^ (2 : ℕ)) ^ i) + (z ^ (2 : ℕ)) ^ (n + 2) :=
        Finset.sum_range_succ _ _
      rw [step, ih1, ih2, g2, g1]
      ring

/-- **B30 §7 (explicit `U_k` form).** The plethysm in mathlib's standard Chebyshev
`U`: `z^k · U_k((z+z⁻¹)/2) = Σ_{i≤k}(z²)^i`. With `z = αᵐ` and `p_m = z + z⁻¹`
this is exactly the draft's claim `p_m(Symᵏπ) = U_k(p_m/2)` (the `Symᵏ` power sum
is the Chebyshev `U`-value at half the trace). -/
@[aesop safe]
theorem chebyshevU_eval_plethysm (z : ℂ) (hz : z ≠ 0) (k : ℕ) :
    z ^ k * (Chebyshev.U ℂ (k : ℤ)).eval ((z + z⁻¹) / 2)
      = ∑ i ∈ Finset.range (k + 1), (z ^ (2 : ℕ)) ^ i := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  have harg : (⅟(2 : ℂ)) * (z + z⁻¹) = (z + z⁻¹) / 2 := by
    rw [invOf_eq_inv]; ring
  rw [← chebyshevS_eval_add_inv z hz k, Chebyshev.S_eq_U_comp_half_mul_X,
    Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, harg]

end

end GaloisForLFunctions
