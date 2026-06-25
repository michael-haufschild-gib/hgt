/-
# The local-orbit obstruction (abstract engine for the Hurwitz quadratic gate)

The reusable core of the Hurwitz all-`N` quadratic tail-independence proof
(`docs/drafts/pipeline/2-fully-proven/new/hurwitz-quadratic-all-n-tail-independence.md`) is *not* a
Hurwitz-specific calculation but a polynomial-orbit obstruction, the formalization shape named in that
card:

> finite relation → orbit polynomial `p(T) = P(R + T·H)` → coefficient obstruction → independence.

The local monodromy around `a = -n` fixes the regular vector `R_n(x)` and multiplies the singular
vector `H(x)` by the diagonal scalar `q = exp(-2πi s)`. Analytic continuation of the relation to every
branch forces `p(q^m) = 0` for every integer `m`. With `deg_T p ≤ 2`:

* if the orbit `{q^m}` has **three distinct points** (`q` not a root of unity of order `≤ 2`),
  polynomial root-counting kills `p` outright — `orbit_eq_zero_of_three_distinct`;
* if `q = -1` (order two), the two values `p(1) = p(-1) = 0` still force the **odd** (linear)
  coefficient to vanish — `coeff_one_eq_zero_of_pm_one` — and the missing top (quadratic) coefficient is
  supplied separately by the local exponent filtration.

This file is the pure-algebra part: no Hurwitz zeta, no monodromy analysis, no `sorry`. It is the
Hurwitz analogue of `Bottcher.algIndep_of_unbounded_monodromy` — the algebraic engine fed by the
analytic inputs built in later bricks.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.LinearCombination

open Polynomial

namespace HurwitzOrbit

/-- **A degree-≤2 polynomial vanishing at three distinct points is zero.** The root-counting core: over
an integral domain, `natDegree p ≤ 2 < 3 = #{t₀,t₁,t₂}` and `p` vanishing on all three forces `p = 0`
(`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`). -/
theorem eq_zero_of_three_roots {R : Type*} [CommRing R] [IsDomain R] {p : R[X]}
    (hp : p.natDegree ≤ 2) {t₀ t₁ t₂ : R} (h01 : t₀ ≠ t₁) (h02 : t₀ ≠ t₂) (h12 : t₁ ≠ t₂)
    (e0 : p.eval t₀ = 0) (e1 : p.eval t₁ = 0) (e2 : p.eval t₂ = 0) : p = 0 := by
  classical
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p {t₀, t₁, t₂} ?_ ?_
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact e2
  · have hcard : ({t₀, t₁, t₂} : Finset R).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
        Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
    omega

/-- **Three-distinct-point orbit form.** If `p` has `natDegree ≤ 2`, the three orbit points `1, q, q²`
are pairwise distinct, and `p` vanishes on the whole forward orbit `{q^m : m ∈ ℕ}`, then `p = 0`. This
is the "enough distinct points" branch of the monodromy obstruction (formalization-shape step 3),
realized at the three smallest powers. -/
theorem orbit_eq_zero_of_three_distinct {R : Type*} [CommRing R] [IsDomain R] {p : R[X]}
    (hp : p.natDegree ≤ 2) {q : R} (h1q : (1 : R) ≠ q) (h1q2 : (1 : R) ≠ q ^ 2)
    (hqq2 : q ≠ q ^ 2) (hroots : ∀ m : ℕ, p.eval (q ^ m) = 0) : p = 0 :=
  eq_zero_of_three_roots hp h1q h1q2 hqq2 (by simpa using hroots 0) (by simpa using hroots 1)
    (hroots 2)

/-- **Order-two orbit: the odd coefficient vanishes.** If `q = -1` (orbit `{1, -1}`), a degree-≤2
polynomial vanishing at both `1` and `-1` has `2 · coeff 1 = 0`: subtracting `p(1) = c₀+c₁+c₂` and
`p(-1) = c₀-c₁+c₂` gives `2 c₁ = 0`. Char-agnostic form; over a field of characteristic `≠ 2` this is
`coeff 1 = 0`. The missing quadratic coefficient is *not* supplied here (the order-two orbit cannot
see it) — it comes from the local exponent filtration in the next brick. -/
theorem two_mul_coeff_one_of_pm_one {R : Type*} [CommRing R] {p : R[X]} (hp : p.natDegree ≤ 2)
    (e1 : p.eval 1 = 0) (em1 : p.eval (-1) = 0) : 2 * p.coeff 1 = 0 := by
  have hsum : ∀ x : R, p.eval x = p.coeff 0 + p.coeff 1 * x + p.coeff 2 * x ^ 2 := by
    intro x
    rw [eval_eq_sum_range' (show p.natDegree < 3 from Nat.lt_succ_of_le hp)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  have h1 : p.coeff 0 + p.coeff 1 * 1 + p.coeff 2 * 1 ^ 2 = 0 := by rw [← hsum 1]; exact e1
  have h2 : p.coeff 0 + p.coeff 1 * (-1) + p.coeff 2 * (-1) ^ 2 = 0 := by rw [← hsum (-1)]; exact em1
  linear_combination h1 - h2

/-- **Order-two orbit over a characteristic-zero field: the odd coefficient is zero.** Specialization of
`two_mul_coeff_one_of_pm_one` to e.g. `ℂ`, where `2 ≠ 0`. -/
theorem coeff_one_eq_zero_of_pm_one {K : Type*} [Field K] [CharZero K] {p : K[X]}
    (hp : p.natDegree ≤ 2) (e1 : p.eval 1 = 0) (em1 : p.eval (-1) = 0) : p.coeff 1 = 0 := by
  have h := two_mul_coeff_one_of_pm_one hp e1 em1
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  exact (mul_eq_zero.mp h).resolve_left h2

end HurwitzOrbit
