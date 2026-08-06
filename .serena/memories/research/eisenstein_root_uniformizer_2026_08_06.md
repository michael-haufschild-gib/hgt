# A root of an Eisenstein polynomial is a uniformizer (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **38**.
Continues [[research/tame_monogenic_different_exponent_2026_08_06]].

## `EisensteinRootUniformizer.lean`

- `addVal_pow (x) (n) : addVal B (x ^ n) = n • addVal B x` — **`map_pow` does not apply to
  `AddValuation`**; prove by induction (recurring trap in this corpus).
- `eval_eisensteinPoly`, `eval_map_monic` — the expansion of a pushed-forward monic polynomial.
- **`addVal_eq_one_of_eisenstein_root`** — for `ψ : A →+* B` of DVRs with ramification index `e`,
  `g : A[X]` Eisenstein monic of degree `e` (all sub-leading coefficients in the maximal ideal,
  `addVal A (g.coeff 0) = 1`), any root `x` of `g.map ψ` has `addVal B x = 1`.

Structure of the proof: the constant term contributes exactly `e`; every other term at least `e`
and, once `v(x) ≥ 1`, at least `e + 1`; `AddValuation.map_add_of_distinct_val` then gives the sum
valuation exactly `e`, so `e·v(x) = e` and `v(x) = 1`.  `v(x) = 0` is excluded separately (the sum
would have valuation ≥ e > 0), and `x ≠ 0` because `ψ (g.coeff 0) ≠ 0`.

**Why it matters**: the different computation
(`addVal_eval_derivative_map_eisenstein`) needed `Irreducible x` as a *separate* hypothesis.  Now
the presentation supplies it: an Eisenstein presentation automatically presents a uniformizer.

## Lean traps (ℕ∞)

- `lt_add_one (e : ℕ∞)` fails — ℕ∞ has no `AddLeftStrictMono` (`⊤ + 1 = ⊤`).  Get strictness by
  casting from ℕ: `((e:ℕ) : ℕ∞) < ((e+1:ℕ) : ℕ∞)` via `exact_mod_cast Nat.lt_succ_self`.
- `zero_le _` is not applicable in ℕ∞ (`zero_le` takes no explicit argument there); use `by simp`.
- `Nat.eq_of_mul_eq_mul_left` needs the goal literally as `e * n = e * 1`; build it with
  `rw [mul_one]; exact hnat` rather than rewriting inside the application.

## Remaining for Theorem A

1. Existence of an Eisenstein presentation (monogenicity — needs Hensel/completeness).
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification (shown unavoidable in module 35).
4. Corollary B: MMP.
