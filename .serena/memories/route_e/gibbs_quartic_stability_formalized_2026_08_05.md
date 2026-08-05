# Quartic criterion + O4 injection formalized (2026-08-05)

Lean: `formal/GaloisForLFunctions/RHTower/GibbsQuarticStability.lean` (RHTower.GibbsGas),
wired, built, no sorry, axioms clean. N3 sector stability now k ≤ 4 in Lean.

## The constructive quartic Routh–Hurwitz proof (reusable technique!)
For real quartic with root s+it, s ≥ 0: conjugate-pair factorization, NOT Cauchy
index/interlacing: define b := a₃+2sa₄, c := a₂+2sb−a₄m (m := s²+t²), r₁ := a₁−(bm−2sc),
r₀ := a₀−cm. Then:
1. Division identity P = (z²−2sz+m)(a₄z²+bz+c) + r₁z+r₀ — pure `ring` after push_cast.
2. z₀²−2sz₀+m = 0 — `linear_combination (t:ℂ)^2 * Complex.I_sq`.
3. r₁ = r₀ = 0 from re/im extraction (t ≠ 0 branch); t = 0 branch by positivity.
4. THE KEY EXACT IDENTITY: a₃a₂a₁ − a₄a₁² − a₃²a₀ = −2sb·[(a₄m−c)² + a₃a₁] — single
   `ring` after rw [← hR1, ← hR2, a₃ = b−2sa₄, a₂ = c−2sb+a₄m]. So Δ₃ > 0 ⟹ no RHP root.
This pattern should extend to higher Routh minors (degree-k criterion via the same
quadratic-factor elimination — candidate route for all-k gas stability in Lean).

## O4 injection in Lean
8 strict Boltzmann comparisons via `exp_pair_lt (u1 u2 v1 v2) (h : v1+v2 < u1+u2)`;
energy inequalities with hints mul_pos (mul_pos (a−1>0) (bc−1>0)) (scale·x>0).
Assembly: NEVER linarith over expanded 96-monomial products (simplex > 1.6M heartbeats);
use calc + mul_lt_mul_of_pos_right/left + add_lt_add + `ring` regroupings +
`rw [add_comm]; exact` closures. `set` the 16 Boltzmann atoms, prove positivity + all
comparisons via rw-of-defs, then `clear_value` ALL atoms before any arithmetic.

## Open next
- All-k stability: the minor chain via energy injection (general combinatorial lemma:
  the (min-extraction, b := min(S∖a'))-injections generalize; likely a clean induction);
  or the degree-k Routh reduction via the quadratic-factor elimination identity.
- Kurtz strong-coupling anchor (c_j² > 4c_{j−1}c_{j+1} ⟹ real-rooted) in Lean.
- N1/N2 infinite-volume Hadamard layer on corpus canonical-product assets.
