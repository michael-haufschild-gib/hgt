# The Hurwitz zeta as a field of ℚ-independent shifted exponential monomials

- **ID:** hurwitz-shifted-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean. Connects the shifted-value pillar to mathlib's actual `HurwitzZeta.hurwitzZeta`.
- **Statement:**
  - `hurwitzZeta_summand_eq_shifted_exp`: the mathlib Hurwitz coefficient `1/(n+a)^s = exp(−s·log(n+a))` — a shifted exponential monomial with frequency `log(n+a)` (a>0).
  - `hasSum_hurwitzZeta_shifted_exp`: on Re s>1, `ζ(a,s) = ∑ₙ exp(−s·log(n+a))` — the actual Hurwitz L-function is the superposition of those monomials (reformulates `HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`).
  - `hurwitzZeta_frequencies_ratIndependent`: for transcendental a>0, the frequencies `{log(n+a)}` are ℚ-linearly independent (via `log_shifts_independent`).
- **Lean:** `formal/GaloisForLFunctions/RHTower/HurwitzShiftedBridge.lean`. Axiom-clean.
- **Significance:** ties the shifted multiplicative/log independence pillar to the concrete Hurwitz L-function object in mathlib — the value-theoretic genericity (rationally independent frequencies) that underlies universality, now anchored to `hurwitzZeta` itself.

## Log
- 2026-07-08 — created (bridging pillar↔actual L-function, per the "connect to the real object" directive).

## Update: Hurwitz truncation Parseval
`hurwitzZeta_truncation_meanSquare`: on Re s=σ, the Cesàro time average of |ζ_N(a,σ+it)|² (modulus square of the N-term truncation ∑_{n∈s}(n+a)^{−σ−it}) converges to ∑_{n∈s}(n+a)^{−2σ} — Parseval for the actual Hurwitz L-function's partial sums, via the ‖∑‖²=∑∑ expansion composed with shifted_dirichlet_meanValue. Axiom-clean.
