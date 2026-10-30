# The three questions of review 3010 (overlap window, Adams producer, flip resolution)

- **ID:** R3010-Q123
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** ../../../reports/review-3010/obstacles-summary.md §2.3
- **Statement:** Answer Q1 (location of the RH transition in the overlap window), Q2 (Adams operations as a Stepanov producer), Q3 (overlap needed to resolve a gauge point from `0`), with Lean proofs.

## Goal
Full answers with unconditional Lean theorems. Estimates, criteria and no-gos are not answers.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach

### Q3 — exact resolution law for flips (first target)
Objects: `W(c,N)` = complete Weil matrix of profile `φ` at width `c/N`; `W_S` = the same with the
odd powers of the primes in a finite set `S` flipped; normalized Ramanujan modes `e_m = c_m/√φ(m)`.

Conjecture C3.1 (limit flip operator). On normalized Ramanujan horizon vectors `r_m`,
`⟪(W_S − W) r_m, r_l⟫ → Q_S(m,l)`, where
`Q_S(m,l) = Σ_{p∈S} Σ_{k odd} 2 log p · p^{-k} (ρ(m,l,p^k) + ρ(l,m,p^k))`,
`ρ(m,l,q) = mean_n e_m(n) e_l(qn)`. Closed form: `e_l(qn) = √(φ(l)/φ(l')) e_{l'}(n)`,
`l' = l/(l,q)`, so `ρ(m,l,q) = √(φ(l)/φ(l')) [m = l']`.
Check: on the prime-square trial `F_p` the `k = 1` term is `(4 log p/p)(−1 + 2/p²)`, the corpus value.

Conjecture C3.2 (exact threshold). With
`λ_S(c) = inf_β (Σ_m E_m(c) β_m² + Σ_{m,l} Q_S(m,l) β_m β_l)/|β|²` over finitely supported `β`:
`λ_S(c) > 0` ⇒ the flipped form is eventually positive definite; `λ_S(c) < 0` ⇒ eventually
negative on an atomic test. `λ_S` is nonincreasing, `→ +∞` as `c → 0`, negative for large `c`;
`c_0(ω_S) = sup{c : λ_S(c) > 0} ∈ (0,∞)`; single flips: `c_0(ω_p) → ∞`.

Mechanism: complement gap (reserve `W ≥ a + β·poleDefect`, finite Ramanujan approximation of
bounded defect) + quasimodes + bounded flip perturbation; 2×2 Schur estimate.

### Q1 — structural notes
- Low zeros (`|γ| ≲ N/c`) enter Ramanujan modes only through the boundary term `N^ρ/ρ` of the
  partial sums of `Σ c_m(n) n^{-s}`: contribution `β_1² · c·Σ_ρ 1/(ρ(1−ρ)) / log N`, the same with or
  without RH. Fixed-`c` positivity is RH-blind for this reason.
- The margin `E(c)` is the dual-sum (approximate functional equation) energy of zeros at height
  `≳ 2πN/c`.
- Off-line zeros can only be seen by synthesized wide tests; their energy is `c·(Q(h)/‖h‖² + κ log N ε_φ(c)²)`
  with `ε_φ` the synthesis (aliasing) error. Expected transition: `log N · ε_φ(c)² ≍ 1`, not
  `E(c) log N ≍ 1`.

### Q2 — open

## Log
- 2026-10-30 — created; Q3 law C3.1–C3.2 derived on paper, Lean development started in
  `RenormalizedArithmeticPotentialTheory`.
