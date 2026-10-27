# Renormalized arithmetic potential theory of the characteristic circle (RAPT)

- **ID:** rapt
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2710/obstacles-summary.md §4 (Q2, B3.25, B3.26, W11, W12)
- **Statement:** Regulators, counterterms, anomalies and couplings of the places of the explicit formula; programme folder `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/`.

## Goal
Answer Q2 of the report (coupled renormalization) with theorems: what a coupling can pay (rank), what
covariance costs (scalar, `log N`), what the anomaly costs (`≥ ½ log N`), which regulator has a
nontrivial survival cone (horizon: polar on uniform profiles, orbital on sublattices, characters
survive).

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proofs of RP1–RP7
- [ ] 2 → 3  Lean modules wired into `RenormalizedArithmeticPotentialTheory.lean`

## Approach (paper proofs)
- RP1 coupled survival: PSD block `B`; `x = (w, s v)` ⇒ `quad B₁₁ w + 2s wᵀB₁₂v ≥ 0 ∀ s` ⇒ `B₁₂ v = 0` when `B₂₂ v = 0`. Survival `quad B x = 0` ⇒ `B x = 0` (PSD symmetric). Prime projection `= −B₁₁⁻¹ B₁₂ w` factors through `range B₂₂`.
- RP3 covariant counterterm: Schur weights `n^{−1/2}`: up-row `Σ_{t ≤ N/n} Λ(t)/t ≤ log(N/n) + log 4 + 4`, down-row `Σ_{t∣n} Λ(t) = log n` ⇒ `P_N ≤ (log N + log 4 + 4)|x|²`. Lower: pole vector, `P(u) = 2Σ_{m ≤ N} (1/m) A(N/m)`, Mertens lower bound, `Σ_{m≤N} log m/m ≤ ½ log² N + c`, `log N ≤ H_N ≤ log N + 1`.
- RP4: `φ(mt) ≤ t φ(m)` ⇒ torsion off-diagonal `≥ P`; diagonal `c(n) = log n − d(n)`, `Σ_{n≤N} d(n)/n ≤ C H_N`.
- RP5: `B(M, M') = Σ_{m≤M} (1/m)(A(M'/m) + A(M/m))` for `M ≤ M'`; Mertens.
- RP6: sublattice sums; `lcm`.

## Log
- 2026-10-27 — created; README first draft written.
