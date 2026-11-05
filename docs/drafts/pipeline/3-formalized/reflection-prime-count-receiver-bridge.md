# Reflection-pair prime counts and the five receivers

- **ID:** reflection-prime-count-receiver-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; receiver composition)
- **Source:** review-0411, §2.1, A29.

## Statement

Let `B` assert, for every real compactly supported `C²` test vanishing on `(0,∞)`,

`|H₀(f) − Σₙ Λ(n)n^(−1/2)(f⋆f)(−log n)| ≤ W(f)`.

Then `B` is equivalent to each existing receiver:

- **WL:** the real Weil-lag function is bounded below.
- **JAS:** every positive exponent bounds the literal Riesz source on the finite
  power window `m < k ≤ m + m/log(m+1)` for infinitely many square shells `m²`.
- **CTF:** real chronological rows bounded by one attain every positive error tolerance.
- **PBM:** the regularized prime-zeta series converges right of `1/2`.
- **RB:** `σ(n) < exp(γ)n log log n` eventually.

These are equivalences, not proofs that any receiver condition holds.

## Proof

[PROVED HERE] The existing two-site identities give
`W(f±f∘R)=2W(f)±2[H₀(f)−ΣₙΛ(n)n^(−1/2)(f⋆f)(−log n)]`.
Under RH both left sides are nonnegative, hence `B`. Conversely, `B` implies
`W(f)≥0` for every test supported in any window `[-A,0]`, since its left side
is an absolute value. The existing window criterion gives RH. Composing this
exact equivalence with the five named receiver theorems proves every statement.

## Lean

`SignedWindowCriticality/TheReflectionPrimeCountFeedsTheClassicalReceivers.lean`:

- `reflectionPrimeCountBand_iff_riemannHypothesis`.
- `reflectionPrimeCountBand_iff_weilLag_bddBelow`.
- `reflectionPrimeCountBand_iff_squareShellRiesz`.
- `reflectionPrimeCountBand_iff_chronological_unit_rows`.
- `reflectionPrimeCountBand_iff_primeRegCoeff_converges`.
- `reflectionPrimeCountBand_iff_eventually_robin`.

Direct leaf check passed. All six transitive axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Owning umbrella import added.
