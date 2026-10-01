# First-prime asymptotic obstructs damping monotonicity

- **ID:** pm-power-damping-monotonicity
- **Stage:** 5-failed
- **Type:** FALSIFIED (positive survivor fully formalized)
- **Source:** Route PM, PM-31, after canonical prime-contraction failure.
- **Statement tested:** Increasing positive power damping eventually makes the literal source's canonical norm nonincreasing.
- **Status:** Closed: 415 lines / 22 declarations in `PMPowerDampedMobiusLargeDamping.lean`, wired and fully audited.

## Dependency-closed paper proof

The literal source is `A_ε=−Σ μ(d)d^(−ε)φ_d`. For `ε≥2`, all sources below
are already canonically admitted by the existing safe-range theorem. With
`x=2^(−ε)`, its first two terms are `−φ_1+xφ_2`.

Every remaining term, multiplied by `2^ε`, has norm at most `3(2/d)^ε`
for `d≥3`. This is bounded by `12/d²` for `ε≥2`, and tends to zero for
each fixed `d≥3`. Dominated convergence of the scalar majorant, Minkowski
for each finite prefix, and Fatou under exact pointwise stabilization prove

`||2^ε(A_ε+φ_1)−φ_2||₂ → 0`.

Let `κ=Re⟨φ_1,φ_2⟩`. Their negative parity values make their product
nonnegative. Both generators equal `−1` on `(1/4,1/3]`, so `κ≥1/12`.
Expanding the squared Hilbert norm now gives

`2^ε(||A_ε||₂²−log 2) → −2κ < 0`.

Thus the energy tends to `log 2` from below. After any prescribed damping
threshold, choose an admitted source with energy below this limit, then a
later damping with energy closer to the limit and strictly greater. Eventual
nonincreasing norm is impossible for the actual source family.

## No-go closure

- **Killing mechanism:** A nonincreasing function on a final interval is
  bounded below by its limit there. The exact first-prime correction forces
  the opposite strict inequality for all sufficiently large dampings.
- **Strongest positive survivor:** Canonical first-prime expansion, exact
  leading energy coefficient `−2κ`, lower bound `κ≥1/12`, and approach to
  the seed energy from below.
- **New insight:** Contractivity cannot be inferred from decreasing every
  literal coefficient, even on this same admitted arithmetic source. The
  first prime reduces the seed norm through its positive physical overlap;
  further damping removes that cancellation. A viable small-damping norm
  bound must retain this dependence on signed cross terms.
- **Paper dependencies:** Existing admission for `ε≥1/2`, generator norm
  and parity identities, scalar dominated convergence, Fatou, and Hilbert
  norm expansion. No zero statement, numerical experiment or new axiom.
- **Lean status:** `PMPowerDampedMobiusLargeDamping.lean`; all 22 declarations
  passed the scratch, including the exact energy coefficient and admitted
  norm-increasing parameter pairs beyond every threshold. Targeted old build, final actual-source check, exhaustive source/API and standard-axiom audits passed.

## Boundary

The result refutes the proposed monotonicity producer. It does not
refute admission for all positive dampings or a finite upper bound that allows
norm growth. PM-31's small-positive-damping admission question remains open.

## Log

- 2026-10-01 — Corpus large-damping search reviewed (all 40 statements and
  ingredient chain); scalar first-coefficient and Banach dominated-convergence
  APIs inspected. Literal first-two-prefix identity, summable vanishing tail
  majorant, canonical scaled-tail convergence, overlap integral and `κ≥1/12`
  passed Lean. Energy expansion implementation in progress.

- Targeted old build passed (32 seconds); final actual-source Lean check passed
  empty. All 22 declaration bodies, unique names, public API entries and umbrella
  import audited. All 22 axiom/API probes passed with only `propext`,
  `Classical.choice`, `Quot.sound`. Formal lint fails solely on 11
  unrelated unwired modules; no own or proof-debt finding.
