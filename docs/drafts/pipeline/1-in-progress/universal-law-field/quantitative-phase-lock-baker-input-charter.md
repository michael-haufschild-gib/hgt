# The quantitative phase-lock: effective transcendence as a new input class

- **ID:** ULF-FIELD-4
- **Stage:** 1-in-progress
- **Type:** ATTACK CHARTER (one theorem sketched; collision pass mandatory before proof work)
- **Parents:** ULF-FIELD-3 §D (the prime-power order invariant), the closed qualitative
  phase-lock test (below), corpus Halász frontier (halasz-route-architecture: the recorded
  deficit is arithmetic, not analysis)
- **Status:** [QUALITATIVE OPENING CLOSED — KILL-TEST EXECUTED] [QUANTITATIVE VEIN OPEN]
  [MV-THEOREM SKETCH ON PAPER] [NOT RH] [NO LEAN — directive]

## Kill-test executed: the qualitative phase-lock collapses (recorded honestly)

Proposed opening: the log-prime lattice's phase structure as an independent route to the
Halász exceptional-frequency repulsion (the corpus's recorded real gap: "no lower bound on
δ; nothing identifies the exceptional frequency"). Test: repulsion needs QUANTITATIVE
equidistribution of {δ log p mod 2π} with rates; rates for prime equidistribution are
exponential sums over primes, i.e. zeta-zero data — the classical pole route the corpus
already owns (Mertens layer, zeta-pole box trick). The qualitative order structure adds no
independent access. **Verdict: CLOSED as an independent leverage source for the Halász gap.**

## The surviving quantitative vein (the actual charter)

The order type of (ℤ + θℤ, ℝ-order), θ = log q/log p, determines θ's continued fraction —
quantitative Diophantine data. Its effective content is NOT zeta-derived:

> **Baker's theorem (effective linear forms in logarithms):** there are effective C, κ > 0
> with |m log p − n log q| ≥ C·max(m,n)^{−κ} for all (m,n) ≠ 0.

This is transcendence theory — an unconditional input class ABSENT from the corpus's entire
engine list (sieve, contour, moments, positivity, spacing, large values: none consume linear
forms in logarithms). Compare the trivial bound: |p^m − q^n| ≥ 1 gives only
|m log p − n log q| ≳ e^{−m log p} — exponentially weaker. On the sparse frequency set
Λ_H = {m log p + n log q : |m|,|n| ≤ H}, Baker upgrades the minimal spacing from
exponentially small to polynomially small in H.

**Theorem sketch (to be proven dependency-closed after the collision pass):** for a
Dirichlet polynomial supported on the prime-power lattice, F(t) = Σ_{λ∈Λ_H} a_λ e^{iλt},
the Montgomery–Vaughan mean value
∫₀^T |F|² = (T + O(δ_min^{-1}))·Σ|a_λ|² acquires, via Baker, the unconditional error
O(H^κ/C) — polynomial in the height — where the trivial spacing gives an exponentially large
error term. An unconditional mean-value theorem for S-unit-supported Dirichlet polynomials
with polynomial-in-height error.

## Honest scope and consumers

- This does NOT directly attack the Halász deficit (which lives on ALL primes, not a
  two-prime lattice). Claiming so would repeat the route-collapse failure. Recorded
  candidate consumers, to be tested one by one: (i) the two-mode gas moment layer (the gas's
  replica/moment structure lives exactly on prime-power lattices); (ii) the UV corner's
  spectral resolution (the AP symbol's frequency module is Λ_H; Baker bounds how fast the
  dense subgroup fills ℝ, quantifying the corner's essential spectrum approximation); (iii)
  any corpus estimate on smooth/S-unit-supported sums where off-diagonal terms are currently
  controlled trivially.
- The field-level point stands independent of consumers: the corpus's obstruction map lists
  the input classes every route draws from; effective transcendence is a new column, derived
  from the field's own order invariant (ULF-FIELD-3 §D). Whether the column is USEFUL is
  exactly what the make-or-die must decide — usefulness is not assumed.

## Mandatory collision pass before proof work

1. S-unit equations / exponential sums literature: Bombieri; Evertse–Győry; Stewart —
   Baker-input mean values may exist verbatim.
2. "Linear forms in logarithms" applications to Dirichlet series / Turán power sums
   (Turán's method consumed Diophantine spacing — check Montgomery's Ten Lectures ch. on
   Turán and the power-sum literature).
3. Corpus: the gas moment layer cards; DirichletLargeValuesCount (spacing hypotheses —
   exact shapes); MultiplicativeResolution / parity-duality cards (two-mode structures).
4. Known uses of Baker in zeta theory (effective ZFR for Beurling?; the
   Rhin–Viola-type explicit measures for log 2/log 3) — establish the exact irrationality
   measure known for log q/log p and its effectivity status.

## Make-or-die

Find ONE recorded corpus estimate that the Baker-improved spacing strictly sharpens, or one
new unconditional theorem consumed by a live lane. If after the collision pass and one
serious attempt no consumer exists: verdict INSIGNIFICANT (a new input class with no
consumers is a curiosity), record, and the program's open-attack list shrinks accordingly.

## Log

- 2026-08-09 — chartered from the closure of the qualitative phase-lock (kill-test above)
  and of ULF-FIELD-3 (three-level equilibrium exhaustion). MV sketch on paper; collision
  pass listed; make-or-die and its INSIGNIFICANT branch pre-declared. No Lean.

## Make-or-die executed: verdict BRIDGE/REDISCOVERED — card CLOSED (2026-08-09)

Collision pass results:
- The spacing half of the sketch is classical: **Tijdeman (1973/74)** proved, via Baker's
  method, effective bounds for gaps between consecutive members of {p^m q^n} (integers
  composed of small primes) — polynomial-type separation, exactly the content the sketch
  attributed to "Baker upgrades the trivial spacing". Parent found.
- Explicit modern constants exist (irrationality exponent < 8.616 for nonzero elements of
  ℚlog2 + ℚlog3).
- The MV assembly (Tijdeman spacing → Montgomery–Vaughan mean value on S-unit support) is a
  one-step composition of two classical theorems: BRIDGE, not new knowledge.
- Consumer check: the corpus's completed-time-torus layer (Kronecker/Weyl density,
  deningerKroneckerFlow_dense, small-ball laws) is qualitative; Baker + Erdős–Turán would
  effectivize it (explicit hitting times for the log-prime torus). Real, but the mechanism is
  a known technique class and the upgrade is engineering-grade infrastructure, not new
  scientific knowledge per the July-2026 gate.

**Verdict: BRIDGE/REDISCOVERED (Tijdeman parent). Per the pre-declared make-or-die branch,
the card is CLOSED.** Standing residue: the corpus's engine list now cites effective
transcendence as an available (classical) input class with named parents, and the
effectivization of the torus layer is recorded as available maintenance if a consumer ever
demands rates.

## Log (appended)

- 2026-08-09 — collision pass executed; Tijdeman parent found; INSIGNIFICANT/BRIDGE branch
  fired as pre-declared. Card closed. Next recorded open test in the program's ledger: the
  corpus's own tree-uniform second-central-jet floor (PrimeIsingTreeCentralMassFloorLaw's
  named "next test").
