# Canonical prime contraction fails for the power-damped Fermi source

- **ID:** pm-power-damped-prime-contraction
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** Route PM, PM-31; `pm-power-damped-mobius-haar.md`.
- **Statement tested:** Some positive damping neighborhood has nonincreasing physical `L²(dt)` norm at every consecutive canonical prime cutoff.
- **Status:** Closed: negative theorem and quantitative positive survivor fully audited in Lean.

## Literal objects

Let `P_N` contain all primes at most `N`. For a finite prime set `S`, define

`B_(S,ε)(t) = −Σ_(1≤d≤ΠS) 1_(primeFactors(d)⊆S) μ(d)d^(−ε)φ_d(t)`.

This is a finite canonical `L²` source for every real `ε`. Its coefficients
are the ordinary Möbius coefficients supported on the squarefree divisors of
`ΠS`; no random phases, changed measure or diagonal surrogate enters its norm.
The empty set gives `−φ_1`, whose squared norm is `log 2`.

For fixed `t>0`, generators with `d>1/t` vanish. Every prime factor of each
remaining index belongs to `P_N` once `N≥floor(1/t)`. Thus
`B_(P_N,ε)(t)=A_ε(t)` eventually in `N`.

## Dependency-closed paper proof

Suppose for some `δ>0` and every `0<ε<δ`, all consecutive canonical cutoffs
have nonincreasing norm. Induction from the empty aperture bounds their norms
by `sqrt(log 2)`. Their exact pointwise stabilization and Fatou bound the
literal `A_ε` by the same number. As `ε` decreases to zero, `A_ε` converges
pointwise to Haar on `(0,1]`. A second application of Fatou gives
`1≤sqrt(log 2)`, contradicting `log 2<1`.

Consequently every positive damping neighborhood contains some `ε` and `N`
with a strict norm increase from `P_N` to `P_(N+1)`. That index `N+1` is prime:
a nonprime index leaves the aperture unchanged. This refutes contraction even
in canonical increasing-prime order, not merely for an arbitrary prime ordering.

## No-go closure

- **Exact killing theorem:**
  `pmFinitePrimePowerDampedFermiSource_exists_canonical_growth` in
  `PMPowerDampedMobiusPrimeGrowth.lean`.
- **Strongest positive survivor:** The limiting canonical norm budget has a
  unit floor. More precisely, along any countably generated nontrivial filter
  of dampings tending to zero, every eventual uniform full canonical norm
  budget is at least one. Along every parameter sequence the restricted norms
  have liminf at least one. Furthermore, every prescribed budget below one is
  exceeded by an actual canonical finite-prime source arbitrarily near zero
  damping. Exact finite-prime cutoff stabilization transfers any uniform
  cutoff norm budget to the literal source.
- **New insight:** A viable prime-based producer must allow accumulated norm
  growth from the seed value `sqrt(log 2)` to at least the Haar floor one.
  Positivity of the diagonal or prime-pair contraction in a different carrier
  cannot justify zero-growth physical synthesis. The required finite budget
  above this floor remains open.
- **Paper dependencies:** Exact Fermi generator norm; literal parameter
  continuity and zero-parameter Haar identity; finite prime coverage; Fatou.
  All have existing Lean proofs. No RH or critical simplicity input.
- **Lean status:** `PMPowerDampedMobiusNormFloor` (89 lines, six declarations)
  and `PMPowerDampedMobiusPrimeGrowth` (203 lines, 13 declarations) are wired
  and passed targeted builds, final actual-source checks, all standard-axiom
  and public-API probes, and exhaustive body/name/index/import checks.

The multiplicative-operator expression and its quadratic insertion formula
motivated the conjecture but are not required by these Lean proofs. The
certified source is the literal finite coefficient sum above.

## Boundary and next question

This retires only a monotone prime-contraction producer. PM-31 admission for
arbitrarily small positive damping remains open. A bounded prime-cutoff
budget may permit strictly positive increments; neither that budget nor a
source-specific damping operator has been proved.

## Log

- 2026-10-01 — Paper contradiction found; strengthened to canonical ordering.
  Norm-floor and finite-prime scratches passed. Targeted builds passed in
  29 and 18 seconds respectively; final audits underway.

- 2026-10-01 — Both final actual-source `lake env lean` checks passed empty.
  All 19 declarations use only `propext`, `Classical.choice`, `Quot.sound`.
  Exhaustive source-body, name uniqueness, public API and unique umbrella imports
  checked. Generated index refreshed. Formal lint exits 1 solely on 14 unrelated
  unwired modules; no own or proof-debt finding. No-go and positive-survivor
  gates complete; moved to `5-failed`. Small-damping admission remains open.
