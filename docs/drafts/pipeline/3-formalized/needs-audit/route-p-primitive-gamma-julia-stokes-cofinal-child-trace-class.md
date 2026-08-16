# Route P primitive Gamma--Julia Stokes cofinal child trace class

- **ID:** `route-p-primitive-gamma-julia-stokes-cofinal-child-trace-class`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105M]`
- **Parent:** `route-p-primitive-gamma-julia-stokes-cofinal-child-kernel.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCofinalChildTraceClass.lean`

## Goal

Decide whether P-G105K's literal cross-prime Stokes child is genuinely trace class, without
diagonalizing away its cubic Cauchy incidence, and identify its ordinary operator trace.

## Conjecturing loop

### Conjecture 1 — summable kernel diagonal plus Hilbert--Schmidt control forces trace class

**False in general.** Hilbert--Schmidt membership and an absolutely summable diagonal do not control
singular-value sum for an indefinite operator. P-G105K therefore did not yet justify ordinary
determinant restoration.

### Conjecture 2 — finite Gram positivity is lost at the cofinal operator

**Falsified.** Every finite child block is a positive scalar diagonal congruence of the actual
P-G186 Gram block. Cofinal coordinate truncations are positive finite-rank operators and converge
in operator norm to the Hilbert--Schmidt represented child. Continuity of the quadratic form makes
the full child positive.

### Conjecture 3 — positivity still does not expose a reusable trace-class criterion

**Falsified constructively.** For a positive bounded operator `T`, let `R = sqrt(T)`. Exact identity
`R ∘ R = T` converts summability of one Hilbert-basis diagonal of `T` into square summability of
`R` on that basis. Thus `R` is Hilbert--Schmidt and `T = R ∘ R` is Schatten-one. This proves:

```text
T positive + summable basis diagonal  ==>  T is Schatten-one,
Tr(T) = sum of that diagonal.
```

No spectral enumeration or finite-rank approximation in trace norm is assumed.

### Conjecture 4 — child trace may differ from formal Stokes diagonal current

**Falsified exactly.** Canonical prime-basis diagonal equals transported prime weight pointwise.
The existing absolute summability and Stokes transport theorem therefore give ordinary operator
trace equal to oriented first-trace current.

## Paper proof

Finite source Gram positivity survives positive diagonal congruence. Coordinate truncations inherit
positive semidefiniteness, and their represented operators converge to full child in operator norm
because Hilbert--Schmidt convergence dominates operator norm. Hence full child is positive.

For positive `T`, functional calculus gives self-adjoint `R = sqrt(T)` and `R^2 = T`. Symmetry of
`R` identifies each diagonal entry of `T` with `||R e_i||^2`. Summability of diagonal makes `R`
Hilbert--Schmidt. Product of two Hilbert--Schmidt operators is Schatten-one, so `T` is trace class.
The standard trace factorization formula then identifies `Tr(T)` with the basis diagonal sum.
Applying this criterion to literal child and using exact transported-weight diagonal proves the
claimed Stokes trace. `QED`

## Novelty and anti-theatre audit

This closes P-G105L's main analytic obstruction:

- proves positivity of actual infinite cross-prime child, not a diagonal surrogate;
- derives Schatten-one nuclearity from source geometry;
- supplies reusable positive-diagonal trace-class theorem missing from local mathlib layer;
- identifies ordinary operator trace with arithmetic Stokes current exactly.

Result is not RH. It does not yet treat indefinite physical channel, finite ordinary determinant
convergence, aperture-wall convergence, or Xi divisor identification.

## Formal status

Lean proves unconditionally:

- every actual finite child block is positive semidefinite;
- truncation quadratic identity, self-adjointness, positivity, and operator-norm convergence;
- full child positivity;
- generic positive plus summable-basis-diagonal Schatten-one criterion;
- generic trace-equals-diagonal theorem under same hypotheses;
- literal child Schatten-one membership and exact ordinary Stokes trace;
- P-G105M capstone over every positive aperture.

Direct Lean and target-only module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Module is umbrella-wired; no umbrella build was run.

## Refined open core

Lift trace class through finite signed Hellinger channel without falsely asserting physical
positivity. Restore ordinary determinant with correct sign convention, prove finite determinant
identity and locally uniform cofinal convergence, then control `d -> 0+` divisor limit and identify
it with Xi without fitting.

## Higher universal principle

Trace class here is not a decay estimate stronger than Hilbert--Schmidt decay. It is an order
theorem: positivity turns a first-moment diagonal budget into singular-value summability through
square-root factorization. Earlier trace obstruction was a shadow of trying to estimate an
indefinite operator before separating its positive source components.

## Log

- 2026-08-16 — Cofinal positivity, positive-diagonal Schatten-one criterion, child nuclearity, and
  exact ordinary Stokes trace paper-proved and formalized.
