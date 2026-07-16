# FE/Schwarz germ gluing is coefficient-gauge trivial

- **ID:** fe-schwarz-germ-gluing-gauge-trivialization
- **Stage:** 3-formalized
- **Type:** carrier-free local descent classification / no-go theorem
- **Status:** `[PROVED ON PAPER + LEAN]`

## Claim

For a rank-one complex germ line, the ordered FE and Schwarz identifications carry no
location-sensitive scalar invariant after the natural pointwise change-of-germ-basis gauge.

1. On a critical-line two-point orbit, the relative FE/Schwarz identification is an anti-linear
   involution `z |-> a * conj z`, hence `a * conj a = 1`.  There is a nonzero basis change `b` with
   `b^-1 * a * conj b = 1`; after a compatible basis choice at the partner point, both FE and
   Schwarz arrows have coefficient one.
2. On a free four-point orbit, a flat square with two complex-linear FE arrows and two anti-linear
   Schwarz arrows is vertexwise gauge-equivalent to the square whose four coefficients are one.

Consequently the separate scalar identifications do not refine the fixed/free orbit dichotomy.
The multiplicity-dependent leading-germ phase `(-1)^m` is also gauge-trivial (`b=1` in even degree,
`b=i` in odd degree) unless an independent orientation of the germ line is supplied.

## Competing moves and attack

- `[FALSIFIED A]` leading-coefficient phase distinguishes fixed from free divisor germs.
  **Attack:** anti-linear line reflections have one complex gauge class.  The phase `(-1)^m` is
  explicitly normalized for every `m`.
- `[FALSIFIED B]` the FE/Schwarz commutation square has a projective central defect.
  **Attack:** the completed scalar functional equations commute exactly; a nontrivial projective
  multiplier would be additional data, not an invariant forced by xi.  Its multiplier is formally
  proved equal to one.
- `[INTERFACE ABSENT C]` the prime-archimedean weld orients the germ line and prevents the gauge.
  **Attack:** the weld canonically orients its own real generator plane, but the existing source
  maps provide no canonical nonzero map to a divisor germ line.  Restricting gauges to positive
  real scalars would therefore insert the missing arithmetic attachment by hand.

## Formal theorem surface

- `antiLinearLineCoeff_sq_iff` identifies the exact involution equation.
- `exists_antiLinearCoeffGauge_eq_one` gives the explicit rank-one Hilbert-90 gauge.
- `germParityCoeff_gauge_trivial` kills the leading-jet parity phase as a complex-gauge invariant.
- `FixedOrbitFESchwarzGluing.exists_normalizingGauge` simultaneously normalizes the two arrows on a
  critical-line two-point orbit.
- `FreeOrbitFESchwarzGluing.projectiveMultiplier_eq_one` kills the proposed central multiplier.
- `FreeOrbitFESchwarzGluing.exists_normalizingVertexGauge` normalizes every flat free-orbit square.
- `scalarGluingDetector_factors_through_orbitShape` proves that every gauge-invariant scalar
  detector factors through one Boolean: fixed versus free orbit shape.

The implementation is
`formal/GaloisForLFunctions/RHTower/FESchwarzGermGluingTrivialization.lean` and is registered in the
`RHTower` umbrella.

## New open core

`[OPEN CORE]` Scalar ordered gluing is exhausted.  A surviving completed invariant must first
derive, from the arithmetic datum itself, a nontrivial reduction of the full complex germ-basis
gauge group: for example a prime grading together with a lattice, filtration, or pairing that the
allowed gauges must preserve.  Merely increasing rank is insufficient without such a reduction,
and merely assigning the prime character `p |-> p^(1-2 Re rho)` restates the zero's location (the
existing susceptibility balance).  The next theorem must therefore construct the reduction
functorially and prove that its obstruction is neither orbit shape, local extension residue,
analytic order, nor a continuous weld character encoding a hidden flow parameter.

## Novelty and significance gates

- **NOVEL:** the branch-specific ordered FE/Schwarz gluing problem is classified rather than
  guessed: both orbit shapes have a unique scalar gauge class and exact commutation leaves no
  projective residue.
- **SIGNIFICANT:** this closes the last scalar version of the live descent/gluing interface.  The
  fixed/free separator cannot come from leading phases, scalar holonomy, or separate arrow
  coefficients; the arithmetic reduction of gauge is now a necessary theorem, not optional
  decoration.
- **NON-TAUTOLOGICAL:** no analytic order or zero location appears in any definition or proof.

## Verification scope

The new module compiles directly and its exact module target builds.  The capstone axiom footprints
are `[propext, Classical.choice, Quot.sound]`.  The umbrella import was added textually; no
project-wide lint or full build was run.
