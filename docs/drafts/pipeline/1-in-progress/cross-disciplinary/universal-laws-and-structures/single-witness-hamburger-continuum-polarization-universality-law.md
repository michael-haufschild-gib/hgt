# Single-witness Hamburger continuum-polarization universality law

- **ID:** single-witness-hamburger-continuum-polarization-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of global bounded-kernel transfer, clopen first/second-kind
  polarization, and Nevanlinna-leaf indeterminacy
- **Statement:** One bounded complex kernel witness for a normalized positive Hamburger moment
  form forces a continuum of representing measures and, at every real point, simultaneous
  first-kind decay and recurrence-weighted second-kind escape.

## Goal

Eliminate the separate zero-base and closedness hypotheses from the corpus endpoints, then join
the global orthogonal-polynomial polarization to the full Nevanlinna representing-measure family.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed warning-free
- [x] 3 → 4 novelty audit: no exact statement found in searched literature

## Corpus inputs

- `boundedKernel_global`
- `isClosed_boundedKernel`
- `clopenKernel_firstSecondKind_complete_polarization`
- `injective_leaf_into_representing`
- `not_subsingleton_representing`

## Proof

**[PROVED HERE]** Let `s` be a positive moment form, normalized by `s 0 = 1`, and suppose
`BoundedKernel s z₀` at one arbitrary complex point. Global kernel transfer gives
`BoundedKernel s z` for every `z : ℂ`, in particular at `z = 0`. The bounded-kernel locus is
closed by the existing Nevanlinna-entire theorem, so the clopen polarization theorem applies to
the original witness. At every real `x` it gives:

- bounded aggregate first- and second-kind kernels;
- positive Christoffel limit;
- summability of normalized first-kind squares;
- convergence of orthonormal evaluations to zero;
- escape beyond every common bound by one of the two adjacent recurrence-weighted second-kind
  coordinates.

At zero, the transferred bounded-kernel witness and `s 0 = 1` feed the Nevanlinna leaf theorem.
It supplies an injective map from `OnePoint ℝ` into measures representing `s`. Hence the
representing-measure class is not a subsingleton. Conjoining these consequences proves the law.
No computation is used. ∎

## Strict gain over corpus endpoints

The polarization theorem assumes closedness and reports no representing measures. The
indeterminacy theorem assumes boundedness specifically at zero and reports no global
first/second-kind behavior. Global transfer discharges the zero-base condition from an arbitrary
complex witness, while the Nevanlinna-entire result discharges closedness. Their closure yields one
single-witness phase law connecting continuum nonuniqueness to global coordinate escape.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.SingleWitnessHamburgerContinuumPolarizationUniversalityLaw`
- Main theorem:
  `singleWitness_hamburgerContinuumPolarizationUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/HTGeometry/SingleWitnessHamburgerContinuumPolarizationUniversalityLaw.lean`
- Result: passed warning-free on 2026-07-23.
- Umbrella:
  `formal/GaloisForLFunctions/HTGeometry.lean`.

## Novelty audit

Performed only after exact Lean proof passed. Classical literature confirms the separate
indeterminate-moment ingredients: square-summability of first- and second-kind polynomials,
Nevanlinna parametrization, and entire Nevanlinna matrices. Searches did not locate the exact
single-witness theorem that additionally packages positive Christoffel limit, first-kind decay,
and escape of adjacent recurrence-weighted second-kind coordinates beyond every common bound.

Closest background:

- Berg–Szwarc, *Indeterminate Jacobi operators*, arXiv:2301.00586.
- Berg–Szwarc, *On the order of indeterminate moment problems*, arXiv:1310.0247.
- Pruckner–Reiffenstein–Woracek, *An upper bound for the Nevanlinna matrix of an indeterminate
  moment sequence*, arXiv:2307.10748.

These sources support the classical components and make clear that indeterminate moment problems
carry square-summable first/second-kind sequences and Nevanlinna families. No exact result matching
the proved recurrence-weighted escape conjunction was found. This is a negative search result, not
a priority claim.

## Log

- 2026-07-23 — terminal-symbol scan paired clopen polarization with the indeterminacy criterion.
- 2026-07-23 — corpus research exposed global transfer and unconditional closedness, eliminating
  both endpoint-specific auxiliary hypotheses.
- 2026-07-23 — dependency-closed proof completed before Lean source or literature search.
- 2026-07-23 — exact-file Lean check passed warning-free; module wired into HTGeometry umbrella.
- 2026-07-23 — post-proof literature audit found classical component results but no exact
  continuum-polarization law.
