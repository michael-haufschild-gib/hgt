# Finite cofactor hulls approach the half-plane curve

- **ID:** finite-cofactor-hulls-approach-the-half-plane-curve
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (Lean completion pending)
- **Parent:** [Q-III](q-iii-escape-state-classification.md)
- **Statement:** Every hull character of a finite-dimensional actual cofactor
  module is a pointwise limit, on the full critical Wiener algebra, of
  half-plane evaluations.

## Corpus evidence and exact scope

`le_norm_bohrEval_of_onTorus` in
`AKernelBoundedBelowOnTheHalfPlaneIsAUnit` constructs vertical characters
approximating finite sets of prime phases with common radial exponent.
Its extracted helper `exists_halfPlanePoint_approx_primes` uses
`primeTorus_cpow_dense`. The checked reusable sequence theorem lets the
prime aperture grow and combines prime factorization with dominated
convergence of absolutely summable Wiener coefficients. One sequence works
on every Wiener element simultaneously.

The pending finite-module modulus classification supplies either
`|omega(p)|=p^(-alpha)` for one alpha>=0 or augmentation. The former case
lies in the closure of the vertical line Re(s)=1/2+alpha. Augmentation
is approached as Re(s) tends to infinity. Values at zero are ignored
by all arithmetic-function evaluations; no artificial normalization of
raw Bohr points is needed for the character statement.

The finiteness hypothesis is finite Hilbert dimension, not merely finitely
many hull points. This is approximation by the whole half-plane curve. It does not assert
exact curve membership, approximation by translated zeta zeros, occurrence
of these points in actual modules, or a result for infinite module hulls.

## Formalization

The helper extraction and reuse passed final canonical audit `5652`.
Choose aperture j+1 and tolerance 1/(j+1). Prime coordinate convergence
extends to positive integers by factorization. Summable domination gives
convergence of all Wiener evaluations using the same sequence.
The augmentation endpoint is the unit-coefficient limit at real infinity.
`TiedBohrToriAreLimitsOfVerticalCharacters` passed required olean `95510`
and final canonical audit `10781`; all three axiom reports contain only
`propext`, `Classical.choice`, `Quot.sound`. The module is umbrella-wired.
Its exact final target is
`exists_halfPlane_sequence_tendsto_bohrEval_of_radial_or_augmentation`.

The common-eigenvector input is complete:
`HTGeometry.exists_common_eigenvector_family`, in
`FiniteCommutingFamiliesHaveCommonEigenvectors`, passed final canonical
source audit `15948` with only standard axioms. Its
olean is available to the written finite-hull application. Numeric operator
order passed required olean `68599` and final canonical audit `42266` with
standard axioms. The first full hull check found one unit-coercion mismatch
in `bohrCofactorCharacter`; it is repaired in the combined and standalone
drafts. Generic and actual common-eigencharacter magnitude lemmas had clean
axiom reports, but the dependent hull reports inherited the failed definition
and are not accepted. The complete retry `83688` passed with all five
standard-axiom reports in `/tmp/qiii-finite-hull-moduli-retry.log`.
The exact common eigenvector, modulus classification and one-sequence
half-plane approximation are now in canonical sources, with umbrella
imports. Individual import-boundary checks remain for
`MonotoneCriticalCharacterNormsArePowers`,
`CofactorEigencharacterMagnitudesArePowers` and
`FiniteCofactorHullsApproachTheHalfPlaneCurve`.
