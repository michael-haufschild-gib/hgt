# Finite cofactor hulls approach the half-plane curve

- **ID:** finite-cofactor-hulls-approach-the-half-plane-curve
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
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

The finite-module modulus classification supplies either
`|omega(p)|=p^(-alpha)` for one alpha>=0 or augmentation. The former case
lies in the closure of the vertical line Re(s)=1/2+alpha. Augmentation
is approached as Re(s) tends to infinity. Values at zero are ignored
by all arithmetic-function evaluations; no artificial normalization of
raw Bohr points is needed for the character statement.

The finiteness hypothesis is finite Hilbert dimension, not merely finitely
many hull points. This is approximation by the whole half-plane curve. It does not assert
exact curve membership, approximation by translated zeta zeros, occurrence
of these points in actual modules, or a result for infinite module hulls.

## Finite-dimensional modulus argument

Each hull character has a nonzero joint generalized character space.
Restrict the commuting Wiener action to that finite-dimensional space and
choose a common eigenvector. An eigenvector in a generalized eigenspace has
the same eigenvalue, so its dilation character is
`chi(p)=omega(p)/sqrt(p)`.

The complete-module horizon inequality makes `p*|chi(p)|^2` antitone in
ordinary integer order. It is nonnegative and multiplicative. The checked
Archimedean classification therefore makes `chi` augmentation or gives
`|chi(p)|=p^(-s)` for one `s>=1/2`. Thus `omega` is augmentation on positive
coordinates or has `|omega(p)|=p^(-alpha)`, `alpha=s-1/2>=0`. Apply the
simultaneous tied-torus or augmentation sequence to obtain the claimed
limit on every Wiener element.

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
source audit `15948` with only standard axioms. Numeric operator order passed
required olean `68599` and final canonical audit `42266` with standard axioms.
The completed modulus and hull leaves are umbrella-wired:

| Canonical module | Final source-only audit | Main declaration |
|---|---|---|
| `HTGeometry/MonotoneCriticalCharacterNormsArePowers` | `64788` | `character_norm_eq_augmentation_or_rpow` |
| `ArithmeticDefectRigidity/CofactorEigencharacterMagnitudesArePowers` | `82260` | `eigencharacter_norm_eq_augmentation_or_rpow` |
| `ArithmeticDefectRigidity/FiniteCofactorHullsApproachTheHalfPlaneCurve` | `82346` | `exists_halfPlane_sequence_of_mem_finite_moduleHull` |

The final application also audits `exists_eigenvector_of_mem_finite_moduleHull`
and `finite_moduleHull_modulus_classification`. Every report contains only
`propext`, `Classical.choice`, `Quot.sound`. Output:
`/tmp/qiii-finite-hull-canonical-final.log`. No theorem on this card remains
paper-only.
