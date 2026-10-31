# Finite Weil Gram errors give explicit index horizon tests

- **ID:** finite-weil-gram-errors-give-explicit-index-horizon-tests
- **Stage:** 3-formalized
- **Target:** State the finite inequalities that ensure an actual atomic synthesis
  retains the negative index of a fixed finite Weil family.

## Mechanism

For a real compact test `F` and perturbation `D` supported in `[-R,R]`, let
`|D|≤e` and `Levy(D)≤V=synthLevy(R,e,L,k)`. The existing upper perturbation
bound applies in both directions. Bound the perturbed base norms by

`a=√∫F²+√(2R)e`, `l=√Levy(F)+√V`,
`c=|coshMoment(F)|+|sinhMoment(F)|+4R cosh(R/2)e`.

Then `|Q(F+D)−Q(F)|≤weilErrBound(a,l,c,R,e,V)`.
Polarization gives an explicit entry error for the whole finite Gram matrix,
using `F_i±F_j`, `2e`, and `4V`. An entry bound smaller than the negative
spectral gap divided by the matrix size preserves its negative subspace.

The Euler–Maclaurin and logarithmic Denjoy–Carleman synthesis theorems
supply the actual errors. This yields a finite horizon test for each chosen
negative family, including the Steklov schedule. It does not give a bound on
unknown negative witnesses solely in terms of their dimension.

## Formalization

The [two-sided finite error and Gram bounds](../3-formalized/finite-weil-perturbations-have-a-two-sided-explicit-bound.md)
passed direct Lean and axiom audits. The [complete finite-family index certificate](../3-formalized/every-finite-weil-family-has-an-explicit-index-horizon-test.md)
also passed, including constructed derivative bounds and negative compression.
The fixed Steklov profile and every integer horizon are covered by the
[specialized certificate](steklov-index-certificates-cover-every-integer-horizon.md).
Both specialized caps passed direct Lean and transitive axiom audits.
