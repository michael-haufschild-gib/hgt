# Operator decay alone controls the annihilator hull

- **ID:** operator-decay-alone-controls-the-annihilator-hull
- **Stage:** 5-failed
- **Type:** NO-GO, with formalized positive survivor
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
- **Failed claim:** Stronger dilation norms, even with exact homogeneous Gram
  scaling, force the full annihilator hull into the corresponding smaller
  Bohr polydisk.

For every `sigma>1/2`, the weighted orthogonal kernel
`K(j,k)=1_(j=k)j^(-2sigma)` has exact dilation norm `p^(-sigma)` and full mixed
scaling. Its critical Wiener action is faithful, so its annihilator hull is
the full polydisk. The all-one character belongs to that hull and is unbounded
in the represented operator norm, even allowing an arbitrary bound constant.
Exact power norms and the spectral-radius formula confirm the smaller
operator radius. The two spectral objects are therefore different.

The positive survivor is exact: the operator-norm-bounded Bohr hull is
nonempty, lies in the annihilator hull, and satisfies
`|omega(p)|<=sqrt(p)||V_p||`. Closed representation image identifies both hulls;
every finite-dimensional actual cofactor module has this property. On actual
escape the paid-ideal inclusion further places this operator hull inside the
obstruction hull.

The complete paper argument and Lean status are on
[the survivor card](../3-formalized/strong-dilation-contraction-does-not-shrink-the-annihilator-hull.md).
Canonical modules are AOT `WeightedOrthogonalCofactorsHaveTheFullHull`,
AOT `TheOperatorHullOfAWienerAction`, and ADR
`TheCofactorOperatorHullObeysItsDilationRadii`. All final source-only checks
passed with `lake --old env lean`; imports are wired. Transitive axiom audits
use only `propext`, `Classical.choice`, and `Quot.sound`.

This retires the generic spectral inference. The weighted family is not
proved to occur as a Möbius escape state; actual translated-zero containment
and Kronecker generation remain open.
