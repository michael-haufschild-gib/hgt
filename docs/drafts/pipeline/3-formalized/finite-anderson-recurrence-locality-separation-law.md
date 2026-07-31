# Finite Anderson recurrence–locality separation law

Status: formalized  
Label: `[LEAN-PROVED]`

## Result

Let \(T\) be any fixed finite Hermitian hopping matrix. For every reference
onsite potential, every finite observation horizon \(H\), and every
\(\varepsilon>0\), there are a positive hopping scale \(g>0\) and onsite
potential \(p\) such that the same Hamiltonian

\[
H_{g,p}=gT+\operatorname{diag}(p)
\]

has both:

\[
\operatorname{rank}_{\mathbb Q}
\{\lambda_j(H_{g,p})-\lambda_0(H_{g,p})\}_{j=1}^{n-1}
=n-1,
\]

and

\[
\max_{i\ne j}\sup_{|t|\le H}
\left|\langle i|e^{-itH_{g,p}}|j\rangle\right|
<\varepsilon.
\]

The first property follows because, for every fixed finite Hermitian hopping
matrix, maximally projective onsite potentials form a dense, residual,
full-Lebesgue-measure set. The second follows from uniform compact-time
continuity at the atomic limit. Density selects one onsite potential having
both properties.

## Formal trace

Generic spectral law:

- `finiteAndersonHamiltonian`
- `finiteAndersonProjectiveMaximalSet`
- `finiteAnderson_exists_maximallyProjective`
- `finiteAndersonProjectiveMaximalSet_dense_residual_fullMeasure`

Finite-horizon locality:

- `scaledFiniteAndersonHamiltonian`
- `FiniteHorizonOffDiagonalSmall`
- `eventually_joint_uniform_all_offDiagonal_small`
- `exists_positive_dense_good_uniform_all_offDiagonal_small`

Joined theorem:

- `scaledFiniteAndersonProjectiveMaximalSet`
- `scaledFiniteAndersonProjectiveMaximalSet_dense`
- `scaledFiniteAndersonHamiltonian_eq`
- `exists_finiteAnderson_maximalProjective_finiteHorizonLocalized`

Direct target checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/FiniteAndersonProjectiveGenericityLaw.lean
lake env lean GaloisForLFunctions/HTGeometry/FiniteAndersonObservationHorizonLocalityLaw.lean
lake env lean GaloisForLFunctions/HTGeometry/FiniteAndersonRecurrenceLocalitySeparationLaw.lean
```

passed on 30 July 2026.

Axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact interpretation

Finite-horizon spatial transition suppression does not force arithmetic
compression of the complete spectrum. Spatial motion and full-spectrum
recurrence dimension are independent in this precise finite-system sense.

## Forbidden extrapolations

This does not prove:

- infinite-time Anderson dynamical localization;
- exponential graph-distance decay;
- thermodynamic-limit localization;
- interacting many-body localization;
- a recurrence-time lower bound;
- visibility of full spectral rank to a localized state or local observable;
- experimental resolvability of exact rational rank.

## Hostile significance verdict

This repairs the manuscript's missing microscopic Anderson bridge. It remains
a `[BRIDGE]`, not a Nature anchor: localization plus generic spectral
nonresonance is established physics. A general-science claim still needs an
operational, non-vacuous local recurrence-time theorem for a preparable state
and bounded physical observable.
