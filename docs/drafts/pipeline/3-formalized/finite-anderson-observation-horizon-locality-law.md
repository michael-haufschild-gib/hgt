# Finite Anderson observation-horizon locality law

Status: formalized  
Label: `[LEAN-PROVED]`

## Result

For any finite hopping matrix \(T\), onsite potential \(p\), observation
horizon \(H\), and tolerance \(\varepsilon>0\), consider

\[
H(g,p)=gT+\operatorname{diag}(p),\qquad
U_{g,p}(t)=e^{-itH(g,p)}.
\]

At the atomic limit \(g=0\), every off-diagonal site transition amplitude
vanishes exactly. Compact-time continuity strengthens this to a simultaneous
finite-horizon law:

\[
\forall\varepsilon>0\quad
\exists\text{ a neighborhood of }(0,p)\quad
\forall(g,p')\text{ in that neighborhood},\quad
\max_{i\ne j}\sup_{|t|\le H}|U_{g,p'}(t)_{ij}|<\varepsilon.
\]

Positive hopping strengths occur in every such neighborhood. More strongly,
if a property of onsite potentials is dense for every \(g>0\), one may choose
\(g>0\) and \(p'\) satisfying that property while preserving the uniform
transition bound.

## Formal trace

- `scaledFiniteAndersonHamiltonian`
- `finiteAndersonEvolution`
- `FiniteHorizonOffDiagonalSmall`
- `finiteAndersonEvolution_atomic_offDiagonal`
- `eventually_uniform_offDiagonal_small`
- `eventually_uniform_all_offDiagonal_small`
- `exists_positive_uniform_all_offDiagonal_small`
- `eventually_joint_uniform_all_offDiagonal_small`
- `exists_positive_dense_fiber_of_mem_nhds_prod`
- `exists_positive_dense_good_uniform_all_offDiagonal_small`

Direct target check:

```text
lake env lean GaloisForLFunctions/HTGeometry/FiniteAndersonObservationHorizonLocalityLaw.lean
```

passed on 30 July 2026.

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Physical boundary

This is an exact finite-system, finite-observation-horizon suppression law
near the atomic Anderson limit. It does not prove standard infinite-time
dynamical localization, exponential decay with graph distance, a
thermodynamic Anderson phase, or interacting many-body localization.

Its role is compositional: a dense spectral genericity property may coexist
with arbitrarily small finite-horizon spatial transitions. That coexistence
does not imply that global spectral recurrence rank is visible to a local
state or observable.

## Hostile significance verdict

The result closes one mathematical bridge but is not a general-science
headline. Localization plus generic spectral nonresonance is established
physics. Nature-level viability still requires a microscopic operational
theorem for a preparable state and bounded local observable, with a
non-vacuous robust recurrence-time law.
