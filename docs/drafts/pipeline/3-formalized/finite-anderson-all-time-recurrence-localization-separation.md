# Finite Anderson all-time recurrence--localization separation

- **ID:** `finite-anderson-all-time-recurrence-localization-separation`
- **Stage:** 3-formalized
- **Type:** FINITE ANDERSON / UNIFORM-IN-TIME DYNAMICAL LOCALIZATION /
  PROJECTIVE RECURRENCE
- **Date:** 2026-07-31
- **Paper-proof status:** `[DEPENDENCY-CLOSED]`
- **Formal status:** `[CLOSED — AUDITED UNCONDITIONAL]`
- **Priority status:** `[EXTERNAL AUDIT OPEN]`

## Theorem

Let \(n\geq 1\), let \(T\in M_n(\mathbb C)\) be Hermitian, and let
\[
  H(p)=T+\operatorname{diag}(p_1,\ldots,p_n),
  \qquad p\in\mathbb R^n .
\]
Fix any off-diagonal tolerance profile \(b_{ij}>0\). Then there is
\(p\in\mathbb R^n\) such that:

1. the canonical spectrum of \(H(g,p)\) has maximal projective rational
   rank \(n-1\);
2. for every \(t\in\mathbb R\) and every \(i\ne j\),
   \[
     \left|\bigl(e^{-itH(p)}\bigr)_{ij}\right|<b_{ij}.
     \tag{1}
   \]

At the same time, completed sampling of the \(n-1\) relative spectral
phases converges to Haar probability on the full projective torus.

In particular, for every finite site metric \(d\) and every \(C,\mu>0\),
one may take
\[
  b_{ij}=C e^{-\mu d(i,j)}.
  \tag{2}
\]

If the off-diagonal support graph of \(T\) is connected, the selected
Hamiltonian has that same connected hopping graph.

## Proof

Put \(D_0=\operatorname{diag}(p^0)\). Its eigenvalues are simple. Choose
disjoint inner spectral intervals around the \(p^0_k\), and continuous
plateau functions equal to one on one inner interval and zero outside its
disjoint outer interval. Continuous functional calculus gives projections
\(P_k(A)\) for every nearby Hermitian matrix \(A\). They are idempotent,
commute with \(e^{-itA}\), and resolve the identity.

For a complete projection family \(P=(P_k)\), define the time-independent
mixing budget
\[
  B_{ji}(P)=\sum_{k,a,b}|P_k(j,a)|\,|P_k(b,i)|.
  \tag{3}
\]
If \(U\) is unitary and commutes with every \(P_k\), then
\[
  U=\sum_k P_kUP_k,
  \qquad |U_{ji}|\le B_{ji}(P).
  \tag{4}
\]
At the atomic point, \(P_k(D_0)=|k\rangle\langle k|\), so
\[
  B_{ji}(P(D_0))=0\qquad(i\ne j).
  \tag{5}
\]
Continuous functional calculus makes every \(A\mapsto B_{ji}(P(A))\)
continuous at \(D_0\). Because there are finitely many off-diagonal pairs,
all budgets lie below one common \(\varepsilon>0\) in a joint neighbourhood
of \(D_0\), where \(\varepsilon\le b_{ij}\) for every \(i\ne j\). Applying
`(4)` to \(U=e^{-itA}\) proves `(1)` simultaneously for every real time.

Continuity of \((g,p)\mapsto gT+\operatorname{diag}(p)\) gives a joint
neighbourhood of \((0,p^0)\) with this all-time property. For each fixed
positive \(g\), onsite packets with maximally projective canonical spectrum
are dense. The dense-fibre selection theorem supplies one \(g>0\) and one
onsite packet \(p\) in that neighbourhood with maximal projective rank.

Now divide the entire Hamiltonian by \(g\):
\[
  g^{-1}\bigl(gT+\operatorname{diag}(p)\bigr)
  =T+\operatorname{diag}(g^{-1}p).
  \tag{6}
\]
Maximal projective rank is invariant under nonzero real energy scaling, and
\[
  e^{-it\,g^{-1}H}=e^{-i(g^{-1}t)H}.
  \tag{7}
\]
Because the transition bound holds for every real time, `(7)` preserves it
exactly. This yields fixed hopping strength. The finite spectral Haar law
gives the completed Haar statement. The exponential specialization `(2)`
follows because its finitely many off-diagonal values are strictly
positive.

## Exact interpretation

The theorem removes the finite-observation-horizon qualifier from the
existing Anderson separation law:

> A connected nonzero-hopping system can remain uniformly localized at
> every time while its global recurrence orbit has the largest possible
> number of independent phases.

Spatial transport and completed recurrence dimension are therefore
independent invariants even inside one finite Anderson family.  Eigenvector
locality controls which phases a site can see; rational eigenvalue
relations control the dimension of the completed global phase orbit.

## Formalization

Implemented in:

- `FiniteSpectralClusterUniformLocalityLaw.lean`
- `FiniteAndersonAllTimeRecurrenceLocalitySeparationLaw.lean`

Capstones:

- `eventually_joint_allTimeOffDiagonalSmall`
- `exists_finiteAnderson_maximalProjective_allTimeLocalized`
- `exists_finiteAnderson_maximalProjective_allTimeLocalized_of_injective`
- `exists_finiteAnderson_maximalProjective_allTimeBelow_of_injective`
- `exists_finiteAnderson_maximalProjective_exponentialLocality_of_injective`
- `exists_finiteAnderson_fixedHopping_maximalProjective_allTimeBelow_any`
- `exists_finiteAnderson_fixedHopping_maximalProjective_exponentialLocality_any`
- `exists_finiteAnderson_fixedHopping_exponentialLocality_fullHaar`
- `scaledFiniteAnderson_projectivePhase_tendsto_haar`

The formal proof uses continuous plateau functional calculus rather than
Riesz contours.  Separated spectral clusters yield exact idempotent
projections resolving the identity.  Their finite entrywise mixing budget
is continuous, vanishes at the atomic point, and bounds every propagator
entry uniformly over all real times.  This closes the all-time gap without
compact-time continuity.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Hostile boundaries

1. This is a finite-dimensional theorem. It does not prove localization
   for an infinite random Anderson operator.
2. The onsite scale is existential and comes from a rescaled atomic-limit
   argument; no probability lower bound for a named disorder ensemble is
   asserted.
3. The required onsite scale may grow with system size and with the inverse
   of the smallest requested envelope value. Equation `(2)` is therefore not a
   volume-uniform localization-length theorem.
4. Maximal projective rank is an exact completed-time invariant, not a
   finite-noise phase discriminator.
5. Uniform site-transition suppression does not imply an interacting
   many-body localized phase.
6. The result proves coexistence, not that localization causes maximal
   recurrence rank.

## Gates

- [x] dependency-closed paper proof
- [x] fixed hopping strength
- [x] all real times
- [x] maximal projective rank in the same Hamiltonian
- [x] full projective Haar completion
- [x] arbitrary positive finite spatial envelope
- [x] finite-volume exponential spatial specialization
- [x] Lean spectral-projector continuity
- [x] Lean all-time propagator decomposition
- [x] Lean capstone
- [ ] external priority audit
