# Compact-observer local-gauge and cofinal-horizon law

- **ID:** `cmr-compact-observer-local-gauge-cofinal-horizon`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / CLASSICAL FUNCTIONAL-ANALYTIC CALIBRATION /
  CONDITIONAL ROUTE TEMPLATE
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [CLASSICAL COMPACTNESS CORE]`
  `[HT/TOPOLOGY/SPECTRAL INTERFACE] [NOT RH] [LEAN-FORMALIZED UNCONDITIONALLY]`
- **Formalized companion:** `compact-observer-local-gauge-cofinal-horizon-law-formalized.md`
- **Statement:** A compact observer can be exactly invertible on every finite source chart while
  every cofinal family of inverse gauges becomes singular; its positive shadow retains the same
  singular-value horizon, and every bounded source history has relatively compact observed image.

## 1. Why this theorem is a falsifiable chart-level calibration

The corpus repeatedly exhibits the same apparent paradox:

1. every finite aperture, jet order, or reporter family is exact;
2. the cofinal observer loses a direction, acquires a vertical relation, or needs unbounded
   reconstruction cost;
3. a positive or recurrent shadow remains well behaved after the lifted history has escaped.

The theorem below identifies one precise mechanism producing all three effects. It does not say
that every route is a compact-operator chart. Its use is falsifiable: a route belongs to this
chart only after constructing the Hilbert source, compact observer, cofinal finite source tower,
and any claimed time action.

## 2. Compact-observer uncertainty theorem

Let `H` and `Y` be Hilbert spaces over `R` or `C`, with `H` infinite dimensional. Let

\[
 K:H\longrightarrow Y
\tag{COH.1}
\]

be compact. Let

\[
 H_1\subset H_2\subset\cdots\subset H,
 \qquad \overline{\bigcup_nH_n}=H,
\tag{COH.2}
\]

be finite-dimensional subspaces, and assume every restriction `K_n=K|H_n` is injective. Define

\[
 \sigma_n=\min_{\substack{x\in H_n\\\|x\|=1}}\|Kx\|,
 \qquad
 \mathcal E_n=\sigma_n^{-2}.
\tag{COH.3}
\]

### Theorem 2.1 — finite exactness forces a cofinal reconstruction horizon

Under `(COH.1)`--`(COH.3)`:

1. `sigma_n>0` for every `n`;
2. `sigma_n` is nonincreasing and `sigma_n->0`;
3. the inverse

   \[
    R_n:K(H_n)\longrightarrow H_n,
    \qquad R_n(Kx)=x,
   \]

   has operator norm `||R_n||=sigma_n^(-1)->infinity`;
4. for source energy `||x||^2`, the worst-case unit-output reconstruction energy is

   \[
    \mathcal E_n=
    \sup_{\substack{y\in K(H_n)\\\|y\|=1}}\|R_ny\|^2
    =\|R_n\|^2=\sigma_n^{-2}\longrightarrow\infty;
   \tag{COH.3a}
   \]
5. there is no bounded operator `R:closure(K(H))->H` satisfying `RK=id_H`.

Thus every finite chart is an exact local gauge, but no uniformly admitted cofinal inverse gauge
exists.

### Proof

The unit sphere of finite-dimensional `H_n` is compact. The continuous function `x->||Kx||` is
strictly positive there because `K_n` is injective, so it has a positive minimum `sigma_n`.
Nestedness gives `sigma_(n+1)<=sigma_n`.

Suppose `sigma_n` did not tend to zero. Monotonicity would give a number `c>0` such that

\[
 c\|x\|\leq\|Kx\|
\tag{COH.4}
\]

for every `x` in `union_n H_n`. By density and continuity, `(COH.4)` would hold on all of `H`.
The image under `K` of the unit ball would then have inverse-Lipschitz preimage equal to the unit
ball of `H`. Compactness of `K` would make that unit ball totally bounded; completeness would make
it compact. A normed space with compact unit ball is finite dimensional, contradicting the
hypothesis. Therefore `sigma_n->0`.

For `y=Kx` with `x in H_n`,

\[
 \|R_ny\|=\|x\|\leq\sigma_n^{-1}\|Kx\|=
 \sigma_n^{-1}\|y\|.
\]

Unit vectors approaching the minimum in `(COH.3)` give equality, so
`||R_n||=sigma_n^(-1)`. This proves (3) and `(COH.3a)`. A bounded global left inverse would imply
`||x||<=||R|| ||Kx||`, contradicting `sigma_n->0`. This proves (5). QED.

## 3. Positive shadow and lost output phase

Set

\[
 A=K^*K:H\longrightarrow H.
\tag{COH.5}
\]

Then `A` is positive and compact. If `P_n:H->H_n` is the orthogonal projection, set

\[
 A_n=P_nA|_{H_n}=K_n^*K_n:H_n\longrightarrow H_n.
\tag{COH.5a}
\]

Then

\[
 \sigma_n^2=min_{\substack{x\in H_n\\\|x\|=1}}\langle Ax,x\rangle.
\tag{COH.6}
\]

Consequently `lambda_min(A_n)=sigma_n^2->0`: the compressed positive metric has the same cofinal
horizon, and its worst-case inverse energy diverges.

For every orthogonal/unitary `W:Y->Y` over `R/C`, respectively,

\[
 (WK)^*(WK)=K^*K.
\tag{COH.7}
\]

The Gram map retains the modulus `|K|=(K^*K)^(1/2)` and forgets polar partial-isometry data. It is
invariant under output orthogonal/unitary transformations. Equality of Gram operators is one
output-unitary orbit only under additional defect-dimension hypotheses. This is the exact scope
in which this specified Gram reduction is polar-data blind; it does not imply that every positive
route is a phase quotient.

## 4. Compact observed image and open lifted history

Let `S` be any set and `x:S->H` a bounded source history. Compactness of `K` implies

\[
 \overline{\{Kx(s):s\in S\}}\subset Y
\tag{COH.8}
\]

is compact. Hence a bounded lifted history can have a closed compact observer image without being
precompact in the source.

The implication is strict. Take `H=Y=ell^2(N)`, let `(e_n)` be its standard basis, and choose
positive `a_n->0`. Define `Ke_n=a_ne_n`. Then `K` is compact and injective,

\[
 \|e_m-e_n\|=\sqrt2\quad(m\ne n),
 \qquad Ke_n\longrightarrow0.
\tag{COH.9}
\]

The source history is open/nonprecompact while its observed history closes at one point. This is
compactification, not recurrence by itself. Exact recurrence additionally requires an integral
phase lattice or another dynamical structure; compactness alone does not manufacture it.

## 5. Hypertranscendental corollary

Suppose a named differential source generator has independent jet directions through every order,
and a Hilbert realization sends their spans to a nested tower `H_n` satisfying `(COH.2)`. If a
compact observer is injective on every finite jet span, then its finite-jet inverse reconstruction
norms diverge by Theorem 2.1. If one uses the standard condition number
`kappa(K_n)=||K_n||||R_n||`, then `||K_n||>=||K_1||>0`, so `kappa(K_n)->infinity` as well.

Therefore:

> **HT/compact-observer uncertainty.** Persistent independent jet growth, compact observation,
> and uniformly bounded exact reconstruction cannot coexist in one Hilbert chart.

Hypertranscendence is not defined as noncompactness. It supplies the unbounded independent tower;
compactness of the chosen observer produces the horizon. A finite or recurrent observer may still
coexist with HT because exactness is only finite-level and its inverse cost diverges.

## 6. Observation-density consequence

The observer `K` may be injective, so its values separate source points algebraically. Nevertheless
Theorem 2.1 proves that separation does not imply stable reconstruction. This theorem proves no
statement about arbitrary faithful or dense nerves. It shows that when such observation is
additionally realized by a compact Hilbert operator, algebraic separation/density supplies no
coercivity estimate; stable reconstruction requires an independent enriched/topological
admission law. This gives two distinct gates in this Hilbert chart:

1. **density:** do probes distinguish and reconstruct the source object algebraically?;
2. **coercivity:** are the reconstruction maps uniformly admitted in the chosen topology/cost
   doctrine?

Collapsing these gates is the mathematical form of the corpus's precision complementarity in this
chart: passing from the compact observer `K` to its positive Gram shadow `K^*K` can preserve
finite-level information while forcing cofinal inverse cost to infinity.

## 7. Route scope and falsifiers

| Organ | What must be constructed before applying the theorem | Status |
|---|---|---|
| differential/HT | Hilbert realization of an unbounded independent jet tower and compact reporter | conditional prediction |
| spectral/Fourier | compact finite-window or smoothing observer on a dense spectral source tower | direct mechanism available in corpus |
| topology/completion | observer whose singular values encode the algebraic-to-continuous loss | compatible with prime-port and graph-horizon laws |
| recurrence/history | separate integral phase action plus compact observer image | compactness alone insufficient |
| positivity | positive shadow exactly of form `K^*K` | exact when constructed |
| Route E | fixed compact Hilbert observer for cofinal incidence/capacity tower | not constructed |
| Mass | linearization preserving affine successor orientation | not constructed; affine datum may escape theorem |
| Stokes | cofinal compact source observer behind finite inertia chart | not constructed |
| Routes G/L/O/R | literal `H,K,H_n` with source-proven admission | open route-by-route |

The theorem is falsified as an explanation of a route if any required object above is absent. It
is not a universal matrix re-encoding of the corpus.

## 8. Conjecture/proof/failure loops

### Loop A — finite uniformly stable exactness should pass to the limit

**Failed.** The diagonal model `(COH.9)` is globally injective, so its algebraic inverse exists on
`K(H)`, but that inverse is unbounded. Its finite inverse norms are
`max_(j<=n)a_j^(-1)` and diverge.

**Survivor.** Uniformly stable cofinal exactness requires a uniform lower bound, not levelwise
injectivity.

### Loop B — compactness creates recurrence

**Failed.** Compactness gives relatively compact observed image, not a recurrent action.

**Survivor.** Recurrence requires separate integral/phase transport; compact observation explains
only why its projected closure can remain small.

### Loop C — positivity is always phase quotient

**Failed.** `(COH.7)` proves this only for the specified Gram reduction `K->K^*K`.

**Survivor.** For any specified positive reduction, identify its full information fibre. For
`K mapsto K^*K`, the forgotten datum is the polar partial isometry; it is not generally a single
output-symmetry orbit.

### Loop D — every cofinal horizon is curvature

**Failed.** The singular inverse in Theorem 2.1 exists without a comparison loop or connection.

**Survivor.** The intrinsic datum here is coercivity collapse. It becomes curvature or holonomy
only after a typed connection/comparison square is constructed.

## 9. Predictions

1. Any compact observer claimed to reconstruct an infinite HT or spectral tower with uniformly
   bounded inverse is impossible.
2. If every finite proof route is exact but its source-to-observer singular floor tends to zero,
   adding more finite certificates cannot provide bounded exact inversion. One must change the
   source topology/norm, use a noncompact or richer observer, weaken or renormalize cost, restrict
   the admitted source class, accept approximate regularization, or accept unbounded inversion.
3. A positive master constraint `K^*K` can determine the reconstruction horizon while remaining
   unable to determine output phase or orientation.
4. Compactness alone supplies no path-action reconstruction theorem. Non-determination requires
   two admitted lifted histories with identical observed endpoint data and unequal action, as in
   the separate GHZ history theorem.
5. A proposed universal geometry that records only algebraic observer density but no coercivity
   profile cannot explain the finite-to-cofinal obstructions.

## 10. Formal support

Formalized; see the companion certificate. The corpus already contains the load-bearing compact
bounded-below theorem in
`formal/GaloisForLFunctions/HTGeometry/CompactOperatorBoundedBelow.lean`, especially
`finiteDimensional_of_isCompactOperator_of_bounded_below`. A later formalization can build the
nested-subspace singular-floor corollary on that theorem. Approximation-number support exists in
`formal/GaloisForLFunctions/RHTower/ApproximationNumberLowerBound.lean`. Compact finite-window
observer parents exist in
`formal/GaloisForLFunctions/RHTower/FiniteTimeBandFourierCompact.lean`.

## 11. Hostile status

The functional-analytic core is classical. This conditional route template places finite local
gauges, positive metric, cofinal inverse horizon, and compact observed history as four exact
shadows of one compact observer. It is a classical functional-analytic calibration, not a source
equation, not a proof that every route is a gauge, and not progress on the final RH selector by
itself.

## Log

- 2026-08-09 — theorem and proof closed on paper.
- 2026-08-11 — formalized unconditionally in Lean 4.
