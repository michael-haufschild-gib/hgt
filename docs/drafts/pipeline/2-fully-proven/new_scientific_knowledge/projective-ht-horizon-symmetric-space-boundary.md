# Projective HT horizons are a symmetric-space boundary at infinity

- **ID:** `projective-ht-horizon-symmetric-space-boundary`
- **Stage:** 2-fully-proven
- **Type:** NONPOSITIVELY CURVED OBSERVER GEOMETRY / TITS BOUNDARY
- **Scientific status:** `[PROVED CONSEQUENCE OVER C] [NOVEL INTERPRETATION CANDIDATE]`
- **Parents:** `projective-horizon-tits-building`,
  `projective-horizon-solomon-tits-topological-charge`
- **Statement:** Over the complex constants, the incidence geometry of common projective HT
  derivative horizons is equivariantly the Tits boundary at infinity of the symmetric space of
  unit-determinant Hermitian observer metrics.

## Complex specialization

Specialize the constant field to `C`. Let `V=C^N` and let

```text
X_N=SL_N(C)/SU(N).                                        (1)
```

The space `X_N` is equivalently the Riemannian symmetric space of positive-definite Hermitian
forms on `V` with determinant one. It is noncompact, nonpositively curved, and has real rank
`N-1`.

The projective HT horizon theorem supplies the spherical building

```text
Delta_HT(V)={nontrivial common-horizon fields mathcal I_S} (2)
```

with flags ordered by reverse field inclusion.

## Theorem

There is a `PGL_N(C)`-equivariant isomorphism of spherical buildings

```text
Delta_HT(V) congruent boundary_Tits X_N.                  (3)
```

Under `(3)`:

- an elementary hyperplane horizon is a vertex at infinity of the corresponding maximal
  parabolic type;
- a strict chain of common-horizon fields is a Weyl simplex at infinity;
- a complete projective observer frame gives an apartment, the Tits boundary of a maximal flat in
  `X_N`;
- the apartment sphere has dimension `N-2`;
- the Steinberg horizon class is the top homology class of the building at infinity.

## Proof

The parent horizon theorem identifies `Delta_HT(V)` with the flag complex of nonzero proper
subspaces of `V*`. The classical boundary theorem for noncompact symmetric spaces identifies
`boundary_Tits(SL_N(C)/SU(N))` with the spherical building of proper parabolic subgroups of
`SL_N(C)`. Using the dual defining representation, this is precisely the flag complex of nonzero
proper subspaces of `V*`, with the contragredient projective action. This direct identification is
`(3)`. Using Hermitian orthogonal complements instead gives the equivalent type-reversing model
through the standard diagram automorphism.

## Metric-degeneration description

Choose the identity Hermitian form as basepoint. A geodesic ray in `X_N` has the form

```text
H_A(t)=exp(tA),                                            (4)
```

where `A` is traceless Hermitian. Its endpoint in the Tits boundary is determined by the flag of
eigenspace sums ordered by the eigenvalues of `A`.

- distinct eigenvalues give a chamber, hence a complete chain of common-horizon fields;
- repeated eigenvalues give a face, hence a partial horizon chain;
- commuting choices of `A` lie in one maximal flat and give one apartment.

Thus every asymptotic degeneration pattern of an observer metric has a precise field label, and
every horizon flag arises from such a degeneration.

## Physical content and boundary discipline

Equation `(3)` is a literal boundary-at-infinity theorem. It gives the projective HT information
geometry a nonpositively curved bulk whose asymptotic directions are exactly horizon contexts.
The parameter `t` in `(4)` is the scale of observer-metric degeneration. It is not a time variable,
not a flow generating the HT source, and not evidence of source dynamics.

This is the strongest justified holographic statement currently available:

```text
HT horizon context geometry = Tits boundary of observer-metric space. (5)
```

It is not a black-hole horizon. No Lorentzian metric, causal structure, Einstein equation,
Hamiltonian, entropy-area law, temperature, or quantum state has been produced. The symmetric
space is attached to projective observer frames, not asserted to be physical spacetime.

## Relation to the nature of hypertranscendence

A jointly HT projective source has maximally free jets, so the full projective observer group acts
faithfully on its differential rational field and the generic-orbit dimension arguments recover
every building face without accidental field identifications. Its observer contexts therefore
have the complete type-`A_(N-1)` boundary geometry. Some specially projectively invariant
differential equations may retain part or all of this group action, so no converse characterization
of HT is asserted here.

The result reframes hypertranscendence as maximal projective boundary thickness: every parabolic
direction and every flag of observer degenerations survives as a distinct differential subfield.

## Novelty and significance gate

- The Tits-boundary description of `SL_N(C)/SU(N)` is classical.
- The horizon building and its realization by differential fixed fields are the new candidate
  content of the parent theorem.
- The new conclusion is their equivariant identification `(3)`, which turns the horizon topology
  into an actual boundary at infinity and supplies the observer-metric bulk interpretation.
- No checked source relates derivative horizons of HT sources to this symmetric-space boundary.

The physical terminology is subordinate to `(3)`; it adds no unsupported dynamics.

## Lean boundary

The arbitrary-dimensional two-chart complementarity feeding the vertices of `(2)` is formalized
in `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonBuilding.lean`. The local Lean
environment has no formal Tits-boundary/symmetric-space library, so `(3)` is not encoded by an
axiom or placeholder.

## RH impact audit

`[GEOMETRIC ORGANISING POSSIBILITY; NOT RH PROGRESS]` A canonical projective zeta observation
could place its horizon flags on the Tits boundary of an observer-metric symmetric space. No map
from that boundary to Weil positivity, the critical line, or zero exclusion is known.

## Gates

- [x] 0 -> 1: literal boundary candidate separated from spacetime and black-hole metaphors
- [x] 1 -> 2: equivariant building-at-infinity identification proved
- [ ] 2 -> 3: parent reconstruction core formalized; symmetric-space boundary unavailable in Lean
- [ ] 3 -> 4: external audit in symmetric spaces and projective differential invariants

## References

- The classical theorem that the Tits boundary of a symmetric space of noncompact type is its
  spherical building at infinity.
- J. Tits, *Buildings of Spherical Type and Finite BN-Pairs*.
- L. Ji, *Buildings and their applications in geometry and topology*.

## Log

- 2026-07-15 — identified the horizon building with the Tits boundary of
  `SL_N(C)/SU(N)` and separated observer-metric degeneration from source time evolution.
