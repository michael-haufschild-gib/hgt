# Analytic-background saturation by maximal translation HT

- **ID:** `analytic-background-saturation-maximal-ht`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; affine background grafting; translation dynamics
- **Statement:** Every fixed analytic background on the upper half-plane admits a residual positive
  Herglotz perturbation whose real-translation orbit is maximally differentially independent; the
  perturbation is asymptotically constant, so the background's infinite cluster sets and limiting
  measures transfer unchanged up to one scalar translation.

## Setup

Let `H={z in C:Im z>0}`.  For `u in ell^infinity(R)`, set

`m_u(z)=sum_(k>=0) 2^(-k-1) exp(u_k)/(k+1-z)`,

`chi(w)=exp((w-i)/(w+i))`,

`S_u=chi o m_u`.                                             (1)

The positive finite measure behind `m_u` gives

`exp(-1)<|S_u(z)|<exp(1)`,                                   (2)

and, with `c=exp(-1)`,

`S_u(z+t)->c`                                                 (3)

locally uniformly on `H` as `t->+infinity` and as `t->-infinity`.

Fix an arbitrary `B in Hol(H)` and define

`G_(u,B)=S_u+B`.                                              (4)

## Analytic-background saturation theorem `[PROVED HERE]`

For every fixed `B in Hol(H)`, there is a comeager set

`U_B subset ell^infinity(R)`

such that, for every `u in U_B`, the family

`{G_(u,B)(z+t):t in R}`                                      (5)

is differentially algebraically independent over `C(z)`.

### Proof

Use the proof of the positive-Herglotz full-translation theorem, restricted to real shifts.  Fix a
finite distinct shift packet, a differential jet depth, and one finite support of expanded
differential monomials.  The real Cauchy-jet spanning lemma provides finitely many mass coordinates
whose variations realize arbitrary complex jets of all shifted `m_u` at a separated evaluation
packet.

The finite jet map induced by `chi` is triangular, with diagonal entry

`chi'(m)=chi(m) 2i/(m+i)^2 !=0`

at every derivative order because `m(H) subset H`.  Hence the same mass coordinates realize
arbitrary shifted jets of `S_u`.

Addition of the fixed background `B` is affine with derivative the identity.  It changes the value
of the universal jet-evaluation map but not its derivative in any mass direction.  Therefore the
universal mass--shift map for `G_(u,B)` is the same real submersion used in the unperturbed proof.

The rank-defect incidence locus for `R` monomials on `N` evaluation rows has complex codimension at
least

`N-q-R+1`,

where `q` is the largest coefficient degree in `z`.  Taking `N` larger than the real shift-parameter
dimension plus `q+R-1`, parametric transversality makes every bad preimage empty on a compact shift
patch.  Finite mass perturbations give density in `ell^infinity`, compact-patch avoidance is open,
and a countable exhaustion over shifts, jet depths, and monomial supports gives the comeager set by
Baire.  Clearing rational denominators identifies support avoidance with differential algebraic
independence over `C(z)`. `QED`

## All-power corollary `[PROVED HERE]`

For every `n>=1` and every `u in U_B`, the family

`{G_(u,B)(z+t)^n:t in R}`                                    (6)

is differentially algebraically independent.

Indeed, each translate is algebraic over its `n`-th power.  Differential dependence of a finite
power packet would keep differential transcendence degree below the packet cardinality after
adjoining the algebraic roots, contradicting (5).

## Invertible-outer cage `[PROVED HERE]`

If `B in H^infinity(H)` and

`norm(B)_infinity<c`,

then every `G_(u,B)` and its inverse belong to `H^infinity(H)`.  Equation (2) gives

`|G_(u,B)|>=c-norm(B)_infinity>0`.

An invertible bounded analytic function has no nonconstant inner factor, so it is outer.  Thus the
saturation theorem holds inside the invertible outer cone for every sufficiently small bounded
background.

## Exact asymptotic transfer `[PROVED HERE]`

Write `B_t(z)=B(z+t)` and `G_t(z)=G_(u,B)(z+t)`.  Equation (3) gives

`G_t-(c+B_t)->0`                                              (7)

in the compact-open topology as `t->+infinity` and as `t->-infinity`.

Define the infinite-parameter cluster set

`C_infty(B)={F: B_(t_j)->F for some |t_j|->infinity}`.

Then

`C_infty(G)=c+C_infty(B)`.                                   (8)

Both inclusions follow immediately from (7): the same parameter sequence has the two limits after
subtracting the vanishing error.

If the real-translation orbit of `B` is relatively compact in `Hol(H)`, then so is the orbit of
`G`; every sequence has either a bounded parameter subsequence or an unbounded subsequence to which
(7) applies.  In this case

`closure{G_t:t in R}={G_t:t in R} union (c+C_infty(B))`,       (9)

where the union need not be disjoint without an additional property of `B`.

## Limiting-measure transfer `[PROVED HERE]`

Assume the orbit of `B` is relatively compact.  Let `mu_T^B` and `mu_T^G` be normalized Lebesgue
measure on `[0,T]`, pushed forward by `t |-> B_t` and `t |-> G_t`, respectively.

If along a sequence `T_j->infinity`,

`mu_(T_j)^B -> mu`

weakly on the compact hull of `B`, then

`mu_(T_j)^G -> (F |-> c+F)_* mu`.                             (10)

To prove this, test against a continuous function on the compact union of the two hulls.  It is
uniformly continuous, while the compact-open distance between `G_t` and `c+B_t` tends to zero by
(7).  Their Cesaro averages therefore differ by a quantity tending to zero.  This proves (10).

In particular, every unique limiting distribution of the background transfers exactly to a
maximally HT translation orbit.

## Law extracted

**Analytic-background saturation law.**  Maximal differential-algebraic freedom of all finite real
translation packets is transverse to the entire fixed analytic background coordinate.  The HT
layer can be grafted onto a prescribed background without altering its infinite cluster geometry or
limiting measure, except for addition of the fixed scalar `exp(-1)`.

Consequently maximal translation HT alone determines none of the following background data:

- compact translation hull or infinite cluster set;
- recurrence and almost-periodic phase geometry;
- invariant or limiting probability measures;
- frequency embeddings and correlation-driving weights;
- DA versus HT type of the background itself.

## Exact RH-route consequence

Any proposed implementation which attempts to derive the following solely from maximal translation
HT is excluded:

1. the Voronin--Bagchi limiting law or strong recurrence;
2. the Bohr--Courant value-distribution hull;
3. the phase-frequency probability space used in Montgomery--Odlyzko/GUE heuristics;
4. a compact dynamical or statistical selector substituted for the Euler product.

Choose that desired or undesired analytic dynamics as the background `B`.  The theorem supplies a
maximally HT orbit asymptotic to it.  Thus the dynamics are an independent coordinate, not a
consequence of the HT matroid.

The full classical results are not refuted: they retain the pointed vertical zeta orbit, Euler
frequencies, explicit formula, and arithmetic measure.

## Attacks and boundaries

1. **The background is fixed before genericity.**  The residual set may depend on `B`; no uniform
   intersection over the uncountable space `Hol(H)` is claimed.
2. **Only real shifts are asserted.**  They preserve `H`.  Full complex translation requires a
   common continuation domain.
3. **Relative compactness is needed only for compact hull and measure statements.**  Maximal HT
   saturation itself holds for arbitrary analytic `B`.
4. **Closure components may intersect.**  Exact disjointness requires an additional decay,
   frequency, or differential-type argument, as supplied in the finite- and infinite-torus cards.
5. **No Euler normalization is preserved.**  The theorem is an information-content obstruction, not
   a zeta deformation.

## Scientific status

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

The theorem is complete and useful, but the parent-theory attack is decisive.  Once the positive
Cauchy-mass jet submersion has been proved, adding a fixed background is an affine map with identity
derivative.  The residual avoidance proof is unchanged, and asymptotic transfer follows directly
from the Stieltjes collapse.  The universal formulation was not found in the searched literature,
but it is a routine consequence of the existing transversality engine rather than a new mechanism.

Adjacent parent theory includes Forstneric holomorphic jet transversality, classical parametric
transversality, and compact-open almost-periodic hull theory.

## Lean status

No complete Lean claim is made.  The theorem requires the positive infinite-mass parameter space,
Baire category, rank-defect stratification, parametric transversality, holomorphic compact-open
hulls, and weak convergence of empirical measures.  The current tree has only isolated finite
algebraic and Kronecker components.  Partial formalization would not justify Stage 3.

## Gates

- [x] 0 -> 1: arbitrary analytic background isolated
- [x] 1 -> 2: complete unconditional paper proof
- [x] novelty verdict: routine affine stability of the existing transversality theorem; bridge
- [ ] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: publication-ready synthesis with the boundary-realization cards

## Cross-references

- `herglotz-full-translation-ht-krein-index-orthogonality.md`: mass-jet submersion parent.
- `maximal-ht-parabolic-orbit-collapse.md`: asymptotically constant HT layer.
- `toral-da-boundary-maximal-ht-outer-orbit.md`: finite DA background with exact torus boundary.
- `infinite-bohr-ht-boundary-maximal-ht-outer-orbit.md`: infinite HT background with exact `T^N`
  boundary and Haar law.

## Log

- 2026-07-11 -- Proved saturation for every fixed analytic background, all powers, small bounded
  outer carriers, exact infinite-cluster transfer, and limiting-measure transfer.
- 2026-07-11 -- Downgraded immediately to a bridge after the affine-parent attack.
