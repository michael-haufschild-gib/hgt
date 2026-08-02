# Pointed Cartan primal--dual alternative

- **ID:** `pointed-cartan-primal-dual-alternative`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Source:** corpus-wide parent law for the Riemann source/descent papers and HT Cartan comparison
- **Statement:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]` A nonzero exponential character cannot be neutralized by invariant positive transport: its real Cartan slope is either zero, killed into the primal seminorm radical, exposed as exact two-sided condition growth, excluded from the invariant-gauge dual, or retained only through an opposite-slope indefinite/graded sector.

## Goal

Replace route-by-route “transverse information” language by one exact rank-one Cartan law and make
clear that critical-line purity cannot be created by a regular completion.  Connect it to the
already formalized higher-rank HT theorem that bounded-conductor differential embeddings preserve
normalized Cartan vectors.

## Exact theorem

Let `E` be a complex vector space, let `V_t` be a real-parameter family of complex-linear maps,
and suppose

\[
                         V_t x=e^{tz}x
\]

for one vector `x` and one complex exponent `z`.  Put `mu=Re z`.  For every complex seminorm `p`,

\[
 p(V_t x)=e^{t\mu}p(x).                                      \tag{1}
\]

Consequently, for `t>=0`,

\[
 \max\{p(V_t x),p(V_{-t}x)\}=e^{t|\mu|}p(x).                \tag{2}
\]

If `p` is invariant on the orbit, then

\[
                         p(x)=0\quad\text{or}\quad\mu=0.    \tag{3}
\]

Thus a nonzero-slope sector maps into the radical of every invariant target seminorm.  Dually, if
a nonzero eigenfunctional `E_z` obeys `E_z(V_tu)=e^{tz}E_z(u)`, a finite nonnegative invariant
gauge dominates `E_z` if and only if `mu=0`.  On the reciprocal real plane of slopes `mu,-mu`,
every invariant symmetric form is a multiple of the cross form when `mu!=0`, and every invariant
positive-semidefinite form is zero.

There is a stronger dual-source form.  If `p(V_t u)=p(u)` and
`L(V_t u)=exp(t z)L(u)`, set `t_n=n Re z` and

\[
 u_n=\exp(-t_nz)V_{t_n}u.
\]

Then

\[
 L(u_n)=L(u),\qquad
 p(u_n)=\exp\!\left(-n(\Re z)^2\right)p(u).
\]

When `Re z != 0`, this is an explicit graph-null sequence with fixed nonzero output.  Consequently
the closed graph relation has a nonzero vertical fibre; over a scalar target, scaling makes that
fibre the whole target.  This is the abstract mechanism behind the exact Meyer Xi graph-closure
phase transition.

## Complete paper proof

Absolute homogeneity of a complex seminorm and `|exp(tz)|=exp(t Re z)` give `(1)`.  Applying `(1)`
at `t` and `-t`, factoring out the nonnegative number `p(x)`, and using

\[
 \max(e^{t\mu},e^{-t\mu})=e^{t|\mu|}
\]

gives `(2)`.  If `p(V_t x)=p(x)` and `p(x)!=0`, equation `(1)` at `t=1` gives
`exp(mu)=1`, hence `mu=0`; this proves `(3)`.

For the dual claim, choose `u` with `E_z(u)!=0`.  Invariance of a dominating gauge would bound
`exp(t mu)|E_z(u)|` in both time directions, impossible unless `mu=0`.  Conversely, at `mu=0`,
`g(u)=|E_z(u)|` is a finite invariant dominating gauge.  For the reciprocal plane, invariance of
`a x^2+2bxy+c y^2` under `(x,y) -> (e^{t mu}x,e^{-t mu}y)` forces `a=c=0`; positivity at `(1,1)`
and `(1,-1)` then forces `b=0`.

For the graph-null sequence, linearity and the dual character law cancel the two exponential
factors, so `L(u_n)=L(u)`.  Absolute homogeneity and invariance of `p` give
`p(u_n)=exp(-t_n Re z)p(u)=exp(-n(Re z)^2)p(u)`, which tends to zero when the real slope is nonzero.

No implication uses RH, a divisor, a completion, numerical evidence, or a target selected from a
spectrum.

## Universal shadow map

1. Complete-source collapse plus projective blow-up: `(2)` is inverse-conditioning growth.
2. Hedenmalm/Meyer dense radicals: `(3)` is the primal radical branch.
   The scaled dual-source sequence gives the stronger exact off-line graph verticality.
3. Half-density completion: zero Cartan slope is exactly its continuous actual-Xi spectrum.
4. Burnol--Sonin aperture vectors and Hedenmalm Borel tails: their logarithmic norm/condition
   exponent is `|mu|`, the scalar in `(2)`.
5. Burnol finite holonomy: `2 sinh(t mu)` is the oriented odd coordinate whose absolute size is
   determined by the condition factor in `(2)`.
6. Green codiagonal and reciprocal Paugam forms: opposite slopes pair invariantly, while each
   diagonal positive sector vanishes.
7. Rees sewing and finite-fibre grading: nonzero slope survives only through singular filtered
   retention; regular ungraded closure erases or verticalizes it.
8. HT differential embeddings: the proved bounded-conductor Cartan comparison is the finite-rank
   version of slope conservation; normalized Cartan vectors cannot be changed by regular
   differential re-embedding.
9. Quantum recurrence: projective gap rank belongs to the unitary/compact character coordinate;
   it is independent of the split Cartan slope and cannot alone force `(3)`.

## Hostile verdict

`[BRIDGE]`, not a novelty claim.  Equations `(1)--(3)` are elementary representation/seminorm
facts, and higher-rank Cartan comparison already exists in the corpus.  The gain is explanatory
compression and a sharper frontier, not standalone difficulty.  The arithmetic significance is
the consequence:

> Regular transport can reveal critical-line purity but cannot create it.  RH therefore requires
> a source-support theorem showing that the actual Xi annihilator selects only zero-Cartan
> characters before regular positive descent.

The minimal scalar form is boundedness of the target-free Gaussian evaluation orbit at every
actual Xi point.  The source-geometric form is inclusion of actual algebraic Xi support in the
continuous spectrum of the canonical half-density quotient.  A producer route must establish
this from ordinary-prime/Gamma/co-Poisson incidence; the finite common-Hardy reporter is proved,
while its presentation-independent infinite arithmetic mate remains open.

## Gates

- [x] 0 -> 1 in-progress: exact statement and shadow/falsity audit fixed
- [x] 1 -> 2 fully-proven: dependency-closed proof above
- [x] 2 -> 3 formalized: primal exact-growth/radical theorem; reuse existing dual and reciprocal-plane theorems
- [ ] 3 -> 4 publication-ready: integrate into the universal paper and antagonist audit

## Log

- 2026-08-02 — extracted the rank-one Cartan alternative from the source/transport corpus and
  identified HT bounded-conductor Cartan conservation as its higher-rank parent.
- 2026-08-02 — formalized exact reflected conditioning and invariant-seminorm radical alternative
  in `formal/GaloisForLFunctions/RHTower/PointedCartanSeminormConservationLaw.lean`; direct
  `lake env lean` verification passed.
- 2026-08-02 — strengthened the law after the live-corpus graph-closure result: formalized the
  universal dual-source graph-null sequence with fixed reporter output and exact
  `exp (-n (Re z)^2)` invariant-capacity decay.
