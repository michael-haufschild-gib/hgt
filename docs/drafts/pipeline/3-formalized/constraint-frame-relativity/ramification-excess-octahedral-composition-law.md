# Ramification marked split-defect composition and inherited-observer blindness law

- **ID:** `cfr-ramification-excess-octahedral`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / MARKED SPLIT DEFECT / FORMATION NO-GO
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [HOSTILE-AUDITED] [SOURCE-ASYMMETRIC SPLIT DEFECT] [STRICT COMPOSITION] [ANALYTIC EXCESS RETAINED] [FORMATION NO-GO FOR INHERITED OBSERVERS] [NOT CURVATURE] [NOT NONTRIVIAL COHOMOLOGY] [NOT RH] [FORMALIZED IN LEAN]`
- **Formalized companion:** `ramification-excess-octahedral-composition-law-formalized.md`
- **Statement:** A ramification power event splits the higher shell into inherited image and a
  nonzero new-law sector. For composable power events these excess sectors satisfy a canonical
  split exact sequence and crossed cocycle identity. Every observer factoring through perfect-power
  restriction annihilates the excess, while inherited data together with the excess projection
  reconstruct the full coefficient law.

## Goal

Retain the source asymmetry erased by the flat escort--logit comparison. The arithmetic map
`P_r(k)=k^r` is injective but not surjective on the higher shell. Its complement must become a
typed relative-law object with a composition law, not an unnamed remainder.

## 1. Shell supports and coefficient modules

For `m>=2`, let

\[
 A_m=\{n\ge2:\max_pv_p(n)=m\}.
\tag{RE.1}
\]

For an integer `r>=1`, the power map restricts to an injection

\[
 P_r:A_m\hookrightarrow A_{rm},
 \qquad k\longmapsto k^r.
\tag{RE.2}
\]

Define its excess support

\[
 X_{m,r}=A_{rm}\setminus P_r(A_m).
\tag{RE.3}
\]

Equivalently,

\[
 X_{m,r}=\{N\in A_{rm}:\text{some }v_p(N)\text{ is not divisible by }r\}.
\tag{RE.3a}
\]

Indeed, `N in A_(rm)` is an `r`-th power precisely when every prime valuation is divisible by
`r`; its unique positive `r`-th root then lies in `A_m`.

For a field `K`, put

\[
 V_m=K^{(A_m)},
 \qquad E_{m,r}=K^{(X_{m,r})},
\tag{RE.4}
\]

where the superscript denotes finite-support functions. Let `J_(m,r):V_m->V_(rm)` send the basis
vector `e_k` to `e_(k^r)`. Let `R_(m,r):V_(rm)->V_m` send `e_(k^r)` to `e_k` and kill every
basis vector indexed by `X_(m,r)`. Let `Q_(m,r):V_(rm)->E_(m,r)` be coordinate projection to the
excess support.

### Theorem 1.1 — inherited/excess reconstruction

There is a canonical split exact sequence

\[
 \boxed{
 0\longrightarrow V_m\xrightarrow{J_{m,r}}V_{rm}
 \xrightarrow{Q_{m,r}}E_{m,r}\longrightarrow0,}
\tag{RE.5}
\]

with

\[
 R_{m,r}J_{m,r}=1_{V_m},
 \qquad
 V_{rm}=J_{m,r}V_m\oplus E_{m,r}.
\tag{RE.6}
\]

For `r>=2`, the excess is nonzero; `e_(2^(rm)3)` belongs to it.

### Proof

The valuation identity

\[
 \max_pv_p(k^r)=r\max_pv_p(k)
\]

proves `(RE.2)`. The supports `P_r(A_m)` and `X_(m,r)` form a disjoint partition of `A_(rm)`.
The displayed basis maps therefore give the direct sum and split exact sequence. Finally,
`2^(rm)3` lies in `A_(rm)` but is not an `r`-th power because its `3`-valuation is one.
`[PROVED HERE]`

Thus the pair `(R_(m,r),Q_(m,r))` is a coefficient-faithful observer:

\[
 (R_{m,r},Q_{m,r}):V_{rm}\xrightarrow{\sim}V_m\oplus E_{m,r}.
\tag{RE.7}
\]

The inherited observer `R_(m,r)` alone is not conservative; its kernel is exactly the new-law
sector.

## 2. Composition and the excess cocycle

Fix positive integers `r,s`. The map `P_s` sends `X_(m,r)` injectively into `A_(srm)`.

### Theorem 2.1 — canonical excess partition

One has the disjoint support identity

\[
 \boxed{
 X_{m,sr}=X_{rm,s}\ \sqcup\ P_s(X_{m,r}).}
\tag{RE.8}
\]

Consequently there is a canonical split exact sequence

\[
 \boxed{
 0\longrightarrow E_{m,r}\xrightarrow{J_s}E_{m,sr}
 \longrightarrow E_{rm,s}\longrightarrow0,}
\tag{RE.9}
\]

and a canonical decomposition

\[
 E_{m,sr}\cong J_sE_{m,r}\oplus E_{rm,s}.
\tag{RE.10}
\]

The root retractions compose strictly:

\[
 R_{m,r}R_{rm,s}=R_{m,sr}.
\tag{RE.11}
\]

### Proof

The higher shell first splits as

\[
 A_{srm}=P_s(A_{rm})\sqcup X_{rm,s}.
\]

The first summand then splits as

\[
 P_s(A_{rm})
 =P_s(P_r(A_m))\sqcup P_s(X_{m,r})
 =P_{sr}(A_m)\sqcup P_s(X_{m,r}).
\]

Removing `P_(sr)(A_m)` proves `(RE.8)`. Passing to free coefficient modules proves `(RE.9)` and
`(RE.10)`. On a basis vector, both sides of `(RE.11)` return the unique `sr`-th root when it lies
in `A_m`, and return zero otherwise. `[PROVED HERE]`

Equation `(RE.9)` is the concrete cofiber-composition triangle for this source category. It is
not an extra fitted law. It is forced by the single identity `P_sP_r=P_(sr)`.

### Theorem 2.2 — bounded-stream split-defect functor

Let

\[
 \mathcal B=\ell^\infty(\mathbb N_{\ge1};\mathbb C).
\]

For `r>=1`, define extension to `r`-th-power support and root restriction by

\[
 (V_rx)(N)=
 \begin{cases}x(k),&N=k^r,\\0,&\text{otherwise},\end{cases}
 \qquad
 (R_ry)(k)=y(k^r).
\tag{RE.11a}
\]

Put `K_r=ker R_r` and `pi_r=1-V_rR_r`. Then

\[
 R_rV_r=1,
 \qquad
 \mathcal B=V_r\mathcal B\oplus K_r,
\tag{RE.11b}
\]

and both sequences

\[
 0\to K_r\to\mathcal B\xrightarrow{R_r}\mathcal B\to0,
 \qquad
 0\to\mathcal B\xrightarrow{V_r}\mathcal B\xrightarrow{\pi_r}K_r\to0
\tag{RE.11c}
\]

split canonically. The shell excess is the distinguished kernel point

\[
 c_{m,r}=a_{rm}-V_ra_m=\pi_ra_{rm}\in K_r.
\tag{RE.11d}
\]

Composition obeys

\[
 \boxed{c_{m,sr}=V_sc_{m,r}+c_{rm,s},}
\tag{RE.11e}
\]

with disjoint supports, and

\[
 K_{sr}=K_s\oplus V_sK_r,
 \qquad
 0\to K_s\to K_{sr}\xrightarrow{R_s}K_r\to0
\tag{RE.11f}
\]

is split by `V_s`.

Define `Ram` to have objects `m>=2` and an arrow `r:m->rm` for every positive integer `r`.
Define a split-defect arrow to be a triple `(R,V,c)` with `RV=1` and `c in ker R`, composed by

\[
 (R_s,V_s,d)\circ(R_r,V_r,c)
 =(R_rR_s,V_sV_r,V_sc+d).
\tag{RE.11g}
\]

Then

\[
 r:m\to rm\longmapsto(R_r,V_r,c_{m,r})
\tag{RE.11h}
\]

is a strict functor. Equivalently, the affine transport

\[
 T_{m,r}(x)=V_rx+c_{m,r}
\tag{RE.11i}
\]

satisfies `T_(m,r)(a_m)=a_(rm)` and
`T_(rm,s)T_(m,r)=T_(m,sr)`.

### Proof

All operator identities follow on coordinates. `V_rR_r` is projection to `r`-th-power support,
so `pi_r` is projection to its complement. This proves `(RE.11b)`--`(RE.11d)`. Since
`V_sV_r=V_(sr)`, subtracting `V_(sr)a_m` from the two-step shell identity gives `(RE.11e)`.
For `y in K_(sr)`,

\[
 y=\pi_sy+V_sR_sy,
\]

where `pi_s y in K_s` and `R_s y in K_r`; uniqueness follows from disjoint supports. This proves
`(RE.11f)`. Equation `(RE.11e)` is exactly the composition rule `(RE.11g)`, proving strict
functoriality and the affine identities. `[PROVED HERE]`

### Hostile classification — marked split defect, not curvature

The cocycle is a coboundary:

\[
 c_{m,r}=a_{rm}-V_ra_m.
\tag{RE.11j}
\]

The depth-dependent translations `theta_m(x)=x-a_m` conjugate `T_(m,r)` to `V_r`. Therefore this
theorem constructs no nontrivial cohomology, curvature, anomaly, or nonsplit `Ext` class. Its
invariant content is the distinguished positive quotient coordinate of the actual shell relative
to the canonical zero and power-image marking. If arbitrary depth-dependent translations are
declared gauge, even that marking disappears.

## 3. Dirichlet transgression

Let `a_m` be the characteristic function of `A_m`, let `b_(m,r)` be its power-image stream, and
let `c_(m,r)=a_(rm)-b_(m,r)` be the excess stream from the parent card. For `Re z>1`, define

\[
 C_{m,r}(z)=\sum_{n\ge1}c_{m,r}(n)n^{-z}.
\tag{RE.12}
\]

### Corollary 3.1 — crossed analytic cocycle

For positive integers `r,s`,

\[
 \boxed{
 C_{m,sr}(z)=C_{m,r}(sz)+C_{rm,s}(z),
 \qquad \Re z>1.}
\tag{RE.13}
\]

### Proof

The characteristic functions of the disjoint supports in `(RE.8)` add. The Dirichlet series of
`P_s(X_(m,r))` is obtained by reindexing `n=k^s`, hence equals `C_(m,r)(sz)`. Absolute convergence
holds because each characteristic stream is bounded coefficientwise by one and `Re z>1`.
`[PROVED HERE]`

Thus the excess is a crossed one-cocycle for Mellin dilation. Its two-step value is not the sum of
two unrelated remainders: the earlier excess must first be transported by `z->sz`.

## 4. Exact blindness of power-diagonal observers

Fix a finite prime aperture `F`. At level `rm`, the Boolean/Gibbs observer uses only the marked
perfect-power coordinates

\[
 \{k^{rm}:k\mid P_F,\ k>1\}\subset P_r(A_m).
\tag{RE.14}
\]

Let `B_(m,r,F)` be restriction of `V_(rm)` to those coordinates.

### Theorem 4.1 — inherited-observer factorization no-go

The power-diagonal restriction factors through the root retraction:

\[
 B_{m,r,F}=\widetilde B_{m,F}R_{m,r}
\tag{RE.15}
\]

for the corresponding lower-level coordinate restriction `tilde B_(m,F)`. Therefore

\[
 E_{m,r}\subseteq\ker B_{m,r,F}.
\tag{RE.16}
\]

More generally, every observer `O:V_(rm)->Y` that factors through `R_(m,r)` is constant on each
affine fibre `x+E_(m,r)` and cannot detect whether an excess component is present. Conversely,
the product observer `(R_(m,r),Q_(m,r))` reconstructs `V_(rm)` by `(RE.7)`.

### Proof

Every coordinate `k^(rm)` is the `r`-th power of `k^m`; `R_(m,r)` sends its coefficient to the
lower coordinate `k^m`. Every excess vector is supported away from all `r`-th powers, so both
`R_(m,r)` and the diagonal restriction kill it. This proves `(RE.15)` and `(RE.16)`. If
`O=O_tilde R_(m,r)`, then `O(x+e)=O(x)` for `e in E_(m,r)`. The converse is `(RE.7)`.
`[PROVED HERE]`

The finite Gibbs vector, its Schur capacity, the raw prime clock reconstructed from its log-odds,
and the resulting phase history all factor through this power-diagonal restriction. They may
detect the changed inherited weight at fixed ambient temperature, but none can detect the
source-new complement. This explains the previous flat comparison: all its objects live on the
same inherited quotient.

The no-go is sharp. The single coefficient probe

\[
 \varepsilon_{2^{rm}3}(x)=x(2^{rm}3)
\tag{RE.16a}
\]

distinguishes `a_(rm)` from `V_r a_m`. One scalar coordinate therefore suffices. Two prime species
are necessary: every one-prime element of `A_(rm)` is `p^(rm)=P_r(p^m)` and lies in the inherited
image. Thus `2^(rm)3` has the least possible prime-support arity for a complement detector.

For an arbitrary reporter `T:V_(rm)->Y`, the following are equivalent: `T` is invariant under all
translations by `E_(m,r)`; `T(x)=T(y)` whenever `R_(m,r)x=R_(m,r)y`; and `T` factors uniquely
through `R_(m,r)`. For linear `T`, these conditions are equivalent to
`E_(m,r) subset ker T`. This is the universal inherited-observer factorization criterion.

## 5. Route-independent exactness principle

For composable monomorphisms `A->B->C` in an abelian category, the standard cofiber sequence is

\[
 0\longrightarrow B/A\longrightarrow C/A\longrightarrow C/B\longrightarrow0.
\tag{RE.17}
\]

The ramification law `(RE.9)` is its canonically split, source-marked realization. This suggests
the following CFR typing:

- a law event carries a relative-law object `cofib(f)`;
- composition carries the octahedral extension from `cofib(f)` and `cofib(g)` to `cofib(gf)`;
- an exact observer preserves this sequence;
- an inherited-only observer annihilates the first relative sector;
- a nonlinear scalarization may fail even to admit induced transport, as proved for Schur
  capacity in the escort--logit card.

This is an exact kinematic principle, not yet a field equation. A nonzero curvature would require
two admitted observer transports whose images of `(RE.17)` fail to agree. No such pair is built
here.

## 6. Conjecture / proof / fail loops

1. **Escort--logit coherence retains the whole source event.** Failed by `(RE.16)`: it lives on
   the inherited power diagonal. **Survivor:** adjoin the excess projection before comparing
   observers.
2. **The two-step excess is an unstructured larger remainder.** Failed by `(RE.8)` and `(RE.13)`.
   **Survivor:** relative-law sectors obey a transported cocycle under composition.
3. **Capacity plus phase can recover the excess.** Failed: both factor through `R_(m,r)` and are
   constant on its nonzero kernel. **Survivor:** an observer family is jointly conservative only
   after adding a probe nonzero on `E_(m,r)`.
4. **Any nonzero cofiber is curvature.** Failed. The present split exact sequence is flat and
   composition-coherent. **Survivor:** reserve curvature for failure of two represented
   transports to preserve the same cofiber-composition law.
5. **The analytic excess is already proved hypertranscendental.** Not proved. `(RE.13)` gives its
   exact composition law only. **Survivor:** test differential rank of the excess separately.

## 7. Scope and boundaries

- `V_m` is the finite-support marked-support core; Theorem 2.2 upgrades the actual full shell
  streams to the bounded coefficient space `B`. Their Dirichlet series are used only on
  `Re z>1`.
- Splitting is canonical because shell supports are marked subsets of the free prime monoid.
  An abstract short exact sequence need not split canonically.
- Power-diagonal blindness covers Boolean/Gibbs/capacity/logit/phase observers in the current
  finite chart. It does not cover arbitrary non-diagonal, continuation, Fourier, Stokes, or
  completion observers.
- The theorem constructs no physical clock, action, contact law, source-normal global section,
  Xi criterion, or RH proof.
- No Lean file has been written or built.

## Lean-return notes

- Formalize the support partition `(RE.8)` before any module or analytic statement.
- The free-module split exact sequence can then be packaged from disjoint-support decomposition.
- Reuse the existing shell power-pullback theorem; do not duplicate recurrence or HT results.
- No Lean file has been written or built.

## Gates

- [x] source-asymmetric relative-law object
- [x] canonical inherited/excess reconstruction
- [x] strict composition and excess cocycle
- [x] analytic Dirichlet transgression
- [x] exact blindness theorem for inherited-only observers
- [x] hostile field-interpretation audit
- [x] exact proof that the defect is split/coboundary rather than curvature
- [ ] second observer carrying the excess nontrivially beyond coefficient-faithful Mellin transform
- [ ] nonzero interchange defect/curvature
- [ ] withheld Stokes or extension/flux response
- [ ] Lean formalization

## Log

- 2026-08-09 — created after flat escort--logit comparison was shown to erase the non-surjective
  complement of the literal source power map.
- 2026-08-09 — hostile audit identified the exact strict split-defect functor, minimal mixed-prime
  detector, and coboundary trivialization; curvature/cohomology interpretations were rejected.
