# Phase-subdiscriminant Kähler--Smith stratification law

- **ID:** `phase-subdiscriminant-kahler-smith-stratification-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / METRIC-FREE PHASE GEOMETRY / ALL-FITTING BRIDGE
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [NO RH CLAIM] [NO LEAN WRITTEN]`
  `[REAL-CHAMBER SQUARE LAW] [COMPLEX-PHASE JUMP LAW]`
- **Statement:** at common-contact horizon, real separated slopes force Kähler persistence to be
  exact double of observer persistence in every Fitting degree, while complex phase cancellation
  creates subdiscriminant walls invisible to total discriminant and observer barcode.

## Setup

Let `R` be discrete valuation ring with uniformizer `a`, fraction field `K`, and residue field `k`
of characteristic zero. Let `c in R` satisfy

\[
 r=v(c)\ge1.
 \tag{1}
\]

Choose units `u_1,...,u_N in R^times` with pairwise distinct residues

\[
 \lambda_i=\bar u_i\in k.
 \tag{2}
\]

Put

\[
 f_i=c u_i,
 \qquad
 P(T)=\prod_{i=1}^N(T-f_i),
 \qquad
 A=R[T]/(P).
 \tag{3}
\]

Let

\[
 J:A\to R^N,
 \qquad g\mapsto(g(f_1),\ldots,g(f_N)),
 \qquad C=\operatorname{coker}J,
 \tag{4}
\]

and let

\[
 \Omega=\Omega_{A/R}\cong A/(P')\,dT.
 \tag{5}
\]

For residues define moment sequence and Hankel subdiscriminants

\[
 m_\ell=\sum_{i=1}^N\lambda_i^\ell,
 \qquad
 H_k(\lambda)=\det(m_{p+q})_{0\le p,q<k}
 \quad(1\le k\le N).
 \tag{6}
\]

By Cauchy--Binet,

\[
 H_k(\lambda)
 =\sum_{|S|=k}\prod_{\{i,j\}\subset S}(\lambda_j-\lambda_i)^2.
 \tag{7}
\]

Over complex residues this is algebraic square, not absolute-value square, so cancellation is
possible.

## Theorem 1: observer common-contact staircase

There is exact Smith decomposition

\[
 \boxed{
 C\cong\bigoplus_{j=1}^{N-1}R/(a^{rj}).}
 \tag{8}
\]

### Proof

Writing `f_i=c u_i`, evaluation matrix in monomial basis factors as

\[
 (u_i^{j-1})_{i,j}\operatorname{diag}(1,c,\ldots,c^{N-1}).
\]

First matrix reduces to Vandermonde on distinct residues `(lambda_i)` and is invertible over `R`.
Smith exponents are therefore `0,r,2r,...,(N-1)r`, proving `(8)`. QED.

## Lemma 2: southwest Kähler minor is phase subdiscriminant

Let

\[
 Q(X)=\prod_{i=1}^N(X-u_i)
 \tag{9}
\]

and write `B=(b_ij)` for multiplication by `Q'(X)` on `R[X]/(Q)` in monomial basis, indexed
`0,...,N-1`. For `1<=k<=N`, southwest `k`-by-`k` block

\[
 B[\{N-k,\ldots,N-1\},\{0,\ldots,k-1\}]
 \tag{10}
\]

has determinant reducing modulo `a` to

\[
 \boxed{\pm H_k(\lambda).}
 \tag{11}
\]

### Proof

For polynomial class `h` of degree less than `N`, let `ell(h)` be coefficient of `X^(N-1)`.
Lagrange interpolation gives trace identity

\[
 \ell(Q'h)=\sum_{i=1}^Nh(u_i).
 \tag{12}
\]

Indeed, leading coefficient of interpolant with values `Q'(u_i)h(u_i)` is sum of these values
divided by `Q'(u_i)`.

For `0<=p<k`, apply `(12)` to `X^(p+q)`, obtaining

\[
 \ell\bigl(X^p Q'X^q\bmod Q\bigr)=\sum_i u_i^{p+q}.
 \tag{13}
\]

Functionals `h mapsto ell(X^p h mod Q)`, `0<=p<k`, are unit anti-triangular combinations of
coefficient functionals of `X^(N-k),...,X^(N-1)`: coefficient of `X^(N-1-p)` occurs with coefficient
one, and only higher coefficients also occur. Thus changing southwest row functionals to these
`k` trace functionals has determinant `+/-1`. Resulting block is moment matrix
`(sum_i u_i^(p+q))_(p,q)`. Reducing modulo `a` proves `(11)`. QED.

## Theorem 3: real chamber all-Fitting square law

Assume residue field is embedded in `C` and all `lambda_i` are distinct real numbers. Then

\[
 \boxed{
 \Omega\cong\bigoplus_{j=1}^{N-1}R/(a^{2rj}).}
 \tag{14}
\]

Consequently, for every `i>=0`, with convention `Fitt_i=R` beyond presentation rank,

\[
 \boxed{
 \operatorname{Fitt}_i^R(\Omega)
 =\operatorname{Fitt}_i^R(C)^2.}
 \tag{15}
\]

Thus observer depth `rj` becomes Kähler/law depth `2rj` at every height, not only in total
determinant.

### Proof

In monomial basis, multiplication matrix `M=m_(P'(T))` presenting `Omega` satisfies exact entry law

\[
 M_{ij}=c^{N-1+j-i}b_{ij},
 \qquad 0\le i,j<N.
 \tag{16}
\]

This follows from

\[
 P(T)=c^NQ(T/c),
 \qquad P'(T)=c^{N-1}Q'(T/c).
\]

Hence for row and column sets `I,J` of size `k`,

\[
 \det M_{I,J}
 =c^{k(N-1)+\sum J-\sum I}\det B_{I,J}.
 \tag{17}
\]

Exponent is minimized uniquely by southwest rows `I={N-k,...,N-1}` and first columns
`J={0,...,k-1}`, where it equals `k(k-1)`. Every `B`-minor lies in `R`, so all `k`-minors have
valuation at least `r k(k-1)`.

For real distinct residues, moment matrix in `(6)` is Gram matrix of vectors

\[
 (1,\lambda_i,\ldots,\lambda_i^{k-1})in\mathbb R^k.
\]

It is positive definite for `k<=N`, hence `H_k(lambda)>0`. Lemma 2 says southwest minor reaches
lower bound. Therefore `k`-th determinantal divisor of `M` has valuation

\[
 r k(k-1).
 \tag{18}
\]

Successive differences are `0,2r,4r,...,2r(N-1)`, proving `(14)`. Comparing with Theorem 1 gives
all determinantal divisors, hence every Fitting ideal, squared. QED.

## Corollary 4: root-height time dilation

In real chamber, associated `a`-graded lengths of observer defect are

\[
 N-1,N-2,\ldots,1,
\]

while those of `Omega` repeat each level twice. Equivalently every type-`A_(N-1)` positive-root
height acquires factor-two normal lifetime in relative-law/Kähler observer.

This is exact algebraic dilation statement. No physical time interpretation is assumed.

## Theorem 5: complex phase walls invisible to total discriminant

Over complex residues, observer module `(8)` remains unchanged while intermediate Smith profile of
`Omega` can jump on phase loci

\[
 H_k(\lambda)=0,
 \qquad 1<k<N.
 \tag{19}
\]

Total length cannot jump as long as residues remain distinct:

\[
 \operatorname{length}_R\Omega
 =v(\operatorname{Disc}P)
 =rN(N-1).
 \tag{20}
\]

### Exact three-phase example

Let `N=3`, `R=C[[a]]`, `c=a^r`, and

\[
 (u_1,u_2,u_3)=(1,\omega,\omega^2),
 \qquad \omega^3=1,
 \qquad \omega\ne1.
 \tag{21}
\]

Then `Q(X)=X^3-1`, so

\[
 P(T)=T^3-c^3,
 \qquad P'(T)=3T^2.
\]

Multiplication by `P'` on basis `(1,T,T^2)` has nonzero entries `3`, `3c^3`, `3c^3`; therefore

\[
 \boxed{
 C\cong R/(a^r)\oplus R/(a^{2r}),
 \qquad
 \Omega\cong R/(a^{3r})\oplus R/(a^{3r}).}
 \tag{22}
\]

Here `H_2=0`, but roots are distinct and ordinary discriminant is nonzero away from `c=0`.
Observer total length and Kähler total length retain `3r` and `6r`; distribution among depths changes.

### Proof

The example proves existence of phase jump and exact profile. In general, Lemma 2 shows vanishing
of `H_k` removes unique minor at naive lowest `c`-exponent. Determinantal-divisor valuation must then
increase unless another minor at same exponent survives; uniqueness of southwest exponent excludes
that. Total determinant remains product of squared pair differences, all units after factoring
`c`, proving `(20)`. QED.

Statement `(19)` gives sufficient exact jump walls. At intersections or when higher-exponent minors
compete, full stratification is governed by valuations of all Kähler minors, not by `H_k` alone.

## Corollary 6: literal prime phase stratification

For finite primes `F`, put

\[
 f_p(a,\theta)=e^{i\theta_p}(p^{Ma}-1)
 =a\,u_p(a,\theta),
 \qquad
 \bar u_p=M\log p\,e^{i\theta_p}.
 \tag{23}
\]

As long as phase nodes `M log p e^(i theta_p)` are distinct:

1. prime sheet-evaluation observer has fixed staircase `(1,a,...,a^(N-1))`;
2. total discriminant order remains `N(N-1)`;
3. intermediate Kähler Smith profile is stratified by algebraic phase subdiscriminants `H_k`;
4. at physical real chamber `theta_p=0`, all-Fitting square law holds.

This phase geometry is source-coordinate and metric-free. It is distinct from optional Berry or
Grassmann connection introduced after choosing Hermitian projection.

## Natural successor exact sequence

For ordered sheets `x_1,...,x_N,x_q`, projection to first `N` coordinates gives natural exact
sequence

\[
 \boxed{
 0\to R/(P_N(x_q))\to C_{N+1}\to C_N\to0,}
 \tag{24}
\]

where `P_N(T)=product_(i=1)^N(T-x_i)`. Indeed, after subtracting polynomial interpolating first `N`
coordinates, kernel is represented by `(0,...,0,z)`; it is evaluation of degree-`N` polynomial
vanishing at first `N` sheets precisely when `z` is multiple of `P_N(x_q)`.

In common-contact real chamber,

\[
 P_N(x_q)=c^N\prod_{i=1}^N(u_q-u_i),
\]

so kernel is `R/(a^(rN))`. Smith classification shows `(24)` splits noncanonically, recovering
successor persistence bar. Exact sequence, unlike direct-sum identification, is source-order natural.

## What this explains—and what it does not

### Explained

1. Scalar discriminant sees total collision work but cannot see redistribution among normal depths.
2. Phase can change relative-law/Kähler structure without changing roots' distinctness, observer
   barcode, or total discriminant.
3. Real prime slopes form positive chamber in which every Fitting level obeys exact square law.
4. Horizon fibre `C/aC` and `Omega/aOmega` both have dimension `N-1`, but their deformation
   thickness differs by factor two. Fibrewise identification is therefore provably lossy.
5. Rank-one/scalar and determinant-only routes miss intermediate phase-subdiscriminant walls.

### Not explained

1. Nothing forces `a=0`; same theorem holds for generalized-prime and unrelated common-contact
   systems.
2. No black-hole, wormhole, or Brown--Susskind observable has been derived.
3. `H_k=0` is phase stratification, not RH criterion.
4. Koszul differential `d(e_p)=f_p` is supplied by chosen defects; source-prior derivation of decisive
   curvature remains open.

## Hostile novelty boundary

- Hermite moment matrices, subdiscriminants, Kähler different, Smith theory, and Cauchy--Binet are
  classical ingredients.
- New-to-corpus exact residue is coupling of phase subdiscriminant strata to full Kähler Smith tower
  of literal prime-holonomy observer, plus all-Fitting square law in real chamber.
- No literature-first claim until specialist search closes; current card is theorem, not priority
  assertion.

## Conjecture/failure loops

1. **Fitting square only holds at index zero.** False in real chamber: `(15)` holds for every index.
2. **Distinct complex slopes force same Kähler staircase.** False by cube-root example `(22)`.
3. **Total discriminant determines relative-law depth distribution.** False: real and cube-root
   profiles have same total length, different partitions.
4. **Observer barcode detects phase walls.** False: `C` remains fixed whenever residues distinct.
5. **Hermitian metric is needed for phase geometry.** False for subdiscriminant Smith walls.
6. **Fibre dimension captures horizon defect.** False: equal fibre dimensions conceal factor-two
   thickness.
7. **All-Fitting square selects radial origin.** False: it holds for every `c`, including off horizon.
8. **One scalar port sees all phases.** False: intermediate `H_k`, `2<=k<N`, are independent of total
   determinant data.

## Predictions

1. For `N>=3`, a complex phase loop can cross Kähler Smith walls while ordinary discriminant never
   vanishes; any theory using only total determinant predicts no event and is falsified.
2. In positive real prime chamber, measured Kähler invariant factors must be exactly double observer
   invariant factors. Any mismatch means common-contact monogenic model is wrong.
3. Physical time restricted to one parameter can detect wall crossings of scalar `H_k(t)` even though
   it cannot pull back curvature two-forms; subdiscriminant stratification is therefore better
   one-clock observable than Berry curvature in this local model.
4. Global Completion Relativity needs transport law for Smith partitions across phase walls, not only
   determinant line.

## Lean-return note

No Lean work authorized. Later formalization: scaling identity `(16)`, southwest-moment lemma,
Cauchy--Binet positivity, determinantal divisors, all-Fitting comparison, and explicit `N=3`
counterexample. Search Kähler different, subdiscriminant, and Smith corpus first.

## Gates

- [x] dependency-closed paper proof
- [x] exact real and complex chambers
- [x] literal prime-phase specialization
- [x] hostile nonselection boundary
- [ ] external specialist novelty review
- [ ] Lean formalization

## Log

- 2026-08-08 -- upgraded total Fitting square to all indices; found metric-free phase walls and exact
  cube-root redistribution counterexample.
