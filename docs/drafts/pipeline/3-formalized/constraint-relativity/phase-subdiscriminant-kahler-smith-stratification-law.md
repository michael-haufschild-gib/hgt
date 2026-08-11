# Phase-subdiscriminant Kähler--Smith stratification law

- **ID:** `phase-subdiscriminant-kahler-smith-stratification-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / METRIC-FREE PHASE GEOMETRY / ALL-FITTING BRIDGE
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`
  `[NO RH CLAIM] [REAL-CHAMBER SQUARE LAW] [COMPLEX-PHASE JUMP LAW]`
  `[ACTUAL PRIME PHASE WALL] [KRONECKER WALL-CLOSURE]`
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

More precisely, ordering southwest rows increasingly gives sign
`(-1)^(k(k-1)/2)` in `(11)`. Identity holds over `R` with moments `sum_i u_i^ell`; reduction is
used only to test whether determinant is a unit.

## Theorem 2A: canonical self-dual observer--cotangent sandwich in the monogenic chart

Let `A^sharp` be trace-dual lattice inside split generic fibre `K^N`, and put

\[
 C^\dagger=\operatorname{Hom}_R(C,K/R).
\]

There are canonical inclusions

\[
 A\subset R^N\subset A^\sharp,
 \qquad
 A^\sharp=(P')^{-1}A,
 \tag{11a}
\]

and canonical exact sequence

\[
 \boxed{
 0\longrightarrow C
 \longrightarrow\Omega_{A/R}
 \longrightarrow C^\dagger
 \longrightarrow0.}
 \tag{11b}
\]

### Proof

Generic evaluation identifies `A tensor_R K` with `K^N`; coordinate trace makes `R^N` self-dual.
Since `A subset R^N`, duality reverses inclusion and gives `R^N subset A^sharp`. Monogenic different
computation gives `A^sharp=(P')^(-1)A`.

Multiplication by `P'` identifies

\[
 A^\sharp/A\cong A/(P')\cong\Omega_{A/R}.
\]

Quotienting sandwich `A subset R^N subset A^sharp` gives

\[
 0\to R^N/A\to A^\sharp/A\to A^\sharp/R^N\to0.
\]

First term is `C`. Trace pairing modulo `R` is perfect between `R^N/A` and `A^sharp/R^N`, so last
term is `C^dagger`. This proves `(11b)`. QED.

Sequence `(11b)` exists without real-rootedness. Its extension class

\[
 [\xi_A]\in\operatorname{Ext}_R^1(C^\dagger,C)
 \tag{11c}
\]

is intrinsic to source--observer sandwich and is lost by total discriminant. Varying complex
tangent nodes can keep isomorphism type of `C` fixed while changing middle-module Smith type of
this extension.

The monogenic hypothesis is essential for identifying the middle term with `Omega_(A/R)`. For a
general finite split order the canonical trace-dual middle is `A^sharp/A`, but it need not be the
Kähler module. For example, over `R=C[[a]]`,

\[
 A=R(1,1,1)+aR^3\subset R^3
\]

has `length(A^sharp/A)=4`, while direct differentiation of
`A\cong R[x,y]/(x^2-ax,y^2-ay,xy)` gives

\[
 \Omega_{A/R}\cong R/(a^2)\oplus R/(a^2)\oplus R/(a)
\]

of length `5`. Thus `(11b)` is a theorem of setup `(3)`, not a theorem about arbitrary split
orders.

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
 (1,\lambda_i,\ldots,\lambda_i^{k-1})\in\mathbb R^k.
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

Module-theoretically, real chamber makes canonical extension `(11b)` maximally non-split at level
of invariant factors: equal observer and dual-observer bars of length `rj` glue into bars of length
`2rj`. No canonical decomposition into independently paired bars is asserted.

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

### Complete constant-tangent three-sheet classification

Let `R=C[[a]]`, `c=a^r` times a unit, and let `u_i=lambda_i in C` be constant, distinct tangent
nodes. Then exactly two Kähler Smith types occur:

\[
 \boxed{
 H_2(\lambda)\ne0
 \Longrightarrow
 \Omega\cong R/(a^{2r})\oplus R/(a^{4r}),}
 \tag{22b}
\]

\[
 \boxed{
 H_2(\lambda)=0
 \Longrightarrow
 \Omega\cong R/(a^{3r})\oplus R/(a^{3r}).}
 \tag{22c}
\]

#### Proof

If `H_2!=0`, `k=2` southwest minor is unit after removing `c^2`; its determinantal-divisor
valuation is `2r`. Total determinant valuation is `6r`, so nonzero Smith exponents are `2r,4r`.

Suppose `H_2=0`. Set

\[
 m=\frac{\lambda_1+\lambda_2+\lambda_3}{3},
 \qquad \mu_i=\lambda_i-m.
\]

Then

\[
 H_2=3\sum_i\mu_i^2.
\]

Thus `sum mu_i=0=sum mu_i^2`. Newton identities give first two elementary symmetric functions of
`mu_i` equal zero, so

\[
 \prod_i(X-\mu_i)=X^3-d
\]

with `d!=0` because nodes are distinct. Choose `s^3=d`. After affine change
`T'=s^(-1)(T-cm)`, an invertible `R`-basis change, polynomial is associated to
`T'^3-c^3`. Multiplication by derivative `3T'^2` has Smith exponents `0,3r,3r`, proving `(22c)`.
QED.

Therefore `N=3` phase stack image has generic maximal-gluing stratum and one equianharmonic balanced
wall. Additional intermediate partitions require higher `a`-jets of tangent nodes, not constant
three-node configuration.

### Theorem: fixed-radius three-phase wall criterion

Let `rho_1,rho_2,rho_3>0`. There exist phases `theta_i` for which distinct nodes

\[
 z_i=\rho_i e^{i\theta_i}
\]

satisfy `H_2(z)=0` if and only if

\[
 \boxed{
 \left(\sum_{i=1}^3\rho_i^2\right)^2
 \ge 2\sum_{i=1}^3\rho_i^4.}
 \tag{22d}
\]

#### Proof

By three-sheet classification, `H_2(z)=0` exactly when nodes are vertices

\[
 z_i=m+s\omega^i
\]

of affine equilateral triple, with `s!=0`. Put `y_i=rho_i^2`,

\[
 A=\frac{y_1+y_2+y_3}{3},
 \qquad d_i=y_i-A.
\]

Every real zero-sum triple `(d_i)` has unique representation, up to indexing convention,

\[
 d_i=2\operatorname{Re}(q\omega^i),
 \qquad
 |q|^2=\frac16\sum_i d_i^2.
 \tag{22e}
\]

Squared moduli of equilateral vertices obey

\[
 |m+s\omega^i|^2=|m|^2+|s|^2
 +2\operatorname{Re}(m\bar s\,\bar\omega^i).
\]

Thus required vertices exist exactly when nonnegative `x=|m|`, `t=|s|` solve

\[
 x^2+t^2=A,
 \qquad xt=|q|.
\]

Such solution exists exactly when `A>=2|q|`. If `q!=0`, both `x,t` may be chosen positive; at
equality they are equal and positive. If `q=0`, choose `x=0` and `t=sqrt(A)>0`. Hence `s!=0` in
every case. Squaring and using `(22e)` gives

\[
 \frac{(\sum y_i)^2}{9}
 \ge\frac23\left(\sum y_i^2-\frac{(\sum y_i)^2}{3}\right),
\]

equivalent to `(22d)`. Positive prescribed radii and `s!=0` give distinct nonzero nodes. QED.

For literal prime radii `rho_p=M log p` with `M>0`, scale `M` cancels. Triple `(101,103,107)` satisfies
criterion strictly. Indeed

\[
 107^3<101^4
 \Longrightarrow
 \log107<\frac43\log101<\sqrt2\log101,
\]

so `(log107)^2<2(log101)^2<(log101)^2+(log103)^2`. Hence largest `y_i` is smaller than sum of other
two; then `max y_i<(sum y)/2`, and

\[
 \sum_i y_i^2\le(\max_i y_i)\sum_i y_i<\frac12(\sum_i y_i)^2,
\]

exactly strict `(22d)`.

Therefore actual independent prime phase torus meets balanced three-sheet Kähler wall. This does
not imply one-parameter orbit `theta_p=t log p` meets it.

### Corollary: one-clock recurrence shadows phase wall

For any distinct primes `p_1,...,p_N`, flow

\[
 t\longmapsto(e^{it\log p_1},\ldots,e^{it\log p_N})
 \tag{22f}
\]

is dense in `N`-torus. Indeed, annihilating integer character would give

\[
 \sum_i m_i\log p_i=0
 \Longrightarrow
 \prod_i p_i^{m_i}=1,
\]

so unique factorization forces all `m_i=0`; Kronecker density theorem applies.

For prime triple `(101,103,107)`, fixed-radius criterion gives phase point `theta^star` with
`H_2=0`. By density and continuity there is sequence `t_n` such that

\[
 \boxed{
 H_2\left((\log p_i)e^{it_n\log p_i}\right)\longrightarrow0.}
 \tag{22g}
\]

Equivalently

\[
 \inf_{t\in\mathbb R}
 \left|H_2\left((\log p_i)e^{it\log p_i}\right)\right|=0.
 \tag{22h}
\]

This proves one-clock orbit has balanced phase wall in closure. It does not prove exact finite
`t` intersection. If no exact zero occurs, Kähler Smith type remains generic at every time while
time orbit approximates balanced extension stratum arbitrarily closely. This is exact recurrence
without law change, not physical wormhole theorem.

For `N=4`, nodes `(1,i,-1,-i)` give `P(T)=T^4-c^4`, `P'(T)=4T^3`, and

\[
 C\cong R/(a^r)\oplus R/(a^{2r})\oplus R/(a^{3r}),
 \qquad
 \Omega\cong(R/(a^{4r}))^3.
 \tag{22a}
\]

Here `H_2=H_3=0` while `H_4!=0`. Cumulative Kähler valuations change from real-chamber
`(0,2r,6r,12r)` to `(0,4r,8r,12r)`. This independently confirms conservation of total defect with
phase redistribution of internal depths.

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

Actual unequal-radius prime phase torus intersection is proved above for three primes. One-clock
orbit approaches wall arbitrarily closely by `(22g)`; exact intersection remains open.

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
6. Cotangent defect canonically glues observer defect to its torsion dual; phase controls extension,
   while determinant records only conserved total length.

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
  of literal prime-holonomy observer, self-dual sandwich `(11b)`, plus all-Fitting square law in real
  chamber.
- No literature-first claim until specialist search closes; current card is theorem, not priority
  assertion.

Primary parents checked:

- https://arxiv.org/abs/1911.01745
- https://arxiv.org/abs/2003.13008
- https://arxiv.org/abs/1207.2434
- https://arxiv.org/abs/math/0609524
- https://arxiv.org/abs/2506.21528
- https://arxiv.org/abs/1302.2015
- https://arxiv.org/abs/2111.03700
- https://arxiv.org/abs/1402.4969
- https://arxiv.org/abs/1405.0923
- https://arxiv.org/abs/1907.00384
- https://arxiv.org/abs/2604.02213

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
9. **Cotangent defect equals observer defect after passing to support.** False as deformation law:
   `(11b)` shows support equality hides self-dual extension and twice total length.

## Predictions

1. For `N>=3`, a complex phase loop can cross Kähler Smith walls while ordinary discriminant never
   vanishes; any theory using only total determinant predicts no event and is falsified.
2. In positive real prime chamber, measured Kähler invariant factors must be exactly double observer
   invariant factors. Any mismatch means common-contact monogenic model is wrong.
3. Physical time restricted to one parameter can detect any wall crossing of scalar `H_k(t)` even
   though it cannot pull back curvature two-forms; whether literal prime recurrence orbit hits such
   wall is open.
4. Global Completion Relativity needs transport law for Smith partitions across phase walls, not only
   determinant line.

## Lean-return note

Formalized, unconditionally.  See `phase-subdiscriminant-kahler-smith-stratification-law-formalized.md`
(same directory).  The note below was written before that work and is kept for the record.

> No Lean work authorized. Later formalization: scaling identity `(16)`, southwest-moment lemma,
> Cauchy--Binet positivity, determinantal divisors, all-Fitting comparison, and explicit `N=3`
> counterexample. Search Kähler different, subdiscriminant, and Smith corpus first.

## Gates

- [x] dependency-closed paper proof
- [x] exact real and complex chambers
- [x] literal prime-phase specialization
- [x] hostile nonselection boundary
- [ ] external specialist novelty review
- [x] Lean formalization

## Log

- 2026-08-08 -- upgraded total Fitting square to all indices; found metric-free phase walls and exact
  cube-/fourth-root redistribution counterexamples; identified phase as canonical self-dual
  extension class.

