# Common-profile Boolean response and anchor-curvature identity

- **ID:** `common-profile-boolean-anchor-curvature`
- **Stage:** `2-fully-proven`
- **Type:** `[PAPER-PROVED] [BRIDGE] [REDISCOVERED] [POSITIVE SALVAGE]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md`, `(PF1)`, `(AC13)`,
  `(AC24)`
- **Statement:** The complete future Bernoulli average of the causally anchored primitive
  response is exactly a squarefree-sieved physical occupancy minus its Euler vacuum; when the
  common physical profile is a Gram kernel, the height-summed occupancy is exactly the Boolean
  anchor curvature of the sifted Gram energy.

## Exact response statement

Fix a gap `h`, a squarefree anchor `c`, and a squarefree future packet `N` with `(c,N)=1`.  Write

```text
nu_h(q)=#{x mod q:q|x(x+h)},
theta_h(q)=nu_h(q)/q,
V_N(h)=product_(p|N)(1-theta_h(p)),
w_(N,h)(r)=theta_h(r)V_(N/r)(h),              r|N.
```

Let `W_h` be the common physical profile, extended by zero, and let `J_h=integral_R W_h`.  With
the Fourier convention of `(PF1)`, define

```text
A_(q,h)=1/nu_h(q) sum_(u!=0) hat(W)_h(u/q)S_(q,h)(u),

B_(c,r,h)=1/(nu_h(c)nu_h(r))
  sum_(u!=0,(u,r)=1)hat(W)_h(u/(cr))S_(cr,h)(u),

Eresp_(c,N,h)=sum_(r|N)mu(r)w_(N,h)(r)B_(c,r,h).
```

Then

```text
B_(c,r,h)=sum_(d|r)mu(d)A_(cr/d,h),                    (CG1)

Eresp_(c,N,h)=sum_(e|N)mu(e)theta_h(e)A_(ce,h),        (CG2)

Eresp_(c,N,h)
 =c/nu_h(c) sum_m W_h(m)1_(c|m(m+h))P_N(m)P_N(m+h)
   -J_h V_N(h),                                        (CG3)
```

where

```text
P_N(m)=product_(p|N)1_(p does not divide m).
```

Equivalently, the normalization that interfaces with `(AC24)` is

```text
theta_h(c)Eresp_(c,N,h)
 =sum_m W_h(m)1_(c|m(m+h))P_N(m)P_N(m+h)
   -theta_h(c)J_hV_N(h).                               (CG4)
```

## Common-Gram anchor curvature

Let `C` be the prime-factor set of `c`.  Suppose a finitely supported real Hilbert packet `g_m`
realizes the same profile:

```text
W_h(m)=<g_m,g_(m+h)>.
```

For every finite prime set `S`, put

```text
P_S(m)=product_(p in S)1_(p does not divide m),
Energy(S)=||sum_m P_S(m)g_m||^2.
```

Then the physical occupancy has the exact Boolean curvature law

```text
sum_(h,m)W_h(m)1_(c|m(m+h))P_N(m)P_N(m+h)
 =sum_(D subset C)(-1)^|D| Energy(N union D).           (CG5)
```

Consequently `(CG4)` joins globally as

```text
sum_h theta_h(c)Eresp_(c,N,h)
 =sum_(D subset C)(-1)^|D| Energy(N union D)
   -sum_h theta_h(c)V_N(h)J_h.                         (CG6)
```

The finite theorem is stronger than the Boolean specialization.  If arbitrary real coordinate
weights `a_p(m)` replace `1_(p does not divide m)`, define

```text
a_S(m)=product_(p in S)a_p(m),
Anchor_C(m,n)=product_(p in C)(1-a_p(m)a_p(n)).
```

For disjoint finite coordinate sets `N,C`, one still has

```text
sum_(m,n)a_N(m)a_N(n)Anchor_C(m,n)<g_m,g_n>
 =sum_(D subset C)(-1)^|D| ||sum_m a_(N union D)(m)g_m||^2.  (CG7)
```

This weighted strengthening is forced by the algebra and remains an elementary bridge.

## Dependency-closed paper proof

For `(CG1)`, insert

```text
1_((u,r)=1)=sum_(d|(u,r))mu(d)
```

into the definition of `B`.  In the `d`-term write `u=dv`.  Because `r` is squarefree and
`(c,r)=1`, the modulus `d` is coprime to `c(r/d)`, so reduced-frequency CRT lifting gives

```text
S_(cr,h)(dv)=nu_h(d)S_(c(r/d),h)(v).
```

Multiplicativity gives `nu_h(cr)=nu_h(c)nu_h(d)nu_h(r/d)`.  The factor `nu_h(d)` therefore
cancels exactly and the remaining term is `mu(d)A_(cr/d,h)`.  This proves `(CG1)` with the
normalization in `(AC13)`; no primitivity condition along the anchor `c` has been introduced.

Substitute `(CG1)` into `Eresp`, put `r=de`, and use squarefreeness.  Since `d` and `e` are
coprime,

```text
mu(de)mu(d)=mu(e),
theta_h(de)=theta_h(d)theta_h(e).
```

For each fixed `e`, the remaining `d`-sum is the complete Bernoulli mass

```text
sum_(d|N/e)theta_h(d)V_(N/(de))(h)=1.
```

This proves `(CG2)`.

Equation `(PF1)` says

```text
A_(q,h)=q/nu_h(q) delta_h(e_q).
```

Hence `(CG2)` and `(c,N)=1` give

```text
Eresp_(c,N,h)=c/nu_h(c) sum_(e|N)mu(e)delta_h(e_(ce)).
```

Expanding `delta_h=beta_h-J_h theta_h`, finite inclusion-exclusion gives

```text
sum_(e|N)mu(e)beta_h(e_(ce))
 =sum_m W_h(m)1_(c|m(m+h))P_N(m)P_N(m+h),

sum_(e|N)mu(e)theta_h(ce)=theta_h(c)V_N(h).
```

Multiplication by `c/nu_h(c)=1/theta_h(c)` proves `(CG3)` and `(CG4)`.

For `(CG5)`, change variables `n=m+h`.  The left side becomes the finite double Gram sum

```text
sum_(m,n)<g_m,g_n>P_N(m)P_N(n)1_(c|mn).
```

For the squarefree anchor,

```text
1_(c|mn)
 =product_(p in C)(1-1_(p does not divide m)1_(p does not divide n))
 =sum_(D subset C)(-1)^|D|P_D(m)P_D(n).                (CG8)
```

Interchange the finite sums and use Gram polarization:

```text
sum_(m,n)P_(N union D)(m)P_(N union D)(n)<g_m,g_n>
 =||sum_m P_(N union D)(m)g_m||^2.
```

This proves `(CG5)` and `(CG6)`.  The same product expansion with arbitrary `a_p(m)` proves
`(CG7)`.

## Hostile audit and exact significance

- **Normalization:** omitting `c/nu_h(c)` in `(CG3)` is false.  The correct AC13-facing form is
  `(CG3)`, and the density-weighted AC24-facing form is `(CG4)`.
- **No independent profiles:** `(CG5)` uses one common Gram family `g_m`; it does not hold for
  sectorwise independently chosen response profiles.
- **No positivity:** Boolean curvature is an alternating sum of positive energies, not a positive
  energy.  Already for one anchor coordinate it is `Energy(N)-Energy(N union {p})`, which can have
  either sign because deleting one vector packet can remove constructive or destructive
  interference.
- **No estimate:** `(CG6)` is an exact change of representation.  It neither bounds the curvature
  nor cancels the Euler vacuum at the `M^(-1)` scale.
- **No RH smuggling:** no zero location or Mertens-strength input appears.  Conversely, the
  unresolved bound for the actual `g_m` remains the same response-correlation problem as `(AC25)`.
- **Internal corpus:** the local tree already contains the Bernoulli mass law, reduced-frequency
  alias lifting, and finite inclusion-exclusion product.  It does not contain this exact common-Gram
  response/curvature join.
- **Parent theory:** `(CG1)`--`(CG7)` are finite Boolean Möbius inversion, CRT alias lifting, and
  Gram polarization.  The verdict is `REDISCOVERED` / `BRIDGE`, not new scientific knowledge.

The exact positive insight is nevertheless useful: **the common physical profile prevents
sectorwise response steering and turns the global future response into a Boolean finite
difference of one energy functional.**  The remaining analytic question is now whether that
specific energy curvature cancels its explicit Euler vacuum after the full causal
`h,p,a,r` joining; positivity or abstract Hilbert geometry alone cannot do so.

## Rank-one sign-surjectivity classification

`[PAPER-PROVED] [POSITIVE CLASSIFICATION OF THE SIGN NO-GO] [BRIDGE]`

The absence of a curvature sign is sharp in the strongest possible finite sense.  Let `C` be any
nonempty finite anchor set disjoint from `N`, and write

```text
kappa_C Energy(N)
 =sum_(D subset C)(-1)^|D| Energy(N union D).           (CG9)
```

For every prescribed real number `y`, there is a one-dimensional common Gram packet for which

```text
kappa_C Energy(N)=y.                                   (CG10)
```

Indeed, let `c=product_(p in C)p`, take a unit vector `e`, and make the only nonzero source vectors

```text
g_1=t e,       g_c=e,       t=(y-1)/2.                 (CG11)
```

Because `C` and `N` are disjoint, both indices survive `P_N`.  The index `c` is killed by every
nonempty `D subset C`, whereas the index `1` survives every coordinate.  Hence

```text
Energy(N)=(t+1)^2,
Energy(N union D)=t^2                 for D nonempty,

kappa_C Energy(N)
 =(t+1)^2+
   (sum_(nonempty D subset C)(-1)^|D|)t^2
 =(t+1)^2-t^2
 =1+2t=y.                                              (CG12)
```

This is a positive range-classification theorem, not merely a pair of counterexamples: every
nonempty Boolean anchor curvature of a common Gram energy has full scalar range already in rank
one.  Thus positive semidefiniteness of the ambient Gram, common-profile coupling, anchor order,
and Boolean finite-difference structure impose no sign or monotonicity whatsoever on `(CG5)`.

The nonempty hypothesis is sharp.  For `C=empty`, `(CG9)` has one term and equals
`Energy(N)>=0`; for every nonempty `C`, `(CG10)` says its range is all of `R`.  Thus empty-anchor
positivity versus nonempty-anchor sign-surjectivity is the complete generic sign classification.

The theorem does **not** falsify an additional arithmetic sign law for the one physical packet
`g_m=(log m/m)k_(log(m/M))`.  It proves that such a law cannot come from Gram geometry or the
connected Boolean recursion alone.  The log-phase hostile source supplies the same rank-one
coherence mechanism, while the twin ridges `(PF5)`--`(PF6)` show why the actual reducible response
has no antisymmetric sign for Bianchi or order averaging to exploit.

The exact Lean extension should be a generic theorem in the common-profile curvature module:
construct the two-supported one-dimensional packet `(CG11)` and prove both
`booleanAnchorCurvature_twoSupport_eq` and
`booleanAnchorCurvature_range_eq_univ`.  The latter must quantify over every nonempty finite
anchor and every `y : Real`; no analytic, RH, or physical-profile hypothesis belongs in it.

## Gates

- [x] Audited against the exact `(PF1)`, `(AC13)`, and `(AC24)` normalizations.
- [x] Checked squarefree/coprime hypotheses and the protected-anchor frequency condition.
- [x] Completed the response, occupancy, and common-Gram paper proof.
- [x] Hostile sign, source-independence, and circularity audit.
- [x] Classified under standard Boolean Möbius inversion and Gram polarization.
- [ ] Exact Lean theorem and axiom gate.


## Fourier-side strengthening: signed shear tensor and density-induced rank collapse

`[PAPER-PROVED] [SAME POSITIVE SURVIVOR] [SPECTRAL NORMAL FORM] [BRIDGE]`

The weighted curvature `(CG7)` has an exact Fourier-side normal form.  For squarefree `l`, identify
`Z/lZ` with `product_(p|l) Z/pZ`, and put

```text
K_l(j,k)=product_(p|l)[p 1_(p|j)+p 1_(p|k)-1].
```

On the local `p`-coordinate let `u_p` be the all-one vector, `e_p` the delta vector at zero, and

```text
a_p=p e_p,                 b_p=u_p-p e_p.
```

Then

```text
K_p=a_p a_p^T-b_p b_p^T,
K_l=sum_(S subset P(l))(-1)^|S|v_Sv_S^T,               (SG1)

v_S=(tensor_(p notin S)a_p) tensor (tensor_(p in S)b_p).
```

The pairs `(a_p,b_p)` are independent, hence the `v_S` are independent.  If `r=omega(l)`, this
proves

```text
rank(K_l)=2^r,
inertia(K_l)=(2^(r-1),2^(r-1),l-2^r).                 (SG2)
```

The local nonzero eigenvalues are

```text
lambda_(p,+/-)=p/2(1 +/- sqrt(4p-3)),                  (SG3)
```

so the global nonzero eigenvalue multiset is indexed by sign choices and consists of their tensor
products.  Different sign choices are not claimed to give distinct products, and the congruence
vectors `v_S` are not claimed to be Euclidean eigenvectors.

The fixed-gap density is precisely the missing diagonal.  Namely

```text
D_l(j)=K_l(j,j)=product_(p|l)(2p 1_(p|j)-1),
A_l(j,k)=1_(j!=k)K_l(j,k),
A_l+diag(D_l)=K_l,                                     (SG4)

D_l(j)=sum_(h mod l)nu_h(l)e(-jh/l).                   (SG5)
```

Thus the density join converts the diagonal-deleted centered shear into the rank-`2^r` Boolean
tensor; it is not an arbitrary ridge deletion.

For Hilbert vectors `xi_x` and the unnormalised packets
`Z_j=sum_(x mod l)e(jx/l)xi_x`, local Fourier transformation of `a_p,b_p` gives

```text
sum_(j,k)K_l(j,k)<Z_j,Z_k>
 =l^2 sum_(S subset P(l))(-1)^|S|
    ||sum_((x,prod_(p in S)p)=1)xi_x||^2
 =l^2 sum_(x,y:l|xy)<xi_x,xi_y>.                       (SG6)
```

This is `(CG7)` with Boolean avoidance coordinates, written in the shear-frequency basis.  The
new spectral delta is exact: the density ridge annihilates `l-2^r` transverse channels and leaves
only the `2^r` branch-parity curvature coordinates.

The hostile verdict is unchanged.  The alternating branch squares are the original Boolean/lcm
incidence, not an estimate.  Replacing their signed difference by the sum of their absolute
energies is the positive-square loss exposed by `(35m66)`.  Summing the joined diagonal with the
Möbius lcm coefficients restores the singular-series density and hence the raw prime covariance,
so it reinserts `(35m55)` rather than controlling it.  Only a source-specific global relation
between the even and odd energies after the full `h,p,a,r` joining can advance `(AC25)`.

The isolated Lean extension is
`GaloisForLFunctions/RHTower/SquarefreeShearKernelSignedTensor.lean`.  It reuses the weighted
common-profile curvature module and adds the local signed-rank-one factorization, the generic
finite-coordinate signed branch outer-product expansion, and its scalar alternating-square
corollary.  Tensor rank/inertia, Fourier normalization, build, and axiom verification remain the
Stage-3 obligations.

## First-crossing conditioning loses the signed tensor gain sharply

`[FALSIFIED AS AN ANALYTIC GAIN] [PAPER-PROVED SHARP BOUNDARY] [BRIDGE]`

The rank-two local tensor has a square-root cancellation, but the first-crossing expansion does
not retain it.  Normalize

```text
T_p=p^(-2)K_p,
A_p=p^(-2)a_p a_p^T,
B_p=p^(-2)b_p b_p^T,

eta(p)=||T_p||=(1+sqrt(4p-3))/(2p),
eta(q)=product_(r prime, r|q)eta(r)            for squarefree q.  (SG7)
```

The local norms are exact:

```text
||A_p||=1,
||B_p||=1-1/p,
||T_p||=eta(p) asymp p^(-1/2).
```

Hence, for squarefree `q` with `(p,q)=1`, conditioning on one `b_p` crossing while retaining the
signed tensor on the earlier coordinates gives the sharp inequality

```text
|<Z,(B_p tensor T_q)Z>|
 <=(1-1/p)eta(q)||Z||^2,                               (SG8)

||(B_p tensor T_q)|| / ||T_(pq)||
 =(1-1/p)/eta(p)
 =(sqrt(4p-3)-1)/2
 asymp sqrt(p).
```

Both constants are attained by tensor products of the corresponding local top vectors.  Thus a
first crossing `q<=D<pq` pays, rather than gains, the square-root scale of the newly exposed prime.
If all already-selected coordinates use their `b` direction, their normalized rank-one outer
square has the equally sharp norm

```text
||tensor_(r prime, r|pq) B_r||
 =product_(r prime, r|pq)(1-1/r)=phi(pq)/(pq).          (SG8a)
```

This has only Euler/logarithmic decay, not a power of the crossing modulus.  The apparent
`eta(pq)` gain in the unconditioned signed tensor comes exactly from cancellation between the
`a_p` and `b_p` outer squares which first-crossing conditioning separates.

The physical bounded-variation estimate confirms the same scale.  Fix an earlier squarefree
product `q`, take crossing primes `p` in `P<=p<2P` with `(p,q)=1`, and retain only complete-period
terms `pq<=H_h`.  From `(PF14)` and `nu_h(pq)<=2^(omega(q)+1)`,

```text
sum_h sum_(P<=p<2P, pq<=H_h) |delta_h(e_(pq))|
 <<_(A,rho) 2^omega(q) q P^2 log(M)^O(1)/M^2
 = 2^omega(q) L^2 log(M)^O(1)/(q M^2),
L=qP.                                                   (SG9)
```

The crude `P^2` is sufficient and uses no prime-density asymptotic.  Equation `(SG9)` reaches the
endpoint scale `M^(-1) polylog(M)` only while `L^2<=qM`.  At `q=1` this is exactly the
`L<=sqrt(M)` boundary of `(PF15)`; at `L asymp M` it leaves scale `1/q`, rather than `1/M`.
For `pq>H_h`, `(PF13)` restores the zero mode and `asymp pq/H_h` undecaying low aliases, so the
bounded-variation argument becomes weaker, not stronger.

There is also no hidden fixed-`q` spacing gain.  If anchor frequencies were required to be
primitive along `pq`, the fractions with `p asymp P` would have spacing at least
`1/(qP^2)`, suggesting the large-sieve constant `M+qP^2`.  Causal anchoring deliberately does not
permit that restriction.  For every nonzero integer `v`, the allowed protected-anchor frequencies
`u_p=pv` satisfy

```text
u_p/(pq)=v/q,

S_(pq,h)(pv)/nu_h(pq)=S_(q,h)(v)/nu_h(q).              (SG10)
```

Thus the conditional response rows are literally identical across the crossing color `p`.
Equation `(SG10)` is the cross-color rank-one form of the already-proved reduced-frequency lifting;
fully reducing these fractions would erase the first-crossing prime.  A log-multiplicative phase
aligns this common row, while the two PF5/PF6 ridges occupy the same zero-coordinate branch and
reinforce it.  Equal-norm generalized-prime bursts tensorize the separated branch squares and
recreate `(35m66)`.  Parity removes the odd-gap terminal sector but leaves the even-gap survival
ramp, so it supplies no compensating sign.

`[POSITIVE SURVIVOR]` Equations `(SG8)`--`(SG10)` give a sharp classification: the full local
signed shear tensor has a square-root spectral gain; exposing one causal Boolean branch costs
exactly its reciprocal square-root factor; and the protected anchor then contains an exact
rank-one alias family across crossing colors.  This is dependency-closed finite linear algebra
plus reduced-frequency CRT lifting.  It explains why the tensor normal form reproduces the
large-sieve/parity wall instead of narrowing `(AC25)`.

The Lean extension, after the existing tensor module elaborates, should prove the exact operator
norms in `(SG7)`--`(SG8a)` and derive `(SG10)` from
`quadraticCongruenceRootSumTotal_causalGCDReduction`.  The analytic estimate `(SG9)` belongs on
paper and should not be encoded as an assumed formal interface.  No Lean or build process was run
for this audit.

## Lean exactness audit -- 2026-08-28

Corpus now certifies the finite structural surface in
`RHTower/CommonProfileBooleanAnchorCurvature.lean` and the
`RHTower/SquarefreeShearKernel*.lean` suite: `(CG2)`, `(CG5)`, `(CG7)`, `(CG9)--(CG12)`,
`(SG1)--(SG8a)`, literal CRT/Fourier transport, rank, inertia, and sharp operator norms.

Card is not yet Stage-3 exact. Remaining literal obligations are:

1. arithmetic `B_(c,r,h)` reduction `(CG1)` and its exact `Eresp` specialization;
2. physical-profile/vacuum identities `(CG3)--(CG4)` and joined law `(CG6)` with card's declared
   normalizations;
3. protected-anchor cross-colour row identity `(SG10)` as the card's literal specialization of
   `quadraticCongruenceRootSumTotal_causalAnchor`;
4. an exact theorem statement for `(SG9)`. Current `<<_(A,rho)` notation does not declare the
   window class, constants, or quantifier order, so an assumption wrapper or guessed constant would
   not be a faithful formalization.

No Lean file was changed or rechecked during this read-only audit. Card remains Stage 2.
