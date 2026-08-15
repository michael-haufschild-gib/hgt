# Completed Suzuki zero modes live in a logarithmic boundary corona

- **ID:** `suzuki-completed-zero-mode-corona-seam-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper correction) + CONJECTURE
- **Scientific status:** `[PROVED CORRECTION] [NEW CONJECTURE] [NOT AN RH PROOF]`
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096, Section 8
- **Analytic source:** H. Chen and T. Weth, *The Dirichlet Problem for the Logarithmic
  Laplacian*, arXiv:1710.03416; P. A. Feulefack, S. Jarohs, and T. Weth, *Small order
  asymptotics of the Dirichlet eigenvalue problem for the fractional Laplacian*,
  arXiv:2010.10448; V. Hernandez-Santamaria, L. F. Lopez Rios, and A. Saldana,
  *Optimal boundary regularity and a Hopf-type lemma for Dirichlet problems involving the
  logarithmic Laplacian*, arXiv:2401.18033v2
- **Statement:** The RH-bearing zero fiber is the kernel of Suzuki's extension of `G_a` to the
  completed derivative space, not necessarily the kernel of the raw compact operator on `L2`.
  The principal boundary model has universal half-logarithmic indicial root `1/2`; conjecturally
  the non-`L2` zero-mode branch realizes this root and transports it to interior prime-power seams.

## Goal

Correct the domain of the CCM first-crossing problem and attack the part missed by raw screw
injectivity. The exact target is

```text
ker(A_a)=0 for every a>0,
```

equivalently nonvanishing of the eigenfunction-variable square Evans section at `lambda=0`.
In the derivative variable the same target is injectivity of the **extended** screw operator on
Suzuki's completion. A proof on raw `L2_0(-a,a)` alone does not close RH unless a regularity lift
is supplied.

> **2026-07-22 two-scale correction.** The model audit in
> `suzuki-corona-regular-two-scale-boundary-law.md` falsifies whole-packet separation by
> inverse-log grades. Nonzero power-scale `H1` solutions and inverse-log-flat non-`H1` solutions
> are invisible to every such grade. The seam hierarchy remains a detector for the corona
> quotient. The corrected gate is source-specific: zero corona trace must imply `H1_0`, after
> which the mode passes to the raw Evans problem.

## 1. Source audit: two derivative spaces must not be identified

Fix `a>0` and choose `mu<lambda_a=inf spec(A_a)`. Suzuki defines

```text
S_(a,mu)=G_a-mu K_a,
K_a=(-Delta_N)^(-1),
```

and completes `C_c^infinity(-a,a) intersect L2_0(-a,a)` in the positive `S_(a,mu)` norm. Denote
the result by `H(S_(a,mu))`. The closed derivative is an isometric isomorphism

```text
Dbar:H(A_a-mu I) -> H(S_(a,mu)),
A_a=Dbar^* Gtilde_a Dbar.                                  (1)
```

Here `Gtilde_a` is the bounded extension of `G_a`. Suzuki explicitly states

```text
H(S_(a,mu)) is not contained in L2(-a,a).                  (2)
```

The generalized eigenproblem is therefore

```text
Gtilde_a u=lambda K_a u,
u in H(S_(a,mu)).                                          (3)
```

At `lambda=0`, equation `(3)` is the kernel of `Gtilde_a`, not automatically the kernel of the
raw continuous-kernel map `G_a:L2_0->L2_0`.

## 2. Completion-corona theorem

Let

```text
j_a:L2_0(-a,a) -> H(S_(a,mu))
```

be the canonical injection. Strict positivity of `S_(a,mu)` makes `j_a` injective, and density
of the smooth core gives dense range. Define

```text
K_raw(a)=ker(G_a:L2_0->L2_0),
K_comp(a)=ker(Gtilde_a:H(S_(a,mu))->H(S_(a,mu))).          (4)
```

`[PROVED]` One has

```text
j_a(K_raw(a))=K_comp(a) intersect j_a(L2_0(-a,a)),         (5)
Dbar:ker A_a -> K_comp(a) is a linear isomorphism.         (6)
```

Consequently every completed zero mode lies in exactly one of two branches:

```text
regular branch:  Dbar v in j_a(L2_0),
corona branch:   Dbar v notin j_a(L2_0).                   (7)
```

### Proof

On the raw core and then by continuity,

```text
Gtilde_a j_a=j_a G_a.                                     (8)
```

If `u in K_raw(a)`, `(8)` puts `j_a u` in `K_comp(a)`. Conversely, if `j_a u` belongs to
`K_comp(a)`, then `(8)` and injectivity of `j_a` give `G_a u=0`. This proves `(5)`. The unitary
factorization `(1)` gives

```text
A_a v=0 iff Gtilde_a(Dbar v)=0,
```

and `Dbar` is bijective, proving `(6)` and `(7)`. `QED`

### First-crossing consequence

If RH is false, Suzuki's continuity theorem gives a first aperture `a_*` with

```text
lambda_(a_*)=0,
K_comp(a_*) != {0}.                                       (9)
```

If raw screw injectivity nevertheless holds at `a_*`, then `(5)` forces every nonzero vector of
`K_comp(a_*)` into the corona branch. Thus raw injectivity cannot be promoted to RH without
proving that the corona intersection is empty. The eigenfunction-variable square Evans map
`N_(a,0)` is completion-safe because it acts on the original `L2` eigenfunction and detects both
branches.

## 3. New half-logarithmic indicial law

The completion gap is not cosmetic. It is predicted by the principal boundary operator. On the
right half-line put `r=dist(x,partial I)`, `L=-log r`, and, after a harmless smooth cutoff away
from `r=0`, set

```text
phi_tau(r)=L^(-tau),  0<tau<1.                            (10)
```

For the unit-normalized one-dimensional logarithmic jump operator, its two leading pieces are

```text
exterior killing:
  phi_tau(r) integral_(-1)^0 1/(r-y) dy
    =L^(1-tau)+o(L^(1-tau)),

interior tail:
  integral_r^1 (phi_tau(r)-phi_tau(y))/(y-r) dy
    =-tau/(1-tau)L^(1-tau)+o(L^(1-tau)).                  (11)
```

The `y<r` block and replacement of `y-r` by `y` contribute lower order. Therefore

```text
L_log phi_tau(r)
 =C_log (1-2tau)/(1-tau)L^(1-tau)+o(L^(1-tau)),           (12)
```

with `C_log>0` determined by normalization. The unique leading indicial cancellation is

```text
tau=1/2.                                                   (13)
```

This recovers the mechanism visible in Chen--Weth's barrier coefficient: their proved boundary
estimate holds for every `tau<1/2`, while the leading barrier coefficient vanishes at `1/2`.
Feulefack--Jarohs--Weth explicitly left the optimal rate open. That gap was closed in 2024 by
Hernandez-Santamaria--Lopez Rios--Saldana: they prove the `tau=1/2` upper bound, show it is optimal
on the torsion solution, and prove a half-log Hopf lower bound for nonnegative supersolutions.
Their result validates the critical scale but does not supply a signed trace limit, trace-zero
`H1` lift, or polyhomogeneous expansion for Suzuki's signed perturbation.

If a nonzero zero mode has

```text
v(a-r)=c_+ L^(-1/2)+lower logarithmic orders,              (14)
```

then

```text
v'(a-r)~(c_+/2) r^(-1)L^(-3/2),                           (15)
```

which is not square integrable. Thus `(14)` produces exactly a corona vector under the closed
derivative.

## 4. Exact logarithmic boundary normal form

The indicial calculation has an exact Volterra form. Let `u` vanish outside `(0,1)` and define the
unit-range logarithmic jump operator

```text
(J u)(r)=integral_(r-1)^(r+1) (u(r)-u(y))/|r-y| dy,
0<r<1,                                                     (15a)
```

where `u(y)=0` for `y notin (0,1)`. Put

```text
r=exp(-L),
F(L)=u(exp(-L)),  L>0.                                    (15b)
```

`[PROVED EXACT NORMAL FORM]` For smooth `F` with a harmless cutoff near `L=0`,

```text
(J u)(exp(-L))
 =2L F(L)-integral_0^L F(t)dt
  +(R F)(L)-log(1-exp(-L))F(L),                           (15c)

(R F)(L)
 =integral_0^infinity [F(L)-F(L+s)]/(exp(s)-1) ds
  +integral_0^L [F(L)-F(L-s)]/(exp(s)-1) ds.              (15d)
```

### Proof

The exterior interval `(r-1,0)` contributes `L F(L)`, while `(1,r+1)` contributes
`-log(1-exp(-L))F(L)`. In the interior pieces use `y=r exp(-s)` for `y<r` and
`y=r exp(s)` for `y>r`. The first substitution gives the first integral in `(15d)`. The second
uses

```text
exp(s)/(exp(s)-1)=1+1/(exp(s)-1)
```

and its `1` part is

```text
L F(L)-integral_0^L F(t)dt.
```

Adding the exterior and interior pieces proves `(15c)`--`(15d)`. `QED`

The remainder is a genuinely lower logarithmic order. For `F(L)=L^(-tau)` after cutoff,
symmetrizing the two integrals for `s<L` gives a second difference divided by `exp(s)-1`; Taylor's
formula and the exponentially small `s comparable to L` tail yield

```text
(R F)(L)=O(L^(-tau-2))+O(exp(-L/2)).                      (15e)
```

Substitution in `(15c)` proves `(12)` with no barrier inequality.

### Canonical half-log trace equation

Set

```text
H(L)=sqrt(L)F(L).
```

The leading Volterra block in `(15c)` satisfies the exact conjugated derivative identity

```text
d/dL [2L F(L)-integral_0^L F(t)dt]
 =F(L)+2L F'(L)
 =2sqrt(L)H'(L).                                         (15f)
```

Consequently, if `(J u)(exp(-L))=Phi(L)`, then

```text
2sqrt(L)H'(L)
 =Phi'(L)-(R F)'(L)
  +d/dL[log(1-exp(-L))F(L)].                              (15g)
```

This is the exact boundary-trace interface. Whenever the right side divided by `sqrt(L)` is
integrable at infinity, the limit

```text
beta_+(u)=lim_(L->infinity) sqrt(L)u(exp(-L))              (15h)
```

exists. The analogous left trace `beta_-(u)` is obtained by reflection. Thus the previously open
boundary-expansion gate has been reduced to a concrete weighted integrability statement for the
lower-order Suzuki forcing, not an unspecified regularity theorem.

For the exact zero-mode equation, zeroth-order multiplication contributes derivatives one full
inverse-log order below `(15f)`; a visible translation samples an interior seam or the opposite
endpoint; and the regular polar--Gamma convolution is smooth at the endpoint. Each propagation
raises inverse-log order, but repeated positive and negative shifts generate a countable orbit,
not a finite seam family. The first unproved analytic step is therefore a simultaneous bootstrap
in a log-graded seam space.

## 5. Prime-seam transport conjecture

The exact Suzuki equation contains the finite visible translation family

```text
-sum_(n<=exp(2a)) Lambda(n)/sqrt(n)
  [v(x-log n)+v(x+log n)].                                (16)
```

A right-end layer `(14)` is transported by the `n`th term to the one-sided interior seam

```text
x=a-log n.                                                 (17)
```

The inverse principal logarithmic multiplier raises a one-sided log exponent by one. Hence the
predicted first transported layer is

```text
v(x)=c_(+,n)(-log|x-(a-log n)|)^(-3/2)+smoother,
c_(+,n)=1/4 Lambda(n)/sqrt(n) c_+,                        (18)
```

in the unit-normalized source convention of `(15c)`.  The exact factor `1/4` is
`alpha/(2alpha+1)` at `alpha=1/2`; Suzuki's displayed minus prime term is moved to the other side
of the zero equation. Iterated seams occur at
additive sums of `log n`, and each propagation raises the log order.

### Log-conormal order-raising theorem

`[PROVED]` Let a one-sided logarithmic conormal germ at `x_0` have high-frequency transform

```text
hat h(xi)
 =A exp(-i x_0 xi)/(i xi)(log|xi|)^(-alpha)
  +o(|xi|^(-1)(log|xi|)^(-alpha)).                       (18a)
```

Let the principal elliptic factor satisfy

```text
c(xi)=kappa log|xi|+O(1),  kappa>0.                       (18b)
```

Then its local inverse has

```text
widehat(c(D)^(-1)h)(xi)
 =(A/kappa) exp(-i x_0 xi)/(i xi)
   (log|xi|)^(-(alpha+1))
  +o(|xi|^(-1)(log|xi|)^(-(alpha+1))).                   (18c)
```

Indeed `(18c)` follows by division of `(18a)` by `(18b)`; the one-sided slowly varying Fourier
Abelian law identifies it with a spatial germ of exponent `alpha+1`. The bounded oscillatory
prime--Gamma remainder changes only subsequent inverse-log orders. Thus the direct coefficient in
`(18)` is nonzero whenever `Lambda(n)c_+` is nonzero.

The exact physical Volterra recurrence is stronger.  A source coefficient \(A L^{-\alpha}\)
produces

```text
alpha/(2alpha+1) A L^(-alpha-1).
```

At successive grades the product is

```text
theta_k=binom(2k,k)/8^k<=2^(-k).                         (18c1)
```

Hence total absolute grade-\(k\) mass is at most
`theta_k M_a^k<=(M_a/2)^k`.  The resulting profiles are nuclear directly in physical
`L2(dL)` on every tail `L_0>M_a/2`; this is proved in
`suzuki-physical-log-grade-nuclear-summability.md`.  Exact recurrence and nonvanishing are
formalized in `SuzukiVolterraLogGradeRecurrence.lean`.

For seams emitted from one fixed endpoint, distinct integers give distinct locations. Opposite-end
direct seams can collide:

```text
a-log n=-a+log m iff exp(2a)=mn.                          (18d)
```

Hence generic apertures have separated direct seams, while the discrete resonant apertures
`2a=log(mn)` carry a two-ended collision at one point.

`[PROVED ORIENTED COLLISION LAW]` That direct collision cannot cancel. The layer transported from
the right endpoint through `v(x+log n)` is supported on the left punctured side of
`x=a-log n`. The layer transported from the left endpoint through `v(x-log m)` is supported on
the right punctured side of `x=-a+log m`. At a resonance `(18d)` their base points coincide but
their one-sided germs remain disjoint. Restriction to the two punctured half-neighborhoods recovers
their coefficients separately. Thus even or odd parity can relate the coefficients but cannot
erase either oriented direct seam.

### Dense graded seam-orbit theorem

The finite visible shift **alphabet** must not be confused with a finite orbit. Once `2` and `3`
are visible, put

```text
alpha=log 2,
beta=log 3,
Gamma=Z alpha+Z beta.                                    (18e)
```

`[PROVED]` The ratio `alpha/beta` is irrational: a rational equality `alpha/beta=m/n` would give
`2^n=3^m`, contradicting unique factorization. Therefore the additive subgroup `Gamma` is dense
in `R`. The unrestricted algebraic seam orbit

```text
(+/-a+Gamma) intersect (-a,a)                            (18f)
```

is dense. This statement alone does not address support pruning, because every intermediate vertex
of a transport word must remain in the aperture.

`[PROVED SUPPORT-PRUNED DENSITY]` If `a>beta=log 3`, the vertices reachable from the right endpoint
by admissible words in `+/-alpha,+/-beta` are dense in the central corridor

```text
C_a=(-a+beta,a-beta).                                    (18f1)
```

The same holds from the left endpoint by reflection.

### Proof

Use density of `Gamma` to choose

```text
d in Gamma intersect (beta,2a-beta).                     (18f2)
```

Write `-d` as a reduced finite word in `+/-alpha,+/-beta`. If both signs occur, order it greedily
around its terminal value `-d`: take a negative letter when the current partial sum is greater than
`-d`, and a positive letter when it is at most `-d`. While both signs remain, one step can cross
`-d` by less than `beta`; after one sign is exhausted, the remaining tail is monotone to `-d`.
Because `d>beta`, every nonempty partial sum is strictly negative. If only negative letters occur,
the monotone ordering has the same property. Thus the ordered word has

```text
-d-beta < partial sum < 0.                               (18f3)
```

Starting at `a`, every noninitial vertex is consequently in `(-a,a)`, because
`d<2a-beta`; its terminal vertex `b=a-d` lies in `C_a` by `(18f2)`.

Now take any `gamma in Gamma` for which `b+gamma in C_a`. Order a reduced word for `gamma`
greedily: while both signs remain, take a positive letter when the current partial sum is
nonpositive and a negative letter when it is positive; after one sign is exhausted the remaining
tail is monotone. Every partial sum then lies between

```text
min(0,gamma)-beta and max(0,gamma)+beta.                 (18f4)
```

Since both `b` and `b+gamma` lie in `C_a`, `(18f4)` keeps the translated path strictly inside
`(-a,a)`. Hence every point of `(b+Gamma) intersect C_a` is admissibly reachable. That set is dense
in `C_a`, proving the claim. `QED`

The threshold `a>log 3` is sufficient, not claimed sharp. Below it the unrestricted orbit remains
dense whenever both shifts are visible, but the support-pruned graph needs a separate interval-
exchange analysis.

At propagation depth `k`, however, only finitely many words occur and their germs have exponent
`1/2+k`. Thus the correct carrier is

```text
finite characteristic packet
 -> countable seam state graded by inverse-log order,
with finite-dimensional piece at every grade.             (18g)
```

The grading prevents a later dense seam from canceling a lower-order direct seam, but it rules out
any proof based on one fixed *a priori* seam matrix.  A subsequent finite-dimensional compression
sharpens the last sentence: the square-Evans characteristic packet is finite-dimensional, so full
convergence of an infinite graded state is not necessary for kernel exclusion.  If exact
finite-order residual coordinates exist at every grade and jointly separate the characteristic
packet, at most `dim F_a` scalar coordinates already separate it, hence all grades through one
finite aperture-dependent cutoff suffice.  The required analytic input is arbitrary finite-order
expansion plus infinite-order log-flatness rigidity, not summation of the dense seam orbit.

### Prime-valuation semiring and first-arrival noncancellation

There is a stronger arithmetic organization. Let `P_a` be the finite set of visible primes and
write `z_p` for the valuation direction of `p`. The prime translation part is represented in the
positive Laurent semiring by

```text
T_a(z)=sum_(p^j<=exp(2a)) (log p)/p^(j/2)
       (z_p^j+z_p^(-j)).                                 (18h)
```

`[PROVED ALGEBRAICALLY]` Before support pruning, the grade-`k` coefficient at valuation vector `nu`
is exactly

```text
[z^nu] T_a(z)^k,                                         (18i)
```

the sum of the positive weights of all length-`k` prime words with net valuation `nu`. Unique
factorization gives

```text
sum_p nu_p log p=sum_p mu_p log p  iff  nu=mu,           (18j)
```

so `(18i)` classifies every same-end spatial collision. After support pruning the coefficient is
the corresponding subsum over admissible words. It is strictly positive exactly when at least one
admissible word reaches `nu`; there is no same-grade arithmetic cancellation.

`[PROVED CONDITIONAL ON THE POLYHOMOGENEOUS EXPANSION]` For the log-parametrix expansion, each prime
propagation contributes the same nonzero real principal factor (its sign depends only on the fixed
operator convention) and raises inverse-log grade by one. Therefore all admissible prime words of
the same length acquire one common sign. The bounded local subprincipal term may insert extra grade
without moving the seam, and the regular polar--Gamma convolution creates no new interior
one-sided singular support. Consequently the **first-arrival** coefficient at any reachable
prime-valuation vertex is a nonzero common-sign multiple of `(18i)`. Later grades may alter its
full expansion but cannot erase its leading one-sided germ.

This closes the iterated-collision gate left open after `(18d)`. Together with support-pruned
density it proves the conditional structural implication

```text
a>log 3 and a nonzero endpoint half-log trace
 -> nonzero first-arrival one-sided seams on a dense subset of C_a.            (18k)
```

It does **not** by itself contradict the logarithmic form domain: the seam grade tends to infinity.
The convergence concern is now resolved at multiplier level by the weighted valuation Wiener
inverse in `suzuki-two-root-valuation-wiener-lift.md`: for sufficiently large logarithmic frequency
the complete Neumann series converges absolutely in `ell^1(Z^(P_a))`, with a geometric remainder,
and all seams are slaved to two exterior endpoint amplitudes.  What remains is not summation but
construction and classification of those two amplitudes on Suzuki's completed form domain.  The
proof-bearing questions are now sharply separated:

```text
corona separation:
  a nonzero square-Evans packet outside the H1 branch produces a nonzero endpoint
  trace or a first nonzero corona descendant;

scale-gap regularity:
  a packet flat in every corona grade lies in H1_0 and enters the raw Evans problem;

finite-grade no-return:
  exact residual coordinates exist to arbitrary finite grade, jointly separate
  the finite characteristic packet, and their finite separating truncation
  cannot satisfy both endpoint residual conditions.                    (18l)
```

### `SUZUKI-COMPLETED-LOG-SEAM-NO-RETURN`

`[REVISED CONJECTURE]` For the actual polar--Gamma symbol and the exact von-Mangoldt coefficients,
every `f` in the finite characteristic packet of the square Evans reduction has a two-ended
half-logarithmic expansion to every prescribed finite order under Dirichlet reconstruction. The
resulting coordinates separate the **corona quotient**, not the whole packet. A packet flat in all
corona grades has an `H1_0` reconstruction and hence enters the raw screw Evans kernel. The corona
residuals have no nonzero two-ended state, and the raw Evans Gram is positive definite.

The chain would be

```text
det N_(a,0)=0
 -> nonzero characteristic packet f
 -> nonzero endpoint half-log coefficient or first nonzero descendant
 -> exact von-Mangoldt seam transport
 -> incompatible two-ended matching
 -> contradiction.                                       (19)
```

Proving `(19)` for every `a` gives `ker A_a=0` for every aperture and therefore RH.

## 6. Scientific tests and kill conditions

1. **Boundary expansion test.** Prove a polyhomogeneous half-log expansion for the Dirichlet
   inverse of `c_(a,0)(D)` on exponential-polynomial data. An upper bound
   `O(log^(-tau))`, `tau<1/2`, is insufficient.
2. **Parametrix test.** Prove that division by the principal log symbol raises a one-sided
   logarithmic seam exponent by exactly one and compute the nonzero coefficient in `(18)`.
3. **Collision test.** Same-end direct seams retain `Lambda(n)/sqrt(n)`. Opposite-end direct seams
   collide exactly when `exp(2a)=mn`, but their opposite one-sided orientations separate them.
   Later same-end collisions are classified by `(18h)`--`(18j)` and cannot cancel at first arrival;
   translations preserve the opposite orientations of two-ended collisions at every depth.
4. **Finite-order graded-carrier test.** Construct exact transport through every prescribed finite
   inverse-log grade.  Full convergence of the countable dense-seam state is sufficient but no
   longer necessary for kernel exclusion.
5. **Trace-separation test.** Prove that a nonzero square-Evans characteristic packet cannot be
   flat at both endpoints and at every recursively exposed seam.
6. **Two-ended test.** Eliminate the graded state to the finite characteristic packet and prove the
   resulting two-ended operator has no nonzero packet.
7. **Hostile generic-symbol control.** Logarithmic ellipticity alone cannot prove the result:
   tuned Dirichlet symbols can have special-aperture zero modes. Any proof that discards the
   actual polar--Gamma remainder or the von-Mangoldt coefficients is rejected.

The former whole-packet conjecture is killed: the principal Volterra problem admits both a nonzero
power-scale `H1` datum and an intermediate inverse-log-flat non-`H1` datum invisible to all
half-log coefficients. The strongest survivor is the two-channel law in
`suzuki-corona-regular-two-scale-boundary-law.md`. Kill the revised conjecture if the exact Suzuki
equation admits an inverse-log-flat non-`H1` zero mode, if the coefficient in `(18)` can vanish for
a visible prime power, or if a nonzero corona state satisfies the exact two-ended seam system.

The bounded homogeneous part of the scale-gap problem is now closed by
`suzuki-bounded-seam-half-log-rigidity.md`: arbitrary bounded vector-valued prime/polar--Gamma
coupling has either zero tail or a nonzero half-log trace. The exact nonlocal remainder `(15d)` is
handled, without replacing it by a pointwise multiplier, in
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-exact-log-remainder-signed-trace-rigidity.md`.
For every bounded classical zero mode with the optimal half-log bound, BV duality for the literal
symmetric remainder and penalized-extremum noncancellation force the signed pointwise endpoint
trace. The completion-to-bounded-weak lift is now proved in
`../3-formalized/new_scientific_knowledge/suzuki/suzuki-completed-eigenmode-atomic-jump-boundedness.md`.
Every completed eigenfunction is bounded because each von-Mangoldt shift pair is a positive atomic
Dirichlet jump minus a scalar potential; the polar--Gamma remainder maps `L2` to `L-infinity`.
The optimal boundary theorem therefore gives continuity and the sharp half-log bound. The weak
pre-trace gap is also closed in
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-weak-signed-half-log-trace.md`:
zero extension joins the exact remainder and killing term into a translation-invariant whole-line
jump; moving mollifiers transfer penalized-extremum noncancellation to bounded continuous weak
solutions. Every completed zero mode therefore has both signed endpoint traces. The exact next gate
is trace-zero regularity: prove that vanishing traces force membership in `H1_0`.

The exact remainder no longer leaves an arbitrary nonconormal homogeneous escape. In
`../3-formalized/new_scientific_knowledge/suzuki/suzuki-gamma-skew-frequency-flux-liouville.md`,
its full Gamma Fourier multiplier is retained. Differentiation turns that multiplier and every
bounded self-adjoint prime-seam adjacency into a skew frequency generator, so

```text
|eta| ||Fhat(eta)||^2
```

is conserved. Hence every homogeneous seam state in `L2(dL)` is zero, including rapidly
oscillating inverse-log-flat states outside all conormal classes. The remaining trace-zero gate is
now the literal completed-carrier connector.  The abstract carrier itself is constructed in
`../3-formalized/new_scientific_knowledge/suzuki/suzuki-support-pruned-selfadjoint-seam-carrier.md`:
it is the exact orthogonal compression of the visible real Laurent adjacency and is bounded
self-adjoint after support pruning.

The analytic part after realization is also closed.  The physical Gamma wall lies in a block
Hardy source space throughout `0<sigma<1`, giving shifted `L2`; the sharp derivative carrier is
not integrable anywhere below the first pole, exposing two high-frequency scattering charges.
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-gamma-weighted-tail-coercivity.md`
then uses the exact lower numerical range of `r(x+i sigma)` and the growing physical coefficient
`2L` to force both charges to vanish on any realized source-supported tail.  Thus the only live
trace-zero connector is no longer a regularity estimate.

The bare Hilbert-map formulation is itself too strong.  On every infinite valuation sector,
physical phase evaluation has unit-modulus response on all seam basis vectors, hence is unbounded
and nonclosable on `ell2`; this is proved source-specifically in
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-support-pruned-evaluation-rigging-fracture.md`.
The corrected connector is rigged: construct the actual completed-domain state in
`ell1(S_a) subset ell2(S_a)`, reconstruct the scalar mode by bounded `ell1` evaluation, and prove
the cutoff equation intertwines in the middle self-adjoint `ell2` space.

The high-frequency global part of this corrected connector is now constructed in
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-exterior-residual-rigged-wiener-realization.md`.
Every bounded completed eigenmode has an `L2` exterior residual and two ordinary `L2` Hardy
amplitudes.  Suzuki's source-normalized multiplier has leading coefficient `kappa=1`; its exact
valuation-Wiener inverse gives an
`L2_frequency(ell1) subset L2_frequency(ell2)` two-root state whose absolute evaluation recovers
the mode above a finite frequency threshold.

The literal pruning map has now been corrected. Exact exterior elimination contributes the
nonzero positive Feshbach self-energy
`P T Q(alpha Q+Q T Q)^(-1)Q T P`; plain compressed adjacency omits every path that leaves and
returns.  A second theorem upgrades the Neumann carrier to
`ell1_seams(L2_position)`, but its unitary boundary-log chart controls only the weighted measure
`exp(-L)dL`.  Physical Gamma analysis requires unweighted `dL`, equivalently nuclear
`L2(dr/r)`.

The apparent standalone measure upgrade has now been falsified.  For any continuous Dirichlet
profile split into low and high Fourier parts, physical `L2(dr/r)` of the high part forces the
low-frequency endpoint moment to vanish.  Even a boundary-flat `C_c^\infty` full profile can have
a nonzero low moment, hence a high part with infinite `dr/r` mass.
`suzuki-physical-log-low-frequency-boundary-lock.md` proves this exact lock, and
`SuzukiPhysicalLogBoundaryMomentLock.lean` formalizes its analytic core.  Nuclear valuation
control is stronger than scalar control and therefore cannot evade it by cancellation.

Remaining carrier gate is the **coupled** low/high two-port return with its two endpoint moments,
followed by exact boundary-log transport of the matched full exterior/Feshbach system and cutoff
identity.  High-frequency physical realization and low-frequency Evans matching cannot be proved
in sequence.

`suzuki-low-frequency-boundary-counterterm-renormalization.md` proves that these two moments
exhaust the singular low-band data.  Adding `m_+` and `m_-` to the two high endpoint profiles
restores the Dirichlet boundary value; the remaining low-band germs and all finite derivatives are
`O(exp(-L))`, hence lie in every exact Gamma strip below the first pole.  The open carrier does not
need an infinite low-frequency valuation state.

The exact scalar benchmark is now complete:
`suzuki-scalar-analytic-forcing-trace-zero-h1.md` proves that a trace-zero solution of the literal
Gamma normal equation with analytic-in-`r` forcing lies in weighted `H1` for every strip below the
first Gamma pole.  Hence it is physical `H1` as soon as the forcing exponent exceeds `1/2`.
Square-Evans exponential-polynomial data pass this test.  Remaining scale-gap issue is exclusively
the source theorem that recursively exposed prime-seam/Feshbach forcing is Gamma-subcritical.

Dense prime breadth and homogeneous Gamma coupling are no longer open.  The exact solution

```text
F_beta(L)=(L I-T/2)^(-1/2)beta
```

in `suzuki-prime-normal-binomial-resolvent.md` sums every prime valuation word with coefficient
`binom(2k,k)/8^k`.  Then `suzuki-gamma-prime-normal-corona-equivalence.md` proves that every
literal Gamma homogeneous solution differs from this prime representative with the same trace by
`O(L^-1)`, hence by a physical `L2(dL)` correction.  Thus the singular homogeneous corona is
exactly the half-log trace space; the remaining scale gap is the concrete completed
exterior/Feshbach forcing and cutoff intertwiner, not dense prime summability or homogeneous
prime--Gamma transport.

The exterior forcing now has a completion-safe model.  Instead of eliminating the two endpoint
roots before the nonlinear boundary-log chart, `suzuki-root-retained-exterior-dilation.md` retains
the full self-adjoint carrier.  Endpoint trace lies entirely in the exterior projection \(Q\), so
the strict-interior projection begins at grade one, belongs to unweighted
`H1(dL) intersect L2(dL)`, and
obeys the exact forced equation

```text
(2L I+R-P T P)(P F)'+P F=P T Q(Q F)'.
```

The right side is `L2(dL)`; every exterior excursion remains in `T^k`.  This bypasses the former
Feshbach--log conjugation gate without replacing the positive self-energy by plain compression.
Live source gap is exact identification of an actual completed zero mode with this root-retained
normal family and its global cutoff equation.  Unweighted `H1(dL)` is not spatial `H1(dr)`:
the latter still requires the trace-zero weighted Gamma upgrade with exponent `sigma>1/2`.

The first nonzero corona grade can no longer be hidden by Gamma scattering.
`suzuki-gamma-three-grade-delay-root-observability.md` sharpens the complete homogeneous
asymptotic to

```text
F_Gamma
 =L^(-1/2)beta+(1/4)L^(-3/2)T beta
  +(3/32)L^(-5/2)T^2 beta+O(L^-7/2).
```

The Gamma phase has a cubic zero and first contributes at grade three.  The grade-one
strict-interior observation has exact Gram

```text
sum_(p^j<exp(2a)) (log p)^2/p^j,
```

times the squared two-root trace norm, so it is injective once `a>(log 2)/2`.  This is immune to
opposite-end spatial resonance because oriented root labels remain orthogonal.  Lean formalizes
the strict-step coordinate injectivity in `SuzukiRootPortFirstGradeObservability.lean`.

The non-prime forcing has also lost its flat escape.
`suzuki-polar-remainder-lipschitz-gamma-subcriticality.md` proves from Suzuki's exact displayed
kernel that `r''` is locally Lipschitz, not merely continuous.  Hence the completed polar
convolution maps `L2` to `C^(0,1)` and its differentiated oriented boundary profile is
`O(exp(-L))`, inside every Gamma strip below the first pole.  The eigenvalue and scalar potential
are diagonal components of the homogeneous \(T\).  After the two low counterterms, every
non-prime source term is therefore Gamma-subcritical.  Remaining trace-zero obstruction is solely
the actual completed-mode-to-valuation-normal-family intertwiner.

That intertwiner cannot be a bounded localized orbit map.
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-localized-orbit-lift-selfadjointness-trilemma.md`
proves that a lift with coordinates `w_nu u(.-ell(nu))` is square summable only with
`w in ell2`, whereas projective prime-translation covariance forces `|w|` constant on each
connected valuation component.  The same condition follows if a diagonal decay is required to
preserve the literal constant-coefficient self-adjoint adjacency.  Infinite valuation components
therefore admit no nonzero bounded lift with all three properties.  This is the analysis-side dual
of the already proved nonclosable physical codiagonal.

The global Wiener state is not contradicted: its decaying entries are source-dependent parametrix
coefficients, not duplicated physical translates.  But it is delocalized, and componentwise
interval cutoff creates exactly the boundary commutator omitted by a naive global-to-log
identification.  The corrected E1 target is consequently a closed rigged relation, not a bounded
operator:

```text
completed source
  <-> graph-closed ell1 subset ell2 coefficient state,
with cutoff commutator retained in the graph norm.
```

Its `ell1` evaluation must reconstruct the scalar mode; self-adjoint Gamma analysis occurs in the
middle `ell2` space before evaluation.  The invariant-modulus core is formalized in
`SuzukiLocalizedOrbitLiftTrilemma.lean`.

The source relation itself is now constructed in
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-wiener-cutoff-closed-graph-relation.md`.
On the closed graph domain of Suzuki's literal multiplier, the high-frequency Wiener inverse maps
the exterior residual boundedly into `L2(ell1) subset L2(ell2)` and absolute evaluation recovers
the high physical mode.  If `P` is interval cutoff, its localized state satisfies exactly

```text
(a_a(D)+T_a)Pc
 =P chi_a(D)S b+[a_a(D),P]c.
```

The low source term is bandlimited analytic, prime adjacency commutes with `P`, polar forcing is
Gamma-subcritical, and scalar/eigenvalue transport is homogeneous diagonal.  The entire missing
cutoff source is the cross-boundary operator

```text
P[a_a(D),P]c=-P a_a(D)(1-P)c.
```

Its principal log kernel is Carleman `1/(s+t)`, so ordinary `L2` boundedness closes the graph
relation.  The remaining E1/E2 statement is strictly weighted: zero physical half-log trace must
place this Carleman port in a Gamma strip of exponent `sigma>1/2`.  That is now the exact content
of `SUZUKI-TRACE-ZERO-H1`.

The proposed trace-only form of that statement is false.
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-carleman-flat-port-weighted-strip-barrier.md`
uses `F(L)=exp(-sqrt L)`, which has zero half-log trace but is not spatial `H1`.  For the literal
Carleman cross block, after subtracting its unique endpoint constant,

```text
d/dL S(F)(exp(-L))=exp(-sqrt L)(1+o(1)).
```

It belongs to no positive Gamma strip.  Thus no combination of trace zero, ordinary Carleman
boundedness, graph closedness, or the two low counterterms proves the weighted upgrade.  The
counterexample is not a completed zero mode; it proves that the omitted completed-source
return equation is indispensable.

The proposed `SUZUKI-CLOSED-TWO-PORT-RETURN` strengthening has now been audited and retired in
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-two-port-return-redundancy-and-interior-null-core.md`.
On the exact relation,

```text
Ev(c)+u_low=u,
```

so exterior evaluation is exactly the support condition already built into the multiplier graph
domain.  Also `Pb=0` is exactly `P p_a(D)u=0`.  Hence the purported coupled class is just the
original supported completed nullspace.

This is not merely a formal observation.  The flat profile is compactly supported BV, therefore
belongs to `H^s` for every `s<1/2`; since `log<xi>` is dominated by every positive Sobolev power,
it lies in the full logarithmic multiplier graph domain and satisfies the exact high/low exterior
reconstruction.  Only the literal interior zero equation is absent.

The valid trace-zero target is therefore again, sharply and without carrier rhetoric,

```text
Pu=u,
P p_a(D)u=0,
beta_+(u)=beta_-(u)=0
 -> u in H1_0.                                           (30)
```

Any proof of `(30)` must extract new information from Suzuki's exact interior operator.  Graph
closedness, exterior support, counterterm matching, and Feshbach/Carleman decompositions are now
proved insufficient as a class.  The nonzero-trace two-port Evans return remains a separate
RH-bearing problem.

The interior equation now has a new exact carrier candidate.
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy.md`
uses the physical translates themselves with exponential valuation weight
`rho^|nu|_1`.  The lift is bounded into `ell2`, the scalar mode is its root coordinate, and prime
translation intertwines exactly with a bounded nonselfadjoint adjacency.  The loss of ordinary
self-adjointness is harmless for terminal Gamma coercivity, which needs only a numerical-range
bound by the operator norm.

The sharp admission invariant is

```text
R(a)=limsup_(|nu|->infinity)
 [-log|2a-sum_p nu_p log p|]_+/|nu|_1.                  (31)
```

For `R(a)<infinity`, one can choose the exponential weight so every nonresonant near-opposite-end
activation is square summable in any prescribed Gamma strip `sigma<1`.  Almost every aperture has
`R(a)=0`.  Dense relative-Liouville apertures have `R(a)=infinity`, and every tempered orbit
weight with bounded generator ratios fails there.  The precise next theorem is therefore
`SUZUKI-TEMPERED-ORBIT-NORMAL-IDENTITY` at finite recurrence type, followed by a continuity or
nontempered passage across the exceptional set.

The local Carleman defect in that identity is now closed by
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-paired-seam-carleman-logistic-normal-form.md`.
At an interior center retain both punctured orientations.  Their exact normal equations have
diagonal `2L+Gamma` blocks and one cross Carleman response.  Differentiation turns the latter into
logistic convolution

```text
k(t)=1/[4 cosh(t/2)^2],
||K||_(exp(sigma L)L2)
 <=pi sigma/sin(pi sigma),       |sigma|<1.             (32)
```

Thus it is a bounded zero-order coupling, not uncontrolled forcing.  A physical endpoint is the
special case whose opposite orientation is the actual zero exterior.  Infinite weighted
assembly and root-only trace support are the remaining finite-type gates.

Finite-grade root support is now closed in
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-interior-seam-indicial-dipole-exclusion.md`.
For an interior paired order `L^(-tau)`, `0<tau<1`, the indicial matrix

```text
[(1-2tau)I-J]/(1-tau)
```

is invertible.  Hence the physical half-log root cannot occur independently at an interior seam.
At `tau=1`, boundedness leaves only an antisymmetric logarithmic dipole; the principal
`2log|xi|` multiplier turns it into a nonzero step jump, which continuity of the full Suzuki
forcing excludes.  Thus every finite conormal interior singularity is a marked forced descendant
of grade at least one.  Remaining trace-support issue is exclusively the all-orders-flat,
nonconormal sector.

The local regular-singular flat-sector calculation survives, but arbitrary bounded-nonnormal Hardy
transfer has been retracted to
`suzuki-paired-gamma-logistic-flat-sector-conjecture.md`.
The paired frequency ODE has regular-singular residue

```text
-(I+J)/2=-P_sym.
```

Its symmetric pole is the subtracted common seam value. Its antisymmetric logarithm is the
`1/log` dipole, and zero physical source jump is the compatibility that removes it. Local
holomorphic gluing through `|Im z|<1` is valid. Quantitative block Hardy requires polynomial
two-sided growth of `exp(-ixB/2)`, not merely boundedness of nonnormal \(B\).

The radial exponential valuation carrier has a Hatano--Nelson positive-orthant limit with complex
elliptic spectrum, so its group grows exponentially on one frequency tail. This inserts a genuine
stable/unstable Evans matching gate for the direct frequency proof.

The primitive-forced equation has a second formulation, proved in
`../3-formalized/new_scientific_knowledge/suzuki/suzuki-primitive-flux-nonnormal-graph-reduction.md`.
With \(Y=(2L+R-B)F-G\), it becomes a first-order graph system whose weighted a priori estimate
uses only \(\|B\|\), not the group \(\exp(-ixB/2)\). The flat-tempered theorem in
`../3-formalized/new_scientific_knowledge/suzuki/suzuki-flat-primitive-flux-volterra-liouville.md`
then proves exponential value/flux decay from zero finite charge. Hatano--Nelson is not an
intrinsic no-go for the equation. Remaining problem is propagation of weighted flux regularity to
the physical root derivative.

The corrected positive class is proved in
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-log-recurrence-polynomial-carrier-trichotomy.md`.
For

```text
T_log(a)=limsup tau(nu)/log(2+|nu|_1)<infinity,
```

a polynomial valuation weight absorbs all Gamma events and makes prime evolution polynomially
bounded. This holds for almost every aperture; logarithmic-Liouville exceptions are dense.
Polynomial growth of degree \(m\) requires matching degree-\(m\) source moments, which are not yet
available from the base Gamma commutator theorem.

Coordinatewise event cutoffs also create a raw first-order commutator, classified in
`suzuki-coordinate-cutoff-covariance-classification.md`. Its exact positive survivor
`suzuki-coordinate-cutoff-primitive-flux-identity.md` rewrites the complete defect as

```text
([R-B,M]F)'+M'(2L+R-B)F,
```

so finite logarithmic recurrence controls the correct primitive-plus-zero-order base source without
assuming \(F'\). The augmented flux system then removes the primitive derivative, gives
arbitrary-nonnormal weighted graph uniqueness, and Volterra Liouville gives exponential value/flux
decay. Root-derivative propagation, literal paired assembly, and exact physical root dipole/flux
matching are now closed. Degree-\(m\) moments and
biweighted dichotomy remain alternative obligations of the direct Hardy architecture.

`../3-formalized/new_scientific_knowledge/suzuki/suzuki-complementary-primitive-flux-derivative-recovery.md`
now closes root-derivative propagation. The \(M\) and \(I-M\) primitive fluxes are exactly the two
cutoffs of the uncut flux, so their rough prime primitives cancel before weak derivative
coercivity.  The subsequent
`../3-formalized/new_scientific_knowledge/suzuki/suzuki-flat-flux-charge-automaticity.md`
discharges physical dipole/flat-flux matching: the one-sided zero-extension has only the half-log
indicial root and no `1/log` dipole, while superpolynomial block flatness forces terminal flux
charge zero. `../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-literal-paired-source-assembly.md`
closes exact two-coset source assembly and total marked-descendant matching. The formalized dyadic
orbit-chart theorem closes compact-middle coverage. Rank-one rough-primitive Hardy admission is
paper-closed on `2a<log 3`; remaining finite-type source gate is higher-rank
finite-to-flat/source-selected cancellation.

## 7. Lean decision

The arithmetic collision classifier is formalized in

```text
formal/GaloisForLFunctions/RHTower/SuzukiPrimeValuationSeam.lean.
```

It reuses the existing unconditional `primeLog_linearIndependent` theorem and proves injectivity of
the complete finite-support prime-valuation seam coordinate, same-end collision classification, and
the exact opposite-end affine resonance law. This is not a wrapper around the RH conjecture.

The formal tree still does not contain Suzuki's closed Weil form, its completed derivative space,
logarithmic Dirichlet reconstruction, or boundary polyhomogeneous calculus. Consequently the
support-pruned density proof, first-arrival asymptotic statement, and two-ended no-return remain
paper mathematics; abstract formalization would not certify source-specific analytic transport.

## Gates

- [x] source-space mismatch isolated from Suzuki Section 8
- [x] raw/completed kernel intersection theorem proved
- [x] first-crossing corona alternative proved
- [x] eigenfunction-variable square Evans route identified as completion-safe
- [x] half-logarithmic indicial exponent `1/2` derived
- [x] exact log-coordinate Volterra normal form derived
- [x] canonical half-log trace equation isolated
- [x] exact visible prime-power seam locations identified
- [x] generic log-elliptic shortcut hostile-tested and rejected
- [ ] prove simultaneous log-Dini bootstrap for exact lower-order Suzuki forcing
- [ ] prove full endpoint half-log expansion for the exact positive factor
- [x] prove local prime-seam order-raising law and nonzero principal coefficient
- [x] prove opposite-end direct resonances cannot cancel by one-sided orientation
- [x] prove support-pruned dense seam reachability for every `a>log 3`
- [x] classify iterated collisions by the positive prime-valuation Laurent semiring
- [x] exclude first-arrival arithmetic cancellation within any valid polyhomogeneous expansion
- [x] formalize prime-valuation seam-coordinate injectivity and opposite-end resonance in Lean
- [x] remove convergence of the infinite graded seam state as a necessary kernel-exclusion gate
- [x] formalize finite-dimensional collapse of a jointly separating hierarchy to finite grade
- [x] falsify whole-packet inverse-log separation and extract two-channel survivor
- [x] classify every bounded pointwise homogeneous seam coupling by its half-log trace
- [ ] construct exact Suzuki transport to every prescribed finite grade
- [x] prove weighted BV pairing and extremal noncancellation for the exact nonlocal remainder
- [x] prove every completion-safe square-Evans zero mode has a bounded weak representative
- [x] prove continuity and optimal half-log boundary decay for every completed zero mode
- [x] extend signed trace to bounded continuous weak zero modes
- [x] prove both signed endpoint traces exist for every completed zero mode
- [x] prove exact Gamma-skew frequency current for the literal nonlocal remainder
- [x] exclude homogeneous nonconormal `L2(dL)` seam coronas under self-adjoint coupling
- [x] construct the abstract support-pruned self-adjoint Hilbert seam carrier
- [x] prove trace-zero homogeneous component belongs to `L2(dL)` after exact carrier realization
- [x] prove forced Gamma-strip decay with physical exponent greater than `1/2` after realization
- [x] prove physical-tail coercivity annihilates both derivative scattering charges after realization
- [x] rule out bounded physical evaluation from the bare infinite `ell2` carrier
- [x] extract the `ell1 subset ell2` rigged-carrier survivor
- [x] construct the high-frequency completed-domain map into the global rigged carrier
- [x] classify and formalize the positive exterior Feshbach return correction
- [x] upgrade the carrier to `ell1_seams(L2_position)`
- [x] prove free-standing high-tail `L2(dr/r)` control is false
- [x] identify and formalize the low-frequency boundary-moment lock
- [x] reduce low band to two counterterms plus Gamma-subcritical forcing
- [x] close scalar analytic-forcing trace-zero `H1` benchmark
- [x] compute exact grade factor `binom(2k,k)/8^k` and physical nuclear threshold `L_0>M_a/2`
- [x] sum every prime valuation grade in the exact binomial resolvent
- [x] identify the literal Gamma homogeneous corona with the prime-normal corona modulo `L2(dL)`
- [x] retain exterior endpoint roots and prove strict-interior carrier lies in `H1(dL) intersect L2(dL)`
- [x] derive exact unweighted `L2(dL)` exterior source while retaining all Feshbach return paths
- [x] prove Gamma leaves prime grades one and two unchanged and first enters at grade three
- [x] prove and formalize strict-step root-port first-grade injectivity
- [x] prove exact polar kernel is locally Lipschitz and Gamma-subcritical after differentiation
- [x] move eigenvalue/scalar term into homogeneous diagonal transport
- [x] prove/formalize bounded localized orbit-lift covariance/self-adjointness trilemma
- [x] replace bounded global-to-local intertwiner by a closed rigged-relation target
- [x] retire the proposed coupled exterior-return condition as redundant
- [x] construct the global-Wiener/support-pruned closed rigged relation
- [x] prove its exact cutoff-commutator graph identity and closedness
- [x] disprove trace-only Gamma-strip decay for the literal Carleman cutoff port
- [x] prove exact exterior evaluation is redundant with supported high/low reconstruction
- [x] prove the flat obstruction lies in the complete logarithmic multiplier graph domain
- [x] retire `SUZUKI-CLOSED-TWO-PORT-RETURN` as a false strengthening
- [x] construct the bounded nonselfadjoint weighted physical-orbit carrier
- [x] prove exact root reconstruction and prime intertwining
- [x] classify the carrier by the aperture recurrence exponent
- [x] derive the paired seam normal form and exact logistic strip bound
- [x] prove finite-grade conormal trace is supported only at physical roots
- [x] exclude the interior borderline logarithmic dipole
- [x] classify paired regular-singular value/dipole charges
- [x] retract arbitrary bounded-nonnormal Hardy transfer
- [x] prove logarithmic-recurrence polynomial-carrier trichotomy
- [x] prove coordinate-cutoff covariance obstruction and primitive-flux survivor
- [x] prove primitive-flux arbitrary-nonnormal weighted graph reduction
- [x] prove flat-tempered primitive-flux Volterra Liouville
- [x] prove complementary primitive-flux root derivative recovery
- [x] prove physical endpoint dipole and terminal flat-flux charge vanish automatically
- [ ] prove `SUZUKI-POLYNOMIAL-ORBIT-NORMAL-IDENTITY`
- [ ] prove degree-m source moments or biweighted Evans dichotomy only if direct Hardy is retained
- [x] derive literal two-coset source assembly with corrected rooted transport signs
- [x] verify total marked-descendant zero-dipole source moment in literal assembly
- [ ] pass recurrence-infinite apertures
- [ ] extract a new source-specific consequence from `P p_a(D)u=0`
- [ ] prove the literal trace-zero supported-nullspace theorem `(30)`
- [ ] prove inverse-log-flat zero modes lie in `H1_0`
- [ ] identify the trace-zero square-Evans kernel with the raw Evans kernel
- [ ] prove corona separation for the finite square-Evans characteristic packet
- [ ] prove raw Evans Gram positivity for every aperture
- [ ] eliminate graded carrier to exact two-ended characteristic operator
- [ ] prove its injectivity for every aperture
- [ ] `det N_(a,0)!=0` for every aperture
- [ ] RH

## Log

- 2026-07-22 — Source audit found raw `L2`/Suzuki-completion mismatch; proved the completion-corona
  alternative, derived critical half-log boundary exponent, and opened the source-specific
  prime-seam no-return conjecture.
- 2026-07-22 — Critical translation flux made every finite log grade metrically observable.
  Finite-dimensional square-Evans compression then removed countable seam convergence as a
  prerequisite: arbitrary finite-order transport plus joint log-flatness separation yields one
  finite separating grade cutoff.
- 2026-08-01 — Retaining the exact Gamma multiplier gives conserved frequency current
  `|eta| ||Fhat||^2`; no homogeneous `L2(dL)` seam corona survives, even with nonconormal
  high-frequency oscillation. Source-carrier realization and forced Gamma-strip decay remain.
- 2026-08-01 — Physical Gamma-wall block Hardy transfer closes shifted `L2` after carrier
  realization.  A sharp derivative-tail theorem exposes two scattering charges, while the exact
  shifted-Gamma numerical-range bound plus `2L` tail coercivity forces both to vanish.  Only the
  literal completed-domain carrier map/intertwiner remains in the trace-zero regularity gate.
- 2026-08-01 — Bare `ell2` carrier evaluation was falsified: the unit-phase codiagonal is
  nonclosable on every infinite seam sector.  Exact survivor is a rigged
  `ell1 subset ell2 subset ellInfinity` carrier; completed-domain `ell1` realization is now the
  precise E1 theorem.
- 2026-08-01 — Bounded completed modes have `L2` exterior residuals.  Exact source normalization
  `kappa=1` and the valuation-Wiener inverse construct their high-frequency
  `L2(ell1) subset L2(ell2)` two-root carrier.  E1 is narrowed to the global-to-logarithmic
  support-pruned intertwiner.
- 2026-08-01 — Hostile carrier audit proved plain support pruning misses a nonzero positive
  exterior Feshbach return.  Wordwise Neumann majorization gives
  `ell1_seams(L2_position)`, but physical log measure is `dr/r`, not `dr`; E1 now turns on that
  sharp nuclear measure upgrade and the corrected boundary-log intertwiner.
- 2026-08-01 — Proved the proposed standalone measure upgrade structurally false.  Physical-log
  mass of the high tail forces low-frequency endpoint moments; a boundary-flat smooth full profile
  need not satisfy them.  E1 carrier realization and E3 low-frequency return are now one coupled
  source problem.
- 2026-08-01 — Proved the positive counterterm survivor: low band contributes only two endpoint
  constants to the singular carrier; after subtracting them its log-boundary germ is
  `O(exp(-L))` throughout every subcritical Gamma strip.
- 2026-08-01 — Closed exact scalar scale gap: analytic-in-boundary forcing plus zero half-log
  trace implies weighted `H1` below the first Gamma pole.  Live gap is now only dense
  prime-seam/Feshbach forcing.
- 2026-08-01 — Exact Volterra coefficient replaces the unspecified first-seam constant by `1/4`.
  Grade `k` carries `binom(2k,k)/8^k`, so a uniform word expansion is nuclear directly in
  physical `L2(dL)` once `L_0>M_a/2`.
- 2026-08-01 — Summed all dense prime words as `(L I-T/2)^(-1/2)beta`.  Exact Gamma scattering
  differs from that representative by `O(L^-1)`, proving both flows have the same non-`L2`
  corona and moving the live gate to the completed exterior/Feshbach forced domain.
- 2026-08-01 — Retaining endpoint roots through Gamma transport makes strict-interior projection
  unweighted `H1(dL) intersect L2(dL)` with exact source `PTQ(QF)'`.  Positive Feshbach return is
  retained pathwise; spatial `H1(dr)` still requires the weighted trace-zero Gamma gate.
- 2026-08-01 — Sharpened Gamma/prime comparison from `O(L^-1)` to `O(L^-7/2)`: Gamma first enters
  at grade three.  Exact first-grade root Gram proves every nonzero two-port trace is observable
  for `a>(log 2)/2`; strict-step injectivity is kernel-checked in Lean.
- 2026-08-01 — Exact polar formula upgrades Suzuki's stated `C^2` remainder to locally Lipschitz
  second derivative.  Polar convolution has differentiated rate `exp(-L)` in every subcritical
  Gamma strip; scalar/eigenvalue potential belongs in homogeneous diagonal transport.
