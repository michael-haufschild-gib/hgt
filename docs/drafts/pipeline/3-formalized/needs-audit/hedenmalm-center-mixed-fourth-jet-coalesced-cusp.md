# Hedenmalm center-mixed fourth-jet coalesced cusp

- **ID:** `hedenmalm-center-mixed-fourth-jet-coalesced-cusp`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (paper) / SOURCE THEOREM / ORDER-THREE POSITIVITY
- **Date:** 2026-07-20
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [AXIOM-AUDITED] [SOURCE-PURE] [NO COMPUTATION] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `hedenmalm-center-mixed-double-positivity-law.md`
- **Statement:** The actual theta source has a strict fourth-order reflection-product Turan law; after center mixing it makes the near-center three-point wall positive for every sufficiently small second gap, producing a source-derived positive-definite cusp at the coalesced corner.

## Goal

For `k = thetaCuspFullSource` and `0 < a < 1/2`, put

```text
M_a(t)=integral_(0,infinity) r sinh(a r) k(r/2+t)k(r/2-t) dr.
```

The already formalized cofinal theorem reduces unconditional order-three positivity to a bounded
two-gap square.  Its asymmetric local theorem opens a collar only when the second gap is large.
The present target is the opposite endpoint: prove that there is `delta_a>0` such that every
`0<y<delta_a` admits `epsilon_(a,y)>0` with

```text
0 < x < epsilon_(a,y)
  -> PosDef [M_a(t_i-t_j)]_(t=(0,x,x+y)).                 (CUSP)
```

This is a nested cusp, not a uniform square.  It leaves a genuine compact middle region open and
does not extrapolate order three to all finite orders.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement, exact attack, and parent-theory audit
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: Lean capstones, narrow build, axiom audit, generated index, and lint green
- [ ] 3 -> 4 publication-ready: standalone theorem, proof, Lean certificate, and external novelty review

## Exact fourth-order source target

Write `L=log k`.  The source theorem to prove is

```text
L''''(u)+4 L''(u)^2 > 0                                  (R4)
```

for every real `u`.  Equivalently, for

```text
P_u(t)=k(u+t)k(u-t),
```

one has the strict derivative Hankel inequality

```text
P_u(0) P_u''''(0)-P_u''(0)^2
  =2 k(u)^4 (L''''(u)+4L''(u)^2)>0.                      (H4)
```

This is the exact local order-three obstruction for the reflected source product.  It is stronger
than strict log-concavity and is not inferred from it.

## Analytic attack without computation

It is enough by reflection to work on `u>=0`.  Put

```text
A=pi exp(2u),        B=A-3/2,        A>3,
phi=thetaCuspSourceTerm(.,1),
k=phi(1+rho),        rho=sum_(n>=2) thetaCuspSourceTerm(.,n)/phi,
eta=log(1+rho).
```

### First atom

For `L_1=log phi`, its positive curvature is

```text
c=-L_1''=4A+6A/B^2.
```

Direct logarithmic differentiation gives

```text
G_1=L_1''''+4L_1''^2
   =16A(4A-1)+24A(8A-1)/B^2-72A^2/B^4.                 (1)
```

Since `A>3` and `B>3/2`,

```text
G_1 > (176/3-128/9)A^2=(400/9)A^2>400.                 (2)
```

Also `c<(20/3)A`.

### Exact tail-ratio differential bounds

For `n>=2`, set `d=n^2-1`, `z=Ad`, and

```text
r_n=thetaCuspSourceTerm(u,n)/phi(u),
h(v)=6/(2v-3),
q_n=(log r_n)'=-2z+h(An^2)-h(A).
```

Because `h` is strictly decreasing and `A>3`,

```text
2z < -q_n < (20/9)z.                                    (3)
```

Writing `T=2v d/dv`, differentiation gives

```text
T h(v)   = -24v/(2v-3)^2,
T^2 h(v) = 48v(2v+3)/(2v-3)^3,
T^3 h(v) = -96v(4v^2+24v+9)/(2v-3)^4.                  (4)
```

The absolute value of `T h` is decreasing on `[3,infinity)`, `T^2 h` is positive and
decreasing there, and `|T^3h|<=416`.  Hence, with `q_j` denoting successive `u` derivatives,

```text
-4z <= q_1 < -4z+8 < 0,
-8z-48 < q_2 < -8z < 0,
q_3 > -16z-832.                                         (5)
```

The Bell-polynomial identities for `r_n` then imply

```text
r_n' < 0,
r_n'' > 0,
r_n''' < 0,
r_n'''' > 0,                                            (6)
|r_n'| <= (20/9) z r_n,
r_n'' <= (400/81) z^2 r_n,
|r_n'''| <= 12 z^3 r_n.                                 (7)
```

For the fourth sign, write `p=-q_n`, `alpha=-q_1`, and `beta=-q_2`.  Then

```text
r_n''''/r_n
 =p^4-6p^2 alpha+3alpha^2+4p beta+q_3
 >=16z^3(z-6)-16z-832>0
```

because `z>=3pi>9`.

The existing exact atom comparison supplies

```text
0<r_n<=2 n^4 exp(-A(n^2-1)).                            (8)
```

### Symbolic exponential sums

Only the already proved inequalities

```text
exp(-3pi)<1/12000,       16 exp(-5pi)<1/1000
```

are used.  Consecutive terms from `n>=3` have a geometric ratio below `1/1600` for
degree eight and below `1/800` for degree ten.  Splitting off `n=2` therefore gives

```text
sum_(n>=2) n^4(n^2-1)^2 exp(-pi(n^2-1)) < 13/1000,
sum_(n>=2) n^4(n^2-1)^3 exp(-pi(n^2-1)) < 37/1000.       (9)
```

The already formalized degree-six sum is

```text
sum_(n>=2) n^6 exp(-pi(n^2-1)) <=4/747.                 (10)
```

Since `A^j exp(-Ad)` decreases on `[pi,infinity)` for `j<=3` and `d>=3`, (7)--(10),
`pi<4`, `pi^2<10`, and `pi^3<32` yield

```text
R_1:=|rho'|       <1/10,
R_2:=rho''        <13/10,
R_3:=|rho'''|     <29,
rho''''           >0.                                  (11)
```

The sharper combination needed below is

```text
8c R_2 < 220.                                           (12)
```

Indeed `c<(20/3)A`, `rho''<=(800/81)A^2 S_2(A)`, and
`A^3 S_2(A)<pi^3(13/1000)<52/125`.

### Closing the logarithmic perturbation

For `eta=log(1+rho)`, the denominator is at least one.  The alternating signs in (6) give

```text
eta'' <= rho'',
eta'''' >= -4 R_1 R_3-3R_2^2-6R_1^4.                   (13)
```

Since `L=L_1+eta`,

```text
L''''+4L''^2
 =G_1+eta''''+8L_1''eta''+4eta''^2
 >400-220-4(1/10)(29)-3(13/10)^2-6(1/10)^4
 >160.                                                  (14)
```

This proves (R4) on the positive half-line; continuity closes the endpoint and theta reflection
closes the negative half-line.

## Center-mixed transfer

For fixed `u`, let `P=P_u`.  Equations (R4)--(H4) imply

```text
P(0)>0,       P(0)P''''(0)-P''(0)^2>0.                  (15)
```

Let `d=M_a(0)`, `m_2=M_a''(0)`, and `m_4=M_a''''(0)`.  With positive measure
`dmu=r sinh(ar)dr` on `(0,infinity)`, differentiation under the integral gives

```text
d   =integral P(0)dmu,
m_2 =integral P''(0)dmu,
m_4 =integral P''''(0)dmu.
```

By (15), `P''''(0)>P''(0)^2/P(0)>=0`.  The quotient is integrable because it is dominated by the
integrable fourth jet.  Cauchy--Schwarz and strict integration give

```text
m_2^2
 <=d integral P''(0)^2/P(0)dmu
 < d m_4.                                               (16)
```

Thus the actual source satisfies the strict fourth-jet determinant

```text
Delta_a:=M_a(0)M_a''''(0)-M_a''(0)^2>0.                 (17)
```

## Coalesced-wall transfer

For an even `C^5` profile `f`, put `d=f(0)`, `f_j=f^(j)`, and

```text
W(y)=(-f_2(0))(d^2-f(y)^2)-d f_1(y)^2.                  (18)
```

This is exactly one half of the surviving second `x`-jet of the determinant at the packet
`0,x,x+y`.  Direct differentiation, using `f_1(0)=f_3(0)=0`, gives

```text
W(0)=W'(0)=W''(0)=W'''(0)=0,
W''''(0)=-6 f_2(0)(d f_4(0)-f_2(0)^2).                  (19)
```

For `f=M_a`, strict center curvature is already formalized and (17) makes the last expression
strictly positive.  Four integrations of the local sign give `W(y)>0` for every sufficiently
small positive `y`.  The existing exact local determinant theorem then produces the `x`-collar,
and the existing radial principal-minor laws upgrade its positive determinant to `(CUSP)`.

## Hostile attack and exact scope

1. **Not log-concavity in disguise.**  For `f(t)=exp(-t^2-t^4)`, strict log-concavity holds but
   `f(0)f''''(0)-f''(0)^2<0`; the fourth wall is independent.
2. **Not Nuttall's RR3 theorem.**  Nuttall proves sign-reverse regularity of the sum kernel
   `Phi(x+y)` through the derivative Hankel determinant
   `det[Phi^(i+j)]_(i,j<3)<0`.  The present invariant is the reflected product
   `Phi(u+t)Phi(u-t)` and then a positive aperture mixture.  Neither statement algebraically
   implies the other away from the reflection center.
3. **Not the generic positive-definite derivative inequality.**  Gneiting's sharp theorem says
   a genuinely positive-definite `C^4` function on the line must satisfy
   `f(0)f''''(0)>=f''(0)^2`.  Here positive definiteness is the open target.  The proof derives a
   strict inequality from the theta source before using it to build a finite positive chamber.
4. **No hidden RH input.**  Only theta atoms, their exact derivative series, reflection, symbolic
   exponential inequalities, integration, and Cauchy--Schwarz enter.
5. **No uniform-square claim.**  `epsilon_(a,y)` may shrink as `y->0`.  The bounded middle of the
   compact two-gap core remains open, as do all higher finite orders.

## Literature audit through 2026

- Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494, supplies the
  theta-source spectral route but not this finite three-point chamber.
- Gershon, *On the Log-Concavity of the Riemann Xi Kernel*, v2 (29 June 2026), treats strict
  order-two log-concavity and explicitly leaves higher-order positivity open.
- Csordas--Norfolk--Varga (1986), Csordas--Varga (1988), and Nuttall's March 2011 report prove
  coefficient/moment and sum-kernel determinantal inequalities of order three.  Their kernels and
  determinants are not (15)--(18).
- Gneiting, *On the Derivatives of Radial Positive Definite Functions* (1999), gives the sharp
  derivative inequality forced by an already positive-definite radial kernel.  It is the parent
  obstruction, not a source-side proof.
- Castano--Paksoy--Zhang, arXiv:1407.2800, identify positive `3x3` correlation matrices with
  triangle inequalities for the associated angles.  That is a scalar reformulation of the final
  matrix test, not a theta-source producer.

No source proving (R4), (17), or `(CUSP)` for Hedenmalm's center-mixed theta density was found.
Novelty remains provisional pending external expert review.

## Lean realization

1. `ThetaCuspFullReflectionFourthTuran` extends the exact source derivative series, proves the
   first-atom margin and tail estimates, and establishes
   `thetaCuspLogSource_fourthTuran_gt_one_hundred_sixty`.
2. The same module derives the actual reflected-product determinant
   `thetaCuspSourceReflectionFourthHankel_pos`.
3. `HedenmalmCenterMixedFourthJetCusp` supplies the generic fourth-wall Taylor identity and the
   conditional local positive-definite cusp.
4. `HedenmalmCenterMixedFourthJetCuspClosure` integrates the pointwise positive quadratic form,
   proves `thetaCuspCenterMixedDensity_fourthHankel_pos`, and discharges the source hypothesis in
   `exists_thetaCuspCenterMixed_coalescedCusp_posDef`.
5. `RiemannHypothesisSOTA2026` imports the closure while retaining the exact global RH boundary.

## Log

- 2026-07-20 -- created in Stage 1 after the compact-corner audit isolated the strict fourth jet
  as the first nonvanishing coalesced invariant; found the noncomputational first-atom/tail attack
  and separated it from Nuttall RR3 and the generic positive-definite derivative condition.
- 2026-07-20 -- hostile attack closed the exact derivative signs, symbolic tail sums, logarithmic
  perturbation margin, strict integral transfer, and fourth-wall Taylor transfer; promoted to
  Stage 2 with novelty still awaiting external review.  The source margin, reflected determinant,
  center-mixed determinant, and unconditional cusp were then formalized and axiom-audited; the
  final `RiemannHypothesisSOTA2026` build completed all 8977 jobs, promoting the card to Stage 3.
