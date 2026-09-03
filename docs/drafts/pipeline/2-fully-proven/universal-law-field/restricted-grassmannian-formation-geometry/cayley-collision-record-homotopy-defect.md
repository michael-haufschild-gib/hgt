# Cayley-collision record homotopy defect

- **ID:** ULF-CCRHD-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor operator theorem
- **Parents:** `ULF-SCIN-001`, `ULF-SKPM-001`, `ULF-DHNJ-001`, `ULF-PHIN-001`
- **Purpose:** replace the separable history weight `diag(w_n) tensor A` by one source-forced
  prime-pair colligation in which the prime collision itself generates history.

## 1. Big-picture law

The old history defect has the correct marginals but factors history from prime formation.  The
Kummer calculation says more: its latent survival coordinate is the squared Cayley contrast of
two literal prime clocks.  History is therefore not an extra damping axis.  It is the open record
of how long one mixed-prime collision survives its complementary Cayley exit.

The required source object is obtained in three forced steps:

```text
cubic prime coherence
  --relative metric transgression-->
Beta(3/2,3) Hodge collision state
  --Cayley survival/exit colligation-->
coherent open history
  --history phase quotient-->
positive integral nuclear record T.
```

No zero, divisor, chosen ordinate, Xi vector, or RH premise occurs.

## 2. Hodge-transgressed prime-pair state

Put `mu(dx)=exp(-x)dx` on `(0,infinity)` and

```text
kappa(x,y)=8(xy)^(3/2)/(x+y)^3,
delta(x,y)=(x-y)/(x+y),
lambda(x,y)=delta(x,y)^2,
g(x,y)=2sqrt(xy)/(x+y).
```

Then

```text
lambda+g^2=1,
kappa=g^3=(1-lambda)^(3/2).                           (CCRHD.1)
```

On `E=L2((0,infinity)^2,mu tensor mu)`, define

```text
Omega_H(x,y)
  =sqrt(105/8) [delta/sqrt(1-lambda)] kappa(x,y)
  =sqrt(105/8) delta(x,y)(1-delta(x,y)^2).            (CCRHD.2)
```

The apparent singular factor in the first formula cancels one half-power of cubic coherence.
Thus `Omega_H` is bounded, square-integrable, reflection-odd, and zero on the equal-clock
diagonal.  It is the oriented relative Hodge state after deletion of the common metric part, not
an independently chosen Beta vector.  Its squared density is the positive relative density
`lambda/(1-lambda)`; choosing its positive square root would discard source orientation.

**Theorem CCRHD-A.** `||Omega_H||=1`, and the law of `lambda` in the vector state `Omega_H` is
`Beta(3/2,3)`:

```text
<Omega_H,F(lambda)Omega_H>
 = integral_0^1 F(a) (105/16)a^(1/2)(1-a)^2 da.       (CCRHD.3)
```

**Proof.** Use `r=x+y`, `v=(x-y)/(x+y)`.  Then

```text
dxdy=r dr dv/2,
kappa^2=(1-v^2)^3,
lambda=v^2.
```

The radial integral is `integral_0^infinity r exp(-r)dr=1`, while

```text
integral_(-1)^1 (1/2)v^2(1-v^2)^2 dv
 =integral_0^1 v^2(1-v^2)^2 dv=8/105.
```

This proves normalization.  Substitution `a=v^2`, including the two signs of `v`, gives
`(CCRHD.3)`. QED.

This corrects a tempting but false interpretation.  The raw squared cubic kernel has contrast
law `Beta(1/2,4)`, not `Beta(3/2,3)`.  The Hodge law is its size-biased relative transgression

```text
Beta(1/2,4) --multiply by lambda/(1-lambda)--> Beta(3/2,3).          (CCRHD.4)
```

Therefore the Beta shift is evidence for a forced anomaly subtraction, not a coincidental
relabeling of the raw Gram measure.

## 3. One conservative prime-collision homotopy

Let `S,E_0 : E -> E` be multiplication operators

```text
S f=delta f,
E_0 f=sqrt(1-lambda)f=g f.                           (CCRHD.5)
```

They obey

```text
S* S+E_0* E_0=I,
S^N ->0 strongly.                                    (CCRHD.6)
```

Define the observability map

```text
O : E -> ell2(Nat;E),
(O f)_n=E_0 S^n f.                                   (CCRHD.7)
```

**Theorem CCRHD-B.** `O` is an isometry and its finite history satisfies the operator telescope

```text
sum_(n<N) S*^n E_0*E_0 S^n + S*^N S^N=I.            (CCRHD.8)
```

**Proof.** All operators in `(CCRHD.5)` commute.  The finite geometric sum gives `(CCRHD.8)`.
Pointwise `|delta|<1`, so dominated convergence gives `S^N f->0` for every `f`.  Taking the
limit of quadratic forms in `(CCRHD.8)` proves `||Of||=||f||`. QED.

For the distinguished Hodge collision state put

```text
e_n=E_0 S^n Omega_H.                                 (CCRHD.9)
```

Its exit and survival masses are exactly

```text
||e_n||^2
 =w_n=630/((2n+3)(2n+5)(2n+7)(2n+9)),
||S^n Omega_H||^2
 =m_n=105/((2n+3)(2n+5)(2n+7)),                     (CCRHD.10)
m_n=sum_(k>=n)w_k,
sum_n w_n=1.                                         (CCRHD.11)
```

**Proof.** Equation `(CCRHD.3)` gives

```text
||S^n Omega_H||^2=E[lambda^n]
  =(105/16)B(n+3/2,3)=m_n.
```

Likewise `||e_n||^2=E[(1-lambda)lambda^n]=m_n-m_(n+1)=w_n`.  Telescope and
`m_n->0` give `(CCRHD.11)`. QED.

This is the missing nonseparable interpretation of `ULF-PHIN-001`: conditional on a literal
prime-pair contrast, lifetime is geometric; averaging only afterward gives the rational Hodge
tail.

## 4. Object nobody asked for

Let `P_n` denote the grade-`n` summand of `R=ell2(Nat;E)`.  Define

```text
mathsf T
  = directSum_(n>=0) |e_n><e_n|,                    (CCRHD.12)
```

or, as one integral kernel,

```text
mathsf T((n;x,y),(k;x',y'))
  =1_(n=k)e_n(x,y) conjugate(e_n(x',y')).            (CCRHD.13)
```

Equivalently, if `D_hist(X)=sum_n P_n X P_n` is history dephasing, then

```text
mathsf T
 =D_hist(|O Omega_H><O Omega_H|).                    (CCRHD.14)
```

Equation `(CCRHD.14)` is the exact meaning of “positivity is phase quotient”: the lifted open
history is one coherent pure state; the closed observer forgets relative history phases but
retains every exit record.

**Theorem CCRHD-C.** `mathsf T` is positive, self-adjoint, nuclear, and integral:

```text
mathsf T>=0,
mathsf T in S_1,
Tr mathsf T=||mathsf T||_1=1,
||mathsf T||=w_0=2/3<1.                              (CCRHD.15)
```

The Stokes chamber orientation gives the signed section

```text
mathsf T(t)=sign(t)mathsf T,
Tr mathsf T(t)=sign(t),
mathsf T(-t)=-mathsf T(t).                            (CCRHD.15a)
```

Moreover

```text
Tr((sum_(k>=n)P_k)mathsf T)=m_n,                     (CCRHD.16)
```

so all Kummer/Hodge jets are jointly reconstructed from one operator.

**Proof.** Each summand in `(CCRHD.12)` is positive rank one with trace norm `||e_n||^2=w_n`.
Equation `(CCRHD.11)` gives trace-class convergence, positivity, and unit trace.  Orthogonality of
history summands gives `||mathsf T||=sup_n w_n`; the explicit formula is decreasing and starts at
`2/3`.  Tail summation gives `(CCRHD.16)`. QED.

Unlike `diag(w_n) tensor A`, the grade-`n` prime-pair amplitude is

```text
e_n(x,y)=sqrt(105/8)delta(x,y)^(n+1)kappa(x,y).       (CCRHD.17)
```

Every positive grade is therefore created by a genuinely unequal prime pair.  Prime collision,
history depth, and cubic coherence cannot be separated by a tensor factorization.

There is also an exact orientation law that the positive masses alone cannot see.  Let
`Jf(x,y)=f(y,x)`.  Then

```text
J Omega_H=-Omega_H,   J S J=-S,   J E_0 J=E_0,
J e_n=(-1)^(n+1)e_n.                                  (CCRHD.17a)
```

Consequently `J mathsf T J=mathsf T`: every diagonal rank-one block loses its sign.  Before
dephasing, however, the `(n,k)` block of `|O Omega_H><O Omega_H|` changes by `(-1)^(n+k)`.
Reflection orientation therefore lives exactly in cross-grade coherence.  History dephasing is
not merely a probabilistic mixture; it is the phase quotient that turns the oriented lifted
record into a reflection-even positive observer.

## 5. Literal atomic prime section

For aperture `d>0`, let

```text
A_d(p,q)=sqrt(pi_d(p)pi_d(q))kappa(log p,log q),
delta_pq=(log p-log q)/(log p+log q),
lambda_pq=((log p-log q)/(log p+log q))^2,
Z_d=sum_(p,q) [lambda_pq/(1-lambda_pq)]|A_d(p,q)|^2. (CCRHD.18)
```

The factor in `Z_d` is harmless because

```text
[lambda/(1-lambda)]kappa^2=lambda(1-lambda)^2<=1.
```

All cross-prime entries are nonzero, hence `0<Z_d<infinity`.  Put

```text
Omega_(H,d)(p,q)=Z_d^(-1/2)[delta_pq/sqrt(1-lambda_pq)]A_d(p,q),
S_d=delta_pq,
E_d=sqrt(1-lambda_pq),
e_(n,d)=E_d S_d^n Omega_(H,d),
mathsf T_d=directSum_n |e_(n,d)><e_(n,d)|.            (CCRHD.19)
```

**Theorem CCRHD-D.** For every `d>0`, `mathsf T_d` is a literal pre-divisor, prime-mixed positive
trace-class operator with

```text
Tr mathsf T_d=||mathsf T_d||_1=1,
||mathsf T_d||=||e_(0,d)||^2<1.                      (CCRHD.20)
```

Its matrix has nonzero entries between arbitrary unequal prime-pair labels in every history
grade.  Under the source quantile chart, `mathsf T_d -> mathsf T` in trace norm as `d->0+`.

**Proof.** Every `lambda_pq` is in `[0,1)`, and the normalized Hodge state has support on
`p!=q`, where `lambda_pq>0`.  The same geometric telescope as CCRHD-B gives total exit mass one;
strict positivity of the mean survival mass gives the strict norm bound.  For wall convergence,
rewrite the apparently singular amplitude as

```text
[delta/sqrt(1-lambda)]kappa=delta(1-lambda).
```

It is bounded and continuous in the quantile coordinates.  Almost-everywhere quantile
convergence plus dominated convergence gives `Omega_(H,d)->Omega_H` and every fixed exit vector.
The tail trace after grade `N` is the `N`-th `lambda` moment.  Its wall limit is `m_N->0`, so a
finite-head/tail split upgrades convergence of the block rank-one operators to trace norm. QED.

Thus the continuum operator is not a fitted probability model.  It is the trace-norm wall landing
of a literal all-prime section.

## 6. Exact RH leverage and boundary

The source colligation has zero residual survival:

```text
S^N Omega_H ->0,
sum_n |exit at n|^2=1.                               (CCRHD.21)
```

An off-line Xi copy instead creates a rank-one multivalued relation horizon.  Therefore a
record-complete theta/Poisson intertwiner that preserves the anomaly-subtracted colligation would
have to send zero source residual to a nonzero completed residual, which is impossible.  This is
the operator mechanism sought by `MUST-156`; it is stronger than trace preservation or a scalar
moment equality because it includes the survival operator, exit operator, coherent lifted state,
and every record grade.

`CCRHD-001` does **not** construct that theta/Poisson intertwiner.  Nor may completion act only on
the positive density `mathsf T`: `(CCRHD.17a)` proves that dephasing forgets the reflection-odd
cross-grade coherence and falls under `CANNOT-227`.  A valid completion object must carry the
marked triple

```text
(Omega_(H,d), S_d, E_d)
```

together with the pole--Gamma countercurrent, and prove its boundary is the completed relation
horizon.  Any ordinary normal channel can concentrate a diffuse state into a pure state, so
trace preservation alone remains useless (`CANNOT-233`).

## 7. Hostile novelty and failure audit

- `[REDISCOVERED]` Stable-contraction observability operators and their telescopes are classical;
  see Ball--Bolotnikov--Fang, arXiv:math/0610634, and the de Branges--Rovnyak operator-model
  literature.
- `[REDISCOVERED]` Hausdorff/Berger moment realizations of subnormal weighted shifts are classical;
  see Curto--Exner, arXiv:1404.1594, and Benhida--Curto--Exner, arXiv:2405.15000.
- `[CORPUS FUSION]` New content here is the forced oriented arithmetic state `(CCRHD.2)`: relative
  transgression changes the raw cubic `Beta(1/2,4)` law into the already observed Hodge
  `Beta(3/2,3)` law, after which signed literal Cayley contrast generates every history grade and
  prime swap becomes alternating history parity.
- The trace integer is the rank of the source line transported by the isometry `O`; it is not yet
  the Xi multiplicity integer.  Equating those integers without the marked boundary theorem would
  restate the missing RH edge.
- `mathsf T` is quadratic in the Hodge amplitude.  Unsquared Euler provenance survives only in the
  marked amplitude before history dephasing; discarding that mark makes the construction
  covariance-even and nonselective.
- No Hausdorff completion claim is made.  The corpus proves continuous energy-faithful Hausdorff
  Xi landing terminal.  The only admissible successor is a source-forced singular relative
  boundary operation on the marked colligation.

## 8. Lean status

Paper proof dependency-closed.  No Lean file was written during the current read-only research
phase.  Existing Lean certifies the cubic prime kernel, positive nuclear source operator, exact
`16/35` Hilbert--Schmidt mass, rational `m_n,w_n`, separable prime--history defect, and scalar
survival telescope.  A future Stage-3 module must formalize the pair Hilbert space, Cayley
multipliers, observability isometry, dephased direct-sum trace-class operator, and atomic-to-wall
trace-norm landing.
