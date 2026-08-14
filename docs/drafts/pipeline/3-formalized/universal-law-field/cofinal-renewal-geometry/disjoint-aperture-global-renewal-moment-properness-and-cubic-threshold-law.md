# Disjoint-aperture global renewal, entropy-moment properness, and cubic threshold law

- **ID:** ULF-CRG-2
- **Stage:** 3-formalized
- **Type:** THEOREM / GLOBAL FORMATION LAW / SHARP CLASSIFICATION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [BRIDGE]`
  `[NOVELTY UNVERIFIED] [LEAN NOT YET WRITTEN] [NOT RH]`
- **Programme:** `cofinal-renewal-geometry`
- **Parent:** `exponential-aperture-polynomial-work-renewal-action-threshold-law.md`

## 1. Why this theorem is stronger than the parent

The parent prices a sequence of scale-wise renewals by the sum of their KL costs.  A hostile
objection is that one arithmetic source intervention might replenish every scale simultaneously,
so summing unrelated local laws could overcount.

This theorem removes that objection.  It uses one baseline source law `mu`, one global renewed law
`nu`, and one KL divergence `D(nu||mu)`.  Disjoint apertures turn cofinal scale into a genuine source
observable.  Finite global information action then forces every source gauge having a finite
exponential partition function to be integrable under renewal.  Persistent work must dominate that
gauge by a summable reciprocal.  The quadratic/cubic boundary is the ordinary-exponential chart of
this coordinate-free law and is sharp by one explicit global renewal law.

## 2. Setup

Let `(Omega,F,mu)` be a probability space.  Let `(A_n)_{n>=1}` be pairwise disjoint measurable
apertures and put

```text
epsilon_n = mu(A_n).
```

Define the aperture-height observable

```text
N(x) = n,  x in A_n,
     = 0,  x outside union_n A_n.                  (GRG.1)
```

Let `nu` be one renewed probability law with `nu << mu`, and put

```text
alpha_n = nu(A_n).
```

Let `W_n>0` be work available in aperture `A_n`; admitted current is

```text
J_n = alpha_n W_n.
```

## 3. Formation partition function and entropy-moment conservation

### Theorem 3.1 — exponential aperture gives a finite formation partition function

Assume

```text
epsilon_n <= C exp(-beta n),       C>0, beta>0.    (GRG.2)
```

For every `lambda` with `0<lambda<beta`,

```text
Z_lambda := integral exp(lambda N) dmu
 <= 1 + C sum_{n>=1} exp(-(beta-lambda)n)
 < infinity.                                            (GRG.3)
```

### Proof

Outside the apertures, `exp(lambda N)=1`.  On `A_n` it equals `exp(lambda n)`.  Pairwise
disjointness gives

```text
Z_lambda
 = mu(Omega \ union A_n) + sum_n exp(lambda n) epsilon_n
 <= 1 + C sum_n exp(-(beta-lambda)n).
```

The last series is geometric with ratio in `(0,1)`.

### Theorem 3.2 — global renewal conservation inequality

If

```text
D(nu || mu) < infinity,
```

then, for every `0<lambda<beta`,

```text
lambda integral N dnu
 <= D(nu || mu) + log Z_lambda.                    (GRG.4)
```

Equivalently,

```text
sum_{n>=1} n alpha_n
 <= (D(nu || mu)+log Z_lambda)/lambda
 < infinity.                                       (GRG.5)
```

This is the global formation/properness law: finite information action controls the complete
cofinal admission moment.

### Proof

For `m>=1`, put `N_m=min(N,m)` and

```text
Z_{lambda,m}=integral exp(lambda N_m) dmu.
```

Define the exponentially tilted probability law

```text
dmu_{lambda,m}/dmu = exp(lambda N_m)/Z_{lambda,m}.
```

The Radon--Nikodym chain rule gives

```text
D(nu || mu_{lambda,m})
 = D(nu || mu) - lambda integral N_m dnu + log Z_{lambda,m}.
```

Relative entropy is nonnegative and `Z_{lambda,m}<=Z_lambda`, hence

```text
lambda integral N_m dnu <= D(nu||mu)+log Z_lambda.
```

Monotone convergence as `m->infinity` proves `(GRG.4)`.  Pairwise disjointness and `(GRG.1)` give
`integral N dnu=sum n alpha_n`, proving `(GRG.5)`.

### Corollary 3.3 — quantitative properness of global renewal sublevels

For every `M<infinity`, every renewal with `D(nu||mu)<=M` satisfies

```text
nu(N>R)
 <= (M+log Z_lambda)/(lambda R).                   (GRG.6)
```

Thus every finite-KL sublevel is uniformly tight in aperture height.  No bounded-action sequence
can export positive mass to arbitrarily high cofinal grade without paying for it.

### Proof

Markov's inequality applied to `(GRG.4)`.

### Theorem 3.4 — coordinate-free formation-gauge/work duality

Let `phi:N_{>=1}->[0,infinity)` be any gauge.  Define

```text
Phi(x)=phi(n),  x in A_n,
      =0,       outside union_n A_n.
```

Assume that, for some `lambda>0`,

```text
Z_phi(lambda)
 := integral exp(lambda Phi)dmu
 = mu(outside) + sum_n exp(lambda phi(n)) epsilon_n
 < infinity.                                           (GRG.7)
```

Then every `nu<<mu` with finite relative entropy satisfies

```text
sum_n phi(n) alpha_n
 = integral Phi dnu
 <= [D(nu||mu)+log Z_phi(lambda)]/lambda
 < infinity.                                           (GRG.8)
```

Consequently, if positive work `W_n` sustains persistent current

```text
alpha_n W_n >= c>0,
```

then the following summability condition is necessary:

```text
sum_n phi(n)/W_n < infinity.                           (GRG.9)
```

This is the invariant law.  A source gauge and an observer-work scale are admissible together only
when their quotient is summable.

### Proof

Repeat the truncated exponential-tilt proof of Theorem 3.2 with `Phi` in place of `N`.  Persistent
current gives `alpha_n phi(n)>=c phi(n)/W_n`; summing and applying `(GRG.8)` proves `(GRG.9)`.

## 4. Sharp global cubic threshold

### Theorem 4.1 — finite global action excludes persistent degree at most two

Fix `K,c>0` and an integer `d>=0`.  Assume

```text
W_n <= K n^d,
alpha_n W_n >= c                  for every n.      (GRG.10)
```

If `D(nu||mu)<infinity`, then necessarily

```text
d > 2.                                                (GRG.11)
```

In particular, no finite-information global source renewal can sustain a uniformly positive
current through exponentially evacuated disjoint apertures when available work is constant,
linear, or quadratic.

### Proof

From `(GRG.10)`,

```text
alpha_n >= c/(K n^d),
n alpha_n >= (c/K)n^(1-d).
```

Equation `(GRG.5)` forces `sum n alpha_n<infinity`.  The p-series
`sum n^(1-d)` diverges exactly for `d<=2`.  Hence `d>2`.

### Corollary 4.2 — every finite-action linear current is summable

If `W_n<=Kn`, then

```text
sum_n J_n
 = sum_n alpha_n W_n
 <= K integral N dnu
 <= (K/lambda)(D(nu||mu)+log Z_lambda).             (GRG.12)
```

So finite global KL does more than forbid uniform linear current: it forces total admitted linear
information current to be finite.

### Theorem 4.3 — one global renewal proves sharpness for every `d>2`

Fix `beta,K>0`, integer `d>2`, and `c>0` satisfying

```text
(c/K) sum_{n>=1} n^(-d) < 1.                       (GRG.13)
```

There exist one countable source law `mu`, one global renewal `nu`, disjoint singleton apertures,
and work `W_n=K n^d` such that

```text
mu(A_n) <= C exp(-beta n),
nu(A_n) W_n = c                  for every n,
D(nu||mu) < infinity.                              (GRG.14)
```

Thus degree three is the first integer degree not excluded by finite global information action.

### Proof

Let

```text
Omega = {star} disjoint_union Nat_{>=1},
A_n = {n},
q = exp(-beta).
```

Define

```text
mu(star)=1/2,
mu(n)=(1/2)(1-q)q^(n-1),

nu(n)=c/(K n^d),
nu(star)=1-(c/K)sum_n n^(-d).
```

Condition `(GRG.13)` makes `nu` a probability with positive `star` mass.  Every atom of `mu` is
positive, so `nu<<mu`.  Also

```text
mu(n)=[(1/2)(1-q)exp(beta)] exp(-beta n).
```

The current identity in `(GRG.14)` is immediate.  The `star` contribution to KL is finite.  On
the aperture atoms,

```text
nu(n) log(nu(n)/mu(n))
 = (c/(K n^d)) [beta n - d log n + constant].      (GRG.15)
```

Its absolute value is bounded by a constant multiple of

```text
n^(1-d) + (log n)n^(-d) + n^(-d),
```

whose series converges for `d>2`.  Hence `D(nu||mu)<infinity`.

### Theorem 4.4 — stretched-exponential phase diagram

Fix `gamma>0`.  Replace ordinary exponential evacuation by

```text
epsilon_n <= C exp(-beta n^gamma).                  (GRG.16)
```

If one finite-KL global renewal sustains current `alpha_n W_n>=c>0` with

```text
W_n <= K n^d,
```

then necessarily

```text
d > gamma+1.                                         (GRG.17)
```

This threshold is sharp across the class: whenever `d>gamma+1` and
`(c/K)sum n^(-d)<1`, there is a countable one-law example with

```text
mu(A_n)=B exp(-beta n^gamma),
nu(A_n)=c/(K n^d),
nu(A_n)W_n=c,
D(nu||mu)<infinity.                                  (GRG.18)
```

Thus the universal critical surface is

```text
work degree = evacuation degree + 1.                 (GRG.19)
```

Ordinary exponential evacuation has `gamma=1`, so the critical work degree is two and cubic is the
first integer finite-action regime.  Gaussian evacuation has `gamma=2`, so quartic is the first
integer regime not excluded.

### Proof

Use Theorem 3.4 with `phi(n)=n^gamma`.  For every `0<lambda<beta`,

```text
sum_n exp(lambda n^gamma)epsilon_n
 <= C sum_n exp(-(beta-lambda)n^gamma)<infinity;
```

the last series converges by comparison with its tail integral (or because stretched exponential
decay dominates `n^-2`).  Hence finite KL gives `sum n^gamma alpha_n<infinity`.  Persistent current
and the work bound imply

```text
n^gamma alpha_n >= (c/K)n^(gamma-d).
```

The last p-series converges only when `gamma-d<-1`, proving `(GRG.17)`.

For sharpness, let `S=sum exp(-beta n^gamma)<infinity`, take `mu(star)=1/2` and

```text
mu(n)=[1/(2S)]exp(-beta n^gamma),
nu(n)=c/(K n^d).
```

Use the remaining mass at `star`.  Aperture contributions to KL have size at most a constant times

```text
n^(gamma-d) + (log n)n^(-d) + n^(-d),
```

which is summable exactly under `d>gamma+1`.  This proves `(GRG.18)`.

## 5. Functional-equation and common-recovery neutrality

The new properness law is compatible with the already-proved packet action rather than replacing
it.

### Theorem 5.1 — functional-equation invariance of global renewal action

Let `R:Omega->Omega` be a measurable involution satisfying

```text
R_*mu=mu,
N(Rx)=N(x).                                           (GRG.20)
```

Then

```text
D(R_*nu || mu)=D(nu||mu),
integral N d(R_*nu)=integral N dnu.                  (GRG.21)
```

Therefore functional-equation reversal is information-neutral and height-neutral, but it cannot
evade the cubic threshold.

### Proof

Measurable bijections preserve relative entropy, and `R_*mu=mu`.  Change variables in the second
integral and use `N o R=N`.

### Corollary 5.2 — lift through a common recovery kernel

Let `K` be any parameter-independent Markov recovery kernel and form

```text
E_K(mu)=mu tensor K,
E_K(nu)=nu tensor K.
```

Then

```text
D(E_K(nu)||E_K(mu))=D(nu||mu).                       (GRG.22)
```

If aperture height is read from the recovered observer coordinate, its expectation is unchanged.
Consequently Theorems 3.2 and 4.1 lift verbatim through packet formation.  Common recovery is
information-neutral; it cannot manufacture the missing renewal budget.

### Proof

Use the common-recovery KL isometry and exact observer recovery already proved in
`ConstitutiveFunctionalEquationPacketLift`.

### Corollary 5.3 — arbitrary packet interventions do not create a loophole

The companion theorem
`horizontal-vertical-packet-renewal-budget-and-cofinal-properness-law.md` removes the split-law
hypothesis.  For every arbitrary joint renewal `Q` relative to `mu tensor K`, observer projection
gives

```text
D(pi_*Q||mu) <= D(Q||mu tensor K).
```

Hence finite total packet action still forces the same cofinal moment and work threshold.  Under
standard-Borel disintegration, the difference is exactly the nonnegative conditional KL from the
renewed history kernel to `K`.  Vertical history consumes action; it cannot replenish horizontal
aperture mass.

## 6. Literal source-horizontal formation is closed

The companion theorem
`source-horizontal-disjoint-class-law-global-renewal-properness-and-current-evacuation.md`
proves that the canonical source-horizontal apertures already form one pairwise-disjoint tower in
each fixed abelian class law.  The proof uses the exact order and socle invariants of

```text
A_N=(Z/pZ)^(N+1),       B_N=Z/p^(2N)Z.
```

It obtains the sharp available exponential rates `(2-a)log p` in the forward law and `2log p` in
the reverse law.  Therefore every single global renewal of finite KL has finite first aperture
moment.  Since adaptive Jeffreys work is linear in grade, Corollary 4.2 forces its total admitted
current to be summable.  A nonsummable or uniformly positive source-horizontal current is
impossible under every finite-action absolutely continuous renewal.

The remaining arithmetic gate is no longer formation of the tower.  It is construction of one
source-native renewal and proof that the same renewed current lands naturally in at least two
other organs.

## 7. Five-organ fusion

This theorem supplies one law across five distinct organs:

| organ | realization |
|---|---|
| source formation | one law `mu`, one renewal `nu` |
| admission | disjoint apertures `A_n` and masses `alpha_n` |
| topology/properness | height observable `N`, tight KL sublevels |
| functional equation | involution preserving `mu` and `N` |
| recovery/packet history | common kernel preserving KL and observer height |

The exact fusion identity is the tilted-law conservation equation behind `(GRG.4)`.  Its fourth-
organ prediction is no longer merely local: finite global source action imposes an exact cubic
entrance wall on every persistent cofinal current.

## 8. Hostile loops

1. **Summing scale-wise KL overcounts one source intervention.** Valid objection to the parent as a
   universal source model.  Survivor: one global law and one KL already imply the cubic wall.
2. **Probability normalization alone gives the cubic wall.** False.  It only forces
   `sum alpha_n<=1`, which excludes `d<=1`.  Finite relative entropy supplies the extra first
   moment and raises the wall to `d<=2`.
3. **Finite KL controls every polynomial aperture moment from ordinary exponential evacuation.**
   False.  It controls exactly those gauges with a finite exponential partition function.  For
   `exp(-beta n)` this includes sublinear and linear gauges but not `n^gamma`, `gamma>1`.
4. **Functional-equation information neutrality cancels renewal cost.** False.  It preserves both
   KL action and height moment.
5. **Common recovery replenishes evacuated mass.** False.  It is an information isometry and
   retains the same observer marginal.
6. **Cubic work guarantees finite-action renewal.** False for an arbitrary source.  Theorem 4.3 is
   sharp existentially.  A superexponential baseline or extra source constraints can still exclude
   cubic renewal.
7. **Evacuation shape is irrelevant.** False.  The exact critical surface is `d=gamma+1` for
   stretched-exponential degree `gamma`.
8. **The source-horizontal tower requires an artificial product source.** False.  The literal
   abelian class space already contains a pairwise-disjoint tower under one fixed law per
   orientation; the companion theorem closes this gate.

## 9. Literature boundary

The entropy inequality

```text
E_nu f <= D(nu||mu)+log E_mu exp(f)
```

is classical Gibbs/Donsker--Varadhan variational mathematics.  Exponential tilting, I-projection,
Schroedinger bridges, and entropy-tightness arguments are established fields.  No novelty is
claimed for Theorems 3.1--3.2 in isolation.

Broad current searches found no exact theorem packaging one exponentially evacuated disjoint
aperture tower, persistent polynomial work, functional-equation invariance, common-kernel recovery,
and the sharp global integer wall `d=2`.  The cross-organ theorem is new to the corpus; external
priority remains unverified.

## 10. Lean status

No Lean was written or built.  The corpus was audited read-only.  Reusable formal parents include
common-kernel KL isometry, measurable-embedding KL invariance, Bernoulli KL formulas, geometric
summability, p-series thresholds, and source-horizontal linear-work bounds.  Formalization remains
a future Stage-2-to-Stage-3 pass.

## Log

- 2026-08-12 — hostile overcount objection to scale-wise action accepted.
- 2026-08-12 — replaced independent renewals by one global law and derived entropy-height
  properness.
- 2026-08-12 — proved sharp global cubic threshold and compatibility with functional equation and
  common recovery.
- 2026-08-13 — literal source-horizontal class invariants were re-audited; they close the previously
  stated disjoint-formation gate and yield unconditional finite-KL global current evacuation.
- 2026-08-14 — Lean formalization completed: global entropy-moment properness, sharp ordinary and stretched work thresholds, involution neutrality, arbitrary-packet closure, and literal source-horizontal corollaries are kernel-checked and umbrella-owned.
