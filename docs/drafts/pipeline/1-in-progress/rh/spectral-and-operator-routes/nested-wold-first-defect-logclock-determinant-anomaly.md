# Nested Wold first-defect log-clock determinant anomaly

- **ID:** `nested-wold-first-defect-logclock-determinant-anomaly`
- **Stage:** 1 — in progress
- **Type:** SOURCE-COFINAL PROBABILITY/DETERMINANT THEOREM /
  SINGULAR-RECEIVER INPUT
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [NOT RH]`
  `[CORPUS-NEW LOG-CLOCK INTERPRETATION]`
  `[EXTERNAL NOVELTY PROVISIONAL]`
- **RH used:** no
- **Computation used:** no
- **Parents:**
  - `../2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`;
  - `prime-wold-determinant-connection-purity-law.md`;
  - `global-wold-volume-gamma-bimoderate-completion.md`;
  - `source-effective-polar-kummer-conormal-purity.md`;
  - `../../../3-formalized/new_scientific_knowledge/prime-first-trace-exponential-flat-graph-fracture.md`;
  - `../4-publication-ready/arithmetic-julia-normal-cone/main.tex`.

## Frontier statement

The telescoping singular increments of the nested Wold sieve are a
canonical probability law.  Under increasing prime order, its atom at
`p_k` is the probability that `p_k` is the first prime at which the
valuation vacuum fails.  The literal prime logarithm has infinite first
moment under this law.

The same atom multiplied by `log(p_k)` is exactly the multiplicative
anomaly in the finite-part-renormalized Wold determinant when the sieve
crosses `p_k`.  Thus the singular prime logarithmic clock, Wold vacuum
volume, and determinant first-trace correction are one source object.

Its bilateral exponential moment domain is the singleton `c=0`.
This supplies a source-native critical-line receiver, but not the
missing theorem that every Xi conormal lands in it.

## 1. First-defect probability law

Let

```text
2=p_1<p_2<...                                             (1)
```

be the increasing rational primes.  Put

```text
P_k={p_1,...,p_k},
a_0=1,
a_k=product_(j<=k)(1-p_j^(-1)),
w_k=a_(k-1)/p_k=a_(k-1)-a_k.                            (2)
```

The established nested-sieve law identifies `a_k` as:

```text
finite-prime Wold vacuum volume;
BV principal-conormal coefficient;
mass of the event v_(p_j)=0 for every j<=k.              (3)
```

Since the prime harmonic series diverges, `a_k -> 0`.
Equation `(2)` telescopes:

```text
w_k>0,
sum_(k>=1) w_k=1.                                       (4)
```

Hence

```text
Pr(P_first=p_k)=w_k                                     (5)
```

defines a probability distribution.  In the prime-valuation product
law, `(5)` is literal: the first nonzero valuation in increasing prime
order occurs at `p_k` exactly when all earlier valuations vanish and
the `p_k`-valuation is nonzero.  These independent probabilities are

```text
Pr(v_(p_j)=0 for j<k)=a_(k-1),
Pr(v_(p_k)>0)=1/p_k.                                    (6)
```

Their product is `w_k`.

## 2. Infinite logarithmic clock

Mertens' product theorem gives

```text
a_(k-1) ~ exp(-gamma)/log(p_k).                         (7)
```

Therefore

```text
w_k*log(p_k)
 =a_(k-1)*log(p_k)/p_k
 ~exp(-gamma)/p_k.                                      (8)
```

Euler's divergence of the prime harmonic series proves

```text
E[log(P_first)]
 =sum_(k>=1)w_k*log(p_k)
 =infinity.                                             (9)
```

Thus the logarithmic prime clock is a well-defined finite random
variable almost surely but is not integrable.  Every finite prime packet
has a finite clock; the obstruction appears only after cofinal
completion.

This supplies a precise probabilistic meaning for the singular
logarithmic normal coordinate in the arithmetic Julia completion:

```text
finite Wold vacuum filtration
  -> probability-one first-defect boundary
  -> nonintegrable prime logarithmic clock.              (10)
```

No Xi zero or divisor is used.

## 3. Exact bilateral moment screen

For real `c`, define

```text
M(c)=sum_(k>=1) w_k*p_k^c.                              (11)
```

Then

```text
M(c)<infinity  iff  c<=0.                               (12)
```

For `c=0`, equation `(4)` gives `M(0)=1`.  For `c<0`,

```text
w_k*p_k^c <= p_k^(c-1),
```

and the right side is summable even over all positive integers.

For `c>0`, equations `(7)`--`(8)` and prime-number-theorem partial
summation give

```text
sum_(p<=x) p^(c-1)/log(p)
 ~x^c/(c*log(x)^2),
```

so `M(c)=infinity`.

Consequently

```text
M(c)<infinity and M(-c)<infinity
  iff c=0.                                               (13)
```

For a centered divisor character

```text
chi_rho(p)=p^(rho-1/2),
c=Re(rho)-1/2,                                          (14)
```

the character and its reflection are both in
`L1({p_k},w)` exactly when `Re(rho)=1/2`.

Equation `(13)` is a target-side selector, not RH.  The RH-bearing
source theorem would have to map every distinguished Xi conormal jet
into this bilateral moment receiver before specializing at a zero.

## 4. Finite-part determinant character

Let

```text
Q_(P_k)=E_(P_k) Q,
T_k(N)=sum_(n<=N,(n,product P_k)=1) 1/n.                (15)
```

The established trace theorem is

```text
T_k(N)=a_k*log(N)+kappa_k+o(1),                         (16)

kappa_k
 =a_k*[
   gamma+sum_(j<=k) log(p_j)/(p_j-1)
 ].                                                      (17)
```

Equations `(2)` and `(17)` give the exact renewal

```text
kappa_k
 =(1-p_k^(-1))*kappa_(k-1)
  +w_k*log(p_k).                                        (18)
```

Thus the same nonintegrable logarithmic atom from `(9)` is the new
finite-part trace supplied when `p_k` enters the nested sieve.

For `|r|<1`, define the finite ordinary determinant ratio

```text
Delta_(k,N)(r)
 =product_(n<=N,(n,product P_k)=1)
   (1-r/n)/(1+r/n).                                     (19)
```

The relation between `det` and `det_2` and equation `(16)` prove the
locally uniform limit

```text
DeltaHat_k(r)
 :=lim_(N->infinity) N^(2*a_k*r)*Delta_(k,N)(r)
 =exp(-2*r*kappa_k)*Phi_(P_k)(r),                       (20)
```

where

```text
Phi_P(r)=det_2(I-r*Q_P)/det_2(I+r*Q_P).                 (21)
```

The nested Wold determinant law and `(18)` now give

```text
DeltaHat_k(r)
 =DeltaHat_(k-1)(r)/DeltaHat_(k-1)(r/p_k)
  *exp(-2*r*w_k*log(p_k)).                              (22)
```

Therefore:

> **Theorem — first-defect determinant anomaly law.**
> The logarithmic anomaly in the finite-part-renormalized Wold
> determinant at the `k`-th prime is exactly
>
> ```text
> -2*r*log(p_k)*Pr(P_first=p_k).                        (23)
> ```

The probability law, prime logarithmic clock, trace finite part, and
determinant multiplicative anomaly are four exact readings of one
nested source increment.

## 5. Meaning for the universal law

The determinant hierarchy now has a source-canonical probabilistic
model:

```text
vacuum survival a_k:
  singular conormal scale;

hazard w_k:
  first Wold boundary event;

clock log(p_k):
  nonintegrable normal coordinate;

hazard times clock:
  determinant finite-part anomaly;

bilateral exponential moments:
  unitary/critical purity screen.                        (24)
```

This explains why a regular scalar completion cannot solve the source
problem.  It integrates the bounded vacuum events and the `det_2`
holonomy but drops the nonintegrable logarithmic observable carried by
their first-defect boundary.

It also explains why normalization is dangerous.  The unnormalized
hazards sum to one, while conditioning the surviving conormal back to
unit mass amplifies consecutive changes from `a_(k-1)/p_k` to `1/p_k`,
which is not summable.  Any successful third completion must retain the
hazard and logarithmic anomaly without demanding total-variation
convergence of conditioned states.

### Exact exponential-grade weld

The formalized actual-prime first-trace graph fracture independently
isolates the scales

```text
source size  asymptotic-to 1/log(p),
response error asymptotic-to 1/p,
source size*(-log response) ->1.                        (24a)
```

The nested Wold survival has exactly the same normalized rate class.
Put

```text
A_k=exp(gamma)*a_(k-1),
B_k=1/p_k.                                               (24b)
```

Mertens' theorem gives

```text
A_k*log(p_k) ->1,
log(B_k)/log(p_k)=-1,
A_k*(-log B_k) ->1,                                     (24c)

B_k/A_k^N ->0
for every fixed N.                                      (24d)
```

The first-defect atom factors as

```text
w_k=exp(-gamma)*A_k*B_k.                                (24e)
```

Thus the Wold first-defect boundary and the Lean-certified Hardy
first-trace graph fracture have the same universal exponential
rate-distortion grade.  The former supplies the global probability and
determinant interpretation missing from the latter; the latter proves
that no finite-order graph/jet completion can retain this grade.

The required global exponential associated graded is therefore no
longer an unspecified topology.  It must resolve polynomial growth in
the clock `x=log p` from exponential growth `exp(c*x)`.  The next
section constructs exactly that target-side rigging.

## 6. Multiplicity-capable first-defect Schwartz rigging

Put

```text
x_k=log(p_k),                                            (25a)

S_fd={
  f:N_(>0)->C :
  q_m(f):=sup_k (1+x_k)^m*|f_k| < infinity
  for every m>=0
}.                                                       (25b)
```

With the seminorms `q_m`, `S_fd` is a Hausdorff Frechet sequence space.
Finite-support sequences are dense in

```text
H_fd=ell2(N_(>0),w),                                     (25c)
```

and

```text
S_fd subset H_fd subset S_fd'                           (25d)
```

is a rigging.  The first embedding is continuous because

```text
||f||_(H_fd)^2 <=q_0(f)^2*sum_k w_k=q_0(f)^2.
```

The second is the Hilbert pairing.

For a coefficient sequence `b=(b_k)`, the coordinate functional

```text
L_b(f)=sum_k w_k*b_k*f_k                                (25e)
```

is continuous on `S_fd` exactly when there is `m>=0` such that

```text
sum_k w_k*|b_k|*(1+x_k)^(-m)<infinity.                  (25f)
```

Sufficiency follows from the bound by `q_m(f)`.  Conversely, continuity
gives a bound by one seminorm `q_m`; applying it to finite-support
sequences with phases chosen to align every summand proves uniform
boundedness of the partial sums in `(25f)`.

For `j` a nonnegative integer and `c,t` real, put

```text
b_(c,t,j)(k)=x_k^j*exp((c+i*t)*x_k).                    (25g)
```

Then

```text
L_(b_(c,t,j)) is continuous on S_fd
  iff c<=0.                                              (25h)
```

If `c<=0`, choose `m>=j`; equation `(25f)` follows from
`sum_k w_k=1`.

If `c>0`, Mertens and prime-number-theorem partial summation give, for
every fixed `m`,

```text
sum_(p_k<=X)
 w_k*exp(c*x_k)*x_k^j*(1+x_k)^(-m)
 asymptotic-to
 exp(-gamma)*X^c*(log X)^(j-m-2)/c,
```

which diverges.  Thus `(25f)` fails for every `m`.

Therefore:

> **Theorem — multiplicity-capable first-defect temperedness.**
> Every unitary prime character and every finite logarithmic
> multiplicity jet
>
> ```text
> x_k^j*exp(i*t*x_k)
> ```
>
> is a continuous distribution in `S_fd'`.  A coherent radial
> character with exponent `c` is continuous exactly on the
> nonexpanding face `c<=0`.  Both reflected characters `c` and `-c`,
> with all finite polynomial jets, are continuous simultaneously
> exactly when `c=0`.

This closes the target-side multiplicity receiver problem left open by
`L1(w)`.  Critical semisimple characters are actual unit vectors in
`H_fd`; their nontrivial multiplicity jets live in the distributional
dual.

### Remaining source comparison

The source-determinant purity conjecture is now sharpened to one
pre-divisor map

```text
principal Xi conormal
  -> S_fd'                                               (25i)
```

whose semisimple specialization at `rho` is `(14)`, whose top
multiplicity coordinate is `(25g)`, and whose source reflection makes
both conormal faces continuous.

No such comparison is proved.  Defining `(25i)` fibrewise is
RH-equivalent and rejected.  Its value is that the receiver, measure,
clock, multiplicity topology, and reflection screen are now all
source-derived rather than chosen from the target divisor.

## 7. Hostile audit

1. **This is not RH.**  Equation `(13)` is only a character
   classification.  Xi conormal landing remains open.
2. **Increasing prime order is load-bearing.**  It is source-canonical
   through the absolute prime norm, but `(5)` is not claimed invariant
   under arbitrary prime permutations.
3. **`S_fd'` is not yet the full third completion.**  It retains all
   semisimple prime-generator characters and multiplicity jets, but it
   does not by itself construct the rational-dilation orbit map, BV
   window presentation independence, or relative Wold ideal.
4. **Weak/TV no-go remains.**  The theorem does not make the normalized
   valuation states strongly Cauchy.
5. **Multiplicity landing remains source-bearing.**  The dual can carry
   every polynomial jet, but no theorem yet says the distinguished Xi
   top jet maps to the named functional without radical loss.
6. **Generalized-prime falsifier.**  An off-line generalized-prime
   system carrying the same increasing ordinary-prime Wold survival
   law, determinant anomaly `(22)`, completed BV/co-Poisson comparison,
   and bilateral conormal landing would falsify the mechanism.
7. **No direct-product repair.**  The law uses nested sieve increments.
   Independent one-prime determinant factors still diverge.

## 8. Literature boundary

Mertens' product theorem, the prime harmonic series, prime-number-theorem
partial summation, survival/hazard probabilities, and determinant
renormalization are parent mathematics.

The least-prime-factor decomposition and the Mertens product attached to
it are classical sieve objects.  In particular, the literature on the
Erdos primitive-set conjecture explicitly partitions integers by least
prime factor and uses

```text
product_(q<p)(1-1/q)
```

as its Mertens-scale density; see the 2023 proof in *Forum of
Mathematics, Pi*:
`https://doi.org/10.1017/fmp.2023.16`.  Lichtman's
`Mertens' prime product formula, dissected`,
`https://arxiv.org/abs/2002.03361`,
analyzes related decompositions of the same prime product.  No novelty
is claimed for the hazard law `(2)`--`(6)` in isolation.

Regularized Gamma determinants, least-prime-factor distributions, and
finite-part trace renormalizations also occur separately in the
literature.  Targeted searches did not locate the transition `(22)` or
an identification of its anomaly with the least-prime-factor hazard,
the Wold/BV conormal decrement, and the bilateral RH-facing moment
screen.  This is a provisional noncollision report, not a priority
certificate.

The parent Wold-sieve card already proves `(2)`, `(4)`, and
`(16)`--`(17)` separately.  The candidate-new content is their exact
joining:

```text
first-defect probability
  = nested conormal decrement
  = coefficient of a nonintegrable prime log clock
  = finite-part determinant multiplicative anomaly,     (26)
```

together with the bilateral moment screen `(13)`.  No external novelty
claim is made before targeted primary-source audit.

## Gates

- [x] first-defect probability law proved
- [x] infinite logarithmic moment proved
- [x] bilateral exponential moment domain proved
- [x] trace finite-part renewal proved
- [x] renormalized determinant transition proved
- [x] normalization and generalized-prime falsifiers recorded
- [x] preliminary primary-literature audit
- [x] multiplicity-capable first-defect Schwartz rigging constructed
- [x] exact reflected temperedness classification proved
- [ ] independent proof audit
- [ ] independent targeted literature audit
- [ ] construct source-first Xi conormal comparison
- [ ] prove source-Hodge/bilateral purity
- [ ] unconditional RH proof
- [ ] Lean formalization after significance and dependency closure

## Log

- 2026-07-29 — Reinterpreted the telescoping nested-sieve increments as
  the first nonzero prime-valuation law.  Proved its prime logarithm has
  infinite mean and its reflected exponential moment domains intersect
  only at the critical radial exponent.
- 2026-07-29 — Reintroduced the finite part removed by `det_2` and
  proved that its prime-enlargement multiplicative anomaly is exactly
  the first-defect probability times the literal prime logarithmic
  clock.
