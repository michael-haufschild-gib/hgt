# Hasse geometric-history global renewal properness and cubic work wall

- **ID:** ULF-CRG-5
- **Stage:** 3-formalized
- **Type:** THEOREM / FOURTH-ORGAN PREDICTION VERIFIED / SHARP CLASSIFICATION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [LITERAL HASSE KERNEL]`
  `[LEAN NOT YET WRITTEN] [NOT RH]`
- **Programme:** `cofinal-renewal-geometry`
- **Parents:**
  - `horizontal-vertical-packet-renewal-budget-and-cofinal-properness-law.md`
  - `../packet-formation-mechanics/hasse-packet-reconstruction-information-properness-and-atomic-refinement-wall.md`

## 1. Prediction and outcome

The horizontal--vertical budget law predicts that a certified latent-history kernel with an
exponential depth partition function cannot carry persistent low-degree history current under a
finite-information global intervention.

The literal Hasse recovery kernel verifies the prediction exactly.  This is structurally different
from the abelian class-law source tower: the apertures are latent generation levels of one Markov
recovery packet, not finite-group isomorphism classes.

## 2. Literal formed packet

Let `mu` be any probability law on `R`.  For `x in R`, put

```text
t(x)=exp(x),
r(x)=[1-exp(-t(x))]/2.                                 (HGH.1)
```

Then

```text
0<r(x)<1/2.                                            (HGH.2)
```

The Hasse recovery kernel on `N` is

```text
K_H(x,n)=[1-r(x)]r(x)^n.                              (HGH.3)
```

It is a probability law for every `x`.  Form the joint packet

```text
P(dx,n)=mu(dx)K_H(x,n).                                (HGH.4)
```

Let

```text
B_n=R x {n}                                            (HGH.5)
```

be the history-depth apertures.  They are a pairwise-disjoint measurable partition of the packet
space.

## 3. Uniform history partition function

### Theorem 3.1 — every Hasse packet has a common exponential history moment

For every real `lambda` with

```text
0<lambda<log 2,
```

the history partition function is finite and satisfies

```text
Z_H(lambda)
 := integral exp(lambda n)dP(x,n)
 = integral [(1-r(x))/(1-exp(lambda)r(x))]dmu(x)
 <= 1/[1-exp(lambda)/2]
 < infinity.                                          (HGH.6)
```

### Proof

For fixed `x`, `(HGH.3)` and `exp(lambda)r(x)<exp(lambda)/2<1` give the geometric sum

```text
sum_(n>=0) exp(lambda n)[1-r(x)]r(x)^n
 = [1-r(x)]/[1-exp(lambda)r(x)].
```

The numerator is at most one and the denominator is at least `1-exp(lambda)/2`.  Integrate the
uniform bound against the probability law `mu`.

## 4. Arbitrary packet renewal

Let `Q` be **any** probability law on `R x N` satisfying

```text
Q << P,       D(Q||P)<infinity.                        (HGH.7)
```

Write

```text
alpha_n=Q(B_n).toReal.                                 (HGH.8)
```

No split form, common conditional kernel, independence, or observer/history factorization is
assumed for `Q`.

### Theorem 4.1 — finite packet action forces finite mean history depth

For every `0<lambda<log 2`,

```text
sum_(n>=0) n alpha_n
 <= [D(Q||P)+log Z_H(lambda)]/lambda
 < infinity.                                          (HGH.9)
```

### Proof

Apply the entropy--exponential-moment inequality directly on `R x N` with the observable
`(x,n)|->n` and use `(HGH.6)`.  Pairwise disjointness of `(B_n)` identifies the expectation with
the series in `(HGH.9)`.

### Corollary 4.2 — total linear history current is finite

If `0<=W_n<=Kn`, then

```text
sum_n alpha_n W_n
 <= (K/lambda)[D(Q||P)+log Z_H(lambda)]<infinity.      (HGH.10)
```

Thus every nonnegative linear history current tends to zero along depth.

## 5. Sharp work threshold

### Theorem 5.1 — persistent polynomial history current requires degree greater than two

Suppose `K,c>0`, integer `d>=0`, and

```text
W_n<=K n^d,
alpha_n W_n>=c>0             for every n>=1.           (HGH.11)
```

Then `(HGH.7)` implies

```text
d>2.                                                   (HGH.12)
```

### Proof

Equation `(HGH.11)` gives

```text
n alpha_n >= (c/K)n^(1-d).
```

The left side is summable by `(HGH.9)`.  The right-side p-series is summable only for `d>2`.

### Theorem 5.2 — cubic is class-sharp inside the Hasse species

For every integer `d>2`, choose any `x_0 in R` and put

```text
mu=delta_(x_0),       r_0=r(x_0),
P(n)=(1-r_0)r_0^n.                                    (HGH.13)
```

For sufficiently small `c/K>0`, define

```text
Q(n)=c/(K n^d),       n>=1,
Q(0)=1-(c/K)sum_(n>=1)n^(-d),
W_n=K n^d.                                             (HGH.14)
```

Then

```text
Q(n)W_n=c,
D(Q||P)<infinity.                                      (HGH.15)
```

### Proof

All geometric masses in `(HGH.13)` are positive, so `Q<<P`.  The zero-depth contribution to KL is
finite.  For `n>=1`,

```text
Q(n)log[Q(n)/P(n)]
 = [c/(Kn^d)]
   [-d log n-n log r_0+constant].                     (HGH.16)
```

Its absolute value is bounded by a constant multiple of

```text
n^(1-d)+(log n)n^(-d)+n^(-d),
```

which is summable for `d>2`.  This proves `(HGH.15)`.

## 6. Functional-equation compatibility

For an even observer law `mu` and reflection `R(x)=-x`, the canonical stochastic packet action
applies `R` and then regenerates history from the same kernel at the reflected observer.  Formation
naturality makes `(HGH.4)` invariant when `R_*mu=mu`; its action is involutive on formed laws and
KL-isometric.

The history-depth observable is not pointwise preserved by regeneration, but its **law and
partition function** are preserved because the whole formed packet is invariant.  Therefore the
functional-equation action cannot change the finite-action wall `(HGH.12)`.

This is information neutrality, not closed lifted history: an individual old generation label is
discarded and resampled.

## 7. What the fourth-organ test establishes

The same formation/properness law now has two literal, nonisomorphic realizations:

| realization | source space | apertures | native tail |
|---|---|---|---|
| abelian class law | finite-group classes | `{A_N,B_N}` | arithmetic prime-power exponential |
| Hasse packet | observer--generation pairs | `R x {n}` | Markov geometric recovery |

Both independently produce the quadratic wall/cubic entrance.  The shared mechanism is not a
renaming of either route object:

```text
finite exponential formation partition
 + finite global KL action
 => finite first occupation moment
 => no persistent work of degree <=2.                 (HGH.17)
```

The theorem predicts the same wall for every other recovery/history organ whose certified kernel
has a uniform exponential depth moment.  The burden is now a source-derived formation map, not a
new inequality.

## 8. Hostile loops

1. **The Hasse result is inherited from the abelian aperture.** False; the source spaces and
   apertures are different and no comparison map is used.
2. **Only split packet renewals are controlled.** False; `Q` is arbitrary.
3. **Observer-dependent recovery destroys the uniform partition function.** False because
   `r(x)<1/2` uniformly.
4. **Finite mean alone gives the cubic wall.** The implication from finite mean is elementary, but
   finite mean of every finite-KL packet renewal is the formation/properness content.
5. **Cubic work always survives.** False.  Theorem 5.2 proves class-sharp existence, not survival
   for every observer law or source constraint.
6. **Functional-equation invariance preserves individual history lifts.** False; it preserves the
   formed law after stochastic regeneration.
7. **This proves a physical recurrence theorem.** False.  `n` is certified Hasse generation depth,
   not elapsed physical time, Krylov complexity, or wormhole length.

## 9. Literature boundary

Geometric distributions, entropy moment bounds, and KL-constrained reweighting are classical.
Common Markov recovery and relative-entropy chain rules are likewise established.  The theorem is
not presented as a new probability inequality.

New-to-corpus content is the theorem predicted from the universal packet-budget law: the literal
Hasse recovery kernel supplies a second independent arithmetic formation chart with exactly the
same sharp work threshold.  No external priority claim is made.

## 10. Lean boundary

No Lean was written or built.  Existing formal parents certify `K_H` as a Markov kernel and its
recovery/information isometry.  Future formalization needs the geometric-series exponential moment,
the entropy--moment inequality, and the p-series threshold.  It should reuse the generic global
properness module rather than duplicate the abelian proof.

## Log

- 2026-08-13 — horizontal--vertical packet law predicted an independent latent-history work wall.
- 2026-08-13 — verified prediction for the literal Hasse geometric recovery kernel and proved
  class-sharp cubic entrance.
- 2026-08-14 — Lean formalization completed: literal Hasse kernel, arbitrary-renewal entropy moment, total-current bound, quadratic wall, sharp cubic witness, and functional-equation neutrality are kernel-checked and umbrella-owned.
