# Xi aperture--Poisson valuation-clock shuttle

- **ID:** `xi-aperture-poisson-valuation-clock-shuttle`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (Lean) / source-to-response coefficient bridge
- **Source:** `XiTransversePrimeSourceProjectiveTangent.lean`,
  `XiShiftPrimeHypertranscendence.lean`, `PoissonCoarseGrainingEnergy.lean`,
  `XiAperturePoissonResponseSignature.lean`, and *Finite Fusion Forces Infinite
  Hypertranscendence*
- **Scientific status:** `[LEAN-PROVED] [CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Statement:** The signed spectral shuttle of the slab Poisson response, sampled at every actual
  prime-valuation clock, is exactly the difference of two Euler-aperture derivatives of the
  normalized Xi transverse source.  It has one explicit finite-depth switch.  After fusing every
  valuation depth at a fixed prime, its exact Bose closed form is strictly negative at every prime.

## Goal

Construct a non-heuristic source-to-response arrow after the signature theorem showed that the
fine-minus-coarse Poisson response has the correct one-negative-channel cubic but is not a Hilbert
Gram.

The theorem below supplies the coefficient-level arrow and completes its valuation-depth fusion.
It does not yet prove that the completed analytic Xi source transports to the full slab quadratic
response, but it identifies the exact signed per-prime multiplier that such a transport must
realize before prime and Gamma completion.

## Actual valuation clock and continuous source primitive

For a prime `p` and valuation layer `e>=0`, put

```text
r_(p,e)=(e+1) log p>0.                                  (VS1)
```

The Brownian--Laplace theorem already identifies the normalized actual Xi transverse source at an
integer aperture `n` with

```text
B_(p,e)(n)=integral_0^n exp(-r_(p,e) t) dt
           =(1-exp(-n r_(p,e)))/r_(p,e).                (VS2)
```

Use the right side to define the canonical real-aperture continuation

```text
B_(p,e)(a)=(1-exp(-a r_(p,e)))/r_(p,e),  a in R.        (VS3)
```

Then

```text
B'_(p,e)(a)=exp(-a r_(p,e)).                            (VS4)
```

Thus the normalized half-line Poisson spectral density

```text
W_a(t)=a exp(-a t)                                     (VS5)
```

is not merely analogous to the transverse source.  At every actual valuation clock,

```text
W_a(r_(p,e))=a B'_(p,e)(a).                            (VS6)
```

It is the Euler vector field in aperture applied to the real continuation of the actual source
primitive.

## The signed scale shuttle `[PROVED HERE]`

For `0<a<b`, define

```text
Sigma_(a,b)(p,e)
 =W_b(r_(p,e))-W_a(r_(p,e))
 =b B'_(p,e)(b)-a B'_(p,e)(a).                         (VS7)
```

Let

```text
tau(a,b)=log(b/a)/(b-a)>0.                             (VS8)
```

Since

```text
W_b(t)/W_a(t)=(b/a) exp(-(b-a)t),                      (VS9)
```

the ratio is strictly decreasing and equals one exactly at `tau(a,b)`.  Therefore

```text
Sigma_(a,b)(p,e)>0  iff r_(p,e)<tau(a,b),
Sigma_(a,b)(p,e)=0  iff r_(p,e)=tau(a,b),
Sigma_(a,b)(p,e)<0  iff tau(a,b)<r_(p,e).              (VS10)
```

The positive clocks form a finite head.  Indeed `(VS10)` implies

```text
e+1 < tau(a,b)/log p                                  (VS11)
```

for every positive clock, and also

```text
p < exp(tau(a,b)/(e+1)).                              (VS12)
```

at each fixed valuation layer.  Hence only finitely many pairs `(p,e)` carry positive shuttle
weight; every cofinal prime tail and every sufficiently deep valuation tail is strictly negative.

## What this changes

The previous signature theorem left a missing indefinite source-to-response map.  Equations
`(VS2)`--`(VS7)` show that its scalar multiplier is already source-pure: it is the difference of
Euler-aperture derivatives of the normalized actual Xi source.  Equations `(VS10)`--`(VS12)` add a
new orientation law:

```text
finite low-clock head  |  one exact switch  |  infinite negative HT tail.   (VS13)
```

## Infinite valuation fusion restores uniform orientation `[PROVED HERE]`

The finite-depth switch leaves mixed signs.  At a fixed prime, however, the entire valuation tower
is geometric.  Put

```text
q_a(p)=exp(-a log p),       0<q_a(p)<1.                (VS14)
```

Then the fully fused half-density is

```text
F_a(p)=sum_(e>=0) W_a(r_(p,e))
      =a sum_(e>=0) q_a(p)^(e+1)
      =a q_a(p)/(1-q_a(p))
      =1/log(p) Phi(a log p),                          (VS15)

Phi(x)=x/(exp(x)-1).                                  (VS16)
```

For `x>0`,

```text
Phi'(x)=(exp(x)-1-x exp(x))/(exp(x)-1)^2<0.            (VS17)
```

The strict numerator sign is equivalent to `1-x<exp(-x)`.  Consequently, for every prime `p` and
every `0<a<b`,

```text
sum_(e>=0) Sigma_(a,b)(p,e)=F_b(p)-F_a(p)<0.           (VS18)
```

Thus the finite positive head never wins against the complete negative tail at any prime.  The
one-switch law is a truncation phenomenon; the infinite valuation tower has a uniform refinement
orientation.

The finite-fusion theorem says the successive valuation layers in that tail are relatively
hypertranscendental over every finite prefix.  Equation `(VS18)` supplies the analytic counterpart:
retaining the whole valuation tower changes a mixed finite-depth response into a uniform signed
per-prime current.  This is a concrete role for infinite HT fusion in the response-amplifier lane,
not merely a certificate that the source is complicated.

There is an important renormalization boundary.  `(VS18)` sums the Euler-aperture derivative
currents `W_a`, not the unweighted normalized primitives `B_(p,e)` themselves.  No interchange of
an aperture derivative with a naively summed primitive tower is asserted.  The positive survivor
is precisely that the differentiated valuation current is absolutely summable and has the Bose
closed form `(VS15)`.

## Exact remaining core

The theorem is coefficient-level.  It does not prove any of the following:

1. that the differentiated per-prime current `(VS15)` admits the required completed prime and
   Gamma assembly;
2. that this completed signed multiplier induces the spatial Lorentzian response kernel after the
   functional-equation join;
3. that the resulting analytic map is bounded on the true aperture completion; or
4. that its negative cofinal tail selects one off-line orbit rather than being masked by the full
   divisor.

The live target is now the **prime--Gamma completed Euler-current intertwining theorem** applying to
the already valuation-fused current `(VS15)` before quadratic response formation.  The signature,
sign-switch, and fusion theorems specify its required finite-depth and completed per-prime behavior
without assuming RH.

## Hostile audit

1. The derivative of an exponential and the one-switch law are standard calculus.  Candidate-new
   content is the exact identification with the actual Xi valuation-clock source and the
   hypertranscendental tail consequence.
2. A sign pattern on coefficients is not a positivity theorem for the full completed response.
3. Differential independence does not imply a norm lower bound or prevent analytic cancellation
   after an infinite non-differential completion.
4. The finite positive head cannot simply be discarded: a valid completed intertwiner must carry
   it.  `(VS18)` proves its cancellation only within each complete valuation tower, before the
   prime, Gamma, and functional-equation joins.
5. Targeted corpus search found the Brownian--Laplace primitive, the Poisson spectral density, and
   the HT fusion tower separately, but not `(VS6)`--`(VS18)` as one source-to-response theorem.
   External specialist novelty review remains open.
6. The geometric series and monotonicity of `x/(exp x-1)` are classical.  Candidate novelty is
   restricted to their exact role in the actual Xi valuation-clock/Poisson response bridge.

## Lean status

`RHTower/XiAperturePoissonValuationClockShuttle.lean` formalizes:

1. `(VS1)` and positivity;
2. the real continuous primitive and its equality with the existing integer Brownian--Laplace
   source sample;
3. `(VS4)`--`(VS7)` by `HasDerivAt`;
4. the exact switch equivalences `(VS8)`--`(VS10)`;
5. the direct threshold corollaries at every prime-valuation clock;
6. summability and the geometric closed form `(VS14)`--`(VS15)`;
7. strict antitonicity `(VS17)` of the Bose aperture factor; and
8. uniform negative complete-valuation orientation `(VS18)` at every prime.

The finiteness of the complete positive `(p,e)` head can remain a paper corollary if formalizing
the prime-counting wrapper would add only finite-set infrastructure; the pointwise threshold is the
load-bearing theorem.

The targeted leaf compilation passes.  `#print axioms` for the integer actual-source bridge, the
continuous derivative, the source Euler-derivative shuttle, all three threshold orientations, and
the prime-valuation negative-tail criterion reports only `propext`, `Classical.choice`, and
`Quot.sound`.  No umbrella or full project build was used.

## Gates

- [x] 0 -> 1: actual source coefficient, response density, and exact map identified
- [x] 1 -> 2: dependency-closed calculus and sign proof
- [x] hostile internal corpus audit: no duplicate exact bridge found
- [ ] external specialist novelty audit
- [x] 2 -> 3: Lean source bridge, sign threshold, targeted leaf check, and axiom audit
- [x] complete valuation-depth fusion and per-prime orientation
- [ ] prime--Gamma completed Euler-current intertwining theorem

## Log

- 2026-07-19 — extracted by differentiating the Brownian--Laplace aperture primitive after the
  Poisson refinement orientation pivot.  This replaces a generic “nonlinear source map” placeholder
  by the exact Euler-aperture derivative multiplier on every actual prime-valuation clock.
- 2026-07-19 — Lean exposed the stronger infinite-fusion law `(VS18)`: although finite valuation
  depths straddle the unique switch, their complete tower is the strictly decreasing Bose aperture
  factor and is therefore uniformly negative under refinement at every prime.
