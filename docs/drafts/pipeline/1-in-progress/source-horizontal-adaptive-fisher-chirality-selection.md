# Source-horizontal adaptive Fisher chirality selection

- **ID:** SH-AFCS-C9
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) plus one unresolved arithmetic producer
- **Source:** cross-corpus Frankenstein seam: HT observer-fibre KL conservation + RHTower adaptive
  Fisher curvature + Xi divisor reflection
- **Statement:** On every retained Xi horizontal class, directed Bernoulli KL chirality is faithful;
  a reversible source with orientation-balanced observer fibres forces that class to vanish.

## Goal

Replace symmetric-work equality by a weaker source-derived relation capable of orienting the two
reflected classes. Preserve prime label, Xi multiplicity copy, both orientations, and hidden source
information until after chirality cancellation.

## Gates

- [x] 0 → 1: source-pure target, exact non-circular endpoint, fail/pivot log
- [x] dependency-closed paper proof of selector calculus
- [x] unconditional direct Lean check
- [x] targeted module build and capstone axiom audit
- [ ] external novelty audit
- [ ] literal arithmetic construction of fibre-balanced reversal certificates
- [ ] RH

## Exact theorem

For prime `p` define adaptive occupation

```text
q_p(t) = p^t/(p+p^t) = sigmoid((t-1) log p).
```

The reflected natural parameters are

```text
x=(t-1)log p,    y=(-t-1)log p,
```

so their common center is `c=-log p` and half-separation is `s=t log p`. Directed Bernoulli KL
chirality is

```text
C(c,s)
 = 2s(sigmoid(c+s)+sigmoid(c-s))
   - 2(softplus(c+s)-softplus(c-s)).
```

Its derivative is

```text
∂_s C(c,s) = 2s(V(c+s)-V(c-s)),
V(x)=sigmoid(x)(1-sigmoid(x)).
```

`V` is strictly increasing on the negative natural-parameter ray. Hence if `c<0` and
`|s|<-c`, then `C(c,s)=0 ↔ s=0`. Every nontrivial Xi divisor satisfies
`|primeDepthBVWoldXiCenteredRate|<1`, so

```text
sourceHorizontalPrimeAdaptiveKLChirality p t = 0 ↔ t=0
```

on the complete Xi strip, and global vanishing is equivalent to RH.

## Heavy conjecture loop

### C8 -- canonical Boolean complement exchanges the reflected occupations

**Verdict: FAILED EXACTLY.** Boolean statistical reversal is not horizontal reflection:

```text
1-q_p(t)=q_p(2-t),
q_p(-t) ≠ 1-q_p(t)
```

for every prime and every real grade. The mismatch is a fixed two-unit translation, or
`2 log p` in natural parameter. Therefore no equivariant Boolean involution can be the producer.

**Positive survivor:** Directed KL chirality of the non-complementary reflected pair is strictly
faithful on the Xi strip. This is stronger orientation data than symmetric Jeffreys work.

### C9 -- the Boolean observer must preserve both directed KL costs

**Verdict: OVERSTRONG; PIVOTED.** Pair-sufficiency kills each conditional KL loss. Exact observer
conservation shows this is unnecessary. If an involution exchanges source laws `P,R`, then total
source chirality is zero. It suffices that hidden forward and reverse conditional KL losses agree:

```text
conditionalForwardKL(P,R,q) = conditionalForwardKL(R,P,q).
```

Both may be nonzero. Their difference is observer-fibre chirality, so equality forces observed
adaptive chirality to vanish and therefore `t=0`.

**Positive survivor:** The shortest producer is a non-equivariant reflection upstairs plus
orientation-balanced disintegration downstairs. This preserves hidden source information instead
of demanding a lossless scalar observer.

### C10 -- Hasse recovery kernels balance their reflected conditional KL costs

**Verdict: FAILED NUMERICALLY BEFORE FORMALIZATION.** Exact geometric-KL formula was evaluated for
Hasse ratios at reflected prime clocks. Occupancy-weighted forward and reverse conditional costs
are unequal generically; their difference can even change sign. No false identity was added to Lean.

**Positive survivor:** Hasse common recovery remains pair-sufficient only when kernel is independent
of compared parameter. Prime-clock reflection changes recovery kernel, so any viable Hasse use must
transport observer and fibre together rather than assert fixed-observer balance.

### C11 -- source reversal identifies losses only after reflecting observer

**Verdict: PROVED; PROPOSED PRODUCER TERMINALIZED AS A RECEIVER.** For source involution `θ`, exact chain-rule cancellation
gives

```text
conditionalForwardKL(P,R,q)
  = conditionalForwardKL(R,P,q∘θ).
```

Therefore balanced fibre chirality is equivalent, after reversal, to one same-source theorem:

```text
conditionalForwardKL(R,P,q∘θ)
  = conditionalForwardKL(R,P,q).
```

This is exactly non-equivariant transport on one source carrier. Source reversal supplies first
equality unconditionally. However Lean also proves, under the already required adaptive reflected
marginals and strip bound,

```text
CondKL(R,P,q∘θ)=CondKL(R,P,q) ↔ t=0.
```

So same-source conditional invariance is an exact RH-equivalent socket, not an independent source
producer. Repackaging it as a remaining assumption would be circular theatre.

### C12 -- adaptive KL chirality and Route-T Wold cubic are independent obstructions

**Verdict: FAILED; POSITIVE SURVIVOR PROVED.** They are not independent. The first nonzero neutral
jet of adaptive KL chirality is cubic and satisfies

```text
∂³_t KLChirality_p(0)
 = G_p · ∂³_t WoldPrimeDeformation_p(0),
G_p = 8p^5/((p-1)^2(p+1)^3),
1 ≤ G_p ≤ 32.
```

Thus information orientation and Route-T cubic anomaly are the same coefficient class through a
uniformly invertible prime-labelled gauge. After inverse gauging and finite prime summation, the
adaptive information moment equals the natural Wold cubic moment exactly. Subtracting terminal
prime holonomy gives the same normalized cofinal limit `-2/3`; Xi specialization preserves every
multiplicity copy and both reflection orientations.

**Positive survivor:** Route-T's cubic horizon is not merely analogous to observer chirality. It is
an adaptive directed-information anomaly. Any source theorem killing/orienting one kills/orients
the other without coefficient loss. Conversely, local observer invariance cannot bypass the
Route-T cofinal anomaly.

## Higher universal principle

Functional-equation reflection does not have to identify the two observed bits. It must exchange
the complete source laws while making hidden information loss orientation-neutral. Symmetric
energies retained only metric distance and therefore could not choose an orientation. Directed KL
chirality is the signed boundary current; observer disintegration identifies its missing source law
as equality of the two conditional currents.

This joins four previously separate organs:

1. source involution/functional equation kills total chirality;
2. observer-fibre chain rule transports that cancellation without discarding hidden current;
3. adaptive Fisher occupation retains prime coefficient and horizontal grade;
4. Route-T Wold cubic supplies the same signed information class at the cofinal prime horizon;
5. Xi critical-strip geometry supplies strict faithfulness and multiplicity-resolved RH landing.

## Exact open producer

Construct a pre-zero arithmetic source law that annihilates the common signed cubic class before
bounded scalarization. Equivalently, it must force the adaptive-information presentation of the
Route-T residual cubic horizon to vanish for every retained Xi copy while preserving prime labels,
divisor multiplicity, and both orientations. Because its normalized source limit is unconditionally
`(-2/3)t_q^3`, this immediately forces `t_q=0`.

It cannot be same-source conditional invariance under `q ↔ q∘θ`: C11 proves that premise equivalent
to `t_q=0` once adaptive marginals are installed. It also cannot be reflected-pair cancellation,
which is automatic for every odd cubic response. Required law must act on one orientation before
pairing—plausibly a coefficient-faithful arithmetic conservation law identifying the terminal
holonomy current with the inverse-gauged adaptive information current.

## Formal capstones

Module:
`formal/GaloisForLFunctions/RHTower/SourceHorizontalAdaptiveFisherChiralitySelection.lean`

- `sourceHorizontalPrimeAdaptiveOccupation_complement_eq_translateTwo`
- `sourceHorizontalPrimeAdaptiveOccupation_reflected_ne_complement`
- `klChirality_bernoulli_sigmoid`
- `sourceHorizontalCenteredBernoulliKLChirality_eq_zero_iff`
- `sourceHorizontalPrimeAdaptiveKLChirality_eq_zero_iff`
- `sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fibreBalancedSourceReversal`
- `sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_conditionalFibreReversal`
- `conditionalForwardKL_sourceReversal_eq_reflectedObserver`
- `sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_reflectedObserverConditionalInvariance`
- `sourceHorizontalPrimeAdaptive_reflectedObserverConditionalInvariance_iff`
- `sourceHorizontalXiAdaptiveKLChirality_eq_zero_iff`
- `riemannHypothesis_iff_sourceHorizontalXi_adaptiveKLChirality_zero`
- `riemannHypothesis_of_sourceHorizontalXi_adaptiveFibreBalancedReversalCertificates`

Bridge module:
`formal/GaloisForLFunctions/RHTower/SourceHorizontalAdaptiveFisherChiralityWoldCubicBridge.lean`

- `iteratedDeriv_sourceHorizontalPrimeAdaptiveKLChirality_three_zero_eq`
- `sourceHorizontalAdaptiveChiralityWoldCubicGauge_mul_woldCubic`
- `sourceHorizontalAdaptiveChiralityWoldCubicGauge_bounds`
- `sourceHorizontalAdaptiveChiralityNaturalCubicMoment_eq_wold`
- `sourceHorizontalAdaptiveChiralityResidualCubicCoefficient_eq_wold`
- `tendsto_sourceHorizontalAdaptiveChiralityResidualCubicCoefficient_normalized`
- `sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicResponse_reflection`
- `sourceZeroHorizontalAdaptiveChiralityPrimeClockCubicLimit_eq_zero_iff`

## Current status

Lean proves complete selector, honesty converse, local cubic bridge, finite adaptive-information
moment identity, cofinal `-2/3` limit, and multiplicity-labelled reflection law without `sorry`,
`axiom`, or numerical computation. Targeted bridge-module build passes; audited capstones depend
only on `propext`, `Classical.choice`, and `Quot.sound`. It does not construct the source law
annihilating the common cubic class. RH is not proved.

## Log

- 2026-08-12 — C8 complement conjecture failed exactly; strict directed chirality survivor proved.
- 2026-08-12 — C9 pair-sufficiency weakened to equality of conditional directional losses; Lean RH
  endpoint formalized.
- 2026-08-12 — C10 Hasse reflected-recovery balance failed pre-formal numerics; no Lean claim made.
- 2026-08-12 — C11 source reversal/reflected-observer conditional identity proved; remaining
  same-source conditional invariance then proved equivalent to neutrality, terminalizing it as a
  receiver rather than a producer.
- 2026-08-12 — C12 independence conjecture failed: bounded coefficient-faithful third-jet and
  finite-moment bridge identifies adaptive information chirality with Route-T cubic anomaly.
