# BAG mixed-frequency rational rows and collisions

- **Stage:** 3-formalized

01ar. Paper proof formalized: actual row/collision scratch14241 emptyPASS;
full masked assembly production7092 emptyPASS, axioms35601 standard3.
P3 card records complete audit. Global eventual local-factor nonvanishing
will also follow from the forthcoming full mixed unlabelled product law.
Part of M1 in `bag-mixed-frequency-mellin-cancellation`, not physical axes saving.

## Exact claim

Fix complex u,v and nonzero real tau. Put L=log N, s=1+u/L,
t=1+v/L+i*tau. Use the original `criticalMellinResponse` and original
prime cutoff, with weights w_p=log(p)/p. The four response rows divided
by L tend respectively to 1-E(u), 1, 1-E(u), 1-E(u), where
E(u)=integral_0^1 exp(u*x) dx. The four exact collision sums from
`ChiRamanujanMaskedMellinSource` divided by L tend to zero. All local
response denominators are nonzero simultaneously for p<=N once N is large.

## Corpus and novelty audit

Use the exact rational response formulas and local conversion in
`ChiRamanujanMovingLabelRows`, the compact-tail/fixed-head argument in
`ChiRamanujanMovingResponseWindow`, and the actual oscillatory weighted
window law in `ChiRamanujanOscillatoryLogWindow`. The existing two-fixed-
displacement law cannot be applied with v replaced by v+i*tau*L.
The new step retains the prime phase as a compact parameter throughout.

Search4018, `/tmp/bag-mixed-response-search-01ar.json`, nonpartial65953files,
generation1246673 (coverage1246682), noerrors, backgroundrefreshincomplete,
semanticcoverageunmeasured. All20candidate+20source entries inspected.
It retrieves the actual excluded-response expansion and critical prime
Mellin ratio. Unrelated proposed periodic-weight ingredients do not prove
this statement and are not used. Relevant exact source files read.

## Proof

For p<=N put z=1/p, x=log(p)/L, theta=p^(-i*tau),
a=exp(-u*x), b=theta*exp(-v*x). Then x is in[0,1] and |theta|=1.
The corpus local identity writes each response as R_k(z,a,b), with the
same explicit numerator and common denominator H as in MovingLabelRows.
At z=0 the denominator is1. At the fixed-prime limit x=0,

  H(z,1,theta)=(1-z*theta)/(1-z).

Both denominator factors are nonzero for z=1/p and |theta|=1.
The a,b denominators are nonzero everywhere in question.

Apply continuity on the compact slice {0} times[0,1] times the unit circle.
For every epsilon>0 there is K such that for every p>=K, every x in[0,1]
and every unit theta,

  |R_k(1/p,exp(-u*x),theta*exp(-v*x))
     -R_k(0,exp(-u*x),theta*exp(-v*x))| < epsilon.

The same argument applied to H-1 makes |H|>=1/2 for all these large
primes. For each of the finitely many primes p<K, x tends to0; continuity
at the displayed nonzero denominator gives convergence and eventual
nonvanishing. A finite intersection proves nonvanishing at every p<=N.
It also bounds every fixed-prime response error. Thus the finite head
of the weighted error divided by L tends to0. The tail norm is at most
epsilon * (sum_(p<=N) log(p)/p)/L, which tends to epsilon by the corpus
Mertens window. Since epsilon is arbitrary, the entire error tends to0.

The four zero-slice values, in order, are exactly

  1-exp(u*x)+theta*exp((u-v)*x),
  1+theta^(-1)*(exp((v-u)*x)-exp(v*x)),
  1-exp(u*x)-theta^(-1)*exp(v*x),
  1-exp(u*x)+theta*exp((u-v)*x)
    +theta^(-1)*(exp((v-u)*x)-exp(v*x)).

After multiplying by w_p/L, each theta term is the actual corpus
oscillatory window x*exp(w*x)*p^(-1-i*tau), and each theta^(-1) term
uses -tau. Both frequencies are nonzero. The proved window theorem gives
zero for every such term. The remaining Mertens windows tend to the
integrals of1 and exp(u*x). This proves the four stated row limits.

For collisions, set W(z)=-z*log z, with W(0)=0. This is continuous and
W(1/p)=w_p. The four exact collision profiles after factoring one w_p are

  W*(R_3-R_0*R_1), W*R_1*R_2, W*R_0*R_2,
  W^2*R_2*(2*R_0*R_1-R_3).

Every profile is continuous on the same zero slice and fixed-prime heads;
every zero-slice value is0. The preceding compact-tail/fixed-head argument
therefore proves each original collision sum divided by L tends to0.
No numerical experiment, dropped prime, assumed row bound, or assumed
boundary convergence enters the proof.

## Remaining obligations

Compact-phase argument, actual rational instantiation and complete masked
assembly are Lean formalized. Combine with actual mixed unlabelled Euler/cofactor limit
and the Mertens normalization to prove M1. Compact-uniform parameter
control and signed physical-profile remainders/tails are still separate
hard obligations; this paper result proves none of those by itself.

Lean exposes a stronger collision theorem: tau may be ANY real number,
including0. Paper re-audit: the collision argument only uses |theta|=1,
continuity of the exact rational denominator at each fixed prime, and the
zero collision slice. It never invokes oscillatory prime convergence or
tau!=0. Thus every collision/L->0 unconditionally for all real tau.
The actual row and complete masked limits still require tau!=0.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiRamanujanMaskedMellinSource` | `criticalLocalMellinBase_eventually_ne_zero`, `criticalWeightedConeEuler_moving_response`, `criticalCompletedConeEuler_moving_response`, `criticalMaskedMellinResponse_expansion`, `criticalCompletedConeEuler_mixed_response` |
| `GaloisForLFunctions.RHTower.ChiRamanujanMixedLabelRows` | `criticalMixedMellinResponseRow_tendsto`, `criticalMixedMellinCollisionMoment_tendsto`, `criticalMixedMaskedMellinResponse_tendsto` |
| `GaloisForLFunctions.RHTower.ChiRamanujanMovingLabelRows` | `criticalMellinResponseRow_tendsto`, `criticalMellinCollisionMoment_tendsto` |
| `GaloisForLFunctions.RHTower.ChiRamanujanMovingResponseWindow` | `criticalLogScaleInv_tendsto_zero`, `criticalMovingResponseWindow_tendsto` |
| `GaloisForLFunctions.RHTower.ChiRamanujanOscillatoryLogWindow` | `criticalPrimeBoundarySum_tendsto`, `criticalOscillatoryLogWindow_tendsto`, `criticalOscillatoryLogWindow_difference_tendsto` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
