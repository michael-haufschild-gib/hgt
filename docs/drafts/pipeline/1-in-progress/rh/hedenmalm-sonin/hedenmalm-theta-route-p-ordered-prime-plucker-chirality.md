# Route-P ordered-prime physical Pluecker chirality

- **ID:** `P-G80`
- **Stage:** `1-in-progress`
- **Type:** universal ordered-prime source theorem
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-physical-plucker-chirality-gain.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalOrderedPrimePluckerChirality.lean`

## Conjecture P-G80.A: P-G79 is a universal ordered-prime law

For arbitrary primes `p<q`, form physical four-rate cell

```text
(p,0), (p,1), (q,0), (q,1)
```

and use any aperture `0<a<log(p)/2`. Conjecture that consecutive-depth Cauchy--Binet minor mass
strictly decreases with prime while Fisher clock strictly increases.

**Verdict: true, unconditionally proved.** The exact consecutive minor at prime `p` is

```text
4 a^2 /
  ((p+1)^4 log(p)^2
   (1/4-(a/log(p))^2)^2
   (9/4-(a/log(p))^2)^2).
```

Every denominator factor strictly increases from `p` to `q`: prime damping, log scale, and both
normalized nonboundary shape factors. Hence

```text
raw_q < raw_p,
probability_q < probability_p.
```

Meanwhile `F_p=(2/3)log(p)^2` is strictly increasing. Exact six-pair cancellation gives

```text
sum_s chi_w(s) F_comp(s)
  = 2 (probability_p-probability_q) (F_q-F_p) > 0.
```

Therefore every ordered two-prime physical packet has complement-Fisher Schur fraction strictly
inside `(1/2,1)`. Its residual at every prime-power label remains positive and is strictly smaller
than symmetrized half residual.

## New knowledge

P-G76's vanished same-prime chirality and P-G79's hostile-cell gain are instances of one
anti-monotone covariance law:

```text
valuation depth creates chirality but carries no Fisher contrast;
ordered prime scale creates opposite minor-mass and Fisher-clock order;
their complement-odd pairing is strictly positive.
```

Thus cross-prime transport does not require an invented orientation rule. Natural prime order
already orients every two-prime physical Pluecker packet. Remaining task is cofinal assembly and
identification with actual source Feshbach reduction, not local sign selection.

## Lean realization

Headline declarations:

- `gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_eq`;
- `gammaSewnCriticalOrderedPrimePlucker_consecutiveRawWeight_strictAnti`;
- `gammaSewnCriticalOrderedPrimePlucker_partition_pos`;
- `gammaSewnCriticalOrderedPrimePlucker_probability_five_lt_zero`;
- `gammaSewnCriticalOrderedPrimePlucker_fisher_lt`;
- `gammaSewnCriticalOrderedPrimePlucker_chiralityFisherMoment_eq`;
- `gammaSewnCriticalOrderedPrimePlucker_chiralityFisherMoment_pos`;
- `gammaSewnCriticalOrderedPrimePlucker_schurFraction_gt_half`;
- `gammaSewnCriticalOrderedPrimePlucker_schurFraction_lt_one`;
- `gammaSewnCriticalOrderedPrimePlucker_reducedWeight_pos`;
- `gammaSewnCriticalOrderedPrimePlucker_reducedWeight_lt_half`.

Exact audit:

```text
lake build GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalOrderedPrimePluckerChirality
Build completed successfully (12733 jobs).
```

Capstone `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Next conjecture P-G81

Pair a finite ordered prime list into adjacent two-prime packets and aggregate their physical
chirality corrections with the P-G78 weak Köthe kernel. Prove positivity survives every finite
cofinal stage and determine whether total Schur gain is summable/nonvanishing at critical
aperture. Then compare resulting reduced all-prime mass with completed seam moments. This must use
literal source coefficients and retain unpaired endpoint data; no averaging or fitted weights.

## Honest boundary

P-G80 proves uniform local sign, strict `(1/2,1)` Schur fraction, and positive sub-half residual
for every ordered two-prime packet. It does
not yet construct cofinal packet assembly, prove infinite gain bounds, identify physical scalar
with actual Feshbach elimination, complete Gamma/polar sewing, or prove RH.
