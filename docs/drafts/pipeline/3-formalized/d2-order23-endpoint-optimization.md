# D2 order-23 endpoint optimization

- **ID:** `d2-order23-endpoint-optimization`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / exact atom-endpoint and D2 threshold advance (Lean)
- **Source route:** D2 plus centered order-23 fourth reciprocal trace
- **Statement:** The existing order-23 atom/source contradiction remains valid through squared
  ordinate `431349/2000`, advancing the premise-free D2 threshold to `141858/10000`.

## Goal

Recover the algebraic margin discarded when the order-23 atom bound was rounded to squared height
`431/2`. Optimize the exact rational endpoint in the same kernel-clean proof, propagate the larger
zero-free band to `RHVerifiedThrough`, and advance the pure-prime D2 endpoint without numerical
zero verification or native computation.

## Gates

- [x] 0 → 1 in-progress: exact endpoint inequality isolated from corpus proof
- [x] 1 → 2 fully-proven: dependency-closed rational inequality and source contradiction
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem note and independent expert audit

## Conjecture

For an off-line Xi zero copy `q`, put

```text
u=(Re(q)-1/2)^2,   v=Im(q)^2,   w=u+v,
V=431349/2000,     W=V+1/4=431849/2000.
```

The divisor strip gives `0<u<1/4`. In the upper annulus

```text
2365/16 ≤ v < V,
```

the exact fourth reciprocal-trace atom should still satisfy

```text
17/800000 < Re(xiZeroCopyReciprocalSquare(q)^2).          (1)
```

Four FE--Schwarz copies would then overspend the strict source budget
`normalizedPrimeArchMoment(1)<17/200000`, forcing every off-line zero to obey `V≤v`.

## Proof

The exact atom formula is

```text
Re(xiZeroCopyReciprocalSquare(q)^2)
  = (v^2-6uv+u^2)/w^4.
```

Since `w<W`, exact rational arithmetic proves monotonicity on the relevant interval by the
factorization

```text
(800000 w^2-17 w^4)-(800000 W^2-17 W^4)
  = (W^2-w^2)(17(W^2+w^2)-800000) > 0.                  (2)
```

The strip and height bounds give `uv<V/4`. At the selected rational endpoint Lean proves

```text
6400000(V/4) < 800000 W^2-17 W^4.                       (3)
```

Combining `(2)` and `(3)` yields

```text
0 < 800000(v^2-6uv+u^2)-17w^4,
```

which is exactly `(1)` after division by positive `800000w^4`. Quartet domination and the strict
global source cap contradict `(1)` for an off-line zero. The older exact fourth-trace theorem
handles `v<2365/16`; therefore

```text
Im(q)^2 < 431349/2000 => Re(q)=1/2,
q off-line            => 431349/2000 ≤ Im(q)^2.          (4)
```

Any `H` satisfying `H^2<431349/2000` consequently satisfies `RHVerifiedThrough(H)`. The exact
rational threshold

```text
R*=141858/10000
```

obeys `(R*+1/2)^2<431349/2000`. Reusing the generic verified-band-to-prime-defect bridge gives an
explicit floor on `233/20<Im(s)≤R*`, and hence

```text
PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow(R*)
  <-> RiemannHypothesis.                                  (5)
```

## Strongest positive survivor and route impact

- **New height gap:** every off-line Xi zero has squared ordinate at least `431349/2000`, an exact
  gain of `349/2000` over the rounded order-23 endpoint `431/2`.
- **New D2 endpoint:** `141858/10000`, strictly above `141799/10000` by `59/10000`.
- **Reusable content:** endpoint factorization `(2)` and the parameterized verified-height bridge;
  future source improvements transfer to D2 without rebuilding prime/Gamma analysis.
- **Remaining burden:** one common pure-prime defect floor only above `14.1858`.
- **Order-24 status:** standard-kernel source-cap certificate remains open; this result is a
  positive survivor, not retirement of the stronger `467/2` target.

## Novelty audit

Mandatory corpus search found the rounded order-23 exclusion at `431/2`, its atom formula, source
cap, and D2 transfer, but no exact endpoint optimization, no height theorem at `431349/2000`, and
no D2 endpoint at `141858/10000`. Primary searches through 2026-08-28 found rigorous finite-height
verification by interval arithmetic/Turing methods and reciprocal-power criteria, but no
noncomputational source-moment theorem `(1)--(5)`. Candidate novelty is restricted to this exact
route-specific synthesis and closed Lean proof; it is not a claim of record numerical RH
verification height.

Primary comparison:

- D. Platt and T. Trudgian, [*The Riemann hypothesis is true up to
  `3·10^12`*](https://arxiv.org/abs/2004.09765).
- M. W. Coffey, [*Toward verification of the Riemann hypothesis: application of the Li criterion*](https://arxiv.org/abs/math-ph/0505052).

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/PrimeArchLogHeightDefectOrderTwentyThreeEndpointOptimization.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct source check: PASS
- Targeted build: PASS (`12861/12861`; initial dependency scheduling race cleared on retry)
- Axiom audit: all five principal declarations use exactly
  `[propext, Classical.choice, Quot.sound]`; no native-decision axiom occurs.
- Principal declarations:
  `seventeen_over_eightHundredThousand_lt_xiFourthReciprocalTraceAtom_orderTwentyThree_optimized`,
  `xiZeroCopy_re_eq_half_of_im_sq_lt_orderTwentyThreeOptimized`,
  `orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine`,
  `rhVerifiedThrough_of_sq_lt_orderTwentyThreeOptimized`,
  `primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_xiOrderTwentyThreeOptimizedThreshold_iff_rh`.
- Formal lint: new module is wired and has no local violation; repository-wide reachability errors
  belong to unrelated dirty-tree Sieve and HTGeometry modules.

## Log

- 2026-08-28 — Mandatory corpus search exposed unused rational margin in order-23 atom endpoint.
- 2026-08-28 — Proved exact atom lower bound at `V=431349/2000` and source-budget exclusion.
- 2026-08-28 — Derived verified-height theorem, strict old/new threshold comparison, band floor,
  and premise-free D2 equivalence at `141858/10000`.
- 2026-08-28 — Passed direct source check, targeted build, standard-axiom audit, and local lint;
  wired theorem-area umbrella and promoted survivor to fully proven.
