# Physical corrected-prime cofinal schedule invariance

- **ID:** `physical-corrected-prime-cofinal-schedule-invariance`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / NO-GO (Lean)
- **Source route:** CCM-FU / PPM / physical theta--Abel corrected-prime contour
- **Statement:** Every cofinal admissible pole-crossing prime-contour schedule has the same Weil limit; contour selection cannot evade a false-RH negative chamber.

## Goal

Determine whether optimizing or adapting admissible rectangles remains a genuine RH proof degree
of freedom after Loop 88. Prove the strongest positive survivor if schedule choice is asymptotically
rigid.

## Gates

- [x] 0 → 1 in-progress: corpus-derived arbitrary-schedule conjecture
- [x] 1 → 2 fully-proven: dependency-closed paper proof and no-go classification
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem/no-go note

## Exact theorem

A `XiPhysicalThetaAbelEnergyPrimeCofinalSchedule` consists of rectangles `(z₁(m),z₂(m))` whose
four edges are explicit-formula admissible, whose geometry crosses the centered archimedean pole,
and which eventually contain every finite `XiZeroCopy` packet.

For every such schedule `S`, every `A,c>0`, and every physical scale `(L,a)`, Lean proves

```text
CorrectedPrime_S(m;L,A,c,a) -> CompleteWeilEnergy(L,A,c,a),  (1)

RawPrime_S(m;L,A,c,a) -> CompleteWeilEnergy(L,A,c,a)
  -[exp(a/2) 2(1-exp(-L/2)) c A]^2.                         (2)
```

Hence for every pair of schedules `S,T`,

```text
CorrectedPrime_S(m)-CorrectedPrime_T(m) -> 0,               (3)
RawPrime_S(m)-RawPrime_T(m) -> 0.                           (4)
```

At all admissible logarithmic samples, sharp zero-floor asymptotic nonnegativity along any fixed
schedule is equivalent to RH. Stronger universal forms are proved:

```text
[every cofinal schedule is asymptotically nonnegative] <-> RH,          (5)
[every cofinal schedule has an eventually strict negative sample]
  <-> not RH.                                                           (6)
```

Closed unit-parameter forms of `(5)--(6)` are included.

## Proof

For a fixed detector, squared values on copied Xi zeros form a summable family. The `HasSum`
finite-set filter says that every finite superset of one sufficiently large packet approximates
the full `tsum`. Schedule cofinality eventually contains that packet. The rectangle residue theorem
identifies the corresponding finite sum with the normalized source contour, and pole-crossing
residue evaluation identifies source with corrected direct-prime contour, proving `(1)`. Removing
the fixed archimedean square proves `(2)`. Subtraction of equal limits gives `(3)--(4)`.

RH makes the common Weil limit nonnegative at every physical logarithmic sample, so each schedule
eventually lies above every negative epsilon. Conversely, a negative Weil value forces every
schedule eventually below half that negative value. This proves schedulewise equivalence and the
universal quantifier forms `(5)--(6)`. Loop 88 supplies an inhabitant of the schedule structure, so
the universal statements are not vacuous.

## No-go closure

- **Exact killing theorem/mechanism:** `(3)--(4)` show all cofinal admissible pole-crossing contour
  choices are asymptotically identical. Under false RH, `(6)` forces every one into a strict
  negative chamber at a common detector scale (with schedule-dependent entry time).
- **Strongest positive survivor:** universal convergence `(1)--(2)` and the all-schedule RH/false-
  RH classifications `(5)--(6)`.
- **New insight:** contour selection can change only transients. It cannot alter the limiting
  corrected-prime sign or hide an off-critical Weil defect.
- **Status:** paper proof dependency-closed; Lean module verified and wired.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeCofinalScheduleInvariance.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS (`11812/11812`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `XiPhysicalThetaAbelEnergyPrimeCofinalSchedule`,
  `xiPhysicalThetaAbelEnergyArithmeticPrimeCofinalSchedule`,
  `XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.tendsto_correctedPrimeSample_weil`,
  `tendsto_correctedPrimeSample_sub_schedule_zero`,
  `tendsto_primeSample_sub_schedule_zero`,
  `XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.asymptoticallyNonnegative_iff_rh`,
  `XiPhysicalThetaAbelEnergyPrimeCofinalSchedule.eventuallyNegativeWitness_iff_not_rh`,
  `unitAllPrimeCofinalSchedulesAsymptoticallyNonnegative_iff_rh`,
  `unitAllPrimeCofinalSchedulesEventuallyNegativeWitness_iff_not_rh`

## Route impact and remaining burden

Adaptive height selection, rational encoding, canonical zero packets, and other cofinal contour
choices are now formally classified as asymptotically irrelevant. The remaining RH burden is not
to choose a better contour schedule. It is to prove a direct prime-side zero-floor estimate for
one—equivalently every—cofinal schedule. Any proposal relying only on selecting favorable late
rectangles is a proven dead end.

## Novelty audit

Targeted corpus and literature searches through 2026-08-27 found no all-schedule corrected/raw
literal prime-contour limit, pairwise null-difference theorem, or universal strict-negative false-
RH classification. Classical presentations choose zero-avoiding heights to derive an explicit
formula; recent Galerkin, screw-operator, and finite-window works analyze particular truncations.
They do not classify every cofinal pole-crossing direct-prime contour schedule. Candidate-new
content is restricted to this route-specific formal synthesis.

Primary comparison points:

- A. Groskin, [*A finite Guinand-Weil dictionary and archimedean tail order for the truncated Weil quadratic form*](https://arxiv.org/abs/2607.02828).
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096).
- A. Connes, [*The Riemann Hypothesis: Past, Present and a Letter Through Time*](https://arxiv.org/abs/2602.04022).
- A. Connes and C. Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368).

## Log

- 2026-08-27 — Mandatory corpus search found no arbitrary-schedule limit theorem.
- 2026-08-27 — Conjectured abstract cofinal pole-crossing schedule and pairwise limit rigidity.
- 2026-08-27 — Proved corrected/raw universal limits and pairwise null differences.
- 2026-08-27 — Proved every-schedule RH and false-RH classifications.
- 2026-08-27 — Direct check, targeted `11812/11812` build, standard axiom audit, and wiring passed.
- 2026-08-27 — Global lint reached the wired module with no local violation; repository-wide gate
  remains blocked by unrelated concurrently edited unwired RHTower/HTGeometry modules.
