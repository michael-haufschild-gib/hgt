# Scale-Signed Incidence Criticality: the resolution calculus of readings and its five wall gates

- **ID:** ssic-2026-10-22
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for the calculus, the six gates and the four exact limits; CONJECTURE for the frontier items F1–F5
- **Source:** docs/reports/review-2110/argon.md Part II (§2.1–2.9, the blueprint of *Scale-Signed Arithmetic Incidence & Criticality Theory*); germ: `RHTower.DeciderBarrier`, `RHTower.Sieve.CoefficientFreeCap`, `TransHorizonIncidenceMechanics.RealCharacterParityPairsAndTheParityBarrier`
- **Statement:** A *reading* is a map `r : D → O` of a class of data; its *shadow* at `d` is `{e | r e = r d}`; for a real invariant `I` its *resolution limit* is `sSup (I '' shadow r d)`. A method reading `r` can prove `I d ≤ β` iff `β` is at least the limit. With this unit: every bounded aperture and every bounded height has width-limit exactly `½`, the unbounded aperture has limit `0`, the amplitude reading has damping floor exactly `½`, asymptotic node readings, structural-flag readings and bounded-radius certificate readings resolve nothing unless RH fails, and any resolving reading must separate the explicit gate pairs (`theWallGates`, `parityWallGate`).

## Goal
Convert the corpus's 594 individual no-gos from a list into one calculus with a number. A no-go
becomes `(class of readings, exact limit)`; an admissibility criterion becomes a checkable
inequality of readings on an explicit pair; and "combining more blind data" is excluded once and for
all by the closure lemmas (post-composition, joins, families of arbitrary cardinality). Not
circular: the calculus assumes nothing about `ζ`; every instance imports its countermodel from the
programme that owns it.

## Gates
- [x] 0 → 1  in-progress: well-posed (README §2), source-pure (readings of the existing corpus data), attack idea (collapse–resolution dichotomy + exact limits), Door passport: the gates are necessary conditions, never a criterion for RH.
- [x] 1 → 2  fully-proven: the calculus, the five gates, the four limits — all unconditional, no open dependency.
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/` (9 modules, each audited with `lake --old env lean`; own umbrella `GaloisForLFunctions.ScaleSignedIncidenceCriticality`, wired into `MainTheorems`).
- [ ] 3 → 4  not applicable (no stage 4; RH only).

## Approach
1. **Calculus** (`TheResolutionLimitOfAReading.lean`): shadows; `Resolves`; `Invisible` collapses;
   the dichotomy and its vacuity form; `resolutionLimit`/`Certifies` with the exactness theorem
   `certifies_iff_resolutionLimit_le`; collapse floors; the refinement order, joins and families;
   faithfulness and the transfer theorem; the dual floor for lower bounds;
   `resolves_iff_exists_factorization` (the bridge that makes every corpus barrier an instance);
   the algebra of blindness.
2. **Aperture face** (`BoundedApertureReadingsHaveTheTrivialResolutionLimit.lean`): limit `½` at
   every aperture and for every *bounded family* of apertures; limit `0` for the unbounded reading;
   the jump.
3. **Ladder** (`TheApertureLadderIsStrictYetEveryStageIsTrivial.lean`): the aperture readings
   strictly refine one another, yet every stage keeps the trivial limit.
4. **Node face** (`AsymptoticNodeReadingsCannotResolveNodePositivity.lean`): asymptotic readings are
   invisible to a one-node deletion; prime-power deletion is uniformly fatal; the fatal collapses are
   exactly the prime powers.
5. **Parity face** (`AmplitudeReadingsCannotResolveTheReceiver.lean`): the actual damped Möbius
   weight against its parity twin at damping `½`; the floor `½` on the damped class; closure under
   amplitude-derived families.
6. **Temperedness face** (`StructuralFlagReadingsCannotResolveCriticality.lean`): the four
   structural flags are constant on `|a| ≤ ¼`; criticality fails at `a = ¼`.
7. **Height face** (`BoundedHeightReadingsCannotResolveTheWidth.lean`): the truncated divisor is
   finite data and misses one off-line pair above the height; limit `½`.
8. **Prime-window face** (`FiniteRadiusCertificateReadingsCannotResolveTheWeilCone.lean`): the
   radius-`R` certificate reading is a function of the primes below `e^{2R}`, and every radius has a
   mimic outside the Weil cone.
9. **Capstone** (`TheWallGatesOfAResolvingReading.lean`): both halves of four faces in one theorem;
   the parity row is `parityWallGate` in its own module (the `SquareRootThreshold` and
   `TransHorizonIncidenceMechanics` import closures cannot be loaded together while the corpus
   declares `RHTower.dilationAverage` twice).

## Lean modules (formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/)
- `TheResolutionLimitOfAReading.lean` — the calculus (no corpus dependency).
- `BoundedApertureReadingsHaveTheTrivialResolutionLimit.lean` — `resolutionLimit_width_aperturePositivity`, `resolutionLimit_width_familyPositivity`, `resolutionLimit_width_fullPositivity`, `apertureResolutionJump`.
- `AsymptoticNodeReadingsCannotResolveNodePositivity.lean` — `not_resolves_of_asymptoticReading`, `fatal_deleteNode_iff_isPrimePow`.
- `AmplitudeReadingsCannotResolveTheReceiver.lean` — `not_resolves_amplitudeReading_receiver`, `half_lt_of_resolves_classAmplitudeReading`, `not_resolves_amplitudeDerivedFamily`, `parityWallGate`.
- `StructuralFlagReadingsCannotResolveCriticality.lean` — `structuralFlags_eq`, `not_riemannHypothesis_of_resolves_structuralFlags`.
- `BoundedHeightReadingsCannotResolveTheWidth.lean` — `finite_support_heightReading`, `resolutionLimit_width_heightReading`.
- `TheApertureLadderIsStrictYetEveryStageIsTrivial.lean` — `apertureLadder`.
- `FiniteRadiusCertificateReadingsCannotResolveTheWeilCone.lean` — `radiusReading_congr_of_agree_below`, `not_riemannHypothesis_of_resolves_radiusReading`.
- `TheWallGatesOfAResolvingReading.lean` — `theWallGates`.
- `README.md` — the foundational document (why / what / how / traps / frontier / principles).

## Frontier (open, in the programme's own unit)
- **F1** (closed 2026-10-22, qualitative part) The prime-side gate: no bounded-radius certificate
  reading resolves the Weil cone. Open: a numerical unit for this face — a cone defect with an exact
  resolution limit at radius `R`.
- **F2** Faithfulness of the rank-two pole compression `a ↦ 𝒫(a)`
  (`SquareRootThreshold.PrimeTailCouplingCriterion`) for the width.
- **F3** The exact limit of the pronic-Gram reading in the exponent unit `θ` (expected `2`, witness:
  `BezoutValuationIncidence.CoherentPrimeBlocksAndTheTypeIIWindowNoGo`).
- **F4** Joint limits: the limit of the intersection of two shadows for the pairs
  (aperture, amplitudes) and (height, nodes) — a strict drop is the quantitative meaning of
  "exploiting a seam".
- **F5** A fatality classification for parity collapses, matching the node-collapse classification.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** (not applicable: the programme proves floors, not a route)
- **Strongest positive survivor:** (open)
- **New insight:** (open)
- **Status:** (open)

## Log
- 2026-10-22 — created in 1-in-progress; programme initiated from argon.md Part II; calculus, six
  faces, ladder and capstone formalised (9 modules, all clean); own umbrella wired into
  `MainTheorems`; README written. Blocker found in the corpus, not in this programme: two
  declarations named `RHTower.dilationAverage` (`RHTower/SoninDilationAverage.lean:31`, added
  2026-08-23, and `RHTower/FermiNymanHaarApproximationEquivalence.lean:152`, added 2026-10-17) make
  `GaloisForLFunctions.RHTower` — and hence any module combining the `SquareRootThreshold` and
  `TransHorizonIncidenceMechanics` closures — fail to load.
