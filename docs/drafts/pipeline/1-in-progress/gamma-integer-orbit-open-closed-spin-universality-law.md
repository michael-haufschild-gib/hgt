# Gamma integer-orbit open/closed/spin universality law

## Status

Fully proven on paper; Lean 4 formalization in progress.

## Theorem-first source

- `differentiallyAlgebraicOver_generalizedSpinTowerChannelMero_iff_integer`: analytically
  continued finite-spin channel collapses exactly at integral tower parameter.
- `differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift`: reduced
  open-string channel collapses exactly at integral crossed-channel separation.
- `differentiallyAlgebraicOver_reducedVirasoroShapiroAmplitudeMero_iff_integerShift`: reduced
  closed-string channel has the same exact boundary after double copy.
- The three complementary `hypertranscendentalOver_..._iff_noninteger` theorems identify the
  entire nonintegral sector, not only a sufficient HT region.

No corpus theorem compares the generalized spin tower with both string channels.

## Universal law

For every complex parameter `N` and every open/closed-string base shift `a`, one integer-orbit
selector controls all three physically different Γ observables simultaneously.  `N` is integral
exactly when the generalized spin multiplier, reduced Veneziano channel, and reduced
Virasoro--Shapiro channel are all differentially algebraic.  `N` is nonintegral exactly when all
three are hypertranscendental.  Mixed differential phases are impossible.

## Paper proof

Each source theorem is an iff with the same selector `N in Z`.  Intersect the three DA iff
statements to obtain simultaneous collapse.  Negating the common selector and using the three HT
iff statements gives simultaneous hypertranscendence.  Transitivity yields pairwise equivalence
between every channel and excludes all mixed phase assignments.

No numerical computation is used; proof is symbolic because task forbids computations.

## Lean formalization

Planned module:
`GaloisForLFunctions.HTGeometry.GammaIntegerOrbitOpenClosedSpinUniversalityLaw`.

## Novelty audit

Pending literature audit after Lean formalization. Corpus audit is negative.
