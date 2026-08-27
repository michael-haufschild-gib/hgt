# GTA theta admissible Schur-quartic nonselection (2026-08-27)

Corpus-led conjecture `[GTA-PQ4-N]` completed and formalized.

## Generic positive survivor

`formal/GaloisForLFunctions/HTGeometry/FiniteMatrixSchurPositiveQuarticDivisorCharge.lean` defines `FiniteMatrixSchurPacket`, its quartic charge, and `FiniteMatrixOrdinaryRealDivisor`. For every finite complex matrix and every Schur packet:

- charge is nonnegative;
- charge = 0 iff every zero of `det(1-zM)` is real;
- any nonreal determinant zero forces strictly positive charge for every Schur packet.

## Source-specific no-go

`formal/GaloisForLFunctions/RHTower/HedenmalmThetaAdmissibleSchurQuarticNonselection.lean` canonically reindexes theta blocks by `Fin` and proves that every approximation accuracy fibre contains an admissible stage with nonreal divisor whose every Schur packet has positive quartic charge. Hence the present `ThetaSourceSignedApproximationProperty` (finite support + regularity + HS proximity + trace zero) cannot select charge-zero stages.

## Exact boundary

Current-spec GTA source selector branch is retired. Replacement burden: add an arithmetic selector not implied by the existing four-field approximation property.

## Verification

- direct `lake env lean` passed for both modules/scratch;
- exact targeted builds passed;
- `scripts/formal_tools.py lint` passed;
- axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

Cards:
- failed/no-go with positive survivor: `docs/drafts/pipeline/5-failed/theta-source-admissible-schur-quartic-nonselection.md`
- related exact endpoint formalized: `docs/drafts/pipeline/3-formalized/theta-source-schur-quartic-charge-flag.md`.