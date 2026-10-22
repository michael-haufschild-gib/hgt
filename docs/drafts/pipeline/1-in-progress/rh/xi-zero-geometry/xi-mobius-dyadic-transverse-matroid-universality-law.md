# Xi Möbius dyadic/transverse matroid universality law

## Status

Fully proven on paper; Lean 4 source written. Exact check deferred because imported
`XiMobiusContinuousApertureStrictDyadicLaw.olean` is absent; dependency build is reserved for final
audit by user rule.

## Theorem-first source

- `xiMobiusContinuousApertureDyadicInnovationGram_posDef`: distinct positive real apertures make
  the completed dyadic-refinement innovation Gram strictly positive.
- `xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_injective_ne_zero`: continuous
  Möbius--Szegő positivity on integral apertures detects exactly nonzero injective shifts.
- `xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_mobiusIntegralApertureSzegoGram_posDef`
  and its all-valuation analogue: the same integral Möbius Gram detects both differential bases.
- `xiMobiusPrimeIntegralApertureSzegoGramMatrix_posDef_iff_cofiniteApertureGram`: that collision
  phase is equivalent to cofinite prime-jet positivity after every finite ray deletion.

The strict dyadic theorem supplied only the forward phase. Reading its actual kernel formula shows
that zero apertures give a zero row and aperture collisions give equal rows, so positive
definiteness supplies the missing reverse classification.

## Universal law

On every finite integral shift packet, all following conditions are equivalent:

1. completed unit-mesh dyadic-refinement innovation Gram is positive definite;
2. continuous Möbius--Szegő integral Gram is positive definite;
3. actual Xi upper-end shift carriers are differentially independent over rational coordinate
   field;
4. they remain independent after adjoining every scalar valuation layer;
5. every finite deletion of prime rays admits a positive square jet-aperture Gram.

Their common obstruction consists exactly of zero shifts and shift collisions.

## Paper proof

If two shifts coincide, corresponding dyadic Gram rows coincide, contradicting positive
determinant. If one shift is zero, disk node is `1`; every innovation feature and hence its Gram
row vanishes, contradicting positive diagonal. Conversely, injective nonzero integral shifts cast
to distinct positive real apertures, so strict dyadic positivity applies. Existing continuous,
transverse, cofinite, and base-change classifiers all reduce to the same injective/nonzero
criterion. No numerical computation is used.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.XiMobiusDyadicTransverseMatroidUniversalityLaw`.

Reverse collision/zero proof exact-checks independently in a scratch module against built parent
dependencies. Full exact command is deferred to final dependency audit.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
