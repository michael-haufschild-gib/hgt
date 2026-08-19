# Helson seam / arbitrary-divisor card — CLOSED at stage 3 (2026-08-19)

Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ht/helson-universal-ht-arbitrary-divisor-orthogonality.md`
Companion: `...-formalized.md` beside it.  Ledger entry appended to `_stage2-to-3-ledger.md`.

## What closed

The last gate was Andersson's arbitrary-divisor continuation theorem.  The whole chain is Lean-proved
and axiom-clean (`propext, Classical.choice, Quot.sound`):

```text
RHTower/Sieve/CharacterStacking.exists_andersson_character        Lemma 7, FULL chain (datum + arith)
RHTower/AnderssonTheoremOne.exists_character_entire_remainder     Theorem 1
HTGeometry/HelsonCharacterLSeries.logDeriv_helsonZetaValue        logDeriv Z_χ = -LSeries(χΛ)
RHTower/AnderssonTheoremTwo.helson_factorization_of_mellin_logDeriv   Theorem 2
RHTower/AnderssonTheoremTwo.exists_continuable_phase_with_prescribed_divisor
RHTower/AnderssonDivisorAtOrigin.exists_continuable_phase_with_divisor_at_origin
RHTower/LocallyFiniteDivisorPresentation.exists_continuable_phase_with_prescribed_locallyFinite_divisor
```

## The three design facts worth remembering

1. **The datum must be inside the recursion, and it must decay.**  Over a window of length `L` the
   continuous datum's Taylor remainder costs `Mq·L`, against a Rayleigh floor also proportional to
   `L`.  A global bound is therefore never enough; Lemma 1's `q = o(1)` is what makes it absorbable,
   past a threshold where `‖q‖ ≤ datumSlack J = 1/(262144 J² blockRayleighConst J)`.  Every size
   condition is split into four quarters (state / forced prime powers / datum / slack).
2. **Theorem 1's entire function comes from gluing, not from one integral.**  The `j`-th
   representation converges on `Re s > (j+1)ϑ + 2θ - j` with `ϑ = θ + (1-θ)/3 < 1`; the abscissas
   decrease to `-∞` and the identity theorem makes the family one germ.
3. **The divisor side had to be made exact.**  `PrescribedDivisorRealization` only pinned the
   support; `analyticOrderAt_weierstrassGenusProduct` now gives the multiplicity, `z^k` supplies an
   order at the origin, and `LocallyFiniteDivisorPresentation` turns an arbitrary locally finite
   `D : ℂ → ℤ` into two sequences whose auxiliary points cancel.

## Reusable assets (search these before rebuilding)

```text
HTGeometry/HalfPlaneMellinAnalytic.lean      convergence + holomorphy of ∫_1^∞ f x^{-w} on Re w > ρ+1
HTGeometry/HalfPlaneSequenceGluing.lean      exhausting half planes glue to an entire function
HTGeometry/DatumNormalization.lean           truncDatum: measurable+bounded+decaying normalization
HTGeometry/JumpProfileLevels.lean            arithJumpProfile, window laws, growth, negation
HTGeometry/WindowAssignmentStep.lean         Lemma 6 in full-chain form
HTGeometry/HelsonCharacterLSeries.lean       phaseChar, Euler product = Dirichlet series, logDeriv
HTGeometry/WeierstrassProductMultiplicity.lean   exact order of a Weierstrass product
RHTower/Sieve/{CharacterWindowStep,LadderCharacterRecursion,StageWindowRecursion,CharacterStacking}
```
