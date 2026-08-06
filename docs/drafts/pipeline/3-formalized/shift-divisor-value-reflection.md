# Shift-divisor value reflection for completed Xi

- **ID:** shift-divisor-value-reflection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** corpus audit of the `Xi*ValueReflection` / `Xi*ValueRelation` family
- **Statement:** For every finitely supported complex divisor `w` of shifts and every function with a
  signed reflection `f(2c₀ − z) = ε f(z)`, reflecting the observation coordinate about `σ/2` is
  exactly reflecting the divisor about `(2c₀ − σ)/2`, with the factor `ε`.

## Goal

The corpus carried a one-shift value reflection (`XiTransverseShiftPrimeDefectValueReflection`) and
a two-endpoint pairwise one (`XiPairwiseShiftValueReflection`), each with its own reflection centre,
its own archimedean cocycle, its own half-cocycle centering, and — in the pairwise case — an
endpoint-order hypothesis discharged by an `if b ≤ a` case split. Independently,
`ReflectionDifferenceFaces` carried the classical centre-shift-and-flip rule for iterated forward
differences. These are all the same statement about a divisor of shifts. Making the divisor the
primitive removes the order hypothesis, removes the integrality hypothesis, and exposes two laws that
hold with no eigen hypothesis at all.

## Gates

- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `lake build` green, `#print axioms` = `propext, Classical.choice, Quot.sound`
- [ ] 3 → 4  publication-ready

## The law

For `w : ℂ →₀ ℂ`, `shiftDivisorValue w f s = ∑ a w a · f (s + a)` and
`reflectShiftDivisor c w` is the divisor with `a ↦ c − a`. Then

    shiftDivisorValue w f (σ − s) = ε · shiftDivisorValue (reflectShiftDivisor (2c₀ − σ) w) f s.

Consequences:

- the value has an exact reflection law about `σ/2` iff the divisor is a reflection eigenvector, and
  the eigenvalue `η` multiplies the functional-equation sign;
- the annihilating divisors of `f` form a submodule stable under translation and (when `ε ≠ 0`)
  under reflection;
- every divisor splits canonically into invariant and anti-invariant parts, so *every* weighted
  completed-Xi family splits into a reflection-fixed piece and a piece vanishing at the centre —
  no eigen hypothesis needed;
- for entire `xi` the vanishing piece vanishes to all orders in the prescribed jet parity.

Arithmetic side: the divisor acts on Dirichlet coefficient streams by its symbol
`n ↦ ∑ a w a · n^(−a)`, and on the Euler half-plane the corrected completed-Xi divisor value is
minus the von Mangoldt L-series twisted by that symbol. Divisor reflection about `(1−σ)/2` is the
symbol inversion `n^(−a) ↦ n^a` twisted by `n^(σ−1)`.

## Lean

| Module | Content |
|---|---|
| `HTGeometry/ShiftDivisorReflection.lean` | divisor value, divisor reflection/translation, the signed reflection law, eigen corollaries, annihilator submodule, canonical splitting, iterated difference divisors, analyticity |
| `HTGeometry/ShiftDivisorLSeries.lean` | Dirichlet symbol, twisted stream, `LSeries_shiftDivisorStream`, symbol inversion under reflection |
| `RHTower/XiShiftDivisorValueReflection.lean` | completed-Xi and `logDeriv xi` instances, corrected value + cocycle + half-centering at divisor level, central jet parity, point/two-point connectors to the existing one-shift and pairwise theories |
| `RHTower/XiShiftDivisorPrimeSymbol.lean` | `logDeriv xi − logDeriv archFactor = −LSeries Λ` on `Re s > 1`, the divisor prime-symbol law, the reflection/inversion dictionary |
| `RHTower/XiShiftDivisorFaithful.lean` | symbol = translation character at frequency `log n`; trivial annihilator of the corrected completed-Xi value; injectivity of divisor ↦ value |

## Faithfulness

The Dirichlet symbol at `n` is the translation character of the divisor at the frequency `log n`
(`shiftDivisorSymbol_eq_translationChar`). Ray-complete translation faithfulness on the prime-log
rays (`euler_translation_faithful`) then gives: a divisor whose symbol vanishes at every prime power
is zero. Feeding the prime-symbol law and Dirichlet-series injectivity into this converts an
*analytic* value relation into the *algebraic* conclusion:

    (∀ s, 1 < Re s → ∑ a w a · (logDeriv xi (s+a) − logDeriv archFactor (s+a)) = 0) → w = 0

for divisors with shifts of nonnegative real part. So the corrected completed logarithmic derivative
satisfies no nontrivial linear difference relation with constant complex coefficients, and distinct
divisors give distinct values. The corpus already had the character-level faithfulness; the new
content is the bridge from the analytic value relation down to it.

In finite-family form (`completedPrimeSource_translate_independent`): distinct complex shifts of
nonnegative real part give linearly independent corrected completed logarithmic derivatives on the
Euler half-plane. The corpus proved the corresponding statement for distinct nonzero *natural*
shifts through differential independence
(`linearIndependent_xiTransverseShiftPrimeDefectRotatedFamily_iff`); the arithmetic route reproves it
and extends it to arbitrary complex shifts with `0 ≤ Re a`.

Named laws: `shiftDivisorValue_signed_reflection`, `shiftDivisorValue_reflection_of_eigen`,
`reflectShiftDivisor_mem_annihilator`, `reflectShiftDivisor_iteratedDifferenceDivisor`,
`iteratedForwardDifference_eq_shiftDivisorValue`, `xiShiftDivisorLogDeriv_reflection`,
`xiShiftDivisorLogDeriv_symm_add_antisymm`, `iteratedDeriv_xiShiftDivisorValue_center_eq_zero`,
`xiShiftDivisorCenteredPrimeValue_reflection`, `LSeries_shiftDivisorStream`,
`xiShiftDivisorPrimeValue_eq_lSeries`, `shiftDivisorSymbol_of_xiReflection_eigen`.

## What this does not do

It does not decide RH. The reflection law is divisor-side bookkeeping of the functional equation; it
creates no positivity and sees no zero location. Its value is that every future weighted family of
completed-Xi translates inherits its reflection law, its centering, and its Dirichlet symbol without
re-proving them, and that the arithmetic shadow of the reflection is now an explicit involution on
symbols.

## Log

- 2026-08-06 — created directly in 3-formalized; four modules built, axioms clean.
