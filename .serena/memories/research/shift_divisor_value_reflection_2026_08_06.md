# Shift-divisor value reflection (corpus-owned)

The one-shift, pairwise, and iterated-forward-difference reflection laws are one divisor law.

## Primitive

`GaloisForLFunctions/HTGeometry/ShiftDivisorReflection.lean`

- `shiftDivisorValue (w : ℂ →₀ ℂ) (f : ℂ → ℂ) s = ∑ a, w a * f (s + a)`
- `reflectShiftDivisor c w` = divisor pushed along `a ↦ c - a` (involutive)
- `translateShiftDivisor τ w` = pushed along `a ↦ a + τ`

## The law

`shiftDivisorValue_signed_reflection`: if `f (2*c₀ - z) = ε * f z` then

    shiftDivisorValue w f (σ - s) = ε * shiftDivisorValue (reflectShiftDivisor (2*c₀ - σ) w) f s

So a translate family has an exact reflection law about `σ/2` **iff** its divisor is an eigenvector
of `reflectShiftDivisor (2*c₀ - σ)`; the eigenvalue multiplies `ε`.

Subsumes (machine-checked connectors exist):
- `forwardDifference_signed_reflection` / `iteratedForwardDifference_signed_reflection`
  (divisor `(δ_τ - δ_0)`; `reflectShiftDivisor_iteratedDifferenceDivisor` gives eigenvalue
  `(-1)^n` about `τs.sum`), via `iteratedForwardDifference_eq_shiftDivisorValue`
- `xiTransverseShiftRawLogDerivDefect_reflection` (point pair `δ_a - δ_0`)
- `xiPairwiseShiftRawLogDerivDifference_reflection` (`pairShiftDivisor a b`, anti-invariant about
  `(a+b)/2`) — the `if b ≤ a then … else …` endpoint-order bookkeeping disappears: the divisor law
  needs no order and no integrality.

## Laws with NO eigen hypothesis

- annihilator `shiftDivisorAnnihilator f` is a `Submodule ℂ (ℂ →₀ ℂ)` stable under translation and
  (for `ε ≠ 0`) under reflection
- canonical splitting `w = ½(w + refl w) + ½(w - refl w)`; hence
  `xiShiftDivisorLogDeriv_symm_add_antisymm`: every weighted `logDeriv xi` family splits into a
  reflection-fixed part and a part vanishing at `σ/2`.  This is the conceptual source of the
  half-cocycle centering in `XiPairwiseShiftValueReflection`.
- `iteratedDeriv_xiShiftDivisorValue_center_eq_zero`: for entire `xi`, all-order central jet parity.

## Arithmetic shadow

`GaloisForLFunctions/HTGeometry/ShiftDivisorLSeries.lean` +
`GaloisForLFunctions/RHTower/XiShiftDivisorPrimeSymbol.lean`

- symbol `shiftDivisorSymbol w n = ∑ a, w a * n^(-a)`; `LSeries_shiftDivisorStream` turns the
  twisted stream into `∑ a w a * LSeries f (s+a)`
- base identity proved here: `logDeriv xi s - logDeriv archFactor s = -LSeries Λ s` for `1 < s.re`
  (`logDeriv_xi_sub_archFactor_eq_neg_vonMangoldtLSeries`)
- `xiShiftDivisorPrimeValue_eq_lSeries`: corrected divisor value = `-LSeries (Λ · symbol w)`
- **dictionary**: divisor reflection about `(1-σ)/2` = symbol inversion `n^(-a) ↦ n^a` twisted by
  `n^(σ-1)` (`shiftDivisorSymbol_of_xiReflection_eigen`)

## Scope boundary

Divisor-side bookkeeping of the functional equation only.  It creates no positivity and is blind to
zero location; do not expect an RH criterion from it.  Use it to avoid re-proving reflection,
centering, and symbol laws for any new weighted family of completed-Xi translates.

All four modules build; `#print axioms` on every named law = `propext, Classical.choice, Quot.sound`.
Card: `docs/drafts/pipeline/3-formalized/shift-divisor-value-reflection.md`.
