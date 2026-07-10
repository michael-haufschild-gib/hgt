# Baker linear-independence Prop discharge in RHTower

- **ID:** rhtower-baker-linear-independence-discharge
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), `[SEARCH]` / `[BRIDGE]`
- **Statement:** Prove `GaloisForLFunctions.RHTower.BakerLinearIndependence` in Lean and remove that
  Prop premise from its concrete RHTower consumers.

## Goal

Formalize the algebraic-coefficient linear independence of logarithms of distinct primes.  Preserve
the existing project interface while proving `bakerLinearIndependence_holds :
BakerLinearIndependence`; do not replace it with a stronger unproved interface or wrapper theorem.

## Gates

- [x] 0 -> 1 in-progress: exact interface and consumers audited; no existing Lean formalization was
  found in Mathlib or the primary-source search.
- [ ] 1 -> 2 fully-proven: the several-variable auxiliary-function, extrapolation, and zero-estimate
  chain closes the exact prime-log statement.
- [ ] 2 -> 3 formalized: `bakerLinearIndependence_holds` builds; all concrete `hB` premises are
  removed; axiom audit and formal lint pass.

## Foundation order

1. [x] Discharge the two-prime algebraic-coefficient fragment from the now-formalized
   Gelfond--Schneider theorem.
2. [x] Normalize the interface as linear independence over `algebraicClosure ℚ ℂ`, with exact transfer
   back to the current coefficient-family encoding.
3. [ ] Formalize the minimal algebraic relation and finite number-field containment reductions.
4. [ ] Build the multivariate auxiliary polynomial with explicit height bounds.
5. [ ] Prove extrapolation, determinant nonvanishing, and the final algebraic-norm contradiction.

## Open core

`[OPEN CORE]` The arbitrary finite-family step is genuine Baker theory.  The exact interface now has
an unconditional proof for cardinality at most two, so any counterexample has arity at least three.
The next proof object is a minimal-support algebraic relation contained in one finite number field;
that is the input shape for the multivariate auxiliary polynomial.

## Log

- 2026-07-10 -- removed two wrapper-only declarations; proved
  `bakerLinearIndependence_iff_algClosure`, `twoPrimeLog_algIndep_complex`, and
  `bakerLinearIndependence_of_card_le_two`.  Targeted build and formal lint pass.  Axiom audit reports
  only `propext`, `Classical.choice`, and `Quot.sound`.
