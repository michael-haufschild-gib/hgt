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
3. [x] Formalize the minimal algebraic relation and finite number-field containment reductions.
4. [x] Build the multivariate auxiliary matrix, obtain a nonzero integral Siegel-kernel vector with
   an explicit height bound, and prove that its exponential polynomial is nonzero while vanishing to
   the prescribed derivative order at every selected sample.
5. [ ] Prove extrapolation, determinant nonvanishing, and the final algebraic-norm contradiction.

## Open core

`[OPEN CORE]` The arbitrary finite-family step is genuine Baker theory.  Any counterexample has now
been reduced to a nonzero minimal relation of arity at least three inside one finite number field.
The multivariate integral auxiliary matrix, nonzero Siegel kernel, distinct-frequency theorem,
nonzero auxiliary exponential polynomial, and its initial high-order sample vanishing are formalized.
The remaining core starts at analytic extrapolation beyond the samples built into the matrix, then
passes through determinant nonvanishing and the algebraic-norm contradiction.

## Log

- 2026-07-10 -- removed two wrapper-only declarations; proved
  `bakerLinearIndependence_iff_algClosure`, `twoPrimeLog_algIndep_complex`, and
  `bakerLinearIndependence_of_card_le_two`.  Targeted build and formal lint pass.  Axiom audit reports
  only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-10 -- formalized the minimal-support reduction, canonical coefficient number field,
  simultaneous integral scaling, normalized pivot relation, multivariate auxiliary matrix, explicit
  Siegel-kernel construction, and the analytic bridge.  Integer independence of prime logarithms
  makes the auxiliary frequencies injective; Vandermonde independence makes the auxiliary function
  nonzero; the matrix kernel forces all derivatives below `T` to vanish at each of the `S` samples.
  Targeted Lean 4.30 build and formal lint pass, and every new declaration has only the standard
  `propext`, `Classical.choice`, and `Quot.sound` axiom footprint.
