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
The shifted component family `G_ν`, its triangular derivative law, its canonical algebraic-integer
values at natural samples, the explicit conjugate house bound, and the asymmetric norm-product
discreteness theorem are also formalized.  Thus the arithmetic half of extrapolation is closed: a
sufficiently small distinguished value now becomes an exact new zero without any Prop interface.
The remaining core is the sharp analytic small-value estimate and its iteration beyond the samples
built into the matrix, followed by the final zero estimate.

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
- 2026-07-10 -- added the local multiplicity upper bound for the nonzero auxiliary function; named
  Baker's shifted component functions; proved the triangular derivative/shift identity and the
  propagation of kernel equations to component derivatives.  Every component value at a natural
  sample is now the distinguished embedding of a canonical algebraic integer.  Proved the exact
  asymmetric discreteness criterion using the field norm: distinguished norm times the remaining
  conjugate house power below one forces the component to vanish.  The explicit finite house bound
  is wired into that criterion.  Targeted build, formal lint, and axiom audit pass.
