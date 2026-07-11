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
The multivariate integral auxiliary matrix now returns both a nonzero kernel vector and its explicit
Siegel coefficient-house bound.  The shifted component family `G_ν`, its triangular derivative law,
algebraic-integer values, multipoint Schwarz estimate, and asymmetric norm-product discreteness
theorem are formalized.  Closed analytic and conjugate bounds reduce one exact extrapolation step to
a scalar inequality containing only `L`, `S`, `T`, the radius, the sample, and fixed invariants of the
relation.  The polynomial parameter family `L=t^(8n-2)`, `S=t^(4n)`, `q=t^(8n)`, `T=2q`, and
`R=t^(4n+1)` formally discharges the matrix dimension and positivity obligations, with at least twice
as many columns as rows.  The full matrix height and coefficient height have closed integer-power
majorants, so the real Siegel exponent is eliminated from the first-step growth budget.  At the first
new sample the exact remaining premise is
`(2/3)^(t^(12n)) * firstStepGrowthMajorant R c t < 1`, while every positive scale in the majorant is
at most `t^(12n-1)`.  The remaining core is to formalize that strict-scale eventual inequality,
iterate exact vanishing over the required shifted components and later samples, and close with the
final zero estimate.

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
