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
- [x] 1 -> 2 fully-proven: the several-variable auxiliary-function, extrapolation, and zero-estimate
  chain closes the exact prime-log statement.
- [x] 2 -> 3 formalized: `bakerLinearIndependence_holds` builds; all concrete `hB` premises are
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
5. [x] Prove strict-scale extrapolation uniformly over a shifted-component box and a growing sample
   window, with all scalar smallness premises discharged.
6. [x] Iterate the enlarged exact-zero box until the main auxiliary function has at least as many
   consecutive zero samples as columns, then close by the ordinary Vandermonde zero estimate.

## Closed core

`[PROVEN]` The arbitrary finite-family step is formalized.  The parameter is restricted to a
cofinal divisible subfamily, so every prescribed multiplicity halving is exact.  At stage `k`, the
sample interval grows by `t/4`, the component cutoff halves, and the closed positive growth budget
has scale `exp(C*t^(12n+k))`; Schwarz decay has the strictly larger scale
`(2/3)^(u^(12n+k+1))`.  A finite-filter intersection makes all stages simultaneous.

After `8*n*(n-1)` stages, Lean proves the consecutive sample count is at least the number `L^n` of
auxiliary coefficients and the remaining component cutoff is positive.  The zeroth component is
the original auxiliary exponential polynomial.  Its natural samples are a Vandermonde system in
the distinct positive nodes `exp(frequency m)`, so the terminal kernel forces the Siegel vector to
be zero, contradicting its construction.  This proves `bakerLinearIndependence_holds` and the
unconditional real-additive and multiplicative consumer interfaces.

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
- 2026-07-11 -- proved the eventual strict-scale inequality and strengthened the first exact zero to
  uniform vanishing of the whole lower shifted-component box throughout the first quarter of the
  Schwarz disc.  Corrected the width to `L=2*t^(8n-4)`: columns now equal twice the initial rows, and
  the extrapolated sample/shift row count eventually exceeds the columns.  Exact component zeros are
  bridged back to an enlarged matrix kernel.  Replaced support deletion by genuine global
  minimal-arity reduction; normalized coefficient ratios and direction coordinates are now proved
  real.  The targeted `BakerParameters` build, generated-index check, formal lint, and axiom audit
  pass; the new declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-11 -- closed long extrapolation in `BakerIteration.lean`.  A cofinal power-of-two parameter
  subfamily supports simultaneous finite iteration with decreasing multiplicity; the terminal
  sample count dominates `L^n`, the remaining cutoff is positive, and an ordinary Vandermonde
  argument forces the nonzero Siegel vector to vanish.  Proved `bakerLinearIndependence_holds`,
  premise-free `primeLog_algIndep` and `baker_prime_mult_indep`.  The targeted Lean
  4.30 build and axiom audit pass; only `propext`, `Classical.choice`, and `Quot.sound` occur.
