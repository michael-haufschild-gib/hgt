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
5. [x] Prove strict-scale extrapolation uniformly over a shifted-component box and a growing sample
   window, with all scalar smallness premises discharged.
6. [ ] Iterate the enlarged exact-zero box until the main auxiliary function has at least as many
   consecutive zero samples as columns, then close by the ordinary Vandermonde zero estimate.

## Open core

`[OPEN CORE]` The arbitrary finite-family step is genuine Baker theory.  A counterexample is now
reduced globally to minimal arity: every nontrivial algebraic relation on its prime family has full
support.  Complex conjugation therefore fixes every normalized coefficient ratio, and the
scale-free eliminated direction coordinates are real.  The multivariate integral auxiliary matrix,
explicit Siegel coefficient bound, shifted components `G_ν`, triangular derivative law,
algebraic-integer values, multipoint Schwarz estimate, and asymmetric norm-product discreteness
theorem are formalized.

The corrected polynomial family is `L=2*t^(8n-4)`, `S=t^(4n)`, `q=t^(8n)`, `T=2q`, and
`R=t^(4n+1)`.  Lean proves the column count is exactly twice the initial row count.  Every analytic,
height, sample, and shifted-direction contribution is bounded by a fixed exponential at scale
`t^(12n-1)`, while Schwarz decay occurs at scale `q*S=t^(12n)`.  Consequently one sufficiently large
parameter produces a nonzero kernel whose entire lower `q`-box of components vanishes at every
natural sample in the first quarter of the disc.  These zeros are repackaged as a kernel for the
enlarged matrix with `quarterSampleCount * q^(n-1)` rows, and Lean proves that count eventually
exceeds `L^n`.

The named remaining core is long extrapolation with decreasing multiplicity: reuse each enlarged
kernel as the next interpolation set, grow the consecutive sample range by a fixed fraction of `t`,
and reduce the component cutoff by a fixed factor.  After finitely many stages depending only on
`n`, the main component has at least `L^n` consecutive integer zeros.  The existing one-variable
Vandermonde estimate then contradicts the nonzero Siegel vector.  This avoids importing a stronger
Philippon zero lemma and uses the classical longer-extrapolation route with the already formalized
weak zero estimate.

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
