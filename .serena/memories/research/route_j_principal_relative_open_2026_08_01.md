# Route J open: principal-relative Julia survivor

Route J is **open**, not retired. The unrenormalized Julia coherent-energy budget is a retired subroute, but its strongest survivor has no other explicit frontier owner and therefore remains Route J under the ownership rule.

Closed unconditionally:
- At (L_m=6\log m), the full bad Julia coherent energy has a source-uniform-in-scale lower floor (log m/20) and is unbounded along the sixth-power apertures.
- Zero-scale de-attenuation restores rank-one coherence rather than cancellation.
- Post-projection diagonal subtraction fails on a one-node packet.
- A nonnegative channel-linear relative current with zero pure-bad diagonal loses all good/bad mixed coupling.
- Universal negative-excursion dominance forces pure-bad diagonal weight at least one.
- Actual sixth-power block primes are pure-bad cells: good term zero and bad term strictly positive.
- Anchored Schur residual orientation fails in the source-faithful zero-scale limit.
- Existing Gamma--Julia endpoint Hilbert--Schmidt dressing cannot orient the undressed pure-bad excursion.
- Stronger global closure: in any symmetric pairwise-positive quadratic kernel, a zero bad diagonal annihilates the entire bad row/column. Any nonzero cross-block rescue incident to a cancelled bad diagonal is ambient-indefinite.

Exact open core:
Construct a source-defined pre-projection principal-relative Julia current satisfying
`negative completed first-clock excursion² ≤ relative capacity ≤ source-uniform constant`.
A quadratic survivor must be Krein/ambient-indefinite and prove nonnegativity only on the literal arithmetic source locus; a genuinely nonlinear source functional is the other unexcluded class. No other named route owns this survivor.

Live card:
- `docs/drafts/pipeline/1-in-progress/route-j-principal-relative-julia-current.md`

Formal modules:
- `formal/GaloisForLFunctions/HTGeometry/TwoChannelRelativeCapacityNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockJuliaPrincipalRelativeNoGo.lean`

Key global declarations:
- `pairwiseNonnegativeKernel_entry_eq_zero_of_diagonal_eq_zero`
- `not_pairwiseNonnegativeKernel_of_entry_ne_zero_of_diagonal_eq_zero`
- `pairwiseNonnegativeKernel_row_eq_zero_of_symmetric_of_diagonal_eq_zero`
- `pairwiseNonnegativeKernel_cross_eq_zero_of_symmetric_of_diagonal_eq_zero`

Verification on 2026-08-01:
direct Lean passed for both modules; exact leaf build passed; standard Lean axioms only; index regenerated. Lint failure was unrelated shared-worktree umbrella drift in four Möbius modules. No computation or full/umbrella build used.