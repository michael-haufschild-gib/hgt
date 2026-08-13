# Route R C29 formalized: closed graph-form coinvariant collapse

Module: `formal/GaloisForLFunctions/RHTower/RouteRClosedPositiveCoinvariantCompletionNoGo.lean`.

Unconditional Lean results:
- `ccmRationalMoritaHilbertLeftScale_fixed_eq_zero`: positive nontrivial rational dilation has no fixed vector on actual `CCMRationalMoritaHilbert = lp (ℚˣ → ℂ) 2`, by infinite orbit + square summability.
- `ccmRationalMoritaHilbertCoinvariantBoundary_denseRange`: actual `U_k - 1` has dense range, via injectivity of its adjoint.
- `ccmRationalMoritaHilbertPrimeCoinvariantBoundary_denseRange`: ordinary-prime specialization.
- `CCMRationalPrimeClosedPositiveCoinvariantCompletion.boundary_ambient_dense`: dense coefficient-faithful source embedding plus exact boundary intertwining derives dense source-boundary image; density is not assumed by actual interface.
- `RouteRClosedPositiveCoinvariantCompletion.form_eq_zero`: graph-norm completeness, exact graph norm identity, and diagonal boundary nullity force full sesquilinear form to vanish. Positivity/Hermitian symmetry are recorded but collapse is stronger and does not use them.
- `CCMRationalPrimeClosedPositiveCoinvariantCompletion.not_exists_retained_nonzero_atom`: no nonzero-energy retained atom exists.

Verification: `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.RouteRClosedPositiveCoinvariantCompletionNoGo` passed; `scripts/formal_tools.py lint` passed; all audited theorem axioms exactly `[propext, Classical.choice, Quot.sound]`. Module wired into `RHTower.lean`. C29 card status updated.

Research delta: closes all honest closed positive/graph-form homological completions as Route R producers. Remaining enlarged survivor must be signed or discontinuous before positive extraction, likely the C30 Hilbert–Schmidt relative-index scalar comparison. This is not RH and goal stays active.