# Route J open: principal-relative Julia survivor

Route J is **open**, not retired. The unrenormalized Julia coherent-energy budget is a retired subroute, but its strongest survivor has no other explicit frontier owner and therefore remains Route J under the ownership rule.

Closed unconditionally:
- At (L_m=6\log m), the full bad Julia coherent energy has a source-uniform-in-scale lower floor (log m/20) and is unbounded along sixth-power apertures.
- Zero-scale de-attenuation restores rank-one coherence rather than cancellation.
- Post-projection diagonal subtraction fails on a one-node packet.
- A nonnegative channel-linear relative current with zero pure-bad diagonal loses all good/bad mixed coupling.
- Universal negative-excursion dominance forces pure-bad diagonal weight at least one.
- Actual sixth-power block primes are pure-bad cells: good term zero and bad term strictly positive.
- Anchored Schur residual orientation fails in the source-faithful zero-scale limit.
- Existing Gamma--Julia endpoint Hilbert--Schmidt dressing cannot orient the undressed pure-bad excursion.
- In any symmetric pairwise-positive quadratic kernel, a zero bad diagonal annihilates the entire bad row/column. Any nonzero cross-block rescue incident to a cancelled bad diagonal is ambient-indefinite.
- Canonical diagonal-null positive-Julia off-diagonal current is copositive but unbounded under every zero-scale cofinal law. Exact source bounds: block bad mass at least (m^2/24), square diagonal at most (65(\log m)^2), ordered pair mass at least (m^4/576-65(\log m)^2), and all block log separations at most 2. Hence Julia off-diagonal energy is eventually at least half that quartic-minus-log-square bound.
- Existing exact calibrated Julia--Euler source current is antisymmetric. It remains meaningful as an exterior two-form, but every finite-packet scalar quadratic energy is identically zero. It cannot be Route J's capacity.

Exact open core:
Construct a source-defined pre-projection principal-relative Julia current satisfying
`negative completed first-clock excursion² ≤ relative capacity ≤ source-uniform constant`.
A quadratic survivor must be a nonzero symmetric sign-changing completed prime--Gamma/co-Poisson Krein current, cancel both bad diagonal and the quartic positive-Julia off-diagonal floor, prove nonnegativity only on literal arithmetic source locus, and retain excursion orientation. A genuinely nonlinear source functional is the other unexcluded class. No other named route owns this survivor.

Live card:
- `docs/drafts/pipeline/1-in-progress/route-j-principal-relative-julia-current.md`

Formal modules:
- `formal/GaloisForLFunctions/HTGeometry/TwoChannelRelativeCapacityNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockJuliaPrincipalRelativeNoGo.lean`

Key new declarations:
- `pairwiseNonnegativeKernel_entry_eq_zero_of_diagonal_eq_zero`
- `pairwiseNonnegativeKernel_row_eq_zero_of_symmetric_of_diagonal_eq_zero`
- `finsetOffDiagonalKernelEnergy_one`
- `kappa_mul_pairMass_le_finsetOffDiagonalKernelEnergy`
- `finsetOffDiagonalKernelEnergy_eq_zero_of_antisymmetric`
- `ccmFirstClockJuliaSixthPower_block_badMass_lower`
- `ccmFirstClockJuliaSixthPower_block_badDiagonal_upper`
- `ccmFirstClockJuliaSixthPower_block_badPairMass_lower`
- `ccmFirstClockJuliaSixthPowerBlockOffDiagonalEnergy_unbounded_of_scale_tendsto_zero`
- `gammaSewnMobiusJuliaCalibratedEulerExteriorCell_swap`
- `gammaSewnMobiusJuliaCalibratedEulerExteriorScalarEnergy_eq_zero`

Verification on 2026-08-01:
direct Lean passed for both modules; exact leaf builds passed; axiom audit found only `propext`, `Classical.choice`, and `Quot.sound`; index regenerated. Lint had no Route J error and failed only on unrelated shared-worktree umbrella gaps `CCMProlateRayleighGroundLock`, `JetPolyLineDatum`, and `StdRatLineRigidity`. No numerical computation or full/umbrella build used.