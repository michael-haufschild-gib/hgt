# Local filtering of the exceptional prime current

- **Obstacle:** B13; cancellation in B134 for several top ordinates.
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** In the finite-layer world, every top ordinate can be recovered from finitely many normalized Gaussian-current readings inside any prescribed positive height window. A fixed linear combination, divided by that ordinate's unit phase, has a nonzero limit.

## Theorem and proof

Write the known normalized current as
`J(t) = -Σγ mγ exp(πγ/4) exp(iγ φ(t)) + o(1)`,
where `φ(t)=(at+log(t/2))/2` and the sum runs over distinct top ordinates.
Let `G` be the top zero copies. For any window length `L>0`, choose `h>0`
small enough that the nodes `zγ=exp(iγah/2)` are distinct for distinct
ordinates and `|G|h<L`. For a target `γ₀`, let
`P(X)=Π_{q∈G, Im ρq≠γ₀}(X−z_{Im ρq})`, retaining zero copies.
The extraction is

`Σj P.coeff(j) J(t+jh) / Wγ₀(t) → -mγ₀ P(zγ₀) ≠ 0`,

where `Wγ(t)=exp(πγ/4)exp(iγφ(t))`.

The logarithmic phase correction tends to zero under each fixed height shift.
Polynomial evaluation annihilates the other ordinates. This forces a
uniform positive normalized reading among the finite probes at every large
height, even when the unfiltered current cancels.

Indeed the quotient limit has positive norm. The triangle inequality bounds
the filtered reading by the sum of coefficient norms times the largest probe.
Hence some probe has a fixed positive normalized norm. The reference mode
grows uniformly beyond a height threshold whenever `a(β−σ)>π/2`.
Thus, for every `B`, every sufficiently late interval `[t,t+L]` contains
`u` with corrected-current norm at least `B`.

## Lean proof

`formal/GaloisForLFunctions/ExceptionalLayerTheory/LocalFiltersRecoverTheTopDivisor.lean`:

- `tendsto_ordinateWave_shift_ratio`
- `tendsto_polynomial_filtered_ordinateWave`
- `not_asymptoticAbscissaLaw_has_local_divisor_filters`
- `not_asymptoticAbscissaLaw_has_short_window_growth`

Direct `lake --old env lean` audit passed. All four transitive axiom lists
are exactly `propext`, `Classical.choice`, `Quot.sound`.

## Novelty boundary

The corpus proves a sharp envelope recurring with bounded gaps and pointwise
divergence for one top quartet. It also proves abstract Vandermonde window
bounds and nonvanishing oscillatory jets. The target here is exact recovery
of each actual top multiplicity from the complete infinite prime current,
with all probes confined to an arbitrarily short prescribed window.

## Remaining input for B13

An independent arithmetic upper estimate for these local current readings.
Filtering alone supplies no such estimate and excludes no zero.
