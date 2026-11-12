# The camera retains exactly its boundary exterior mass

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** A78; replace uniform exterior gaps by an exact limiting obstruction.
- **Statement:** At fixed centre and width, the complete width-centered exterior
  norm mass converges, as lag grows, to its maximal-depth exterior contribution.

Let `b=zetaZeroWidth`, `δ≥1`, and let `s` be any finite core. Put
`wρ=mρ |FT(K_b,δ)(γρ-t)|`. The exterior mass at lag `δ+u` is exactly

`Σ_(ρ∉s) wρ exp((Reρ-1/2-b)u)`.

The weights are dominated by the summable multiplicity-weighted Lorentzian
kernel. Every exponent is nonpositive. Dominated convergence therefore gives

`mass(δ+u) → Σ_(ρ∉s, Reρ-1/2=b) wρ`.

No common depth deficit or ordinate gap is needed. Capturing every
maximal-depth zero makes the full exterior mass vanish, even when lower
depths accumulate at the maximum. Conversely, positive boundary exterior
mass cannot be suppressed by increasing lag.
Every tolerance strictly above that boundary mass eventually bounds all
finite exterior sums simultaneously, with one common lag threshold.

This is a fixed-centre limit. It supplies no rate uniform in height and
does not impose the logarithmic lag restriction needed by A78's prime estimate.

Sources: `TheDepthCenteredCameraPaysItsExteriorMass` supplies actual zero-width
centering and the summable Lorentzian majorant;
`TheRightSubstripsHaveSummableReciprocalZeros` supplies the boundary-projection
argument. Exact camera translation supplies the exponential factor.

Lean: `TheCameraRetainsItsBoundaryExteriorMass` passed `lake --old env lean`;
umbrella wired. Main declarations:

- `tendsto_widthCenteredExteriorMass`.
- `eventually_sum_widthCenteredCamera_exterior_lt_of_boundary_lt`.
- `tendsto_widthCenteredExteriorMass_zero_iff`.
- `tendsto_widthCenteredExteriorMass_zero_of_boundary_subset`.
