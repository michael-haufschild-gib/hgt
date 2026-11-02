# Exact height law and cusp escape of normalized resonant states

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Parent:** [arithmetic measure rigidity](../1-in-progress/resonant-state-arithmetic-measure-rigidity.md).

## Statement

For an actual resonance `u`, put `κ=-2 Re u∈(0,1)` and let `ν_(u,Y)` be the
height marginal of `|Λ^Y E_u|² dμ / ||Λ^Y E_u||²`, for `Y≥1`.
Conjectured exact probability-measure identity:

`ν_(u,Y) = Y^(-κ) ν_(u,1) + κ Y^(-κ) 1_(1,Y](y) y^(κ-1) dy`.

After rescaling height by `Y`, this would give the uniform bound

`|∫ f(y/Y) dν_(u,Y) − ∫_0^1 f(t) κ t^(κ-1) dt| ≤ 2 ||f||∞ Y^(-κ)`

for bounded measurable `f`. The limiting probability density is positive for
every negative rate and explicitly retains that rate.

A related local bound should hold for every `1≤C≤Y`:

`ν_(u,Y)((0,C]) ≤ (C/Y)^κ`.

Hence cutoffs tending to infinity lose all mass on fixed-height sets whenever
`κ` stays bounded away from zero, uniformly in the spectral ordinate.

## Candidate proof

On `(1,Y]`, the difference `Λ^Y E_u−Λ¹ E_u` is exactly the constant Weyl mode
`B(u)y^(1/2-u)`. The cutoff-one state has zero constant Fourier mode there.
Thus the cross term integrates to zero against every height test. Below one
and above `Y`, the two truncations agree. The established Maass–Selberg norm
`|B(u)|²Y^κ/κ` gives the proposed mixture.

After height rescaling, the missing part of `κt^(κ-1)dt` on `(0,1/Y]` and the
remaining cutoff-one component both have mass `Y^(-κ)`. This yields the bound.
For the local estimate, truncations at `C` and `Y` agree below height `C`;
compare local mass with the full norm at `C`.

## Dependencies and boundary

Existing inputs: `cutoff_pairing_of_le`, `setIntegral_band_mul_tail_eq_zero`,
`setIntegral_fd_height`, `integral_norm_sq_of_msA_eq_zero`, and nonvanishing of
`msB u`. The measure identity, bounded-measurable test extension, normalization,
and uniform error still require Lean proofs.

This tests tightness and constructs a positive limiting measure. It does not
establish Hecke recurrence, entropy, or critical-line selection.
