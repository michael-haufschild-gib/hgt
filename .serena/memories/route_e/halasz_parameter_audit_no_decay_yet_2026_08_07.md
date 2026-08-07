# Halász chain: parameter audit says NO decay yet (2026-08-07)

The assembled chain (`mem:route_e/halasz_fully_explicit_2026_08_07`) is unconditional and green, but
costing the parameters shows it does NOT give decay. Two independent losses:

## (1) The covering step loses a factor `T·log z`

`volume_largeValues_le` permits one exceptional window PER CELL of length `π/log z`, so the
large-value set has measure `≍ T·δ` over `[-T,T]` — a fixed proportion of the range. Times trivial size
(`≍ log N`) times kernel size (`≍ N`) gives `≍ N log N T δ`, never `o(N)`.

**Fix, corpus-available:** the `π/log z` restriction comes from `HalaszWindow.sq_sub_mul_logSqWeight_le`
(it uses `1 − cos x ≥ x²/π²`, hence `|(t−u) log p| ≤ π`). GLOBAL uniqueness instead follows from
`DistanceTriangle` + an UPPER bound on `∑_{p≤z} cos(v log p)/p`, i.e. an upper bound on
`|ζ(1+1/log z+iv)|` — `Sieve/ZetaOneLineBound.lean`. Then
`D(n^{it},n^{iu})² ≥ log log z − log log(2+|t−u|) − O(1)`, so `2δ ≥ √(log log z − log log T − O(1))`
forces uniqueness over the WHOLE range, and the exceptional set is a single window of width
`O(δ/log z)`.

## (2) The kernel constant must be explicit in `H`

`exists_bound_mellin_smoothWeight_line` gives `∃ C, ‖W‖ ≤ C(1+y²)⁻¹`. The entire `1/log N` saving of
Halász's theorem lives in the `H`-dependence: the second-order bound is `‖W(σ+iy)‖ ≲ (N+H)^σ/(H y²)`, so
`∫_ℝ‖W‖ ≍ N/H`, and `H = N/log N` is what turns `exp(P(σ)) ≍ log N` into `O(1)`. An existential constant
cannot express that. `SmoothWeightMellin.norm_mellin_smoothWeight_mul_eq` is the exact identity to
extract the explicit constant from.

## Discipline

Do NOT claim a Möbius or general decay bound from this chain until both upgrades land. The chain as it
stands is a fully explicit unconditional ESTIMATE; the arithmetic does not close.
