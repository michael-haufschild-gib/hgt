# A prescribed radius for the density-matched window model

- **ID:** A89
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

For a prescribed nonnegative radius `R(T)=o(log T)`, construct a tempered
reflection-symmetric configuration with logarithmic local zero count,
unattained positive top depth, and arbitrarily late windows of radius `R(T)`
on which the spline trace exceeds every fixed floor.

## Existing result and obstruction

`SubLogarithmicWindowsMissTheMinimalFace` constructs its own radius,
equal to `k+1` at the recursively chosen centres. It does not establish
the prescribed-radius quantifier.

Its binomial block has degree `m₀=4ΓR`, coefficient cost `64^m₀`,
and phase-splitting error proportional to `1/T`. The existing error bound
therefore requires `log T` to dominate `ΓR`. The sufficient local-count
condition separately requires `log Γ` to dominate `R`. These sufficient
conditions are incompatible with many sub-logarithmic prescriptions,
including `R(T)=sqrt(log T)` for all sufficiently large `T`.

This is a limitation of the present construction, not a counterexample
to the target. A new block construction or sharper phase-error estimate
is required; enlarging the recursive centres alone is insufficient.

## Lean status

Endogenous radius: `SubLogarithmicWindowsMissTheMinimalFace`. Prescribed radius up to
`(C/256) log log T`: `DoubleLogarithmicWindowsMissTheMinimalFace`. Beyond: open.

## Where the construction stops (2026-11-11)

Level `k` uses `P_{m₀}(z)`, `z = e^{iδv}`, `δ = 1/(4R)`, frequencies `dδ ∈ [Γ, 2Γ]`, phase-split
pairs: `8R` zeros per unit height at height `Γ`. Class `𝒵` allows `C log(Γ+3)`, so
`Γ ≥ e^{8R/C}`. The coefficients reach `64^{m₀}`, `m₀ = 4ΓR`, against a phase precision `R/T`:
`log T ≳ ΓR`. Together `R e^{8R/C} ≲ log T`, i.e. `R ≲ (C/8) log log T`.

Both costs are intrinsic to one level of this kind. Positivity on `|v| ≤ R` with frequencies
`≥ Γ` needs signed coefficients of size `≥ exp(c(ΓR)^α)` (test the window against a Gevrey bump:
`|φ̂(γR)| ≤ exp(−c(γR)^α)`); nonnegative coefficients give no positivity beyond `|θ| ~ 1/m₀`.
Frequencies at density `≤ C log t` approximate on a window of length `2R` only where
`C log t ≳ R` (Landau density), so `Γ ≳ e^{cR}`.

**Survivor (formalized).** One configuration serves every prescribed `R(T) ≤ (C/256) log log T`:
`3-formalized/double-logarithmic-windows-miss-the-minimal-face.md`. Open: `log log T ≪ R(T) = o(log T)`.

