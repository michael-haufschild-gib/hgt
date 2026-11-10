# Absolute and signed exceptional prime windows

- **ID:** A76
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every `σ ≥ 0` and `0 ≤ δ < 1`, all zeta zeros satisfy `Re ρ ≤ 1/2 + σ` iff the absolute cubic-spline trace is bounded by `K p^σ` on arbitrarily late logarithmic prime windows after at most `C exp(δT)` omissions. The signed-deletion criterion has the same exact width on log-square windows. At `σ = 0`, both criteria are RH.

## Proof

The absolute logarithmic bound implies the existing one-sided floor; the width bound gives the converse with empty exceptional sets. For signed deletion, choose `δ < γ < β < 1`, `β > 7/12`. Prime avoidance and the trace Lipschitz bound transfer the observations to continuous windows. Complex deletion improves width `a` to `max(σ,a+β−1)`. Apply this at `a=Θ−1/2`; since `β<1`, the improvement forces `a≤σ`.

## Formalization

Namespace `GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality`:

- `ExceptionalAbsoluteWindows.lean`: `zeta_re_le_iff_abs_prime_logarithmic_power_windows_off_finset` and its RH specialization.
- `ExceptionalAbsolutePrimeWindowTransfer.lean`: `abs_prime_power_windows_transfer_off_finset`.
- `ExceptionalSignedWindows.lean`: `zeta_re_le_iff_abs_prime_logSquare_power_windows_signed_off_finset` and its RH specialization.
- Direct `lake --old env lean` audits passed for all three modules. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `GaloisForLFunctions/SurfaceOfSpecZ.lean`.
