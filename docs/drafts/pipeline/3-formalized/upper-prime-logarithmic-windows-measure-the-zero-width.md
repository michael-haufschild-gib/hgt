# Upper prime logarithmic windows measure the zero width

- **ID:** A73
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `σ≥0`, every zeta zero satisfies `Re ρ≤1/2+σ` iff one constant bounds `2 Re S(log p)` above by `K p^σ` on arbitrarily late prime windows `|log p−T|≤32 log(T+2)`. At `σ=0` this is RH.

## Proof

Apply the positive quartet filter to the negative normalized trace. The retained finite spectrum has a nonzero deepest mode and dense negative excursions. Logarithmic kernel moments bound leakage outside the observation window, so an upper trace bound on arbitrarily late windows excludes every deeper zero.

Prime gaps transfer a prime upper bound of exponent `σ` to the continuous trace at exponent `max(σ,a−1/3)`, where `a` is the current zero width. Apply the receiver at the zeta abscissa: `a≤max(σ,a−1/3)` forces `a≤σ`. The global absolute estimate gives the converse.

## Formalization

- `SurfaceOfSpecZ/ScaleLocality/UpperLogarithmicWindows.lean`: `zeta_negative_kernel_logarithmic_floor`, `zeta_re_le_of_upper_logarithmic_windows`.
- `SurfaceOfSpecZ/ScaleLocality/UpperPrimeLogarithmicWindows.lean`: `upper_prime_power_windows_transfer`, `zeta_re_le_iff_upper_prime_logarithmic_power_windows`, `riemannHypothesis_iff_upper_prime_logarithmic_windows`.
- Both direct Lean checks passed. Axiom audits omitted as requested.
- Both modules imported by `SurfaceOfSpecZ.lean`.
