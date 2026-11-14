# Large critical multiplicity requires local off-line compensation

- **Stage:** 1-in-progress
- **Type:** Paper derivation; not Lean-certified
- **Target:** For each `c>0`, a sufficiently high critical zero of multiplicity at least `c log T` forces `Ω_c(log T)` off-line zero copies within a fixed height distance and a fixed positive horizontal depth.
- **Dependency:** The fixed-line logarithmic-derivative and contour-exhaustion inputs in `zeta-sech-strip-multiplicity.md`. Their required quasi-RH split module lacks compiled dependencies; no final zeta theorem is certified.

Put `h=min(1,c√π)` and `A=exp(9/(64h²))`. The Gaussian test at
horizontal depth `δ` and vertical offset `u` has real part

`exp((δ²−u²)/h²) cos(2δu/h²)`.

On the strip `|δ|≤3/8`, its absolute value is at most `A exp(−u²/h²)`.
The proposed contour asymptotic has main term `h/(2√π) log T ≤ (c/2)log T`.
An atom of mass `c log T` therefore requires negative contributions from
off-line copies. A negative contribution satisfies `|δu|>πh²/4`.

With `C=8(|xiLineTwoLogDerivConstant|+2)`, set

`R=1+2πh²/3+h√(2 log(1+16AC/c))`, `d=πh²/(4R)`.

The Lorentz-mass tail estimate would bound the contribution from `|u|>R`
by `(c/8)log T`. The remaining negative mass gives at least
`(c/(4A))log T` copies with `|u|≤R` and `|δ|≥d`.
The Gaussian algebra alone does not discharge the required contour asymptotic
or its uniform tail bound. Those steps remain unformalized.
