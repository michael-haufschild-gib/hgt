# Positive Euler twins remain passive horizons

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean in progress
- **Obstacle:** O11, review 1511 §2.2.
- **Connection:** positive finite Euler modifications in the Selberg programme and the Schur criterion of arithmetic scattering.

## Statement

For every finite coefficient prefix and every `1/2 < σ < 1`, a positive, bounded, multiplicative Dirichlet series agreeing with ζ on that prefix has a reflection-symmetric completion with an off-line zero at real part σ, a globally contractive reduced scattering symbol, and unitary scattering on the imaginary axis. Its logarithmic Euler coefficient at the square of the modifying prime is negative.

## Proof [PROVED HERE]

Choose a prime p beyond the prefix. Set `r=p^σ`, `u=p^(1−σ)`, `A=r+u`; then `ru=p` and `r,u>1`. The existing Selberg construction gives

`F(s)=ζ(s)(1+A p^(−s)+p p^(−2s))`,

with positive bounded multiplicative coefficients. The balanced multiplier `E(s)=p^s+A+p^(1−s)` satisfies `E(1−s)=E(s)` and vanishes at `(log r+iπ)/log p`, whose real part is σ. Multiply ξ by E.

Writing `v=p^(−2w)`, its multiplier in the reduced scattering symbol is

`E(2w)/E(1+2w)=(1+A v+p v²)/(p+A v+v²)`.

The denominator factors as `(r+v)(u+v)` and is nonzero for `|v|≤1`. The identity `(r−1)(u−1)>0` gives `A<p+1`. The existing theorem `schur_bound_iff` with trace `−A` makes this quotient contractive on the disk. The difference-of-squares identity gives modulus one on its boundary. Multiplication by the actual modular scattering symbol preserves these properties. Nonvanishing of the denominator also gives holomorphy throughout the closed right half-plane.

The two local Euler roots are `−r,−u`. The existing logarithmic expansion identifies the coefficient at `p²` as `(1−r²−u²)/2`, which is negative because `r,u>1`. This coefficient is an explicit arithmetic obstruction independent of zero estimates. Ordinary coefficient positivity does not supply it.

## No-go closure

- **Rejected route:** add ordinary nonnegative multiplicative coefficients to the physical positivity laws to distinguish ζ.
- **Positive survivor:** the actual logarithmic coefficient at the first repeated prime is negative for every constructed countermodel; the ordinary coefficients remain positive at every integer.
- **Known inputs:** `PositiveFiniteEulerCoefficients`, `PositiveFiniteEulerCompletion`, `PositiveFiniteEulerZeros`, `PositiveFiniteEulerProduct`, `schur_bound_iff`, modular scattering contractivity and unitarity.
- **Lean:** `BlackHoleRingdown/ThePositiveEulerTwinsArePassive.lean`; full theorem and audits pending.
- **Count:** unaccepted until formalization and significance review. Axiom checks skipped at user request.
