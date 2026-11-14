# Large critical multiplicity requires local off-line compensation

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For each `c>0`, a sufficiently high critical zero of multiplicity at least `c log T` forces `Ω_c(log T)` off-line zero copies within a fixed height distance and a fixed positive horizontal depth.
- **Dependencies:** The unconditional `RiemannGaussian.gaussianArithmeticExplicitFormula_eq_canonical`, the quasi-RH strip bound, and `RHTower.lorentzMass_le_log`. No new contour identity is required.

Put `h=min(1,c√π)` and `A=exp(9/(64h²))`. The Gaussian test at
horizontal depth `δ` and vertical offset `u` has real part

`exp((δ²−u²)/h²) cos(2δu/h²)`.

On the strip `|δ|≤3/8`, its absolute value is at most `A exp(−u²/h²)`.
The explicit formula gives main term `h/(2√π) log T ≤ (c/2)log T`:
the digamma density has logarithmic coefficient one, its Gaussian convolution
has mass `h√π`, and the prime series is uniformly bounded in the center.
An atom of mass `c log T` therefore requires negative contributions from
off-line copies. A negative contribution satisfies `|δu|>πh²/4`.

With `C=8(|xiLineTwoLogDerivConstant|+2)`, set

`R=1+2πh²/3+h√(2 log(1+16AC/c))`, `d=πh²/(4R)`.

Since `h≤1`, `(1+u²)exp(−u²/h²)≤2exp(−u²/(2h²))`.
Also `lorentzMass(T)≤C log T` for sufficiently large `T`.
Thus the contribution from `|u|>R` is at most `(c/8)log T`.
The Gaussian sum is eventually at most `(5c/8)log T`, leaving negative mass
at least `(3c/8)log T` before removing that tail. The remaining negative mass gives at least
`(c/(4A))log T` copies with `|u|≤R` and `|δ|≥d`.

## Lean declarations

`GaloisForLFunctions.SquareRootThreshold.GaussianLocalCompensation` proves:

- `exists_gaussian_compensating_copies`: the exact finite compensation inequality,
  using actual zero copies with analytic multiplicities.
- `exists_local_offLine_compensation`: for every `c>0`, there are positive
  `R,d,κ` and `T₀≥8` such that every critical zero at height `T≥T₀` with
  `m≥c log T` forces a finite set of at least `κ log T` actual copies satisfying
  `|Imρ−T|≤R` and `|Reρ−1/2|≥d`.

Supporting modules in `GaloisForLFunctions.ConjugateDiagonalGeometry`:
`GaussianLogarithmicAsymptotic`, `GaussianCompensationKernel`, and
`GaussianZeroCopies`. They establish the arithmetic Gaussian asymptotic,
explicit tail and depth estimates, multiplicity-preserving transport to the
xi divisor, and the canonical zero-sum coefficient `sqrt(π/ε)/(2π)`.

Both final statements pass Lean. Transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.

This is a necessary compensation law, not a contradiction: exclusion of the
forced off-line configurations remains unproved. B47 remains open.
