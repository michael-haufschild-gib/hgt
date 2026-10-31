# Undilated prime heads have a uniform torsion finite part

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Q1/O1](../1-in-progress/three-frontier-questions-full-solutions.md);
  [Gram plateau](harmonic-gram-remainders-have-a-logarithmic-plateau.md).

For a real conductor packet through `Q`, write `M=sum a_m²`,
`G(Y)=sum_(n≤Y)(sum_m a_m u_m(n))²/n`, and let `T` be its normalized
torsion pairing. Put `A(N)=sum_(k≤N)Lambda(k)/k`. For all `Q,N≥2`,

`|2 sum_(k≤N)Lambda(k)G(floor(N/k))/(k log N)`
`−[2 sum_(n≤N)log(n)/n]/log N · M + 2A(N)T/log N|`
`≤256(1+log Q)² M/log N`.

The scalar term is exact: divisor summation gives
`sum_(k≤N)Lambda(k)H_(floor(N/k))/k=sum_(n≤N)log(n)/n`.

Consequently, one absolute `C>0` gives

`|2 sum_(k≤N)Lambda(k)G(floor(N/k))/(k log N)−log N·M+2T|`
`≤C(1+log Q)² M/log N`.

## Proof

Write `R(Y)=G(Y)−H_Y M+T` and split at `K=floor(N/Q²)`.
For `k≤K`, the quadratic remainder gives
`|R(floor(N/k))|≤Q²kM/N`; Chebyshev summation costs at most `7M`.
For `k>K`, use the logarithmic plateau. The elementary bound
`|A(n)−log n|≤log4+4≤7` and logarithmic roundoff give
`A(N)−A(K)≤2log Q+15`, also when `K=0`.
The plateau is at most `8(1+log Q)` and this tail mass is at most
`15(1+log Q)`. The weighted remainder is at most
`127(1+log Q)² M`; multiplication by `2/log N` gives the stated bound.

For the second form, let `C_H` be the sum of the absolute logarithmic
harmonic increments. Its summability is already proved in
`HTGeometry/LogHarmonicFinitePart.lean`, and
`|sum log(n)/n−(log N)²/2|≤C_H`.
The Mertens correction costs at most `14|T|/log N` and
`|T|≤7(1+log Q)M`. Hence `C=354+2C_H` suffices.

This controls the full undilated component on growing packets. The actual
dilated correction, Gamma, pole, and successor-shell comparison remain
separate.

## Lean

`SuccessorShellArithmetic.Conductor.PrimeConductorUndilatedNorm` proves
`primeHead_harmonic_convolution`,
`abs_primeConductorUndilatedPacket_remainder`, and
`exists_abs_primeConductorUndilatedPacket_finitePart_le`.
Direct production audit passed. All three dependency closures contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
