# Growing resonator means below the Kronecker scale

- **ID:** growing-resonator-means-below-the-kronecker-scale
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A37.
- **Statement:** Extend the actual-zeta resonator mean uniformly to polynomially growing finite resonators on `1/2<σ<1`.

## Candidate range

For `R_T(t)=Σ_{m≤M(T)} r_T(m)m^{it}` and
`c_T(k)=Σ_{m|k}r_T(m)(k/m)^(−σ)`, seek

`T⁻¹∫_T^{2T}|R_T(t)ζ(σ+it)|²dt − Σ_k|c_T(k)|²
 = o(Σ_m|r_T(m)|²)`

uniformly for `M(T)≤T^κ`, with `0≤κ<2σ−1`.

Put `E=Σ_m|r_T(m)|²`, and truncate the zeta factor at `N=ceil(T^a)`,
where `a>1` is close to one. Divisor-wise Cauchy–Schwarz and
`d(k)≤Cε k^ε` give

- `Σ_k|c_T(k)|² ≪ M^ε E`;
- `Σ_k|c_T(k)−c_T^N(k)|² ≪ M^ε E N^(1+ε−2σ)`;
- `Σ_k k|c_T^N(k)|² ≪ M^(1+ε) E (N^(2+ε−2σ)+1)`.

The diagonal discrepancy is therefore
`O(M^ε E N^((1+ε−2σ)/2))`. The sharp Hilbert mean-value estimate
has error at most `208/T` times the third sum. Choose `a>1`, `ε>0`
so that

`κ(1+ε)+a(2−2σ+ε)−1<0`,
`κε+a(1−2σ+ε)/2<0`,
`κ+a(1−σ)−1<0`.

These inequalities hold for sufficiently small positive `a−1,ε` because
`κ<2σ−1`. The last inequality controls the Euler–Maclaurin pole term
after multiplication by `M`. Every derivative correction has exponent
`κ−aσ−(a−1)j<0`; choose remainder order `k=2m+2` with
`κ+a(1−σ)−(a−1)k<0`. Hence the uniform truncation error `e(T)`
satisfies `M e(T)→0`. Since `|R_T|²≤M E`, Cauchy–Schwarz and the
unweighted Carlson mean transfer this estimate to the squared means.

The fixed-resonator theorem is
`TailArithmeticOfThePrimeOrbit/TheResonatorMeanOfZeta.lean`.
Actual-zeta truncation and finite polynomial estimates are in
`RHTower/ZetaSuperlinearCutoff.lean` and
`RHTower/ZetaDirichletBandMeanSquare.lean`.
The divisor estimate is `RHTower.Sieve.card_divisors_le_rpow` in
`RHTower/Sieve/DivisorBound.lean`.
The uniform growing theorem remains unformalized.
