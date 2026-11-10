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

uniformly for `M(T)≤T^κ`, with `0≤κ<σ(2σ−1)/2`.

Use the existing superlinear zeta truncation `N=ceil(T^(σ+1/2))`.
The sharp polynomial mean error is bounded by
`C M² N^(2−2σ)/T` times coefficient energy. The exponent is
`2κ−σ(2σ−1)<0`. Minkowski bounds the coefficient tail by
`M N^(1/2−σ)` times coefficient energy; this also tends to zero in
the stated range. At the limiting exponent
`κ₀=σ(2σ−1)/2`, multiplication by `T^κ₀` leaves exponent `−1/2`
in the pole term, `−σ` in the half-endpoint term, and
`−σ−(σ−1/2)j` in the `j`-th derivative term. For remainder order
`k=2m+2`, its exponent is `1/2−(σ−1/2)k`; choose
`k>1/(2σ−1)`. Thus the Euler–Maclaurin error also survives the
growing weight. Cauchy–Schwarz and the unweighted Carlson mean control
the passage from uniform truncation error to squared means.

The fixed-resonator theorem is
`TailArithmeticOfThePrimeOrbit/TheResonatorMeanOfZeta.lean`.
Actual-zeta truncation and finite polynomial estimates are in
`RHTower/ZetaSuperlinearCutoff.lean` and
`RHTower/ZetaDirichletBandMeanSquare.lean`.
The uniform growing theorem remains unformalized.
