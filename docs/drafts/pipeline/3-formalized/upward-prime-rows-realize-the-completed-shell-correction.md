# Upward prime rows realize the completed shell correction

- **ID:** upward-prime-rows-realize-the-completed-shell-correction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

For every fixed `c>0`, conductor `m≥1`, and nonzero compact `C²` unit profile,
put `g_N=atomDilate φ (c/N)`, `M_N=∫g_N²`, and `r_m(j)=c_m(j)/√j`. Then

`‖[upwardPrimeRow(g_N,N,r_m)/M_N − shellCorrection(φ,c,m) r_m]/√log N‖₂ → 0`.

The row is the literal infinite prime-power sum with exact ratios removed.
This identifies its signed near-source action. Complete Weil positivity is
not asserted here.

## Proof [PROVED HERE]

Put `M=∫φ²`, `G=φ⋆φ`, and `B=⌈c exp c⌉`. Exact finite-offset geometry gives
only `1≤h≤B`, with positive cutoff `kn+h≤N` and negative cutoff
`h<kn, kn−h≤N`; no prime power with `k>N+B` contributes.
After multiplying row `n` by `√n`, each source term has weight
`(Λ(k)/k)c_m(j)√(kn/j)G((N/c)log(j/(kn)))/M`.

The uniform kernel estimate replaces this kernel by `G(N(j−kn)/(ckn))`
with error `C/N`, retaining the actual cutoffs. Since `|c_m|≤ϕ(m)`, the
entire square-root row error is at most
`a_N=2Bϕ(m)C·mertensSum(N+B)/(MN)→0`.

Move both cutoffs to `kn≤N`. Negative coefficients become
`c_m(kn+mh−h)=c_m(kn−h)` whenever `h≤kn`; when `kn≤h`, the reciprocal kernel
vanishes for `N≥c`. Every remaining discrepancy satisfies `|kn−N|≤B`, hence
`k∈[⌊N/n⌋−B,⌊N/n⌋+B+1]`. Its absolute square-root row cost is at most
`4Bϕ(m)F_B(⌊N/n⌋)`, where
`F_B(Y)=Σ_{Y−B≤k≤Y+B+1}Λ(k)/k→0`. This last limit follows from
`Λ(k)/k≤log(k)/k→0` and bounded interval cardinality.

After these replacements, the row is exactly the average of the two
reciprocal affine-shell corrections with shifts `h` and `mh−h`, evaluated
at `X=N/n`. Indeed `⌊N/n⌋` is the product cutoff; shells `h≥c` vanish by
support. Both shifts have coefficient `c_m(h)`, so both signed means are
`c_m(n)·shellCorrection(φ,c,m)`.

The shifted weighted-source theorem gives vanishing squared harmonic norm
for this reciprocal residual. The geometric error contributes at most
`a_N² H_N/log N→0`. The boundary error contributes at most a constant times
`Σ_{n≤N}F_B(⌊N/n⌋)²/(n log N)→0`, by the harmonic-quotient theorem.
The squared triangle inequality and square-root continuity give the claimed
norm limit. Every analytic source input is already proved; no hypothesis
on prime distribution or mode cancellation is added.

## Formalized inputs

- `TheWeightedAffinePrimeShellsHaveTheirSignedMean`;
- `TheWeightedAffineShellErrorsVanishInHarmonicNorm`;
- `TheUpwardPrimeRowsHaveUniformKernelBounds`;
- `HTGeometry.tendsto_harmonicQuotient_square_error`.

## Lean

`CriticalArithmeticCorrelationTheory/TheUpwardPrimeRowsRealizeTheCompletedShellCorrection.lean`:

- `sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient`;
- `exists_logarithmicUpwardCoefficient_error_bound`;
- `abs_linearizedUpwardCoefficient_sub_reciprocal_le`;
- `reciprocalUpwardCoefficient_eq_shifted_corrections`;
- `tendsto_actualUpwardRowError_sq_div_log`;
- `tendsto_normalizedUpwardPrimeResidual_norm`;
- `tendsto_tiltedUnitSpline_normalizedUpwardPrimeResidual_norm`.

Final direct no-olean audit passed without warnings. Both headline norm
limits and both exact source identities have only `propext`,
`Classical.choice`, and `Quot.sound`. CACT umbrella wired. The generic theorem
retains only profile regularity/support and positivity of its mass; the
explicit tilted-spline theorem has no profile premise.

This discharges the upward-source input in
`TheCompleteWeilResidualIsTheUpwardDefect`. Complete spectral positivity is a
separate assembly step.
