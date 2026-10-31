# A theta–prime expression for the resolvent depth

- **ID:** hef-theta-prime-depth
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q2/defect.
- **Statement:** Express the exact resolvent depth at `s=4` using only finite integer
  theta-prefix curvature readings, the Gamma factor, and the absolutely convergent prime series.

## Construction

Let `χ_R` be the existing smooth compact source cutoff, with inner radius
`R+1` and outer radius `R+2`. Set
`w(z)=1/(|4−z|²+χ_0(z−4))`. Its denominator is positive everywhere and
`w(ρ)=|4−ρ|⁻²` throughout the zero strip. Each `χ_R w` is globally smooth
and compactly supported. Use the prescribed finite theta reading `Q_n(χ_R w)`.

The exact identity is

`D(4) = (7/2) lim_R lim_n Q_n(χ_R w)
        − Re(logDeriv archFactor 4) + Σn Λ(n)n⁻⁴`.

For fixed `R`, compact-current convergence identifies the inner limit with
the multiplicity-exact divisor trace. Absolute summability gives the cutoff
limit `S(4)`. The full-divisor depth and prime identities are already formalized
in `TheXiResolventDepthIdentity`.

## Lean

`ConjugateDiagonalGeometry/FiniteThetaReadingsRecoverCompactCurrents.lean`
proves compact-current convergence with error `Bφ exp(−n⁴+56n²+62)`.

`HilbertianExplicitFormulas/TheResolventDepthHasAThetaPrimeExpression.lean`:

- `tendsto_xiResolventThetaReading`: the inner limit.
- `tendsto_lim_xiResolventThetaReading`: the outer limit.
- `xiResolventThetaSamePoint_eq`: the source reading equals `S(4)`.
- `summable_vonMangoldt_four`: absolute convergence of the prime series.
- `xiResolventDepth_four_eq_thetaPrime`: the exact depth identity.
- `xiResolventDefect_four_eq_thetaPrime`: the requested same-point defect identity.

Both modules are imported by their umbrellas. Direct capstone-file check passed;
both capstone axiom sets are exactly `propext`, `Classical.choice`, `Quot.sound`.

The expression does not assert that `D(4)=0`.
