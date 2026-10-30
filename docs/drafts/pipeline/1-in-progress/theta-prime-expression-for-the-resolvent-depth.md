# A theta–prime expression for the resolvent depth

- **ID:** hef-theta-prime-depth
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q2/defect.
- **Statement:** Express the exact resolvent depth at `s=4` using only finite integer
  theta-prefix curvature readings, the Gamma factor, and the absolutely convergent prime series.

## Construction

Let `χ_R` be the existing smooth compact source cutoff, with inner radius
`R+1` and outer radius `R+2`. Set
`w(z)=1/(|4−z|²+χ_0(z−4))`. Its denominator is positive everywhere and
`w(ρ)=|4−ρ|⁻²` throughout the zero strip. Each `χ_R w` is globally smooth
and compactly supported. Use the prescribed finite theta reading `Q_n(χ_R w)`.

The proposed identity is

`D(4) = (7/2) lim_R lim_n Q_n(χ_R w)
        − Re(logDeriv archFactor 4) + Σn Λ(n)n⁻⁴`.

For fixed `R`, compact-current convergence identifies the inner limit with
the multiplicity-exact divisor trace. Absolute summability gives the cutoff
limit `S(4)`. The full-divisor depth and prime identities are already formalized
in `TheXiResolventDepthIdentity`.

## Lean obligations

- General compact-test convergence for the prescribed finite theta reading.
- Xi-copy/carrier trace transport with summability.
- Two exact limits and the final theta–prime identity.

The expression does not assert that `D(4)=0`.
