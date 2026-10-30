# A theta–prime expression for the resolvent depth

- **ID:** hef-theta-prime-depth
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q2/defect.
- **Statement:** Express the exact resolvent depth at `s=4` using only finite integer
  theta-prefix curvature readings, the Gamma factor, and the absolutely convergent prime series.

## Construction

Let `w_k(z)=1/(|4−z|²+1/(k+1))` and let `χ_R` be the existing smooth compact
source cutoff. Each test `χ_R w_k` is globally C² and compactly supported.
Use the existing prescribed finite theta reading `Q_n(χ_R w_k)`.

The proposed identity is

`D(4) = (7/2) lim_k lim_R lim_n Q_n(χ_R w_k)
        − Re(logDeriv archFactor 4) + Σn Λ(n)n⁻⁴`.

For fixed `R,k`, compact-current convergence identifies the inner limit with
the multiplicity-exact divisor trace. Absolute summability gives the cutoff limit.
Finally `0≤w_k(ρ)≤|4−ρ|⁻²` and pointwise convergence identify the outer limit
with `S(4)`. The full-divisor depth and prime identities are already formalized
in `TheXiResolventDepthIdentity`.

## Lean obligations

- General compact-test convergence for the prescribed finite theta reading.
- Xi-copy/carrier trace transport with summability.
- Three exact limits and the final theta–prime identity.

The expression does not assert that `D(4)=0`.
