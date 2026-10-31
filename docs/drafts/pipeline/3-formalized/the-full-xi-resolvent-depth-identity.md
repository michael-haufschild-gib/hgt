# The full Xi resolvent depth identity

- **ID:** hef-xi-depth
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3010/obstacles-summary.md` A14; Q2/defect input.
- **Statement:** For `Re s>1`, the multiplicity-exact Xi divisor satisfies
  `(Re s−1/2) Σρ |s−ρ|⁻² − Re ξ′/ξ(s)
   = Σρ 2(Re s−1/2)(Re ρ−1/2)²/(|s−ρ|²|s−ρ*|²) ≥ 0`,
  where `ρ*=1−conj ρ`; both series converge absolutely.

## Proof

The positive summable field `Re(s−ρ)⁻¹` dominates the squared Cauchy kernel
with factor `(Re s−1)⁻¹`. Subtracting the reciprocal field gives the summable
signed series `Σ(Re ρ−1/2)/|s−ρ|²`. Reindex by critical-line reflection and
average. Each reflected pair has the displayed nonnegative depth term.
The exact Euler logarithmic derivative then replaces `Re ξ′/ξ(s)` by
`Re(logDeriv archFactor s) − Σn Λ(n)n^(−Re s)cos(Im s log n)`.

## Lean

Module: `formal/GaloisForLFunctions/HilbertianExplicitFormulas/TheXiResolventDepthIdentity.lean`.

- `summable_xiSamePointResolvent`
- `summable_xiResolventDepthTerm`
- `sub_mul_xiSamePointResolvent_sub_logDeriv`
- `xiResolventDepth_nonneg`
- `xiResolventDepth_eq_samePoint_sub_arch_add_prime`

Direct `lake --old env lean` check passed. Both capstone axiom audits report
only `propext`, `Classical.choice`, `Quot.sound`. Imported by the HEF umbrella.

## Scope

This extends the finite resolvent identity to the actual full divisor.
It proves neither zero depth nor equality of the two source orientations.
The theta-prefix identification at `s=4` is formalized in
[the theta–prime expression](theta-prime-expression-for-the-resolvent-depth.md).
