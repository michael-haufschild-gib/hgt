# FZZ linear replica-area holonomy selector

- **ID:** FZZ-AREA-HOL-1
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Linear neutral fractional-winding area tangent has resonant Fourier data `c₀=-2`, `c_{±2n}=2/3`; its normalized rectangular-torus response is passive iff radial monodromy vanishes.

## Goal

Reduce FZZ-P chain

`literal parity-Mellin divisor → torus replica-area response → passivity → zero radial monodromy → critical line → RH`

to one source-side premise: passivity of actual divisor-mode area response. Frontier map is read-only.

## Gates

- [x] 0 → 1: source-pure object from Halder--Jafferis (3.29),(3.33) and corpus torus characters
- [x] 1 → 2: dependency-closed paper proof
- [x] 2 → 3: Lean theorem, direct check, targeted build, axioms, umbrella wiring

## Frozen statement and proof

For `χ_j(s)=exp(2πijs)` and `n≠0`, compact-holonomy part of
`∂δ(W⁺_δ+W⁻_δ)|₀` is

`B_n(s)=2πin·s(χ_{-n}(s)-χ_n(s))`.

Radial dressing derivative adds an arbitrary `aχ_n+bχ_{-n}`. Put
`A_n=B_n+aχ_n+bχ_{-n}`. Then

`ĉ_n(0)=-2`, `ĉ_n(2n)=ĉ_n(-2n)=2/3`,

independently of `a,b`. Indeed
`∫₀¹sχ_j(s)ds=1/2` for `j=0` and `(2πij)⁻¹` for `j≠0`; character orthogonality kills radial terms at `0,±2n`. Direct substitution gives stated three coefficients.

Corpus resonance law therefore gives

`∫₀¹ A_n(s₂) H_n(s₁i+s₂)^2 ds₂ = 1+(β_n(s₁i)^2+γ_n(s₁i)^2)/6`.

Here `βγ=1`, `β_n(s₁i)^2=exp(-4πns₁)`, and `γ_n(s₁i)^2=exp(4πns₁)`. Hence normalized real response

`R_n(s₁)=3/4+(exp(4πns₁)+exp(-4πns₁))/8`

satisfies `R_n≥1`; moreover
`8(R_n-1)=(exp(2πns₁)-exp(-2πns₁))²`, so `R_n≤1 ↔ s₁=0`.
For canonical Mellin twist, `s₁=-(log 2)/(2π)(Re ρ-1/2)`, thus passivity is equivalent to `Re ρ=1/2`.

## Novelty audit

- `[BRIDGE]`: elementary sawtooth Fourier integral and exponential equality case.
- `[NEW candidate]`: exact application to nonlocal FZZ area tangent, radial-term decoupling, and single-passivity reduction. Halder--Jafferis leave toroidal one-point open; targeted search found no published torus evaluation through 2026-08.
- Scope: holonomy sector only. Does not assert divisor-mode passivity or full torus CFT one-point.

## Hostile checks

- Positivity not assumed.
- Radial derivative from (3.29) retained as arbitrary `a,b` and proved off-resonant.
- No claim that area response is automatically passive.
- No zeta/Xi data enters response calculation; divisor passivity remains explicit producer.

## Formal certificate

- Module: `GaloisForLFunctions.RHTower.FZZCigarParityLinearReplicaAreaHolonomySelector`
- Endpoint: `fzzLinearReplicaAreaDivisorPassive_iff_riemannHypothesis`
- Pointwise selector: `fzzLinearReplicaAreaNormalizedResponse_mellinTorusTwist_le_one_iff`
- Audit: direct Lean PASS; targeted build PASS; standard axioms only; umbrella wired. Global lint is blocked only by unrelated concurrent un-wired modules; this module is reachable and has no forbidden declaration.
