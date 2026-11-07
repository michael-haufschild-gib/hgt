# The different fixes the analytic trace character

- **ID:** analytic-trace-character-normalization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every nonzero Eisenstein modulus has the primitive character `ψ_c(x)=exp(2πi Tr(x/(c(1+2ω))))`; the exact Möbius conversion holds for this character.

## Proof

The integral power basis `1,ω` has minimal polynomial `X²+X+1`.
Its derivative gives the different `(δ)`, where `δ=1+2ω`. Thus the
trace dual of `(c)` is `(δc)⁻¹ O`. Integral traces make the displayed
phase independent of the representative modulo `c`.

If multiplication by `r` annihilates the character, then `r/(δc)` lies in
the trace dual `δ⁻¹O` of `O`. Cancellation gives `r∈cO`, proving primitivity.
For a product of distinct primes away from two and three, their canonical
primary generators multiply to a generator of the product ideal. Transport
along this equality and the established composite Gauss identity give
`μ(I) conjugate(G₁(I,ψ)) = c(I,ψ) G₂(I,ψ)`, with `|c(I,ψ)|=1`, for this
specific analytic trace character.

The same power basis gives `Tr(ω)=−1`, hence
`Tr((a+bω)/(1+2ω))=b` for rational `a,b`. Its integral coordinates satisfy
`|a+bω|²=a²−ab+b²`, and reduction modulo a nonzero rational `m` identifies
the residue set with `(ZMod m)²`.

## Lean and scope

Module: `MetaplecticMobiusDescent/TheDifferentNormalizesTheTraceCharacter.lean`.

- `Eisenstein.different_eq_traceLambda`
- `Eisenstein.traceDual_principal`
- `Eisenstein.principalTraceChar_primitive`
- `Eisenstein.analyticCompositeAddChar_apply`
- `Eisenstein.analytic_moebius_conversion`

Direct `lake --old env lean` passed. Five endpoint axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. The construction uses the corpus's
actual Hecke trace characters and mathlib's different/codifferent theory.

`MetaplecticMobiusDescent/EisensteinCoordinates.lean` proves these coordinate
identities through `Coordinates.coordinateEquiv`, `complex_norm_eval_sq`,
`trace_div_traceLambda`, and `rationalCoordEquiv`. Its direct check and four
endpoint axiom audits also passed with only standard axioms.

The quadratic Gauss phase and automorphic theta identification remain separate
claims. This normalization alone proves no mean-square cancellation estimate.

## Quadratic coordinate phase

`QuadraticTraceCoordinates.lean` proves
`Tr((x+yω)/(δ(a+bω)))=(ay−bx)/(a²−ab+b²)` for nonzero `a+bω`.
Multiply numerator and denominator by the conjugate, then apply the intrinsic
trace formula. Squaring the argument gives the oscillatory quadratic form.

The fixed dual phase `ψ_4(−cy²)` is periodic modulo two in `y`. Its four
residue values give `(1+i^(−b)+i^a+i^(b−a))/2`, depending only on `c mod 4`.
The four endpoint audits and direct Lean check passed with standard axioms.
This finite evaluation alone does not identify the normalized Gauss sum.
