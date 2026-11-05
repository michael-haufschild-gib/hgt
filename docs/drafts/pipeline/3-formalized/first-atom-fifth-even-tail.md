# The first theta atom has a positive fifth even tail

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Scope:** The literal first atom; the complete theta sum remains open.

Let `f₁(x)=thetaCuspSourceTerm x 1`. For every `r≥0`, the matrix

`T₁(r)ᵢⱼ = ∫_(s>r) (−1)^(i+j) ∂ₜ^(2(i+j))[f₁(s/2+t)f₁(s/2−t)]|ₜ₌₀ ds`,

with `0≤i,j<5`, is positive definite. More generally this holds when
`q=πexp(r)≥3`.

## Proof

Put `E(q)=q^(3/2)exp(−2q)` and
`I_α(q)=∫_(t>q) t^α exp(−2t) dt`. For `q>0`, `α>0`, integration by parts gives

`I_α(q)=q^α exp(−2q)/2+(α/2)I_(α−1)(q)`.

Thus `z=I_(3/2)/E ≥ 1/2+3/(8q)`. The normalized power moments satisfy
`J₀=z` and `J_(n+1)=q^(n+1)/2+(2n+5)Jₙ/4`.
Applying the known signed radial polynomials through order sixteen gives
the five-coordinate model `M(q,z)`.

The recurrence is affine in `z`:
`M(q,z)=B(q)+(z−1/2)A`, where `B(q)=M(q,1/2)` and `A=M(0,1)`.
All five cleared Schur signs of `B(3+y)` have positive constant terms
and nonnegative other coefficients for `y≥0`. The five Schur signs of
`A` are positive rational numbers. Two Schur square completions therefore
give `B(q)>0` for `q≥3` and `A>0`.

The exact radial tail matrix is

`R(q)=E(q)B(q)+(3/4)I_(1/2)(q)A`.

Its surplus over `E(q)B(q)` is itself positive definite for every `q>0`.
The exponential change of variable gives
`T₁(r)=4π^(−1/2)R(πexp(r))`. Both scalar factors are positive, and
`r≥0` implies `πexp(r)>3`. This proves the claim.

## Formalization

Namespace `GaloisForLFunctions.ThetaCuspSections.FifthAtomTail`.

- `FifthEvenFirstAtomTailModel.lean`: `half_model_posDef`,
  `mass_model_posDef`, `model_affine`, `model_posDef`.
- `FifthEvenFirstAtomTail.lean`: `tailMatrix_posDef_of_scale`,
  `tailMatrix_posDef`, `gammaMass_enhanced_lower`,
  `radialTailMatrix_decomposition`, `radialTailMatrix_sub_half_posDef`.

All 20 audited declarations use only `propext`, `Classical.choice`,
`Quot.sound`. Both modules pass direct `lake --old env lean` checks and
are wired into `ThetaCuspSections.lean`.

Unequal atom pairs and the infinite remainder must still be paid to obtain
the complete fifth even tail and rank-nine integrated positivity.
