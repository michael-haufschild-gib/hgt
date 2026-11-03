# The actual Lewis period has its prime-three Hecke eigenvalue

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `MayerScattering/LewisHeckePrimeThreeEigenvalue.lean`.
- **Statement:** For `0<Re s<1/2` and every `a>0`, the actual completed period satisfies `T₃,s E_s(a)=(1+3·3^(−2s))E_s(a)`. The same holds for the resonant period at every Mayer resonance.

`T₃` has the seven determinant-three branches with arguments
`3a`, `a/3`, `(a+1)/3`, `3a/(a+1)`, `(a+2)/3`, `3a/(2a+1)`, `(2a+1)/(a+2)`
and weights respectively
`1`, `3^(−2s)`, `3^(−2s)`, `(a+1)^(−2s)`, `3^(−2s)`, `(2a+1)^(−2s)`, `(a+2)^(−2s)`.

## Proof

The [audited Barnes cone identity](f2-prime-three-barnes-hecke-identity.md) gives the eigen-equation for `Re w>2`, `w=2s`. Barnes reciprocity replaces the `a/3` branch by `3/a`, with combined weight `a^(−w)`. For `1<a<7/6`, all seven reduced arguments lie in `(1/2,7/2)`.

Multiply the local defect by `w−2`. Its evaluations of the pole-cleared Mayer state are holomorphic on `Re w>0`; the defect vanishes in the absolute chamber, hence throughout that half-plane. Divide by `w−2` in `0<Re w<1`. The state equation identifies the disc values with the actual completed period, whose reciprocity restores the original branch. All seven compositions and weights are real analytic on `a>0`, extending the equation to the entire positive line. At a resonance the zeta forcing vanishes, identifying completed and resonant periods.

## Lean audit

- `eisensteinLewisPeriod_hecke_three`
- `resonantLewisPeriod_hecke_three`

Final individual `lake --old env lean` check passed without warnings. Both transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Wired into `RenormalizedIntersectionTheory.lean`.

This establishes the second source Hecke action. The window intertwining and complete Weil positivity are separate claims.
