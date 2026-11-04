# Complete common kernel at scale seven

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ6
- **Statement:** The complete native fifth even source at `x₇=½log(7/π)` is positive definite on `span(e₀,e₁,(0,0,−420,1,−1/1568))`.
- **Lean:** [FifthEvenScaleSevenKernel.lean](../../../../formal/GaloisForLFunctions/ThetaCuspSections/FifthEvenScaleSevenKernel.lean), namespace `GaloisForLFunctions.ThetaCuspSections.EvenFiveScaleSeven`: `kernelGram_coercive`, `kernelGram_posDef`, `coherentKernel_scale_seven_posDef`.
- **Audit:** Canonical file check clean; all three declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Proof

Write `Pₖ(a,X)` for the radial polynomial and `mₖ=Pₖ(49,14)/121`.
Set `d=m₀m₂−m₁²`, `b₀=−420m₂+m₃−m₄/1568`,
`b₁=−420m₃+m₄−m₅/1568`,
`h₀=−(m₂b₀−m₁b₁)/d`, `h₁=(m₁b₀−m₀b₁)/d`.
Use the basis
`e₀`, `(-m₁,1,0,0,0)/100`,
`(h₀,h₁,−420,1,−1/1568)/10⁶`.
Its first-atom Gram matrix `D` is diagonal with every diagonal greater than `1/100`.

For basis vectors `vᵢ`, let `Qᵢⱼ(a,X)=Σᵤᵥ vᵢ,u vⱼ,v Pᵤ₊ᵥ(a,X)` and
`Tᵢⱼ=Σᵤᵥ |vᵢ,u vⱼ,v|(2u+2v)!/[10¹³(3/20)^(2u+2v)]`.
The two-atom expansion and Cauchy remainder give, with `f=thetaCuspSourceTerm x₇ 1>0`,

`|Hᵢⱼ−f²Dᵢⱼ| ≤ f² Eᵢⱼ`,

where `Eᵢⱼ=(8·10⁻⁹|Qᵢⱼ(196,35)|+16·10⁻¹⁸|Qᵢⱼ(784,56)|)/121+Tᵢⱼ`.
Here `0<exp(−21)≤10⁻⁹`; the all-order Cauchy estimate uses denominator `10¹³`.

Exact rational inequalities give `Eᵢⱼ≤1/1000` unless `(i,j)=(2,2)`.
For the last diagonal, the mixed contribution is at most `D₂₂/2`,
and the last-atom and Cauchy contributions are each at most `1/3000`.
Thus every complete diagonal is at least `f²/250`, and every off-diagonal
has absolute value at most `f²/1000`.

Split off the actual diagonal. The remaining three-dimensional matrix has
quadratic absolute value at most `3f²‖z‖²/1000` by Cauchy–Schwarz.
Consequently `zᵀHz ≥ f²‖z‖²/1000`.
The displayed triangular basis change is invertible, so the original common-kernel form is positive definite.

This removes the common-kernel obstruction at the second endpoint. Positivity
of the complementary endpoint Schur interval and the intervening source region remain open.
