# Complete native fifth section at scale seven

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ6
- **Statement:** `nativeShiftedMatrix 5 0 (½log(7/π))` is positive definite.
- **Lean:** [FifthEvenScaleSevenNative.lean](../../../../formal/GaloisForLFunctions/ThetaCuspSections/FifthEvenScaleSevenNative.lean), namespace `GaloisForLFunctions.ThetaCuspSections.EvenFiveScaleSevenNative`: `nativeGram_coercive`, `nativeGram_posDef`, `native_scale_seven_posDef`.
- **Audit:** Canonical file check clean; all three declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Proof

Let `x₇=½log(7/π)`, `f=thetaCuspSourceTerm x₇ 1>0`, and
`mₖ=Pₖ(49,14)/121`, where `Pₖ` is the radial polynomial.
Put `A=[[m₀,m₁],[m₁,m₂]]`, `d=det A`, and let column `j` of `B`
be `(mⱼ₊₂,mⱼ₊₃)`, for `j=0,1,2`.
The numerator of the three-dimensional Schur form is
`Qᵢⱼ=d mᵢ₊ⱼ₊₄−Bᵢᵀ adj(A) Bⱼ`.
Set `Δ=Q₀₀Q₁₁−Q₀₁²` and use tail vectors

`t₀=(1,0,0)`,
`t₁=(−Q₀₁/Q₀₀,1,0)`,
`t₂=(-(Q₁₁Q₀₂−Q₀₁Q₁₂)/Δ,(Q₀₁Q₀₂−Q₀₀Q₁₂)/Δ,1)`.

The five columns are `e₀`, `(-m₁,1,0,0,0)`, and
`vⱼ₊₂=(-A⁻¹Btⱼ,tⱼ)`.
Exact rational identities give a diagonal first-atom Gram form with
strictly positive entries `Dᵢ`. The column matrix is upper triangular
with diagonal one.

Write `Rᵢⱼ(a,X)=Σᵤᵥ vᵢ,u vⱼ,v Pᵤ₊ᵥ(a,X)` and
`Tᵢⱼ=Σᵤᵥ |vᵢ,u vⱼ,v|(2u+2v)!/[10¹³(3/20)^(2u+2v)]`.
Thus `Dᵢ=Rᵢᵢ(49,14)/121`.
The complete-source bilinear estimate gives

`|Hᵢⱼ−f²Dᵢδᵢⱼ| ≤ f²Eᵢⱼ`,

where `Eᵢⱼ=(8·10⁻⁹|Rᵢⱼ(196,35)|+16·10⁻¹⁸|Rᵢⱼ(784,56)|)/121+Tᵢⱼ`.
The retained expansion uses `exp(−21)≤10⁻⁹`; the remaining analytic
error is the proved all-order Cauchy bound with denominator `10¹³`.

Exact rational inequalities bound the three diagonal error contributions
by `Dᵢ/2`, `Dᵢ/100`, and `Dᵢ/100`. Hence `Eᵢᵢ≤13Dᵢ/25`.
For `i<j`, `Eᵢⱼ²≤DᵢDⱼ/400`.
For couplings `(2,4)` and `(3,4)`, this follows by weighted Cauchy–Schwarz:
the squared mixed contribution is at most `DᵢDⱼ/625`, and the squared
second-atom and tail contributions are each at most `DᵢDⱼ/40000`.
The adjacent pivot identity `D₃D₄=det Q/(d²Q₀₀)` cancels the internal
Schur denominator in the last tail estimate.

Divide column `i` by `√Dᵢ`. The complete normalized Gram matrix has
diagonal at least `12f²/25` and off-diagonal absolute values at most `f²/20`.
After splitting off its actual diagonal, the remaining quadratic form has
absolute value at most `5f²‖z‖²/20`. Therefore

`zᵀHz ≥ (23/100) f²‖z‖²`.

The normalized column matrix has positive diagonal and is invertible.
Congruence transfers strict positivity to the complete native fifth block.

This supplies the positive native endpoint needed for the coupled-load
Schur interval. Compatibility with the origin and positivity across the
intervening source region remain open.
