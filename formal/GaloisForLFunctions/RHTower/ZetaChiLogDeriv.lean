import GaloisForLFunctions.RHTower.ZetaCarrier

/-!
# The logarithmic derivative of the chi factor

`χ(s) = Γ_ℝ(1−s)/Γ_ℝ(s)`, so the reflection in the numerator contributes with a minus sign and the
two archimedean logarithmic derivatives **add** rather than cancel:

```text
(χ'/χ)(s) = − (Γ_ℝ'/Γ_ℝ)(1−s) − (Γ_ℝ'/Γ_ℝ)(s) .
```

On a vertical line both arguments have modulus `≍ |t|/2`, so Stirling
(`HTGeometry/GammaDigammaStirlingBound`) turns the right-hand side into `−log(|t|/2π) + O(1/|t|)`.
This is the quantity the Levinson combination `ζ + λ ζ′` is designed to cancel: the dual edge of
`ζ + λζ′` carries the factor `1 + λ·(χ'/χ)(s)`, which vanishes to leading order when
`λ ≍ 1/log(|t|/2π)`.
-/

open Complex

namespace RHTower

/-- **The logarithmic derivative of the chi factor.**  Since `χ(s) = Γ_ℝ(1−s)/Γ_ℝ(s)`, the
reflection in the numerator contributes with a minus sign and the two archimedean logarithmic
derivatives **add**:

`(χ'/χ)(s) = −(Γ_ℝ'/Γ_ℝ)(1−s) − (Γ_ℝ'/Γ_ℝ)(s)`.

On a vertical line both arguments have modulus `≍ |t|/2`, so Stirling turns the right side into
`−log(|t|/2π) + O(1/|t|)`.  That is the quantity Levinson's combination `ζ + λζ′` is designed to
cancel against. -/
theorem logDeriv_zetaChi {s : ℂ} (h1 : Complex.Gammaℝ s ≠ 0)
    (h2 : Complex.Gammaℝ (1 - s) ≠ 0)
    (hd1 : DifferentiableAt ℂ Complex.Gammaℝ s)
    (hd2 : DifferentiableAt ℂ Complex.Gammaℝ (1 - s)) :
    logDeriv zetaChi s
      = -logDeriv Complex.Gammaℝ (1 - s) - logDeriv Complex.Gammaℝ s := by
  have hinner : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hnum : HasDerivAt (fun z : ℂ => Complex.Gammaℝ (1 - z))
      (-deriv Complex.Gammaℝ (1 - s)) s := by
    have h := hd2.hasDerivAt.comp s hinner
    simpa [Function.comp_def] using h
  have hden : HasDerivAt Complex.Gammaℝ (deriv Complex.Gammaℝ s) s := hd1.hasDerivAt
  have hquot : HasDerivAt (fun z : ℂ => Complex.Gammaℝ (1 - z) / Complex.Gammaℝ z)
      ((-deriv Complex.Gammaℝ (1 - s) * Complex.Gammaℝ s
        - Complex.Gammaℝ (1 - s) * deriv Complex.Gammaℝ s) / (Complex.Gammaℝ s) ^ 2) s :=
    hnum.div hden h1
  have hfun : zetaChi = fun z : ℂ => Complex.Gammaℝ (1 - z) / Complex.Gammaℝ z := rfl
  rw [hfun, logDeriv_apply, hquot.deriv, logDeriv_apply, logDeriv_apply]
  field_simp

end RHTower
