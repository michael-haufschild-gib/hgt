# The untwisted continuation has no Mellin poles

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** O2; strengthening of contribution 2, no additional count.
- **Statement:** `besselSqMellin s ≠ 0` on `Re s>2/3`; the actual untwisted squarefree series continues holomorphically through `2/3<Re w<13/6, Im w>0`, with pointwise agreement on `2<Re w<13/6, Im w>0` and the previously established nonzero simple pole at `2/3`.

## Paper proof [PROVED HERE]

1. In MMD's positive-ray Schläfli integral substitute `t=(x/2)e^u`, for `x>0`. The Jacobian combines with `t^(ν−1)` to give `(x/2)^ν e^(νu)`, and the exponent becomes `−x cosh u`. The normalizing factor cancels `(x/2)^ν`. The existing whole-line exponential representation is twice HTGeometry's Bessel function; its factor two cancels the Schläfli prefactor. Thus `schlafliBesselK ν x = modifiedBesselKOrder x ν` for every complex order.
2. Apply the corpus two-K Mellin product with both orders `1/3`. Absolute convergence holds exactly when `Re s>2/3`, and
   `M(s)=2^(s−3) Γ(s/2+1/3) Γ(s/2)^2 Γ(s/2−1/3)/Γ(s)`.
3. All four Gamma arguments have positive real part, so every factor is nonzero. The power of two is also nonzero. Therefore `M(s)≠0` throughout this half-plane.
4. The existing completed untwisted function is holomorphic on the upper strip. Compose with `s=2w` and divide by nonvanishing `M(2w)`. Its initial product identity now gives pointwise agreement everywhere in the initial strip. The previously proved local pole and exact nonzero residue remain unchanged.

## Lean

Module: `SpectralTheoryOfTheCubicCover/TheUntwistedContinuationHasNoMellinPoles.lean`.

- `schlafliBesselK_eq_modifiedBesselKOrder`
- `besselSqMellin_eq_gamma`
- `besselSqMellin_ne_zero`
- `continuedUntwistedTheta_differentiableOn`
- `continuedUntwistedTheta_eq_series`
- `untwistedSquarefreeSeries_holomorphic_simple_pole`

Final plain `lake --old env lean` check passed; module umbrella-wired. No axiom checks.

## Scope

This connects the cubic-cover arithmetic normalization to the two-Bessel Mellin formula already used for modular cusp modes. It removes artificial quotient poles and strengthens [the isolated arithmetic pole](the-unramified-theta-square-has-a-nonzero-pole.md). Vertical growth and real spectral poles remain separate requirements for a smoothed asymptotic.
