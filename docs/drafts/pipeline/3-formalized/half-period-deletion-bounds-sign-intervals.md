# Half-period deletion bounds sign intervals

- **ID:** A92-sign
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `γ_j ≥ Γ > 0`, a nonzero real trace `F(t)=Re Σ_{j<n} a_j exp(iγ_j t)` that is nonnegative on an interval of length `L` satisfies `L ≤ Σ_j π/γ_j`, hence `ΓL ≤ nπ`. Without the nonzero premise, the exact alternative is this bound or `F≡0`.

## Proof

Each positive translation operator `1+τ_{π/γ_j}` annihilates its corresponding mode. Their product annihilates the sum and has support in `[0,D]`, where `D=Σ_j π/γ_j`. If `L>D`, translate this identity inside the sign interval. Every summand is nonnegative and the unshifted summand occurs, so `F` vanishes on a nonempty open interval. Real-analytic uniqueness gives `F≡0`. Finally, `D≤nπ/Γ`.

No frequency separation or distinctness is required. The zero-trace alternative is necessary: the original sign claim omits a nonvanishing condition. The weighted and prime-side clauses of A92 remain separate obligations.

## Formalization

- Module: `SurfaceOfSpecZ/ScaleLocality/HalfPeriodSignResolution.lean`.
- Namespace: `GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality`.
- Theorems: `sign_interval_le_sum_halfPeriods`, `exponentialSum_sign_interval_resolution`, `exponentialSum_sign_interval_short_or_zero`.
- Direct `lake --old env lean` audit passed. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `GaloisForLFunctions/SurfaceOfSpecZ.lean`.
