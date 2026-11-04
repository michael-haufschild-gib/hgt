# Effective fifth cross-load ray

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6
- **Lean:** `ThetaCuspSections/FifthEvenEffectiveCrossRay.lean`

The fixed endpoint-compatible source `H(x)+G(x)LᵀVL` is positive definite
whenever `q=π exp(2x)≥5000`. Its normalized Gaussian quadratic floor is
`20000`. In particular, it is positive for every center `x≥4`.

**Proof.** Put `K=4q² exp(x−2q)` and let `C(q)` be the native Gaussian
coordinate map. The complete native form retains
`((2q−3)²/1000−147/4000)I` after division by `K` and congruence by `C(q)`.
For `U=L C(q)`, the two row squared norms are at most `1/(2000q⁴)`
and `1/(10⁷q⁶)` on `q≥7`.

The exact positive coefficient matrix satisfies `V₀₀≤5·10⁷` and
`V₁₁≤10¹³`. Positivity evaluated at `(a,−b)` bounds its energy at `(a,b)`
by `2V₀₀a²+2V₁₁b²`. Cauchy–Schwarz therefore gives
`q⁴ vᵀUᵀVUv≤50002‖v‖²` on `q≥5000`.
The complete mass and slope bounds, together with `16x≤q`, give
`G/K≥−(26/25)q⁴`. The adverse correction costs at most
`(26/25)·50002‖v‖²`, while the native reserve is at least `75000‖v‖²`.
This leaves `20000‖v‖²`. The coordinate map is invertible, so the native
cross-loaded source is positive definite. Finally, `π exp(8)>5000`
gives the stated center cutoff.

Public certificates in `FifthEffectiveCrossRay`:

- `compensation_lower`
- `crossGram_coercive`
- `crossGram_posDef`
- `crossRepair_posDef_of_scale_ge_fiveThousand`
- `crossRepair_posDef_of_four_le`

Transitive axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
The unresolved global source sign is now confined to the explicit interval `[0,4]`.
