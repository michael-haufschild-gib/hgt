# Growing conductors at the critical curve (review-0311 §2.5.4)

- **ID:** R0311-25-4
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0311/obstacles-summary.md` §2.5.4
- **Statement:** Along `c⁸ = K log N`, the conductor decomposition of the tilted-spline form —
  Weil's form on untwisted horizon windows, positive counts on twisted ones, no mixed terms — holds
  uniformly for conductors `m ≤ M(N)` with `M(N) → ∞`; the count form holds exactly on the range
  `m = o(c_N)` and fails at `m ≍ c_N`, in particular for `M(N) = N`; up to `N^θ`, `θ < ½`, the
  decomposition persists with the counts replaced by the scaled counts `J(m)c^{−7}R_m(c/m)`.

## Answer

1. **Uniform growing range.** With `x_1 = h/√n` (untwisted) and `x_m = c_m(n)g/√n` (`m ≥ 2`), the
   normalized form `q_N(x) = c⁻¹Q(T_x)/∫φ_N²` satisfies, for some `M(N) → ∞` and every `ε > 0`,
   eventually `|q_N(Σ_{m ≤ M(N)} b_m x_m) − Σ_{m ≤ M(N)} b_m²λ_m| ≤ εΣ b_m²` uniformly in `b`, with
   `λ_1 = κQ(H) + (7J(1)/K)‖H‖²_{−8}` and `λ_m = (7φ(m)J(m)/K)‖G‖²_{−8}`.
2. **The count form ends at the resolution.** The twisted direction of conductor `m` carries
   `E_m(c) = J(m)c^{−7}R_m(c/m)`; the count ratio `ρ = c⁷E_m(c)/J(m) = R_m(c/m)`:
   `sup_{m ≤ M(N)}|ρ − 1| → 0` whenever `M(N)/c_N → 0`; `ρ ≤ ½` once `m ≥ λ₀c`; so the count form is
   not uniform on `m ≤ N` (`c_N = o(N)`).
3. **Up to `N^θ`.** For every `θ < ½` the Ramanujan horizon vectors of all conductors `m ≤ N^θ` are
   collective quasimodes of the complete matrix along the critical curve, with eigenvalues
   `E_m(c) = J(m)c^{−7}R_m(c/m) ≥ 0`.

## Proof

1: `q_N` is the quadratic form of the bilinear pairing `B_N(x, y) = c⁻¹W(T_x, T_y)/∫φ_N²`
(`weilPair` is bilinear on tests, `T_x` linear in `x`). Each Gram entry converges by polarization of
the fixed-family limits (`horizon_layer_criticalCurve_exact`, `graded_ramComb_criticalCurve_exact` with
windows `h` or `0` and supports `{m}`, `{m, m'}`): `B_N(x_m, x_{m'}) → δ_{mm'}λ_m`. The entrywise error
`D_k(N) = Σ_{m,m' ≤ k}|B_N − λδ|` tends to `0` for each `k`; a diagonal choice of `M(N)` keeps
`D_{M(N)}(N) → 0`, and `|Σ b_m b_{m'}(B_N − λδ)| ≤ (Σb²)D_{M(N)}(N)`.
2: the exact scaling form `c⁷E_m(c) = J(m)R_m(c/m)`; `R_m(x) → 1` as `x → ∞` uniformly in `m`; and
`R_m(x) ≤ Cx` uniformly in `m` (pure end).
3: the collective quasimode theorem holds for every schedule with `c²/log N → 0`; on the critical curve
`c²/log N = (c⁸/log N)c^{−6} → 0`.

## Lean

`formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/`:

- `TheConductorDecompositionHoldsOnAGrowingRange`: `exists_tendsto_diagonal`, `layerForm_sum`,
  `tendsto_layerPair_conductorWindow`, `exists_uniform_conductor_range`.
- `TheCountFormEndsAtTheResolution`: `countRatio_eq`, `eventually_abs_countRatio_sub_one_le`,
  `exists_countRatio_le_half`, `eventually_countRatio_conductor_le_half`,
  `not_uniform_countRatio_up_to_N`, `tendsto_criticalCurve_quasimodes`,
  `completedConductorEnergy_eq_scaledCount`.

Wired into `ArithmeticHodgeTheoryOfDegenerations.lean`.

## Gates
- [x] 0 → 1  statement
- [x] 1 → 2  paper proof
- [x] 2 → 3  every module passes `lake --old env lean`
