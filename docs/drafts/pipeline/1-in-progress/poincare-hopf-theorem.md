# The Poincaré–Hopf index theorem

- **ID:** poincare-hopf
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean target)
- **Source:** user goal, 2026-08-21
- **Statement:** For a compact smooth manifold `M` without boundary and a smooth vector field `v`
  on `M` whose zero set is finite (isolated zeros), the sum of the local indices of `v` at its
  zeros equals the Euler characteristic of `M`.

## Goal
Mathlib does **not** contain this theorem, nor any of its main prerequisites:
- no Brouwer degree (`grep -ri Brouwer Mathlib` returns only lattice-theoretic hits);
- no Sard theorem file;
- no Euler characteristic of a topological space (only `Algebra/Homology/EulerCharacteristic.lean`,
  the alternating rank sum of a homological complex);
- no hairy-ball theorem, no local index of a vector field.
So the whole tower has to be built inside the corpus.

## Architecture (bottom-up layers)

**Stage I — Brouwer degree in `ℝⁿ = (Fin n → ℝ)`, analytic construction.**
The mollified-determinant (Heinz) definition
  `D(f, Ω, y, φ) = ∫_Ω φ (f x - y) · det (Df x) dx`,
`φ` a bump with `∫ φ = 1` supported in `B_ρ(0)`, `ρ < dist (y, f '' frontier Ω)`.

- I.1 `CofactorPermutation` — permutation-sum formula for the cofactor matrix, identification with
  `Matrix.adjugate`, and the row/column contraction identities.
- I.2 `PiolaIdentity` — for `u` of class `C²`, `∑ j, ∂_j (cof (Du))_{i j} = 0`
  (rows of the cofactor matrix are divergence free).  Proof: a sign-reversing involution
  `(j, l, σ) ↦ (l, j, σ ∘ swap j l)` on the permutation index set, using symmetry of second
  derivatives.
- I.3 `CompactSupportDivergence` — `∫_{ℝⁿ} div V = 0` for `C¹` compactly supported `V`
  (mathlib's box divergence theorem with the faces pushed outside the support).
- I.4 `DivergenceForm` — `(div W)(u x) · det (Du x) = div_x (x ↦ cof(Du x)ᵀ · W (u x))`.
- I.5 `DegreeIntegral` — definition, independence of the bump `φ`, homotopy invariance.
- I.6 `RegularValueCount` — at a regular value the integral equals `∑ sign det Df`.
- I.7 `DegreeContinuous` — extension to continuous maps, excision/additivity, normalization.

**Stage II — local index of a vector field.**
- II.1 `LocalIndex` — `ind_p v = deg (v, B_ε p, 0)`, independence of `ε`.
- II.2 invariance under diffeomorphisms of the chart (so the index is chart independent).

**Stage III — manifold layer.**  Index sum for a compact manifold; independence of the field.

**Stage IV — Euler characteristic.**  Homological `χ` and the identification.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  full paper proof, dependency closed
- [ ] 2 → 3  Lean theorem, unconditional, umbrella wired
- [ ] 3 → 4  preprint

## Landed Lean modules (all unconditional, umbrella-wired)

All under `formal/GaloisForLFunctions/HTGeometry/PoincareHopf/`, namespace
`GaloisForLFunctions.HTGeometry.PoincareHopf`.

| Module | Main declarations |
|---|---|
| `CofactorPermutation` | `cofSum`, `cofSum_eq_adjugate`, `sum_cofSum_mul` |
| `PiolaIdentity` | `jac`, `hess`, `hess_symm`, `cofD`, `hasFDerivAt_cofSum`, `piola` |
| `CompactSupportDivergence` | `fieldDivergence`, `integral_fieldDivergence_eq_zero` (wraps the corpus' `HTGeometry.integral_divergence_eq_zero_of_hasCompactSupport`, all dimensions) |
| `DivergenceForm` | `piolaField`, `hasFDerivAt_piolaField`, `fieldDivergence_piolaField`, `contDiff_piolaField`, `clm_apply_eq_sum` |
| `VanishingLemma` | `integral_divergence_comp_det_eq_zero` |
| `TranslationInvariance` | `degIntegral`, `transField`, `transDeriv`, `continuous_det_jac`, `integrableOn_of_continuous`, `degIntegral_translate` |
| `MollifierIndependence` | `integrable_uncurry_of_continuous`, `degIntegral_convolution`, `degIntegral_eq_of_mass_one` |
| `Degree` | `bumpWeight`, `AdmissibleRadius`, `degree`, `exists_admissibleRadius`, `degree_eq_degIntegral` |

Key design decisions that made this work:
- ambient space `Fin n → ℝ` with the sup norm, so `volume` is the pi measure and mathlib's box
  divergence theorem applies directly;
- the **mollifier independence** proof avoids the compactly supported Poincaré lemma entirely: it
  goes through translation invariance plus Fubini on a convolution;
- **translation invariance** avoids differentiation under the integral sign: the `t`-derivative of
  `φ (w - t z)` is the divergence of the explicit field `-φ (w - t z) · z`, so the fundamental
  vanishing lemma applies slicewise and FTC + Fubini finish.

## Next layers (Stage I remainder)
- I.8b general divergence form: `div (x ↦ (j ↦ ∑ i, cof (Du x)_{i j} G_i x)) = ∑ i j, cof_{i j} ∂_j G_i`
  for an arbitrary `C¹` field `G` of `x` (generalizes `fieldDivergence_piolaField`).
- I.9 Jacobi's formula `∂_t det M t = ∑ i j, cof (M t)_{i j} · ∂_t M t _{i j}`, same reindexing as
  `piola`.
- I.10 general homotopy invariance (FTC in `t` + Fubini, exactly as in `degIntegral_translate`).
- I.11 excision and additivity (immediate from the integral formula: the integrand is supported in
  `{x : ‖f x - y‖ < ρ}`), and normalization `degree id Ω y = 1` for `y ∈ Ω`.
- I.12 the regular value formula `degree f Ω y = ∑ sign det`, hence integrality.

## Log
- 2026-08-21 — created; mathlib audit done (no Poincaré–Hopf, no degree, no Sard, no χ of a space);
  corpus audit done (`BrouwerFixedPoint`, `SmoothNoRetraction`, `DeterminantPolynomialIntegral`
  exist; no degree theory).  Architecture frozen as above.
- 2026-08-21 — Stage I core complete through the definition of the Brouwer degree and the theorem
  that it equals the integral against every admissible weight.
