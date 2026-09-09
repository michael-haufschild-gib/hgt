# Actual Einstein–Hilbert variation and its boundary current

Status: local first variation formalized in Lean. Physical endpoint evaluation and extinction remain open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact identity

Let `g` and `h` be actual complex matrix fields on real coordinates, C³ at an exterior point `x`. Assume `g` is symmetric and `det(g(x))≠0`. Form the affine field `g_t(y)=g(y)+t h(y)` before taking any spatial derivatives. With the local complex square-root branch fixed at one, define

```text
L(t) = exp(log(det(g_t(x))/det(g(x)))/2) · (R(g_t)(x) - 2Λ)
ν_x(y) = exp(log(det(g(y))/det(g(x)))/2)
V^a(g,h) = sum_ij g^{ij} δΓ^a_ji - sum_iu g^{ia} δΓ^u_ui.
```

`δΓ` is the previously proved actual variation of the metric-derived Christoffel symbols. `R` is the original complete coordinate scalar-curvature contraction. The proved formula is

```text
L'(0) = - sum_ij (g^(-1) h (g^(-1))^T)_ij · (Einstein(g)_ij + Λ g_ij)
        + sum_a ∂_a[ν_x V^a](x).
```

The derivative in the last term acts on the spatial variable `y`, with reference point `x` fixed. Both index raising and the volume derivative are retained. The contraction is complex bilinear, with no conjugation. No Einstein equation or boundary condition enters this identity.

The literal BM specialization uses `g=g0+εH`, where `H` is the original infinite-cusp metric reconstruction, and an independent original reconstruction as testing field `h`. Frequencies, spectral parameters, and scalar/vector amplitudes of the two fields are independent. For every exterior point, the formula holds throughout an actual nondegenerate neighborhood of `ε=0`. All regularity and symmetry premises are discharged. With `Λ=-3`, its bulk term is exactly the original `D4BMActualMetricSource.source`, contracted with the raised literal test.

## Derivation from the original contractions

The determinant slope already obtained by differentiating its full permutation expansion is identified with `det(g) tr(g^(-1)h)`. The proof differentiates `det(1+tB)` and factors the actual affine determinant; it uses no numerical evaluation. This gives the exact volume variation `tr(g^(-1)h)/2` on the fixed branch.

Differentiate the original Ricci contraction and retain all four connection-product terms. Metric compatibility gives

```text
∂_a g^(-1) = -(Γ_a g^(-1) + g^(-1) Γ_a^T).
```

Finite index rearrangement and torsion-free symmetry then prove

```text
sum_ij g^{ij} δRicci_ij
  = sum_a [∂_a V^a + (sum_b Γ^b_ba) V^a].
```

This is first proved on complete metric two-jets. A separate field proof identifies every displayed derivative with the actual spatial derivative: the inverse variation, its spatial derivative, the linearized connection, and the current. Neither an independent current nor prescribed derivative arrays replace the original fields.

Metric compatibility also proves `tr(g^(-1)∂_a g)/2=sum_b Γ^b_ba`. Direct differentiation of `ν_x` therefore identifies the entire right side with `sum_a ∂_a[ν_x V^a](x)`. Omitting the connection-trace term would give the wrong divergence.

The remaining scalar-curvature variation is the negative contraction of the raised perturbation against Ricci. Combining it with the volume variation and the cosmological volume term yields the displayed negative Einstein-residual pairing. Finally, complete field-jet linearity proves that this is the derivative of the action density formed from `g_t` itself, including every ordered second spatial derivative.

## Formal declarations and audit

Six leaves, 686 lines, 21 new public declarations:

- `HTGeometry.CoordinateMetricVolumeTrace`: complex determinant trace and volume derivative.
- `HTGeometry.CoordinateEinsteinActionCurrent`: complete current and contracted Ricci divergence.
- `HTGeometry.CoordinateEinsteinActionVariation`: actual jet-density variation and the bulk sign.
- `HTGeometry.ComplexMetricActionCurrent`: actual spatial connection/current derivatives.
- `HTGeometry.ComplexMetricActionVariation`: spatial volume density, affine field-jet identity, and the actual-field first variation.
- `RHTower.ThetaCuspHawkingBMActionBoundary`: literal BM source/testing-field specialization without regularity, symmetry, or field-equation premises.

All foreground scratch checks and all six individual final `lake build <module>` audits passed. Final leaf builds had no warnings. New-only `#print axioms` checks for all 21 public declarations report only `propext`, `Classical.choice`, and `Quot.sound`. All six imports are wired into their owning umbrellas. No umbrella build or mathematical computation was run. Installed source, olean, and ilean hashes match all 18 audited artifacts.

Generated indexes were refreshed, all six new imports were verified unique, and `git diff --check` passed. The frontier map's hash is unchanged. Global `scripts/formal_tools.py lint --check-generated` reports two concurrently added SQB modules unreachable from their umbrella: `SelbergNativeConstantMode` and `SelbergResummedSource`. It reports no HB errors; its existing large-file warnings remain. Those unrelated files were preserved.

## Remaining hardest obligation

This closes the local Einstein–Hilbert first-variation identity, extending the [complete mixed bulk coefficient](hb-mixed-action-source-coefficient.md). It does not evaluate the augmented physical action or its endpoint flux. The amplitude neighborhood depends on the exterior point; no common neighborhood reaching both horizon and AdS is supplied. The local spatial density is normalized at that point. Integration requires a common physical volume normalization and justified endpoint limits.

Boundary-counterterm variations, the antisymmetrized action variation giving the physical Green pairing, the complete causal correction fields, and their horizon/AdS contributions remain to be derived. No conservation identity here forces an individual boundary term to vanish. The complete radiative pairing `2 Ω(B(p,p)/2,B(m,m)/2)` has not been shown to vanish at the fixed Hawking clock. RH remains unproved.

The next direct attack is the actual physical Green-current identity and its endpoint evaluation, using this derived current with a common volume normalization and retaining the full source and boundary corrections.
