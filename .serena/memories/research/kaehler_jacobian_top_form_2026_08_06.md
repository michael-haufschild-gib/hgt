# The Jacobian on top differential forms (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **24**.
Continues [[research/eigenvolume_boundary_divisor_eq6_2026_08_06]].

## `KaehlerJacobianTopForm.lean`

- `jacobian R σ φ : Matrix σ σ (MvPolynomial σ R)` — entries `pderiv j (φ (X i))`.
- `pullbackDifferential R σ φ` — the **`MvPolynomial σ R`-linear** map on `Ω[MvPolynomial σ R⁄R]`
  determined by `d x_i ↦ d (φ x_i)`, built with `Module.Basis.constr` on
  `KaehlerDifferential.mvPolynomialBasis`.
- `D_eq_sum_pderiv_smul` — `D p = Σ_j (pderiv j p) • D (X j)`.
- `pullbackDifferential_D_X_eq_sum` — the Jacobian identity.
- `toMatrix_pullbackDifferential` — the matrix is `(jacobian)ᵀ`.
- `det_pullbackDifferential` — `LinearMap.det = jacobian.det`.
- **`exteriorPower_pullbackDifferential_apply`** — on `⋀^(card σ)` the map is multiplication by
  the Jacobian determinant.  Uses `exteriorPower_map_card_apply` from
  `TopExteriorPowerDeterminant.lean`.

This makes the Jacobian factor `J` of the card's order law a **defined object**, not a posited one.

## Key design decision — avoiding semilinearity

`KaehlerDifferential.map R S A B : Ω[A⁄R] →ₗ[A] Ω[B⁄S]` needs `Algebra A B`; for an endomorphism
of `S` that means `letI := φ.toAlgebra` on `Algebra S S`, which **clashes with the identity
instance** (the same trap recorded in
[[research/eigenvolume_horizon_capstone_2026_08_06]]).  The geometric pullback `f*` on forms is
genuinely *semilinear* over φ.

**Fix: do not use `KaehlerDifferential.map` at all.**  Define the pullback directly as the
`S`-linear map `d x_i ↦ d (φ x_i)` via `Basis.constr` — that is exactly how `f*` is written in
coordinates, it is honestly linear, and `LinearMap.det` / `exteriorPower.map` apply unchanged.

## mathlib assets found

`KaehlerDifferential.mvPolynomialBasis R σ : Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]`,
with `mvPolynomialBasis_apply` (`= D (X i)`) and `mvPolynomialBasis_repr_apply`
(`repr (D x) i = pderiv i x`).  **No Jacobian, no top-exterior-power statement.**

## Lean traps

- `Basis.constr_basis` does not resolve — it is `Module.Basis.constr_basis`
  (dot notation on a basis term works, the bare name does not).
- `ᵀ` needs `open scoped Matrix`; without it the error is a bare `expected token`, and the
  resulting broken statement causes confusing downstream `rw` failures.

## Remaining for Theorem A

1. `ord J = e − 1` — the different exponent beyond the Eisenstein presentation.
2. Sheaf of differentials on a scheme (mathlib has only the ring-level `KaehlerDifferential`).
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
