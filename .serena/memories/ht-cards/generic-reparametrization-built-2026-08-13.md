# Generic reparametrisation of a differential field — BUILT (2026-08-13)

New reusable infrastructure (all axiom-clean, wired into `GaloisForLFunctions.HTGeometry`).

## `HTGeometry/CoefficientDerivation.lean`
Coefficient derivation of `MvPolynomial σ K` induced by `Differential K`.
TRICK: dual numbers. `coeffGraphHom : K →+* DualNumber (MvPolynomial σ K)`,
`a ↦ (C a, C (δ a))` — `map_mul` IS Leibniz; then `coeffEval = MvPolynomial.eval₂Hom coeffGraphHom
(fun i => TrivSqZeroExt.inl (X i))`; `coeffEval_fst` by `MvPolynomial.ringHom_ext` against
`TrivSqZeroExt.fstHom ℤ`; the `.snd` component is the derivation and Leibniz comes free from
`TrivSqZeroExt.snd_mul`.
Decls: `coeffGraphHom`, `coeffEval`, `coeffEval_fst`, `coeffDerivFun(_C/_X/_zero/_add/_mul)`,
`coeffDerivation`, `coeffDerivation_apply`.

## `HTGeometry/GenericReparametrization.lean`
`ReparamPoly K := MvPolynomial ℕ K`, `ReparamField K := FractionRing (ReparamPoly K)`.
`polyDerivation K := (X 0) • coeffDerivation K ℕ + restrictScalars ℤ (mkDerivation K (X ∘ succ))`.
`fieldDerivation` via corpus `fractionRingDerivation`; `instance : Differential (ReparamField K)`.
KEY: `deriv_jet : (jet i)′ = jet (i+1)`, `deriv_algebraMap : (algebraMap a)′ = algebraMap (δ a) * jet 0`
(the chain rule). Instances Field/Algebra K/IsScalarTower/CharZero mirror the corpus's `JetField`.

## `HTGeometry/ReparametrizationAutomorphism.lean`
`mvPolynomial_derivation_ext` (ℤ-derivations agreeing on C and X are equal),
`polyEquiv e := MvPolynomial.mapEquiv ℕ e`, `fieldEquiv e := IsFractionRing.ringEquivOfRingEquiv`,
`fieldEquiv_jet/base/symm_jet/symm_base`, `conjDerivation`,
**`fieldEquiv_deriv`**: a base automorphism commuting with δ extends to one commuting with D.

## WHY
Makes `(℘, ℘')` a differential-generic point of the elliptic curve while the deck action stays the
analytic translation of the plane — so the ℘ ADDITION THEOREM IS NEVER NEEDED.

## NEXT STEP (identified, not yet built)
The isogeny protocol map in the reparam model is a **c-twisted** automorphism: `planeScale m` does
not commute with `d/dz` but satisfies `(planeScale m a)′ = m · planeScale m (a′)`. Its extension
must send `jet i ↦ c · jet i` with `c = m`. So generalise `fieldEquiv` to:
  given `e : K ≃+* K` and a constant `c` with `δ (e a) = c * e (δ a)` and `δ c = 0`,
  the map `C a ↦ C (e a)`, `X i ↦ C c * X i` on `ReparamPoly K` is a ring equiv whose
  fraction-field extension commutes with `D`.
Then: card 4 items (2)/(6)/(7) for the elliptic column, then cards 6 and 5.
Also still needed for (7): `jet 0` differentially transcendental (algebraic independence of the
jet variables over K, triangularity argument).
