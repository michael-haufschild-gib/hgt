# First-order nonautonomous rational tails are parabolic-orbifold currents — formalized

- **ID:** `nonautonomous-rational-first-order-tail-orbifold-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `nonautonomous-rational-first-order-tail-orbifold-law.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

Symbol extraction, expansion budgets and signature classification:

```text
formal/GaloisForLFunctions/HTGeometry/FirstOrderRationalTailSymbol.lean
formal/GaloisForLFunctions/HTGeometry/NonautonomousFirstOrderTailSymbol.lean
formal/GaloisForLFunctions/HTGeometry/NonautonomousFirstOrderTailSymbolLaw.lean
formal/GaloisForLFunctions/HTGeometry/VerticalSymbolTransformation.lean
formal/GaloisForLFunctions/HTGeometry/ExpandingProtocolVanishing.lean
formal/GaloisForLFunctions/HTGeometry/EuclideanConeSignature.lean
formal/GaloisForLFunctions/HTGeometry/ParabolicSignatureClassification.lean
formal/GaloisForLFunctions/HTGeometry/HyperbolicSignatureGap.lean
```

Deck fixed fields and transported currents of the six parabolic signatures:

```text
formal/GaloisForLFunctions/HTGeometry/ScalingInvariantRationalFunction.lean
formal/GaloisForLFunctions/HTGeometry/LogarithmicDerivativeFixedField.lean
formal/GaloisForLFunctions/HTGeometry/ChebyshevQuadraticCurrent.lean
formal/GaloisForLFunctions/HTGeometry/EuclideanOrbifoldCurrents.lean
formal/GaloisForLFunctions/HTGeometry/RootOfUnityScalingFixedField.lean
formal/GaloisForLFunctions/HTGeometry/TranslationRotationDeckFixedField.lean
formal/GaloisForLFunctions/HTGeometry/DihedralInversionFixedField.lean
```

The compact-signature protocol presentation, on a carrier where the orbifold coordinate is a
differential-generic point:

```text
formal/GaloisForLFunctions/HTGeometry/EllipticMeromorphicOrderTools.lean
formal/GaloisForLFunctions/HTGeometry/EllipticEvenPolynomialWeierstrass.lean
formal/GaloisForLFunctions/HTGeometry/EllipticEvenRationalWeierstrass.lean
formal/GaloisForLFunctions/HTGeometry/EllipticFunctionFieldWeierstrass.lean
formal/GaloisForLFunctions/HTGeometry/MeromorphicPlaneField.lean
formal/GaloisForLFunctions/HTGeometry/MeromorphicPlaneDifferential.lean
formal/GaloisForLFunctions/HTGeometry/MeromorphicPlaneTranslation.lean
formal/GaloisForLFunctions/HTGeometry/MeromorphicPlaneAlgebra.lean
formal/GaloisForLFunctions/HTGeometry/EllipticPlaneSubfield.lean
formal/GaloisForLFunctions/HTGeometry/EllipticIsogenyDeck.lean
formal/GaloisForLFunctions/HTGeometry/EllipticIsogenyTailPlane.lean
formal/GaloisForLFunctions/HTGeometry/CoefficientDerivation.lean
formal/GaloisForLFunctions/HTGeometry/GenericReparametrization.lean
formal/GaloisForLFunctions/HTGeometry/ReparametrizationAutomorphism.lean
formal/GaloisForLFunctions/HTGeometry/ReparametrizationDescent.lean
formal/GaloisForLFunctions/HTGeometry/TwistedReparametrizationAutomorphism.lean
formal/GaloisForLFunctions/HTGeometry/EllipticReparamProtocolTail.lean
formal/GaloisForLFunctions/HTGeometry/EllipticVelocityTail.lean
formal/GaloisForLFunctions/HTGeometry/EllipticReparamCurrent.lean
formal/GaloisForLFunctions/HTGeometry/PlaneScaleSimilarity.lean
formal/GaloisForLFunctions/HTGeometry/EllipticRotationTail.lean
formal/GaloisForLFunctions/HTGeometry/EllipticPhaseTailReparam.lean
```

All are imported by the theorem-area umbrella `GaloisForLFunctions.HTGeometry`.

## The formal theorem chain

**§1, the symbol comparison.**  `symbolDegree_comp_scaling` and `symbolCoeff_comp_scaling` show that
the fibre coordinate's exponent at vertical infinity is invariant under the substitution and that
the leading coefficient transforms as a `k`-differential; `symbolDegree_const_of_protocol` makes `k`
phase-independent along the whole protocol; `symbol_comparison` states both together.
`verticalRatFuncLaurentWeight_eq_of_transport` and
`verticalRatFuncLaurentCoefficient_eq_zpow_of_transport` are the underlying Laurent-transport
statements, and `eq_zero_of_expanding_degree_law` rules out a nonconstant order-zero tail.

**§2, the transient.**  `eventually_eq_zero_of_expanding_bound`: multiplicities obeying
`2^n · Z_n ≤ Z_0` vanish from some depth on.

**§3, quantization and the signature.**  `weight_quantization` is `(8)`: past the finite exceptional
bound a shifted tensor order is `0` or a positive divisor of `ℓ`.  `parabolic_of_pole_orders` turns
the divisor-degree budget into `∑(1 - 1/ν) = 2`, and `parabolicSphereSignature_iff` /
`parabolic_signature_classification` prove that the six Euclidean signatures are exactly its
solutions; `hyperbolic_signature_gap` separates the hyperbolic ones by `1/42`.

**§4, the tail.**  Cusp `(∞,∞)`: `iInter_powAdjoin_eq_logDerivField` computes
`{x | ∀ n, x ∈ F⟨y^{D n}⟩} = F⟨y′/y⟩`.  Dihedral `(2,2,∞)`:
`setOf_scaling_inversion_invariant_eq_differentialAdjoin_sqCurrent` with
`logDeriv_sq_eq_chebyshev_current`.  Compact signatures:
`setOf_translation_rotation_invariant_eq_differentialAdjoin_derivPow` and its tower form
`setOf_forall_fixed_eq_differentialAdjoin_derivPow` compute the deck fixed field, and
`weierstrass_square_current`, `weierstrass_cubic_current`, `weierstrass_quartic_current`,
`weierstrass_sextic_current` are the transported currents.

**§4, the protocol presentation of the compact signatures.**  The carrier is
`ReparamField MeromorphicPlane`: the meromorphic functions of the plane — a genuine field, built as
germs along the codiscrete filter — composed with a completely free reparametrisation of the
variable, with the chain-rule derivation `(a)′ = (δa)·u′` (`ReparamField.deriv_algebraMap`,
`ReparamField.deriv_jet`).  There:

* `exists_rational_weierstrass_representation` and `ellipticSubfield_eq_adjoin` identify the phase
  fields: the `Λ`-elliptic functions are exactly `ℂ⟮℘, ℘'⟯`;
* `exists_mem_ellipticSubfield_planeScale_iff` is the depthwise deck identity: the image of the
  isogeny pullback is the fixed field of its division points;
* `deckInvariantField_eq_velocityField` computes the translation layer, `C⟨u′⟩`;
* `setOf_deck_rotation_invariant_eq_differentialAdjoin_jetPow` adds the rotation layer, `C⟨(u′)ⁿ⟩`;
* `iInter_baseAdjoinJets_eq_velocityField` and
  `iInter_baseAdjoinJets_rotation_eq_differentialAdjoin_jetPow` are the phase tail itself: the
  intersection of the phase fields of all depths;
* `weierstrass_square_current_reparam` identifies the current downstairs:
  `(P′)² = (4P³ - g₂P - g₃)(u′)²`.

No uniformization theorem is used, and no `℘` addition theorem: the deck transformations are the
analytic translations and scalings of the plane, transported to a carrier on which the orbifold
coordinate is differential-generic.

## What is proved and what is not

Proved unconditionally in Lean: every step of the card's proof listed above, and the elliptic
function field theorem `C(℘)·f = A(℘) + ℘'·B(℘)` that the compact presentation rests on, which
mathlib does not carry.

Not claimed here: the three-way equivalence `1 ⟺ 2 ⟺ 3` is formalized step by step, not as one
assembled biconditional; and the tail computation for the compact signatures is carried out on the
generic reparametrisation of the meromorphic plane field, which is one presentation of the card's
free differential model rather than a statement about every rational protocol.

## Verification

Each module elaborates under `lake env lean`, is imported by `GaloisForLFunctions.HTGeometry`, and
every theorem named above reports `[propext, Classical.choice, Quot.sound]` (several report only
`[propext, Quot.sound]`) under `#print axioms`.  The project lint gate reports no proof debt and no
unreachable module for any of them.
