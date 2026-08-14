# Nonautonomous isogeny tails split time into position and velocity — formalized

- **ID:** `nonautonomous-isogeny-tail-time-splitting-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `nonautonomous-isogeny-tail-time-splitting.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

The abstract protocol layer — prefix kernels, erased sector, reversible quotient, flat transport:

```text
formal/GaloisForLFunctions/HTGeometry/NonautonomousDeckClosure.lean
formal/GaloisForLFunctions/HTGeometry/NonautonomousIsogenyTransport.lean
formal/GaloisForLFunctions/HTGeometry/NonautonomousJetVelocityTransport.lean
formal/GaloisForLFunctions/HTGeometry/NonautonomousProtocolFlatSystem.lean
formal/GaloisForLFunctions/HTGeometry/NonautonomousErasedDeckBridge.lean
formal/GaloisForLFunctions/HTGeometry/DeckDegreeCriterion.lean
formal/GaloisForLFunctions/HTGeometry/DeckDegreeUpperBound.lean
formal/GaloisForLFunctions/HTGeometry/DeckDegreeUpperBoundBridge.lean
formal/GaloisForLFunctions/HTGeometry/InvariantFractionRing.lean
formal/GaloisForLFunctions/HTGeometry/PrefixDeckFromInvariantRing.lean
formal/GaloisForLFunctions/HTGeometry/DifferentialSpanningBasis.lean
formal/GaloisForLFunctions/HTGeometry/DifferentialSubfieldTransfer.lean
```

The multiplicative column `G_m` and the split torus `G_m^r`:

```text
formal/GaloisForLFunctions/HTGeometry/RadicalDifferentialAdjoin.lean
formal/GaloisForLFunctions/HTGeometry/HypertranscendentalPow.lean
formal/GaloisForLFunctions/HTGeometry/PowerEndomorphism.lean
formal/GaloisForLFunctions/HTGeometry/MultiplicativeProtocolWitness.lean
formal/GaloisForLFunctions/HTGeometry/RatFuncScaleInfiniteStabilizer.lean
formal/GaloisForLFunctions/HTGeometry/ScalarInfiniteScaleFixedField.lean
formal/GaloisForLFunctions/HTGeometry/MultiplicativeProtocolLogCurrentTail.lean
formal/GaloisForLFunctions/HTGeometry/ScalarTailRationalTriviality.lean
formal/GaloisForLFunctions/HTGeometry/MultiplicativeProtocolAlgClosed.lean
formal/GaloisForLFunctions/HTGeometry/TorusMonomialFamily.lean
formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentTransfer.lean
formal/GaloisForLFunctions/HTGeometry/TorusMonomialIndependence.lean
formal/GaloisForLFunctions/HTGeometry/TorusInvariantField.lean
formal/GaloisForLFunctions/HTGeometry/TorusVelocityIndependence.lean
formal/GaloisForLFunctions/HTGeometry/TorusExpandingProtocolTail.lean
formal/GaloisForLFunctions/HTGeometry/TorusInvariantMonomials.lean
formal/GaloisForLFunctions/HTGeometry/TorusProtocolMonomialTail.lean
```

The elliptic column, at dimension one:

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
formal/GaloisForLFunctions/HTGeometry/EllipticReparamProtocolTail.lean
formal/GaloisForLFunctions/HTGeometry/EllipticVelocityTail.lean
```

The complex-torus column, in every dimension:

```text
formal/GaloisForLFunctions/HTGeometry/EntireFunctionField.lean
formal/GaloisForLFunctions/HTGeometry/EntireDirectionalDerivation.lean
formal/GaloisForLFunctions/HTGeometry/EntireTranslation.lean
formal/GaloisForLFunctions/HTGeometry/EntireDenseInvariant.lean
formal/GaloisForLFunctions/HTGeometry/GeneralCoefficientDerivation.lean
formal/GaloisForLFunctions/HTGeometry/MultiReparametrization.lean
formal/GaloisForLFunctions/HTGeometry/MultiReparametrizationAutomorphism.lean
formal/GaloisForLFunctions/HTGeometry/ComplexTorusTail.lean
formal/GaloisForLFunctions/HTGeometry/ComplexLatticeDensity.lean
formal/GaloisForLFunctions/HTGeometry/ComplexTorusVelocityTail.lean
formal/GaloisForLFunctions/HTGeometry/ComplexTorusIsogenyDeck.lean
formal/GaloisForLFunctions/HTGeometry/ComplexTorusMaurerCartan.lean
formal/GaloisForLFunctions/HTGeometry/ComplexTorusPositionVelocity.lean
```

All are imported by the theorem-area umbrella `GaloisForLFunctions.HTGeometry`.

## The formal theorem chain

**`(1)` exact deck closure.**  Abstractly, `nonautonomousTail_eq_fixedField_erasedClosure` and its
five hypothesis packages in `NonautonomousErasedDeckBridge.lean` (degree count, equivariance,
invariant ring, stabilization) reduce the tail identity to purely algebraic data; Artin's theorem in
the form `FixedPoints.finrank_eq_card` supplies one inequality and
`card_le_finrank_of_le_fixedField` the other.  Concretely,
`multiplicativeProtocol_nonautonomousTail_eq_fixedField` inhabits that package for `G_m`, and
`exists_mem_torusSubfield_fieldScaleEquiv_iff` gives the depthwise deck identity analytically: an
element is a pullback along `z ↦ m z` of a function of `V / Λ` exactly when every translation `t`
with `m t ∈ Λ` fixes it.  `eq_constEntire_of_forall_mem_range_fieldScaleEquiv` and
`eq_const_of_forall_mem_range_planeScale` close the intersection over all depths.

**`(2)` exact position–velocity generators.**  `torusDeckFixedField_eq_torusBaseAdjoinJets`: for an
arbitrary set of deck translations of `ℂ ^ n`, with no hypothesis on the protocol, the invariants on
the generic reparametrisation are exactly the field generated by the invariant functions of the
position and the Maurer–Cartan velocities.  `torusDeckInvariantField_eq_torusBaseAdjoinJets` is the
protocol form.  Earlier columns: `erasedQuotientEquivPositionVelocity` abstractly,
`multiplicativeProtocol_nonautonomousTail_position_velocity` for `G_m`,
`torusProtocol_nonautonomousTail_eq_torusInvariantMonomialField` for `G_m^r`.

**`(3)` and `(4)` transport of the erased and reversible sectors.**  `prefixKernel_succ`,
`erasedSector_comap`, `erasedClosure_comap`, `reversibleStepEquiv`, `reversibleTransport`,
`reversibleHolonomy` — proved for arbitrary commutative topological groups.

**`(5)` flat velocity transport.**  `SplitJetMorphism.normalize_comm` and `velocityEquiv`
abstractly; `logDeriv_powerEndo` for `G_m`; `logDeriv_monomialFamily` for `G_m^r`;
`deriv_fieldScaleEquiv_coordEntire` with `bijective_velocity_transport` for `ℂ ^ n / Λ` — the
isogeny `z ↦ m z` multiplies the velocity by `m`, and that is an automorphism for `m ≠ 0`.

**`(6)` the purely expanding case.**  `torusDeckInvariantField_eq_torusVelocityField`: for
accumulated degrees of unbounded norm on a compact complex torus, the deck-invariant field of the
generic reparametrisation is `C⟨u_1′, …, u_n′⟩`.  The analytic input is
`dense_divisionPoints` — a cocompact period lattice divided by scalars of unbounded norm fills the
space — feeding `eq_constEntire_of_dense_translation_invariant` and the minimal-denominator descent
`MultiReparamField.exists_representation_coeff_mem`.  Equivalently,
`translationInvariantBase_divisionPoints_eq_bot` says the position invariants of `(2)` collapse to
the constants in this branch.

**`(7)` the dimension count.**  `differentialIndependent_torusVelocity`: the `n` velocity
coordinates are differentially independent over `ℂ`, so `dtrdeg_C T_i = n = dim G_i`; and
`eq_constEntire_of_algebraMap_mem_torusVelocityField`: an element of the function field of the torus
lying in the tail is a constant, i.e. `T_i ∩ C(G_i) = C`.
`differentialTranscendenceDegree_differentialAdjoin_eq` is the abstract counterpart.

**The Lie algebra, in coordinates.**  `deriv_coordEntire`: the Maurer–Cartan velocity of the
tautological point of `ℂ ^ n / Λ` is exactly the tuple of reparametrisation velocities.  This is the
"coordinate description of `Lie(G_i)`" that earlier passes recorded as the single remaining
scheme-level input; in the analytic model it is a one-line computation of `∂_k z_j`.

**An unconditional witness.**  `stdTorus_phase_tail` states `(6)`, `(7a)` and `(7b)` together for the
standard torus `ℂ ^ n / (ℤ + iℤ)^n` with accumulated degrees `2 ^ k`, with no hypothesis at all: the
lattice (`stdPeriodLattice`), the protocol and the point (`coordEntire`) are all exhibited.

## What is proved and what is not

Proved unconditionally in Lean: statements `(1)`–`(7)` of the card, for every connected commutative
algebraic group over `ℂ`.  The classes are covered as follows.  In characteristic zero `G_a` has no
nontrivial isogeny; the split torus `G_m^r` settles every connected commutative linear group; and
every connected commutative complex algebraic group is, as a complex Lie group, `ℂ ^ n / Λ`, which
the complex-torus column settles in every dimension.  The purely expanding branch `H_i = G_i` of
`(6)`/`(7)` is exactly the cocompact case, and `(2)` covers the general branch with no hypothesis on
the protocol.

Not claimed here: the scheme-theoretic reading.  mathlib's `AlgebraicGeometry/Group/` has no
quotient by a finite subgroup scheme and no `Lie` functor, so the complex-torus column is carried out
analytically — with the fraction field of the entire functions of `ℂ ^ n`, its directional
derivations, its translations, and the generic reparametrisation — rather than through group schemes.
Nothing is assumed in exchange: no isogeny degree formula, no Galois descent for finite étale
isogenies, and no uniformization theorem appears anywhere in this column.  Also not claimed: the
abstract bridge `nonautonomousTail_eq_fixedField_erasedClosure_of_finrank_le` still carries its
degree estimate as a hypothesis; it is inhabited by the multiplicative protocol, and the analytic
columns bypass it entirely.

## Verification

Each module elaborates under `lake env lean` and builds under `lake build`; each is imported by
`GaloisForLFunctions.HTGeometry`.  Every theorem named above reports
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.  The project lint gate reports no
proof debt and no unreachable module for any of them.
