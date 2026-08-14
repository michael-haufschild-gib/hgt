# Elliptic column of ht cards 4/5/6 — state and plan (2026-08-13, checkpoint 5)

## DONE — all axiom-clean, all wired into `GaloisForLFunctions.HTGeometry`, indexes regenerated
Modules added this session (in dependency order):
1. `EllipticMeromorphicOrderTools`, `EllipticEvenPolynomialWeierstrass`,
   `EllipticEvenRationalWeierstrass`, `EllipticFunctionFieldWeierstrass`
   → **elliptic function field theorem** (`mem:ht-cards/elliptic-function-field-theorem-proved-2026-08-13`)
2. `MeromorphicPlaneField`, `MeromorphicPlaneDifferential`, `MeromorphicPlaneTranslation`,
   `MeromorphicPlaneAlgebra`, `EllipticPlaneSubfield`
   → **the field of meromorphic functions on ℂ** + `ellipticSubfield_eq_adjoin`
   (`mem:ht-cards/meromorphic-plane-field-carrier-2026-08-13`)
3. `EllipticIsogenyDeck` (`exists_mem_ellipticSubfield_planeScale_iff`),
   `EllipticIsogenyTailPlane` (`eq_const_of_small_periods`,
   `eq_const_of_forall_mem_range_planeScale`) → card 4 item (1) for elliptic curves
4. `CoefficientDerivation`, `GenericReparametrization`, `ReparametrizationAutomorphism`,
   `TwistedReparametrizationAutomorphism`
   → **the generic reparametrisation** (`mem:ht-cards/generic-reparametrization-built-2026-08-13`)
5. `ReparametrizationDescent` (minimal-denominator descent),
   `EllipticReparamProtocolTail`, `EllipticVelocityTail`
   → **card 4 items (2)(6)(7) for the elliptic column**:
     `deckInvariantField_eq_velocityField`, `differentialIndependent_jet_zero`,
     `eq_constPlane_of_algebraMap_mem_velocityField`
6. `EllipticReparamCurrent` → `deriv_reparamWeierstrassP` (`P′ = Q·u′`),
   `weierstrass_relation_reparam`, **`weierstrass_square_current_reparam`**
   (`(P′)² = (4P³ - g₂P - g₃)(u′)²`, the `(2,2,2,2)` current on the generic carrier)

## NEXT BRICK (card 6 rotation layer) — detailed plan
New module `EllipticRotationTail.lean`:
1. redeclare the LOCAL instances `Differential ℂ` (deriv := 0) and
   `DifferentialAlgebra ℂ (ReparamField MeromorphicPlane)` (copy from `EllipticVelocityTail.lean`;
   they are `local`, so they do NOT propagate);
2. `DerivationClosed velocityField` from `derivationClosed_differentialAdjoin`;
3. `Differential ↥velocityField` via `derivationClosedDifferential`;
   `DifferentialAlgebra ℂ ↥velocityField`, `CharZero ↥velocityField` manually;
4. `v₀ : ↥velocityField := ⟨ReparamField.jet 0, jet_mem_velocityField 0⟩`;
   `DifferentialIndependent ℂ (fun _ : Fin 1 ↦ v₀)` (transfer from
   `differentialIndependent_jet_zero`) and
   `differentialAdjoin ℂ (Set.range fun _ : Fin 1 ↦ v₀) = ⊤` (transfer from
   `velocityField = differentialAdjoin ℂ {jet 0}`, cf. corpus
   `coe_mem_differentialAdjoin_of_subfield` in `TranslationRotationDeckFixedField.lean`);
5. the order-`n` rotation acts by `ReparamField.twistFieldEquiv` with `c = ζ` (a root of unity in ℂ,
   sent into `MeromorphicPlane` by `constPlane`); show its restriction to `↥velocityField` equals
   `torusScaleEquiv` (use `tailEquiv_ext`, as in `TranslationRotationDeckFixedField.lean`);
6. conclude with the corpus
   `RootOfUnityScalingFixedField.setOf_rootOfUnity_invariant_eq_differentialAdjoin_pow`:
   the rotation-invariant part of `C⟨u′⟩` is `C⟨(u′)ⁿ⟩` — the card's compact-signature current.
CRITICAL LESSON (from `mem:ht-cards/stage3-sweep-progress-2`): pass the generator EXPLICITLY
(`v₀ := ⟨…⟩`, hypotheses over `(fun _ : Fin 1 ↦ v₀)`); implicit `adjoinLift` palettes cause a whnf
defeq explosion (>6.4M heartbeats).

## AFTER THAT
- card 4: decide dimension-one scope vs. building several-variable `MeromorphicPlane` for general
  abelian varieties (the gate says "full algebraic-group statement").
- card 6: assemble the six signatures and promote.
- card 5: Lie–Cartan rank ≤ 3 (deep, separate).
- cards 1, 2, 3: untouched this session; see `mem:ht-cards/stage3-sweep-2026-08-13` for their recon.
