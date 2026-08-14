# Complex-dynamics substrate shared by the RG/clock hypertranscendence cards — formalized

Five cards of the `nad` folder (`asymmetric-binary-tree-channel-rg-clock-hypertranscendence`,
`bethe-padic-holographic-rg-clock-hypertranscendence`,
`diamond-ising-da-scheme-rg-generation-hypertranscendence`,
`diamond-ising-family-rg-generation-hypertranscendence`,
`postselected-qubit-clock-integrability-fracture`) share one dynamical mechanism.  This file records
the Lean surface they share.  All modules are wired into `GaloisForLFunctions.HTGeometry`; every
declaration resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

## The real interval and the interior fixed point

| Module | Content |
|---|---|
| `HTGeometry/RealTreeBPFirstCrossing.lean` | `exists_first_zero_of_pos_of_neg`, `deriv_nonpos_of_first_zero` (both mathlib-absent), the map `treeBP`, its exact derivative `hasDerivAt_treeBP`, the multiplier `hasDerivAt_treeBP_zero`, and **`exists_treeBP_interior_fixedPoint`** — the interior non-superattracting, non-repelling fixed point, with channel and symmetric specializations |
| `HTGeometry/TreeBPComplexMultiplier.lean` | `treeBPC`, `treeBPC_ofReal`, `hasDerivAt_treeBPC`, `exists_treeBPC_nonsuper_nonrepelling_fixedPoint`, and **`treeBPC_not_conj_special`** |

## Exclusion of every family on the Ritt list

`HTGeometry/SpecialMapFixedPointMultiplier.lean`:

- `multiplier_eq_of_conj` — the multiplier is a conjugacy invariant;
- `powerMap_multiplier`, `not_conj_powerMap_of_nonsuper_nonrepelling`;
- `invPowerMap_multiplier`, `not_conj_invPowerMap_of_nonrepelling`;
- `exists_joukowski`, `dicksonMap_joukowski`, `dicksonMap_deriv_joukowski`,
  `two_le_norm_dicksonMap_multiplier`, `not_conj_dicksonMap_of_nonrepelling` (Chebyshev, through
  mathlib's Dickson identity and `T_derivative_eq_U`);
- `hasDerivAt_weierstrassP`, `norm_derivWeierstrassP_eq_of_weierstrassP_eq`,
  `norm_multiplier_lattes`, `not_lattes_of_nonrepelling` (Lattès, through the Weierstrass
  differential equation);
- `norm_multiplier_of_linearizingSemiconj` — the mechanism common to all three branches.

## The Poincaré/Schröder function

| Module | Content |
|---|---|
| `HTGeometry/KoenigsLinearizationGerm.lean` | `exists_quadratic_bound`, `exists_contraction_ball`, `orbit_norm_le`, `koenigsApproxGerm_dist_succ`, `koenigsApproxGerm_tendstoUniformlyOn`, `koenigsGerm_differentiableOn`, `koenigsGerm_zero`, `deriv_koenigsGerm_zero`, `koenigsGerm_semiconj`, `eq_koenigsGerm_of_linearizer` — **Koenigs' theorem, existence and uniqueness**, for a general holomorphic germ |
| `HTGeometry/PoincareFunctionGerm.lean` | `exists_poincare_of_linearizer`, `exists_poincare_koenigs` — local inversion gives `Φ(0)=0`, `Φ′(0)=1`, `Φ(μw) = g(Φw)` |
| `HTGeometry/EntirePoincareExtension.lean` | `poincareApprox_eq_of_le`, `exists_admissible_exponent`, **`exists_entire_poincare`** — the germ extends to an entire solution on `ℂ` |

mathlib has none of this and the corpus previously had Koenigs only for `z² + c`
(`Bottcher/KoenigsLinearization.lean`).

## Card-specific algebra

`HTGeometry/AsymmetricBinaryTreeRG.lean`, `HTGeometry/BetheHolographicIsingRG.lean`,
`HTGeometry/DiamondIsingRG.lean`, `HTGeometry/DiamondIsingFamilyRG.lean`,
`HTGeometry/PostselectedQubitRationalDynamics.lean` — the exact rational families, degree and
primitive noncancellation, fixed anchors and multipliers, derivative cross-numerators, block-weight
identities, and the projective/qubit factorizations.

## Boundary

The converse classification — Ritt / Becker--Bergweiler: *a rational map whose Schröder/Poincaré
function is differentially algebraic is Möbius-conjugate to a power, inverse-power, signed Chebyshev
or Lattès map* — remains a cited classical input, exactly as each card states in its own Lean
boundary.  It is not postulated in Lean: no axiom, no `sorry`, no placeholder.  What the corpus now
owns is the whole *other* direction, which is the part these cards prove themselves: the interior
fixed point, and the exclusion of all four families from it.
