# ULF-FRM-3 — Lean certification record

Card: `gaussian-quotient-fusion-capital-exact-depth-and-testing-properness-law.md`
Promoted to Stage 3 on 2026-08-30.

## Modules

| Module | Role |
|---|---|
| `GaloisForLFunctions.HTGeometry.QuotientFusionProjectionGenesis` | pre-existing: the *scalar* quotient--fusion genesis, `sharedEnergy`, `separateEnergy`, `generatedEnergy`, `quotientFusionGenesis_eq_zero_iff` |
| `GaloisForLFunctions.HTGeometry.GaussianShiftInformation` | **new** shared layer: `lintegral_pi_prod`, `pi_withDensity`, `map_withDensity_measurableEquiv`, the Cameron--Martin density, the Gaussian MGF, the Rényi/Hellinger integrals, `stdGaussian_prodL2` |
| `GaloisForLFunctions.HTGeometry.GaussianQuotientFusionCapital` | **new**: the whole card |
| `GaussianFormationRateRegion`, `GaussianPacketTestingLaw` | reused from `ULF-FRM-4` |

All are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Card result → Lean declaration

| Card | Lean |
|---|---|
| `(GQF.1)`–`(GQF.3)` fused gauge, local histories | `fusedMap`, `fusedRange`, `historyVector`, `localOptimalHistory` |
| `(GQF.2)` inherited residual `ℓ` | `inheritedResidual` |
| `(GQF.4)` genesis signal `g` | `genesisSignal` |
| `(GQF.5)` `E_sep = ‖ℓ‖²`, `Q = ‖g‖²` | `norm_sq_inheritedResidual`, `norm_sq_genesisSignal` |
| `(GQF.6)` `E_shared = E_sep + Q`, zero classification | `sharedEnergy_eq_norm_sq`, `norm_genesisSignal_eq_zero_iff` |
| `(GQF.8)` `L ⊥ R`, `ℓ ∈ L`, `g ∈ R` | `coordRange`, `genesisSignal_mem_coordRange`, `inheritedResidual_mem_orthogonal`, `inner_inheritedResidual_genesisSignal` |
| **Thm 2.1**, `(GQF.9)` factorization | `gaussianPacket_factorization` (+ `starProjection_coordRange_split`, `coe_orthogonalProjectionOnto_genesis/inherited`) |
| `(GQF.10)` multiplicative affinity | `gaussianAffinity_fused`, `gaussianRenyiIntegral_orthogonal`, `norm_sq_inheritedResidual_add_genesisSignal` |
| `(GQF.11)` `C_H = Q/8`, `D₀ = D₁ = Q/2`, `J = Q` | `gaussianCapital_half`, `klDiv_stdGaussian_shift`, `klDiv_stdGaussian_shift_left`, `formationJeffreys_stdGaussian_shift` |
| `(GQF.12)` `C_α = α(1-α)Q/2` | `gaussianCapital`, `gaussianRenyiIntegral_eq_exp_neg_capital` |
| `(GQF.13)`–`(GQF.15)` Gaussian integrals | `lintegral_cameronMartin_sqrt`, `klDiv_stdGaussian_shift`, `lintegral_cameronMartin_rpow` |
| **Thm 3.1**, `(GQF.16)`, `(GQF.17)` | `nonempty_gaussianFormation_iff` (both halves; sufficiency by the explicit garbling `(GQF.18)`–`(GQF.19)` = `garblingOp`, `gaussianGarbling`) |
| **Cor 3.2**, `(GQF.20)` | `nonempty_gaussianFormation_genesis_iff` |
| `(GQF.21)` `d_max = ⌊b/Q⌋` | `depth_le_floor_iff` |
| **Thm 4.1**, `(GQF.22)`, `(GQF.23)` | `genesis_eq_zero_of_cofinal`, `norm_genesisSignal_eq_zero_iff` |
| **Cor 4.2**, `(GQF.24)`–`(GQF.26)` | `displacement_eq_zero_of_cofinal` |
| **Thm 5.1**, `(GQF.27)` | `bayesError_genesisPacketPow` |
| `(GQF.28)` testing exponent `Q/8` | `tendsto_testing_exponent` (with `gaussianReal_Iic_neg_le` — a Chernoff bound from the Gaussian MGF — and `le_gaussianReal_Iic_neg`) |
| `(GQF.29)`, `(GQF.30)` equivariance | `localOptimalHistory_equivariant`, `genesisSignal_equivariant`, `starProjection_linearIsometryEquiv` |
| `(GQF.31)` `Q(Ux) = Q(x)` | `generatedEnergy_equivariant` |
| `(GQF.32)` packet isomorphism | `gaussianPacket_isometry_map` |

## Infrastructure built here

* `lintegral_pi_prod` — Tonelli for a coordinatewise product on a finite product measure.  Mathlib
  has only the Bochner analogue.
* `pi_withDensity` and `map_withDensity_measurableEquiv` — the two transport lemmas that give the
  coordinate-free **Cameron--Martin density** `stdGaussian_shift_eq_withDensity` and hence
  `rnDeriv_stdGaussian_shift`.
* `lintegral_exp_inner_stdGaussian` — the multivariate Gaussian moment generating function, from
  which both the Rényi integrals and the Chernoff tail bound follow.
* `starProjection_linearIsometryEquiv` — an orthogonal isomorphism preserving a subspace commutes
  with the orthogonal projection onto it.

## Verification

* Both new modules elaborate with 0 errors and build.
* `#print axioms` over every public theorem of `GaussianShiftInformation` and
  `GaussianQuotientFusionCapital` (57 + 47 declarations, counted across the two audits) reports only
  `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration; the only hypotheses are the
  card's own data conditions.
