# Private claim-trace audit

Audit date: 2026-08-04. Manuscript: `submission.tex`.

This file is private verification evidence. The paper contains no reference to Lean.

## Central status

- `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`: coefficient-generated published Cartan forms, locally
  and after global physical-rank fusion, satisfy
  `negative inertia + nullity <= 1` because all nonpositive energy factors through one rank port.
- `[CANDIDATE NEW ARITHMETIC BRIDGE]`: relative-channel-invisible scalar twists are exactly
  componentwise central; coefficient generation leaves one component, determinant restriction
  reads its scalar with exponent `M`, and the rank-powered rational-adelic Xi transgression is
  `(delta_n(rho)^M - 1)c_rho`.
- `[CANDIDATE NEW STOKES--MERTENS LAW]`: reflection pairs two normalized unsquared Xi
  transgressions into a positive prime energy; positive rank gives an exact finite vanishing locus,
  and rank-scaled critical windows converge to one universal Mertens profile.
- `[LEAN-PROVED]`: exact coefficient, analytic-wall, microlocal, global, Rees, corona, tangent,
  leg, and spectral statements listed below compile without project axioms.
- `[NOVELTY UNVERIFIED]`: priority remains provisional until independent expert circulation.

## Exact theorem coverage

| Paper result | Exact private witness | Coverage |
|---|---|---|
| Highest-difference law | `FinitePuiseuxFamily.contactNumerator_acute`, `contactNumerator_pos_of_ne` in `StokesFinitePuiseuxDendrogram.lean` | Exact coefficient theorem |
| Canonical coefficient dendrogram | `NatContactDendrogram.canonicalDendrogramHierarchy`; `FinitePuiseuxFamily.canonicalCuts_contact_eq` | Exact hierarchy and contact reconstruction |
| Coefficient coarea identity | `PuiseuxOrbitCoareaDatum.cartanQuadratic_eq_coefficient_onePort`; `OrbitCoareaDatum.contactPairing_eq_root_rank_sq_sub_blockEnergy` | Exact quadratic identity |
| Galois integrality | `EquivariantFinitePuiseuxFamily.coverDegree_mul_orbitContactIndex` | Actual cyclic equivariance, no supplied divisibility |
| Published Cartan identification | `OrbitCoareaDatum.publishedCoreCartanQuadratic_eq_cartanQuadratic`; `coefficientPublishedCoreCartanForm_apply` in `StokesPublishedDiagramBridge.lean` | Exact published matrix formula |
| Local joint inertia/nullity | `equivariantPublishedCoreCartanForm_sigNeg_add_radical_finrank_le_one` | Genuine continuation-orbit Cartan form |
| Quasi-Hamiltonian dimension | `WildSmoothReduction.tangent_finrank_eq_expectedDim`; `cohomologicalEuler_eq_expectedEuler` in `StokesQuasiHamiltonianReductionDimension.lean` | Source rank-nullity derivation from explicit factor counts |
| Global coefficient Witt law | `EquivariantGlobalWitt.globalOrbitWittForm_sigNeg_add_radical_finrank_le_one` | Genuine orbit quotient at every marked point; every genus |
| Handle and sewing laws | `GlobalPuiseuxWitt.globalRankCoefficient_succ_genus`; `scalarRankCoefficient_sewing` | Exact common-rank coefficient laws |
| Microlocal quotient | `CellularStokesCategory.microstalkFunctor`; `arc_wall_vanishing_exact`; `nearbyToVanishing_surjective` | Functorial quotient and exactness |
| One oriented vanishing cycle | `CellularStokesCategory.exponentialGerm_exactly_one_vanishing` | Exact alternative with positive fiber rank |
| Complete analytic wall classification | `AnalyticWall.cellularWallEquivAnalytic`; `analyticStokesWall_card`; `analyticStokesWall_simple` | Exact phase-zero set, cardinality, simplicity |
| Analytic cyclic order/orientation | `AnalyticWall.labelledWallAngle_nextWall`; `labelledWall_transverse_sign` | Successor is rotation by `pi/k`; derivative sign exact |
| Actual coefficient-pair walls | `AnalyticWall.branchPairWallEquivAnalytic` | Uses highest nonzero difference coefficient of actual branches |
| Exponential microsupport and cycle | `CellularMicrolocal.isInMicrosupport_iff_active`; `fullCharacteristicMultiplicity_sum`; `directedDecayMicroRank_sum` | Exact microstalk ranks and masses |
| Analytic-wall characteristic cycle | `AnalyticMicrolocal.isInAnalyticMicrosupport_iff_active`; `analyticWall_transverse_sign`; `branchPairFullCharacteristicMultiplicity_sum` | Invariants transported onto actual phase-zero subtype |
| Directed microlocal Hom index | `PuiseuxOrbitCoareaDatum.normalizedMicrolocalHomMass_eq` in `StokesPuiseuxMicrolocalIndex.lean` | Exact normalized branch-pair sum |
| Categorical microlocal coarea | `categoricalMicrolocalPairing_eq_contactPairing`; `categoricalMicrolocalIndex_eq_coarea_onePort` in `StokesUniversalMicrolocalWittLaw.lean` | Exact equality of microstalk and coarea polarizations |
| Irregular-realization transport | `realizationTransport_exact`; `realizationTransport_exponential`; `realizationTransport_finrank_invariant` | Universal theorem for every exact realization functor and natural isomorphism |
| Principal-conormal Hessian | `GlobalPuiseuxWitt.localPositiveForm_associated_apply`; `localWittForm_associated_apply` in `StokesPrincipalConormalHessian.lean` | Exact polarized Gram/Hessian form |
| Global multi-Rees Witt law | `globalReesWittForm_sigNeg_add_radical_finrank_le_one` | Every nonnegative specialization, joint bound |
| Polynomial multi-Rees construction | `eval_polynomialReesBlockEnergy`; `eval_one_polynomialReesCartanQuadratic`; `eval_polynomialReesBlockEnergy_zero_deleted`; `eval_polynomialReesCartanQuadratic_pos_of_physicalRank_eq_zero` in `StokesPolynomialReesCoarea.lean` | Actual polynomial family over one variable per threshold channel |
| Capacity normal form/trichotomy | `cartanQuadratic_eq_centered_capacity`; `cartanQuadratic_pos_of_capacityGap_pos`; `cartanQuadratic_nonneg_of_capacityGap_eq_zero`; `cartanForm_sigNeg_eq_one_of_capacityGap_neg` | Exact three phases |
| Root-height invariance | `capacity_update`; `capacityGap_update_invariant`; `determinant_capacity_prefactor_invariant` in `StokesCartanCoronaCapacity.lean` | Exact Sherman--Morrison laws |
| Euler--capacity refinement | `fusionForm_eq_centered_eulerCapacity`; `eulerCapacityGap_eq_eulerCharacteristic_sub_defects` in `StokesEulerFusionCapacity.lean` | Exact arbitrary-genus centered form |
| Exact corona--vanishing law | `harmonicGraph_relativeVanishing_exact`; `fullEnergy_eq_correction_add_effective`; `fullEnergy_eq_effective_iff_hiddenMinimizer` in `StokesCoronaSchurVanishing.lean` | Exact sequence and Schur complement |
| Corona order independence | `successiveElimination_order_independent` | Exact finite elimination law |
| Source-derived tangent dimension | `WildSmoothReduction.tangent_finrank_eq_expectedDim` | Exact quotient dimension |
| Self-dual Euler count | `WildSmoothReduction.d1_comp_d0`; `finrank_H0`; `finrank_H2`; `cohomologicalEuler_eq_expectedEuler` | Exact complex and cohomology dimensions |
| Path completion and leg stability | `TypeALeg.path_completion`; `EulerFusionTypeALegs.fullFusionForm_sigNeg_add_radical_finrank_le_one` | Arbitrary finite type-A legs, joint bound |
| Nonabelian Hodge diagram law | `equivariantPublishedCoreCartanForm_sigNeg_add_radical_finrank_le_one` plus `fullFusionForm_sigNeg_add_radical_finrank_le_one` | Published core plus marking completion |
| Second-eigenvalue obstruction | `StokesSpectralWitt.cartanPolarization_secondEigenvalue_obstruction` | Exact Hermitian spectral translation |
| Twisted-triangle sharpness | `sharpTriangle_inertia`, `sharpTriangle_equivalent_weightedSumSquares`, `sharpTriangle_det`, `sharpTriangle_trace` | Exact congruence and inertia |
| Scalar component-kernel classification | `scalarHomTransport_invisible_iff_componentwise`; `scalarHomTransport_invisible_iff_constant` in `ArithmeticXiStokesCentralRankPort.lean` | Exact equivalence closure of arbitrary directed interaction relation |
| Component determinant ports | `componentPhysicalRankNat`; `componentScalar_determinantWeight`; `commonScalar_determinantWeight` | Exact determinant character factorization by finite component labels |
| Coefficient-spectrum connectedness | `PuiseuxOrbitCoareaDatum.normalizedHomIrregularity_pos_of_ne`; `scalarTwistInvisible_iff_constant` | Every distinct orbit pair has positive mixed irregularity; unique common center |
| Physical-rank/contact no-go | `continuousPhysicalRankFamily_constant`; `not_exists_continuousPhysicalRank_eq_centralDefect`; `contactNumerator_eq_of_sameCoefficientEqualityPattern`; `cartanQuadratic_eq_of_contactNumerator_eq` | Continuous arithmetic defect is not discrete rank; bare formal contact forgets coefficient magnitude |
| Arithmetic character and reflection | `centralHolonomyDefect_mul_clock`; `centralHolonomy_reflection`; `centralHolonomy_pow_clock` | Multiplicative positive clock, reflected inverse, and exact clock-power law |
| Determinant rank-port/Xi transgression | `ccmXiResidue_rankPortClock_eq_determinantCentralHolonomyDefect`; `centralHolonomyDefect_pow_clock_eq_determinant` | Source residue at clock `n^M` equals determinant holonomy-minus-identity |
| Trace-one prime specialization | `ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one`; `ccmXiPrimeResidue_eq_centralHolonomyDefect` | Literal `p tensor p^-1` rational-adelic cycle; no divisor in source definition |
| Pointwise and global critical classifier | `ccmXiPrimeDeterminantCentralHolonomyDefect_eq_zero_iff`; `xiArithmeticCentralCharacterUnitary_iff_riemannHypothesis` | Positive rank-port defect vanishes exactly on critical line; global unitarity iff RH, not asserted |
| Reflection-product factorization | `centralHolonomy_pow_eq_exp_rankPort`; `determinantCentralGainDefect_reflection_product`; `stokesRankPortPrimeEnergy_eq_reflectionDefectSum` | Negative product of reflected normalized determinant defects is exactly the positive hyperbolic prime energy |
| Finite arithmetic vanishing theorem | `primeClockCutoffEnergy_eq_zero_iff`; `stokesRankPortPrimeEnergy_eq_zero_iff` | For `N >= 2` and `M > 0`, energy vanishes exactly at `Re(s)=1/2` |
| Universal-profile parity and strictness | `primeClockUniversalProfile_neg`; `primeClockUniversalProfile_quadratic_lower`; `primeClockUniversalProfile_eq_zero_iff`; `primeClockUniversalProfile_pos_iff` | Profile is even, bounded below by `2c^2`, and strictly positive away from zero |
| Stokes--Mertens three-regime law | `tendsto_stokesRankPortPrimeEnergy_zero_of_scaled_tendsto_zero`; `tendsto_stokesRankPortPrimeEnergy_critical_profile`; `tendsto_stokesRankPortPrimeEnergy_atTop_of_scaled_tendsto_atTop` | Vanishing, universal critical crossover, and divergence under exact rank-scaled logarithmic coordinate |
| Target-free Möbius--theta Xi-jet source | `mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC`; `tendsto_mobiusThetaInternalJetFourierLaplace_cofinal_at_divisor` | Explicit source precedes spectral evaluation and reaches every multiplicity jet cofinally |
| Rational-adelic cyclic trace/transgression | `ccmRationalAdelicEpsilonZero_isTrace`; `ccmRationalAdelicDegreeOneTrace_rotate`; `ccmMobiusThetaTwoLegParacyclicDefect_residue` | Exact crossed-product trace and unsquared two-leg residue computation |

## External ancestry, not novelty claims

Published inputs are limited to identification of the established nonabelian-Hodge diagram and
the analytic theories in which its data arise. Their finite algebraic outputs are reconstructed
above rather than assumed as free matrices. The manuscript explicitly attributes:

- Boalch--Yamakawa/Douçot core adjacency and diagram dimension formula;
- Boalch/Boalch--Yamakawa quasi-Hamiltonian wild-character construction;
- Sabbah and D'Agnolo--Kashiwara irregular Riemann--Hilbert theory;
- known fission trees, ultrametric constraints, and Hiroe scalar Euler identities.
- classical theta representation of completed zeta, rank-one local systems, determinant scaling,
  the adeles-class-space crossed-product ancestry, Mertens's first theorem, and weighted-prime
  test-function limits.

No theorem in the manuscript assumes a rooted cut realization, arbitrary orbit partition,
microlocal multiplicity table, or finite wall set as primitive input.

## Trust gate

- Stokes source scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Capstone axiom reports: only `propext`, `Classical.choice`, and `Quot.sound`.
- Stokes modules are wired into `GaloisForLFunctions/HTGeometry.lean`; the arithmetic bridge is
  wired into `GaloisForLFunctions/RHTower.lean`.
- Repository-wide lint currently fails only because two unrelated owned modules are unreachable:
  `RHTower.MobiusMertensFiniteSectionEnergy` and
  `HTGeometry.KleinGordonTimePotential`.
