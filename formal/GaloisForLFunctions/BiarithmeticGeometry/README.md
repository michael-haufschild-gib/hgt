# BiarithmeticGeometry (BG)

Namespace `GaloisForLFunctions.BiarithmeticGeometry`; umbrella `BiarithmeticGeometry.lean`; 75 modules (2 in `Affine/`).
All results are unconditional.

## 1. Motivation

Over a finite field Frobenius is a ring map on a complete finite object. Over ℤ, a finite horizon
`{0,…,N}` carries both successor and dilation, but completing it to a period `lcm(1..N)` changes the
observation scale. BG studies the joint additive–multiplicative action at the horizon itself and builds
the payment theory of explicit calibration sources (prime-five geometric towers, the golden curve datum)
inside the critical Wiener algebra `WienerAlgebraAt (1/2)`. The aim: find which signed estimates the
ring action supplies, and classify exactly where payment (receiver boundedness) fails.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Horizon space | `HorizonSpace`, `horizonCell`, `horizonAffine` | cells `0..N`, `e_j = 0` for `j > N`; `T_{a,b} e_j = e_{aj+b}` |
| Box defect, torsion | `chebyshevTwoPoleDefect` (AIP), `horizonTorsionOrder`, `HorizonTorsion` | `E(s) = e^s + s − 1 − ψ(e^s)`; `Q_N = lcm(1..N+1)/(N+1)` |
| Transition groups | `HorizonPeriodGroup`, `HorizonTransition`, `horizonPeriodJump` | `ℤ/lcm(1..N)`; reduction kernels |
| Digit rows | `fiveDigitRow`, `fiveWeightedDigitRow`, `fiveDigitProfile` | base-5 digits evaluated at `a`; self-similar limit |
| Tower source | `localFactorInverse 5 a` (AOT), `fiveTowerKernelLift`, `fiveCriticalKernelLift` | `a^r` at `5^r`; kernels on powers of 5 |
| Golden source | `goldenArithmeticSource`, `goldenPrimaryRoot`, `goldenSecondaryRoot`, `goldenCriticalParameter` | inverse golden zeta coefficients on `5^r`; roots `(5±√5)/2` |
| Cofactor action | `actualKernelAction`, `cofactorPrefixAction`, `formalWienerCofactor` | `Σ_{j≤n} k(j) A(⌊n/j⌋)` |
| Graph domain | `cofactorGraphDomain`, `cofactorGraphInput`, `cofactorGraphOutput` | `{(k, coordinates)} ⊂ W × ℓ²` |
| Pronic space | `PronicHilbertSpace`, `pronicDilationOp`, `pronicWienerRepresentation`, `pronicRowCoordinate` | completed pronic ℓ², exact dilations |
| Critical coefficients | `CriticalCoefficientSpace`, `criticalCoefficientDomain`, `criticalTotalEvaluation`, `criticalCoefficientLift` | ℓ¹(ℂ) on the 5-tower; partial sums in ℓ² |
| Unpaid families | `criticalUnpaidCoeff`, `criticalPowerCoeff`, `powerTailWiener`, `CriticalPowerExponent` | tail differences of `(n+1)^{−α}` |
| Quotients | `CriticalGoldenPaymentQuotient`, `CriticalGoldenPaymentClosureDefect`, `CriticalReducedCoefficientCokernel` | unreduced / closure / reduced cokernels |
| Chirps | `logarithmicChirpPhaseGroup`, `chirpCauchyKernel` | `j ↦ e^{−2it log j}` orbit closure; Cauchy kernels |
| Countermodels | `cyclicKernel`, `twistedHorizonAffine`, `goldenNormalizedCubePointCount` | non-homogeneous metric, normalization twists, broken positivity |

## 3. Language

- **Paid** source: `ReceiverBounded c` (centred prefix has bounded pronic energy). **Paid ideal** `paidIdeal c`: Wiener kernels `k` with `k ⋆ c` paid (AOT).
- **Critical contact**: tower parameter `a = √5`, the boundary of the critical Wiener radius.
- **Graph norm**: max of Wiener input norm and ℓ² output norm on the cofactor graph.
- **Unreduced / reduced** cokernel: quotient by the paid ideal / by its closure.

## 4. Mechanisms

**A. Affine horizon geometry.**
1. Truncation keeps the affine semigroup exactly: `T_{a,b}T_{c,d} = T_{ac, ad+b}`, `D_a U = U^a D_a`; exactly `1 + (N+1)(N+2)/2` distinct operators, determined by images of cells 0 and 1.
2. Joint commutant of successor and `D₂` is scalar, yet the action is not irreducible: invariant subspaces are exactly the `N+2` coordinate tails (a chain, indecomposable).
3. Exact boundary loss: affine pairing + escaped-cell pairing = original pairing; successor-invariant observables are constant.
4. Every multiplicative character twist preserves all affine relations: covariance cannot fix the dilation normalization.
5. Finite-dimensional unitary representations kill translations (continuous family with expanding dilation; any rep of `Aff(ℚ)`); finite-dimensional rational translations are unipotent.

**B. Integral invariants.**
6. `E(log(3/2)) ∈ (0,1)`: no `h⁰ − h¹` model. `E(log(N+1)) = N − log Q_N`, `Q_N` = order of a canonical reduction kernel; transition kernels have log-order `Λ(N+1)`, size `p` at prime powers, trivial elsewhere.
7. Shared budgets do not glue: singleton-feasible allocations sum within budget iff `k ≤ 1` or `B = 0`; sharp excess `kB`.

**C. Visibility and domains.**
8. Complete-period covariance fixes Selberg magnitudes only; finite prefixes range over an interval of exact diameter `2·prefixVisibility`; determined iff every mode term vanishes.
9. Diagonal power law + packet contraction do not force homogeneous mixed covariance (cyclic 2-adic model); averaging restores it.
10. Prime-log jump forms `Σ w_p ‖f − τ_{log p} f‖²` have full domain iff `Σ w_p < ∞`, else only `f = 0`.

**D. Payment as an operator domain.**
11. Payment ⇔ bounded full cofactor action (mean correction is paid by the critical Wiener norm).
12. The cofactor graph is closed and complete for every row; its input image is exactly the paid ideal; that image is Wiener-closed iff a uniform output ≤ C·input estimate holds.
13. Completed pronic space: `‖D_j f‖² = ‖f‖²/j` exactly, `D_j D_k = D_{jk}`; unital contractive Wiener representation whose coordinates are the finite cofactor sums; formal cofactor actions compose for arbitrary rows.
14. Paid perturbations (critical Wiener sources) leave paid ideals unchanged.

**E. Prime-five laboratory.**
15. Digits: `f(5n+r) = r + a f(n)`; tower prefix `= −(a/(5−a))·fiveDigitRow a n` exactly; digit-row energy finite ⇔ `Σ x_l²/5^l < ∞`; leading digit variance cannot be cancelled.
16. Tower paid ⇔ `|a| < √5`. Kernel `k(5^r) = f_r` repairs ⇔ `Σ (a²/5)^l (Σ_{r≤l} f_r/a^r)² < ∞`; at `a = √5` ⇔ partial sums of `g_r = f_r/√5^r` in ℓ².
17. Expanding division (`a > √5` side): causal response at ratio `1/b` has finite energy ⇔ `Σ b^r g_r = 0` (closed evaluation kernel).

**F. Critical non-closedness.**
18. Critical lift ℓ¹(ℂ) → Wiener is an isometry onto 5-tower kernels; payment = partial sums in ℓ².
19. Domain closure = ker(total evaluation); corrected truncations converge in graph norm; zero-sum finite repairs converge to an unpaid norm-2 kernel. Paid ideal not closed.
20. Power tails `α ∈ (0,1/2)` are independent modulo payment ⇒ unreduced quotient and closure defect have Hamel dimension continuum; continuous dual of the unreduced quotient and the reduced cokernel are both one-dimensional.

**G. Golden source.**
21. Inverse golden series = difference of two damped towers; source = `−tower(primary t)/√5 + paid remainder`; paid ideal = primary tower's; paid ⇔ `primary·t < √5`; mean `(5−6t+t²)/(5−5t+t²)`; divisor response depends only on `v₅(n)`, ≤ 1.
22. Intrinsic counting receiver cancels the counting pole exactly; centred point kernels have shell energy ≤ `6·5^{−r}`.
23. Fixed-determinant cubing `z ↦ z³/p`: integral positive-count survivors force `T = 0` (or `p ∈ {2,3}`) and pure roots `|a| = √p`; golden datum goes to point counts `−4, −64`.

**H. Chirps and shells.**
24. Three rotation samples detect any nonzero amplitude (prime-two chirp angle `2(log 2)² ∈ (0,π)`); chirp orbit closure is a compact group of completely multiplicative phases; finite chirp Cauchy Grams at distinct cofactors are positive definite for every phase.
25. Five-shell rows: energy finite ⇔ every ordinary pronic norm bounded; shell shifts are isometries; geometric shell completion is one-dimensional.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Affine horizon geometry | `horizonAffine_comp`, `card_horizonAffine_image`, `horizon_joint_commutant`, `horizon_affine_submodules` | unconditional |
| Finite affine rigidity | `finite_rational_affine_unitary_rigidity`, `finite_rational_affine_translation_unipotent` | unconditional |
| Arithmetic Euler formula | `no_dimension_model_for_boxDefect`, `boxDefect_eq_degree_sub_log_kernel`, `log_card_horizonTransition` | unconditional |
| Exact visibility | `prefix_visibility_diameter`, `prefix_covariance_determines_iff` | unconditional |
| Payment = graph | `paidIdeal_iff_existsUnique_cofactorGraph`, `isClosed_range_cofactorGraphInput_iff` | unconditional |
| Pronic representation | `norm_sq_pronicDilationOp`, `pronicDilationOp_comp`, `formalWienerCofactor_comp` | unconditional |
| Escape bridge | `admitted_or_paidKernelAction_vanishes`, `admits_or_all_actual_moduleHulls` | dichotomy |
| Tower admission | `receiverBounded_fiveTower_abs_iff`, `receiverBounded_goldenArithmeticSource_iff` | unconditional |
| Prime-five payment | `receiverBounded_fiveTowerKernelLift_iff`, `mem_paidIdeal_fiveTower_iff` | unconditional |
| Expanding division | `summable_sq_geometricCausalResponse_iff` | unconditional |
| Non-closed payment | `not_isClosed_golden_critical_paidIdeal`, `closure_criticalCoefficientDomain` | unconditional |
| Continuum defect | `rank_criticalGoldenPaymentQuotient_eq_continuum`, `rank_criticalGoldenPaymentClosureDefect_eq_continuum` | unconditional |
| One-dimensional reduced data | `finrank_criticalReducedCoefficientCokernel`, `finrank_criticalUnreducedContinuousDual` | unconditional |
| Cubic purity | `exists_normalizedCubicTrace_iff`, `normalizedCubicRoot_survivor_pure` | unconditional |
| Chirp positivity | `chirpCauchyKernel_posDef`, `logarithmicChirpPhase_mul` | unconditional |

## 6. Tools

**Developed.**
- Horizon calculus: `horizonPairing_affine_add_boundary`, `horizonAffineImageEquiv`, `horizonInvariantSubspaceEquiv`.
- Digit calculus: `fiveDigitRow_concat`, `sum_sq_fiveWeightedDigitRow_block`, `bounded_fiveDigitPronicEnergy_iff`, `fiveTruncatedDigitReadout_convolution`.
- Finite Young bound: `sum_sq_finiteGeometricConvolution_le`; future tails: `tsum_norm_geometricFutureTail_le`.
- Payment calculus: `receiverBounded_dirichletConv_iff_cofactorNorm`, `paidIdeal_smul_add_criticalWiener`, `receiverBounded_of_criticalWiener`.
- Energy domains: `bounded_pronicNorm_iff_summable`, `summable_complex_pronicEnergy_iff`, `finitePronicPairing_eq_integral`.
- Completed pronic module: `pronicWienerRepresentation`, `pronicRowCoordinate_wiener`, `pronicFiniteExtension_wiener`.
- Critical coefficient machinery: `criticalCoefficientLift`, `criticalCorrectedTruncation_graph_errors_tendsto`, `criticalCoefficientDomain_continuous_annihilator`, `criticalReducedCoefficientCokernelIsometry`.
- Power-tail independence: `criticalPowerCoeff_independent_mod_squareSums`, `summable_sq_criticalPowerCoeff_partialSum_iff`.
- Pole extraction: `geometricPole_extraction`; three-rotation rigidity: `complex_three_rotation_rigidity`.

**To build.**
- A uniform cofactor-energy estimate (graph closedness) for the actual Möbius source, or a proof it fails.
- An allocation complex with shared capacity whose integer obstruction matches degree minus log torsion.
- Transfer of prime-coordinate coercivity to the dense chirp orbit (infinite-rank positivity).
- Multi-prime version of the prime-five payment criterion.

## 7. Open questions

1. Is the paid ideal of the actual damped Möbius source closed in `W_{1/2}`? By `isClosed_range_cofactorGraphInput_iff` this is a uniform cofactor-energy bound.
2. Classify actual escape modules relative to paid ideals beyond hull containment.
3. Does the unreduced continuum defect at critical contact have an analogue for genuine L-function sources, and does it see zeros?
4. Can the joint ± and × action bound signed off-diagonal sieve entries at polynomial horizon (between prefix and full period)?
5. An independently positive polarization compatible with ring action and a fixed normalization (§4A4 shows covariance alone cannot fix it).

## 8. Traps

| Trap | Fact |
|---|---|
| Affine identities fix a normalization | character twists preserve them (`twisted_dilation_two_distinct`) |
| `E` is a dimension | `E(log 3/2) ∈ (0,1)`; it is degree minus log torsion |
| Local feasibility glues | shared budget excess `kB` (`singletonPaymentsGlue_iff`) |
| Diagonal scaling fixes mixed covariance | cyclic model breaks homogeneity (`cyclicKernel_not_homogeneous`) |
| Truncated repairs repair | finite zero-sum repairs converge to an unpaid kernel |
| Paid ideals are closed | critical golden ideal is not (`not_isClosed_golden_critical_paidIdeal`) |
| Zero evaluation means payment | only closure; power tails `α ≤ 1/2` are unpaid |
| Reduced index measures the defect | reduced cokernel is 1-dim while unreduced defect is continuum |
| Complete-period data see signs | they fix magnitudes only (`prefix_visibility_extrema`) |
| Determinant preservation keeps positivity | normalized cubing of golden datum gives counts `−4, −64` |
| Finite-dim unitary models of translations | they are trivial; escape needs infinite rank |

## 9. Context

| Uses (imports) | Count | Used by | Count |
|---|---|---|---|
| HTGeometry | 11 | BezoutValuationIncidence | 1 |
| ArithmeticOrientationTheory | 8 | ArithmeticEffectivityTheory | 1 |
| RHTower | 6 | ArithmeticCorrelationGeometry | 1 |
| ArithmeticDefectRigidity | 3 | | |
| ArithmeticCastelnuovoSeveri | 3 | | |
| TransHorizonIncidenceMechanics | 2 | | |
| BSU, BVI, APD, AIP, ACCE, ACompT | 1 each | | |

| Neighbour | Interface |
|---|---|
| ArithmeticOrientationTheory | `paidIdeal`, `obstructionHull`, `localFactorInverse`, Wiener coefficient functionals |
| TransHorizonIncidenceMechanics | `CriticalWiener`, `ReceiverBounded`, centred prefixes, critical prefix bound |
| ArithmeticDefectRigidity | escape modules (`PaidWienerKernelsAnnihilateTheCofactorLimit`), forcing scale, closed-annihilator index |
| ArithmeticCastelnuovoSeveri | golden datum (`WittIntegralityIsNotPurity`), point-count positivity |
| ArithmeticIncidencePositivity | two-pole Chebyshev defect |
| ArithmeticPositiveDuality | `AffineGroupQ` and its conjugation law |
| BezoutValuationIncidence | Selberg coordinates (uses BG `PronicEnergyDomain` back) |
| ArithmeticEffectivityTheory | imports `PrimePowerTransitionGroups` (horizon torsion) |
| ArithmeticCorrelationGeometry | imports `HorizonBoundaryCalculus` (boundary of a dilation) |

## 10. Big picture

BG asks what the integers' two operations, kept together at a finite horizon, can certify. The answer is
mostly structural: the action is rigid (scalar commutant, polynomial-size, unipotent in finite rank) but it
cannot pick an analytic normalization, cannot see signs that complete periods erase, and its integral
invariant is a degree minus a logarithmic torsion rather than a dimension. Structure alone does not orient.

The calibration laboratory shows what payment really is: membership in an operator graph, exact for
geometric towers, with a sharp `√5` threshold. At critical contact payment stops being a closed condition;
the reduced obstruction is one number (a total evaluation) while the unreduced defect is a continuum of
power-tail directions. For RH this says the decisive estimate is quantitative and lives exactly at the
critical boundary: a uniform cofactor-energy bound for the actual source, which no closure argument or
finite index can replace.
