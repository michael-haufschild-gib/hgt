# Arithmetic Orientation Theory (AOT): programme card

- **ID:** aot-2026-10-23
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** docs/reports/review-2310/fable.md §3–§4 (the walls as questions; the field)
- **Statement:** Develop the theory of orientation invariants of arithmetic sources that survive
  passage to unbounded aperture, horizon, damping and height: frustration and holonomy of signed
  incidence forms, the companion (parity) orientation of divisor rows and the readings faithful to
  it, section counts of node divisors (Nyquist–Riemann–Roch), the stability class of paid
  receivers, and the width dictionary as one theorem. Lean in
  `formal/GaloisForLFunctions/ArithmeticOrientationTheory/`, umbrella
  `GaloisForLFunctions.ArithmeticOrientationTheory` (registered in `MainTheorems.lean`).

## Goal
Give each face of the three walls (sign in estimates, parity class in transport, effectivity in
realization) an exact integer- or sign-valued invariant with a theorem, and decide each research
topic of the review by a theorem or by a recorded open problem with its sharp boundary.

## Gates
- [x] 0 → 1 folder, umbrella, registration (`MainTheorems.lean`), modules compiled with `lake --old env lean`
- [x] README written (`formal/GaloisForLFunctions/ArithmeticOrientationTheory/README.md`)
- [x] research topics T1–T10 of the review each addressed by a Lean theorem or recorded in README §7

## Plan (modules)
1. `FrustrationIndexControlsTheGroundEnergy`: switching classes, frustration index, signed
   Dirichlet form; ground energy zero iff balanced; `λ_min ≤ 4ν/n`; switching covariance.
2. `TheSumDifferenceFormOfTheOddPrimeSide`: discrete multiplicative model; odd autocorrelation
   = 2·ratio − product; product correlation at a prime power is tower-local.
3. `TheNyquistRankBound`: rank of a Gram with unit diagonal and frame bound `K` is `≥ RN/K`;
   sections (Dirichlet polynomials vanishing at separated heights) have codimension `≥ RN/K`.
4. `TheEvenFlipIsReadByTheDyadicTower`: first pronic moment difference across the even flip
   equals `−2 log 2 · Σ_a W_c(2^a)`; squarefree rows read at the prime 2.
5. `TheCriticalWienerMonoid`: critical Wiener kernels form a convolution monoid with
   submultiplicative norm; paid receivers are unions of its orbits.
6. `OrientedReadings`: involutions, orientation-faithful readings, the parity collapse law.
7. `TheDampingChainTransportsOrientationExactly`: residue-mode combinations keep their sign
   pattern under the damping flow.
8. `TheWidthDictionary`: TFAE assembling the corpus equivalences (index, effectivity, damping,
   positivity) into one statement.
9. README.

## Outcomes
- `OrientedReadings`: `OrientationFaithful`, closure law of blindness (`Invisible.comp/join/pi/of_refines`),
  `forall_iff_of_resolves_of_invisible`, `orientationFaithful_of_resolves_of_flips`,
  `not_resolves_of_invisible_of_flips`, orientation classes.
- `FrustrationIndexControlsTheGroundEnergy`: `signedDirichletForm_eq`, `signedDirichletForm_switch`,
  `frustrationIndex_switch`, `isBalanced_iff_frustrationIndex_eq_zero`, `signedDirichletForm_signVector`,
  `groundEnergy_le_frustrationMass`, `groundEnergy_eq_zero_iff_isBalanced`, `frustrationIndex_oddWeilLedger_le`.
- `TheFrustrationIndexOfThePrimeTriangle`: `misalignedCount_eq_two_mul`,
  `two_le_frustrationIndex_of_not_isBalanced`, `frustrationIndex_le_two_fin3`, `frustrationIndex_primeTriangle` (= 2).
- `PrimePowerSumsRegroupByTowers`: `sum_primePow_eq_sum_towers`, `sum_vonMangoldt_mul_eq_sum_towers`,
  `sum_vonMangoldt_productCorr_eq_sum_towers` (global product part = Σ_p log p (S_p² − q(1)²) for M ≥ X²).
- `TheFrustrationOfATowerIsRankOne`: `productCorr_prime_pow`, `sq_sum_eq_sum_cauchy`,
  `sum_vonMangoldt_productCorr_prime_pow` (tower product part `= log p (S_p² − q(1)²)`),
  `towerProductPart_nonneg`, `latticeOddPrimeSide_le_of_eq_zero`, `sum_towerProductPart`.
- `TheNyquistRankBound`: `h0_add_rank`, `card_sub_card_le_h0`, `frobeniusMass_le_rank_mul`,
  `h0_le_nyquist`, `h0_dirichletSampling_le` (Dirichlet polynomials at separated heights).
- `TheEvenFlipIsReadAtThePrimeTwo`: `evenFlip_apply`, `evenFlip_evenFlip`, `dampedClass_evenFlip`,
  `firstPronicMoment_evenFlip_sub` (`M(c♭) − M(c) = 2 log 2 W_c(2)`),
  `firstPronicMoment_separates_evenFlip_iff`, `invisible_amplitude_evenFlip`,
  `not_resolves_amplitude_receiverBounded` (parity floor for readings), `orientationFaithful_firstPronicMoment`.
- `TheCriticalWienerMonoid`: `criticalWiener_dirichletConv`, `tsum_abs_dirichletConv_le`,
  `dirichletConv_unitKernel`, `dirichletConv_assoc`, `receiverBounded_orbit`.
- `TheDampingFlowPreservesOrientation`: `centeredOperator_residueCombination`, `sign_coeff_centeredOperator`,
  `centeredOperator_residueCombination_twice`.
- `TheWidthDictionary`: `widthDictionary_tfae` (eight units), `one_positive_square_iff_cofinal_budget`,
  `exists_effectivity_iff_meanSquare_band`.
- `TheLatticeOddLedgerIsBalanced`: `primeKernel_tower_le`, `primeKernel_log_add_le`, `oddFold_lattice_nonpos`,
  `isBalanced_lattice`, `frustrationIndex_lattice_eq_zero`, `nonneg_iff_locallyPayable_lattice`,
  `oddFold_le_primeKernel`, `frustrationMass_le_primeSumCharge`.
- `TheRatioPartDecomposesOverCosets`: `ratioCorr_prime_pow_eq_sum_cosets`, `towerRatioPart_eq_sum_cosets`,
  `towerOddPrimeSide_eq` (coset law: 2·Toeplitz over p-free cosets − Hankel square).
- `LocalFactorsAreTheUnitsOfTheWienerMonoid`: `dirichletConv_localFactor_inverse`,
  `criticalWiener_localFactorInverse_iff` (|a| < √p), `dirichletConv_comm`, `inverse_unique`, `isWienerUnit_localFactor_iff`.
- `TheNyquistRankBound` (extended): `h1`, `h0_sub_h1`, `h1_eq_zero_iff`, `h1_eq_zero_of_frobeniusMass_ge`,
  `h0_eq_zero_of_frobeniusMass_ge`.
- Axiom audit: every capstone listed above depends only on `propext`, `Classical.choice`, `Quot.sound`
  (`#print axioms` over all ten modules); no `sorry`, no premises, no raised budgets.
- Open: README §7 (frustration index of the actual odd ledger at growing aperture; beyond the rank-one law;
  Nyquist–Riemann–Roch beyond rank–nullity; orientation-faithful norm; inverses in the Wiener monoid;
  transport in aperture; the Nyquist bound at the diagonal).

## Log
- 2026-10-23 — created in 1-in-progress from review-2310/fable.md; thirteen modules compiled, README written
