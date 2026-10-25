# Arithmetic Positive Duality (APD)

- **ID:** arithmetic-positive-duality-2026-10-25
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — research programme
- **Source:** `docs/reports/review-2510/fable.md` §4 (the proposed field), §1, §2.3, §3 Focus 1
- **Statement:** The rigidity and capacity theory of positive arithmetic Poisson pairs under
  self-duality and integer quantization: answer the central questions of §4.2 and build the tools
  listed there.

## Goal
Lean programme `formal/GaloisForLFunctions/ArithmeticPositiveDuality/`, umbrella
`ArithmeticPositiveDuality.lean`, foundational `README.md`, unconditional theorems.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: modules checked with `lake --old env lean`, wired into the umbrella,
  axioms `propext`, `Classical.choice`, `Quot.sound` only
- [x] README foundational document (P1–P17, F1–F8, answers to Q1–Q8)

## Status
Modules (all wired in `ArithmeticPositiveDuality.lean`):

| Topic | Module | Main theorems |
|---|---|---|
| Theta rigidity | `PositiveMeasureHamburgerRigidity`, `BeurlingRiemannFunctionalEquationRigidity` | `measure_eq_of_measureTheta_relation`, `beurlingSystem_rigidity_of_completed_functional_equation` |
| Q5 Poisson rigidity | `PositiveSelfDualMeasuresWithAGapAreDiracCombs` | `tentSelfDual_iff_eq_smul_diracComb`, `eq_zero_of_wide_gap`, `exists_tentSelfDual_not_comb`, `measure_Icc_le_of_poissonPair` |
| Q1 Integer classification | `IntegerPositiveDefiniteFunctionsAreSignCharacters` | `intValued_posDef_iff_signCharacter`, `isolation_forces_dirac_iff` |
| Tool: Herglotz–Bochner on `ℤ^ι` | `HerglotzBochnerOnLattices` | `isPosDefOnLattice_iff`, `fourierCoeff_map_kroneckerLine` |
| Q2 Multi-channel barrier | `TheBarrierOfACertificateIsTheBarrierOfItsFibre` | `fibre_purchase_le_fejer`, `twoChannel_joint_barrier_attained`, `twoChannel_width_cap` |
| Q3 Two-prime Bochner | `TheTwoPrimeSplineOrbitIsABochnerProblemOnTheTorus` | `riemannHypothesis_iff_exists_torusMeasure` |
| Q6 Affine carrier | `AffinePositivityIsInducedFromTheDilations` | `exists_isPosDefOnGroup_extension_iff`, `riemannHypothesis_iff_exists_affine_posDef` |
| Q7 Topology | `TheBlindIdealIsClosedOnlyWhereOffLineZerosAreSeen` | `isClosed_meyerTraceBoundedIdeal`, `isClosed_criticalJet_iff` |
| Q4 Quantum budget | `TheQuantumBudgetOfMultiplicativePositivity` | `admissible_iff_le_quantumBudget`, `fejer_quantumBudget_half` |
| `𝔽_q` calibration | `WeilsTheoremForCurvesIsPositiveDefinitenessOnZ` | `curve_rh_tfae` |
| Both sides of the explicit formula | `PositivityOnBothSidesOfTheExplicitFormula` | `positive_duality_of_the_explicit_formula`, `splineCorr_prime_term_eq_zero` |

Open (README §9): the third forcing instance in the strip (intrinsic charge), oscillatory
capacity, coupled scale positivity, a base over `Spec ℤ`, depth homogeneity as a law, prescribed
successor coordinates, rank-`r` realization, crystalline measures beyond degree one.

## No-go closure
- **Opening C (non-commutative carrier).** Killing theorem: `exists_isPosDefOnGroup_extension_iff`
  (affine positivity is induced from the dilations). Positive survivor: the restriction–induction
  law and `riemannHypothesis_iff_exists_affine_posDef`. Insight: a forcing law on the affine group
  must prescribe the successor coordinates from the source. Lean: done.
- **Rank-two height coupling (Opening A, height side).** Killing theorem: `fibre_purchase_le_fejer`.
  Positive survivor: exact fibre barrier and the product joint barrier
  (`twoChannel_joint_barrier_attained`). Lean: done.
- **Critical-data topologies (Q7).** Killing theorem: `isClosed_criticalJet_iff`. Positive survivor:
  `isClosed_meyerTraceBoundedIdeal` in the natural topology. Lean: done.
- **Quantization at the critical line in multiplicative positivity (Q4).** Killing theorem:
  `fejer_quantumBudget_half`. Positive survivor: the exact quantum budget
  `admissible_iff_le_quantumBudget`. Lean: done.
