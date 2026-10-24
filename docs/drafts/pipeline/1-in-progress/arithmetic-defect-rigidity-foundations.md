# Arithmetic defect rigidity: quantitative foundations

Status: paper proofs complete; individual Lean checks in progress.

## Objective

Finish the existing foundational proof package for Arithmetic Defect Rigidity: quantitative
source constraints preserving signed energy, forcing, cofactor operations and moving support.
The package implements concrete parts of §6 of `docs/reports/review-2410/astra.md`.

The arithmetic no-escape theorem remains an open research objective. Completing these
foundations does not assert source exclusion, critical-energy admission or RH.

## Mathematical outputs

For each fixed damping `0 < ε < 1/2`:

| Mechanism | Exact output |
|---|---|
| Two source scales | Positive power-law forcing floor, actual VK comparison, `E/F → 0`, `F/E → ∞`, and impossibility of a common scalar normalization. |
| Signed Gram geometry | Exact receiver distance and determinant; forcing normalization loses the distance retained at receiver normalization. |
| Cofactor tails | Uniform head/tail budgets and a source-defined growing window whose complementary tail retains the complete forcing. |
| Successor/cofactor words | Explicit denominator and boundary cost; uniform displacement energy and complete-forcing work bounds, with fixed-word collapse on escape. |
| Paid subtraction | Explicit forcing power plus globally bounded pronic remainder; signed antipodality and total-variation control, including arbitrary bounded moving localizations. |
| Absolute forcing mass | Exact prime-power mass and logarithmic derivative, finite-horizon bounds, convergence and uniformly decaying new-cell budgets for bounded word errors. |
| Boundary trace | Absolute actual-source Mellin trace, exact forcing coefficient, linear cofactor subtraction on its proved domain, and actual-image domain membership. |
| Fixed trace-domain dilations | Absolute summability proved by finite blocks, exact mass scaling and harmonic trace weights for finite cofactor packets. |
| Paid commutator | Exact rank-one dilation commutator and uniform trace budget, including arbitrary moving integer dilations. |
| Energy quantiles | First crossings, monotonicity, bounded overshoot, diffuse energy transport and signed cofactor work with uniform endpoint error. |
| Joint fixed-cofactor limits | One subsequence retaining all signed entries, unit receiver mass, finite packet positivity and simultaneous dilation contraction. |
| Exact reconstruction | Residual/trace pair injective; residual kernel contained in the explicit inverse-power line; actual-source reconstruction. |

The existing THIM smooth-power expansion, Mellin-cell calculus, first-moment identity,
countable compactness and weighted Möbius floor inversion are reused inputs, not new claims.
Actual source membership and every arithmetic budget used above are proved independently of
critical-energy admission.

## Lean status

Eleven modules passed their required dependency checks:

- `TheForcingDominatesTheReceiver`
- `ForcingScaleSeparation`
- `FixedSuccessorsDisappearFromEscapingProfiles`
- `TheCofactorTailCarriesTheForcing`
- `TheForcingSplitsIntoAPowerAndAnAdmittedRemainder`
- `TheForcingHasFinitePronicMass`
- `TheActualReceiverHasAnAbsolutePoleTrace`
- `TheRenormalizedCofactorIsAntipodalOnEscape`
- `EnergyQuantilesRetainDiffuseEscape`
- `ThePoleTraceDefinesALinearCofactorRenormalization`
- `CofactorSuccessorWordsHaveABoundaryCost`

`FixedCofactorsHaveAHarmonicBoundaryTrace` is undergoing its required dependency check.
Eight leaf modules await their ordinary checks:

- `TheReceiverIsTheGramTangent`
- `ForcingEscapesAMovingCofactorWindow`
- `BoundedWordErrorsHaveAnAbsoluteHorizonTail`
- `EnergyQuantilesPreserveTheSignedCofactorPairing`
- `CountableCofactorCovariancesHaveACommonLimit`
- `CofactorRenormalizationHasABoundedDilationCommutator`
- `TheResidualAndPoleTraceDetermineTheRow`
- `MovingLocalizationsRetainTheSignedDensity`

All twenty final checks that write no object files remain pending. Exact per-module status is
maintained in `logs/arithmetic-defect-rigidity-final-audits.txt`. Accepted modules are wired
into `formal/GaloisForLFunctions/ArithmeticDefectRigidity.lean`, which is imported by
`MainTheorems.lean`; neither umbrella is compiled.

Checks run directly from `formal/` with `lake --old env lean`, one owned Lean process at a
time. Missing dependency objects are generated only for already written consumers. No
Python orchestration, `lake build`, umbrella build, axiom checks or raised limits are used.

## Remaining research questions

These are unproved research leads, not completed paper arguments awaiting transcription:

- Reconcile fixed-cofactor covariance limits, energy quantiles and the full moving cofactor
  boundary in one carrier retaining the necessary spatial data and rates.
- Prove a selective arithmetic estimate excluding nonzero escaping states.
- Determine general domain invariance and quantitative bounds for the full renormalized
  cofactor operator.
- Establish trace-domain membership and trace value of the inverse-power row before claiming
  a nonzero residual kernel; exact reconstruction does not supply those analytic inputs.
- Define domain-correct successor transport on repairing data, then prove its source-selective
  effect. Row-valued bounds do not automatically establish the coefficient mean summability
  required by the existing repairing ideal.
- Supply full unbounded-receiver compensation, shared Gamma/polar allocation, multiplicity-
  sensitive anti-collapse, source effectivity and correctly signed enumerative bounds.

## Evidence

The foundational README is `formal/GaloisForLFunctions/ArithmeticDefectRigidity/README.md`.
Corpus searches, inspected source arguments, paper proofs and diagnostics are recorded in
`logs/arithmetic-defect-rigidity-research.txt`. The report is rewritten around the mathematical
results and open questions, without a history section.
