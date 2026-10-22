# Formalization certificate — `ccm-sonin-three-grade-relative-carrier-law`

- **Card:** `ccm-sonin-three-grade-relative-carrier-law.md`
- **Stage:** 3-formalized / not-new
- **Lean modules:**
  - existing corpus endpoints (verified present): `SoninRelativeGramDefect`,
    `SoninSemilocalTraceObstruction`, `SoninAllPrimeResidualKernel`, `SoninSemilocalRelativeTrace`,
    `SoninEulerCalkinPartialIsometry`, `SeamSpectralFlow`, `MeasuredIndexBlindness`
  - new: `formal/GaloisForLFunctions/RHTower/CCM/CCMSoninCompressedCommutator.lean`
- **Umbrella:** wired from `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` (two theorems use `[propext]` only)
- **Hypotheses:** only the algebraic symmetry data (`Q` projection, `X` self-adjoint, `Z`
  skew-adjoint); no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(3)` relative Gram identity | `centralSoninRelativeGramDefect_eq_linearCross_add_energy` |
| grade 0: Calkin shell, prime faithfulness | `evenCentralSoninQuadraticCorner_isCalkinPartialIsometry`, `finitePrimeArchimedeanEulerGram_not_isCompactOperator_of_ne_zero` |
| grade 1: Hilbert–Schmidt cross, unsquared coefficient | `centralSoninRelativeGramLinearCross_isHilbertSchmidt`, `centralSoninSemilocalRelativeGramLinearCross_eq_coefficient_smul` |
| grade 2: positive trace-class residual | `soninAllPrimeResidualOperator_isHilbertSchmidt`, `soninAllPrimeResidualEnergyOperator_isTraceClass` |
| `(9b)`–`(9c)` compressed commutator split | `compress_split`, `compressed_commutator_split` |
| `(9d)` trace split | `degree_one_trace_split` |
| Krein/index readers | `kreinNonneg_iff_no_negDef`, `exact_neg_inertia` |

The card's remaining open gates (construct `E_a`, the degree-one semilocal relative functional, the
contractions `(11)`, the index transport, RH) are route gates, not statements of this card.
