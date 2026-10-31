# Arithmetic rigidity at critical scale

Namespace: `GaloisForLFunctions.CriticalScaleArithmeticRigidity`.
Programme umbrella: `CriticalScaleArithmeticRigidity.lean`.

## Motivation

The complete Weil form has positive conductor energies and an identified pole ground state, yet its smallest positive energy decreases as the test profile approaches a scale that detects every off-line zero. An absolute error estimate can destroy this information by charging the smallest energy to every conductor and every interaction. Separately estimating the prime, successor, pole, and Gamma terms can also destroy their exact cancellation.

This programme studies which signed states remain compatible with the joint arithmetic identities of addition and multiplication. Its aim is to derive arithmetic rigidity and relative energy bounds at growing scales. The source, its archimedean boundary, and its pole functional remain part of every object.

The initial foundation is a research specification. Existing results below are imported foundations; the proposed tools and questions are not assertions of new theorems.

## Objects and language

| Object | Meaning |
|---|---|
| Arithmetic packet | A finite combination of conductor modes with its actual arithmetic source and finite-horizon Gram matrix |
| Successor difference | The change under `n ↦ n + 1`, retaining boundary terms |
| Prime dilation difference | The change under `n ↦ p n`, retaining divisor and torsion terms |
| Complete energy | Prime, Gamma, pole, diagonal, and successor contributions combined before estimation |
| Relative error | An interaction measured in the completed energy of the states involved, rather than the smallest ambient spectral floor |
| Pole-neutral state | A vector in the kernel of the actual pole functional |
| Weak conductor sector | Modes whose completed energy degenerates along the chosen profile schedule |
| Arithmetic concentration profile | A limiting state retaining successor, dilation, source, and boundary identities |
| Critical schedule | A profile-preserving growth schedule whose tests detect the desired zero-depth range |

Horizon, overlap, conductor, profile, and detection depth are separate parameters. Fixed-conductor identities, conductor averages, and uniform statements over growing conductors are different results.

## Foundational mechanisms

1. **Arithmetic differences before norms.** Expand the joint successor and dilation expressions, cancel exact divisor and torsion terms, and only then estimate the remaining signed expression.
2. **Relative quadratic forms.** Separate the weak sector from its full orthogonal complement. Retain the mixed Schur correction; positive diagonal entries alone do not pay it.
3. **Concentration and rigidity.** Derive restrictions on every hypothetical negative complete state, rather than on states with a source-blind defect bound alone.
4. **Quantitative source preservation.** Transfers and limits must preserve the actual arithmetic weights, Gamma contribution, pole functional, and prescribed renormalization.
5. **Matched profiles.** Positivity and completeness must refer to the same profile and compatible scales.

## Imported foundational pillars

* The complete Weil ground state is the conductor-one pole direction.
* Tilted-spline complete Weil matrices have unconditional all-vector positivity on a nontrivial power-log overlap range.
* Joint top-band shell and pole expressions admit cancellation absent from separate estimates.
* Prime dilation has an exact square-energy identity on conductor packets, with weights `log m + tameDifferent m`.
* The actual Chebyshev cyclotomic energy splits into near and far bands; the far band has an explicit conductor-over-bandwidth bound.
* The prime coalescent surplus enters an unconditional selected-profile simple-critical-zero certificate.
* Hecke invariance of the positive collided pairing is an additional arithmetic requirement; reconstructing that pairing from theta data does not establish invariance.

These foundations belong to the programmes listed below. A new contribution must add a proved arithmetic consequence, not rename one of these identities.

## Tools to develop

| Tool | Required mathematical output |
|---|---|
| Prime-dilation energy calculus | Polarization, rigidity, and scale-sensitive control for actual conductor packets |
| Joint successor–dilation calculus | Exact mixed identities with their arithmetic and boundary terms retained |
| Relative mixed-form estimates | Bounds for growing packets in their true conductor energies, including the complementary-block correction |
| Arithmetic concentration theory | Exhaustive alternatives for negative complete states, with quantitative control of conductor escape |
| Moving-conductor harmonic analysis | Cancellation bounds for the literal Chebyshev near-band packets |
| Signed prime-pair estimates | Control of the actual oscillating surplus, retaining parity and the full frequency range |
| Quantitative integer approximation | Bounds on support, coefficients, and error cost as producer slope approaches one |
| Arithmetic conjugation | A constructed correspondence explaining the required invariance without assuming critical positivity |
| Effective index detection | Resolution estimates derived from arithmetic information, with gap dependence explicit |

## Core research questions

1. What states can be simultaneously close to successor and prime-dilation invariance while remaining pole-neutral? Which exact arithmetic energies classify them?
2. Can joint Gamma–pole–shell cancellation bound the mixed weak-sector interaction relative to completed conductor energy at growing overlap?
3. Can negativity of the complete form force stronger confinement than boundedness of the source-blind defect?
4. Can the actual Chebyshev near-band energy at bandwidth of order `sqrt N` be bounded by `N^(3/2 + ε)`? The weaker five-sixths target uses bandwidth of order `N^(1/3)` and exponent `5/3 + ε`.
5. Can the profile-compatible prime coalescent surplus be bounded by `(1/18 + o(1)) N(T, 2T)`?
6. Can the constant in `ψ(x) ≤ (1 + ε)x + Cε log² x` be bounded polynomially in `1/ε` for actual integer producers?
7. Which arithmetic construction forces collided-pairing invariance and excludes the known gauge twins?
8. Which arithmetic data control the resolution required to detect every nonzero integer collision defect?

The RH-complete versions of these questions remain research targets. Their conclusions are not available as assumptions, structure fields, or imported interfaces.

## Traps

| Invalid inference | Required distinction |
|---|---|
| Positive conductor diagonals imply a positive complete form | Mixed interactions and the full complement must be paid |
| Small average residual excludes every negative vector | Exceptional directions can carry the whole obstruction |
| A source-blind defect bound gives polynomial conductor capture | Existing counterexamples force stronger arithmetic input |
| A smoother receiver inherits tilted-spline positivity | Its Fourier tail and spectral floor change together |
| Fixed packets establish a growing-horizon theorem | Parameter dependence and common horizons must be explicit |
| One-sided prime-pair bounds control a signed kernel | Positive and negative parts require compatible discrepancy control |
| Near-line density implies on-line density | Shallow off-line pairs can survive every fixed-depth bound |
| Local pole squares assemble into the single global square | The archimedean coupling is essential |
| Source reconstruction proves positivity or invariance | These are separate arithmetic assertions |
| A new equivalent criterion answers a core question | A new discharged source estimate or construction is required |

## Position in the corpus

| Programme | Interface |
|---|---|
| `ArithmeticCastelnuovoSeveri`, `ArithmeticOrientationGeometry` | Scaling surfaces, signed intersection forms, arithmetic actions, and orientation obstructions |
| `CriticalArithmeticCorrelationTheory` | Complete conductor energies, ground state, finite-horizon residuals, and unconditional growing-overlap positivity |
| `SuccessorShellArithmetic` | Joint shell–pole identities and exact prime-dilation energies |
| `RenormalizedArithmeticPotentialTheory` | Completed conductor energies and their scale dependence |
| `ArithmeticDefectRigidity` | Defect confinement and its precise limits |
| `TransMetzlerWeilPositivity`, `EffectiveArithmeticHodgeTheory` | Profile-matched completeness and index-exhaustion schedules |
| `CompletedArithmeticForms` | Literal Chebyshev cyclotomic energies and moving near-band targets |
| `TransThresholdPairCorrelation` | Parity-sensitive signed prime surplus and critical-line census |
| `ArithmeticKreinLangerTheory`, `ArithmeticOfSquareRootPrecision` | Integer producers, precision costs, and zero-width laws |
| `ArithmeticPolarization`, `ConjugateDiagonalGeometry` | Source reconstruction, collided forms, conjugation, and integer detection |
| `AdelicKreinGeometry`, `RenormalizedIntersectionTheory` | Global pole coupling, renormalization, and exact index identities |

This programme owns joint arithmetic rigidity and relative estimates across these interfaces. It imports existing identities from their owners and supplies new arithmetic consequences back to them.

## Contribution and success criteria

A contribution must prove an unconditional identity, classification, inequality, or construction for explicitly defined arithmetic objects. Its mathematical inputs must be discharged. Its source, constants, parameter ranges, and quantifiers must survive formalization unchanged.

Useful advances include a relative mixed estimate with a genuinely smaller inverse-floor loss, a classification of arithmetic near-invariant states, a moving-conductor power saving, a better actual zero census, or a quantitative producer-cost theorem. Exact obstructions qualify only together with their strongest nontrivial positive survivor.

The programme succeeds in its full aim when its source-specific tools answer the core questions at the scales needed by their receivers. A foundational document, abstract interfaces, and existing equivalences do not by themselves meet that criterion.
