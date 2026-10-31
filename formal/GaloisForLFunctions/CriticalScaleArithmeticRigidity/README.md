# Arithmetic rigidity at critical scale

Namespace: `GaloisForLFunctions.CriticalScaleArithmeticRigidity`.
Programme umbrella: `CriticalScaleArithmeticRigidity.lean`.

## Motivation

The complete Weil form has positive conductor energies and an identified pole ground state, yet its smallest positive energy decreases as the test profile approaches a scale that detects every off-line zero. An absolute error estimate can destroy this information by charging the smallest energy to every conductor and every interaction. Separately estimating the prime, successor, pole, and Gamma terms can also destroy their exact cancellation.

This programme studies which signed states remain compatible with the joint arithmetic identities of addition and multiplication. Its aim is to derive arithmetic rigidity and relative energy bounds at growing scales. The source, its archimedean boundary, and its pole functional remain part of every object.

The finite-packet foundation consists of exact joint arithmetic rigidity and source-preserving sampling theorems. The complete critical-scale questions require these tools to interact with the full signed form and its exceptional states.

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

## Exact packet calculus

Write `c_m(n)` for the actual Ramanujan sum. The raw packet is

`F_a(n)=Σ_(1≤m≤Q) a_m c_m(n)`.

Complete-period averaging uses the common period `Q!`. Its coefficient norm is `Σ_m φ(m)a_m²`. Normalized coordinates instead use `c_m/√φ(m)` and Euclidean coefficient mass. Prime adjunction energy in normalized coordinates is

`L_Q(a)=Σ_(1≤m≤Q)[log m+tameDifferent(m)]a_m²`.

The two coordinate conventions serve different exact identities; no weight is discarded when transferring between them.

### Successor transversality and the pole

For `r_m(h)=c_m(h)/φ(m)`, every approximating packet satisfies

`mean (F_a(n+h)−F_b(n))²`
`=Σ_m φ(m)(b_m−r_m(h)a_m)² + Σ_m φ(m)(1−r_m(h)²)a_m²`.

This is the raw-coordinate realization of the existing successor projection geometry in `BezoutValuationIncidence`. At lag one, its sharp three-quarters leakage controls every conductor above parity. The added dyadic reading is exact:

`mean (F_a(2n)−F_a(n)) = 1_(2≤Q)a_2`.

Consequently successor approximation error plus the square of this pole reading controls three quarters of the entire nonconstant coefficient mass. The constant is optimal. The common zero fibre consists exactly of constant packets with matching approximants. See [DyadicPoleRigidity.lean](DyadicPoleRigidity.lean), `three_quarters_nonconstantPacketMass_le_jointRigidityEnergy`, `universal_joint_rigidity_lower_iff`, and `jointRigidityEnergy_eq_zero_iff`.

### Affine sampling without period-length horizons

An integer affine map sends each primitive root to a root of no greater order and changes its phase. The exact affine spectrum sums coefficients at every collision before taking a norm. Thus, for

`f(n)=F_a(kn+h)−F_b(ln+j)` and `E(f)=mean_(n<Q!) f(n)²`,

`|Σ_(A<n≤A+K) f(n)²−K E(f)| ≤ Q(Q−1) E(f)`.

This holds for every `Q≥2`, every window, and all affine parameters and coefficient families. The error is relative to the actual difference energy, including its mixed terms. Harmonic sampling gives

`[log(N+1)−log(Q(Q−1)+1)] E(f) ≤ Σ_(1≤n≤N) f(n)²/n`.

[AffineWindowEnergy.lean](AffineWindowEnergy.lean) proves these identities and estimates through explicit spectral transport, finite Parseval, and the corpus's sharp two-sided large sieve. Complete-period arithmetic energy therefore becomes an observable quantity at quadratic conductor horizons.

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
| Rigidity of conductor packets classifies every negative complete state | The actual negative state still needs quantitative conductor capture |
| Relative adjunction control is relative completed-energy control | The completed conductor floor also includes shell, Gamma, and pole contributions |
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
| `BezoutValuationIncidence` | Exact successor projection, sharp phase loss, affine conductor identities, and two-sided large-sieve sampling |
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
