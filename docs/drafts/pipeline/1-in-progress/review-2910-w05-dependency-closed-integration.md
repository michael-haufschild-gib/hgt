# Dependency-closed integration of the working sources

- **ID:** review-2910-w05-dependency-closed-integration
- **Stage:** 1-in-progress
- **Type:** THEOREM / integration
- **Source:** W05 of the obstacles summary.
- **Statement:** Integrate and audit ZeroSideStratum, LiouvilleTwinSelectivity,
  AKLT, ASRP, the CACT touching capstone, ACS Haar prime edges, and the real
  loop-group spherical function with their actual dependency closure.

## Scope

Existing implications and classifications retain their stated mathematical
scope. Integration supplies no missing RH sign, index ceiling, growing-rank
estimate, arithmetic quotient or measure. No component is accepted merely
because its umbrella lists an import or a nearby theorem compiles.

## Gates

- [ ] Identify every named component's actual terminal statements and imports.
- [ ] Resolve missing dependencies individually; preserve existing oleans.
- [ ] Check affected terminal leaves directly and inspect transitive axioms.
- [ ] Wire all finished imports and reconcile source documentation.
- [ ] Record exact surviving conclusions and remaining mathematical boundaries.

## Mathematical scope of the integrated results

1. The actual ζ atomic Gram has negative index bounded by the number of right
   zeros on the finite stratum, uniformly in scaled width. The tempered
   single-pair countermodel shows why this conclusion alone cannot supply
   fixed-width positivity. The Liouville witnesses and narrow-width survival
   concern the complete twisted form, including its unchanged pole terms.
2. Cyclic restrictions detect finite Krein–Langer pairs; tower-faithful spectra
   carry their index on all but finitely many towers. Fine towers recover the
   whole index without a finite-support assumption. Local axis assemblies
   obey a zero-or-infinity law, while unitary twists preserve locality.
   Minimal exceptional waves recover weights and multiplicities, and the
   actual ζ collision law agrees with the fine-tower index.
3. The count's stabilizer is exactly the square-root partial-sum class.
   Tower positivity has trivial stabilizer above coefficient one. The Nair
   lattice is attained exactly; its two precision halves are the respective
   one-sided counts, with exponent equal to the zero width. Monotone
   Möbius inversion retains Mertens precision; the exact Stirling split
   preserves the separate smooth and sawtooth terms. Two primes separate
   each ordinate difference quantitatively, without a many-node Gram floor.
4. The touching capstone gives one eventual horizon for all scaled widths
   in `(0,1]`. The Haar source retains its literal divisor-square reserve
   after Gamma payment, and every original prime edge has a strict negative
   full-Weil interaction. An entry sign does not determine the whole form.
5. The real loop-group spherical function uses actual Iwasawa factors.
   Their character values agree because the generated compact subgroup
   meets Borel in the sign torus. This proves equivariance and invariance;
   it supplies no arithmetic quotient, invariant measure, or convergent
   Eisenstein coset sum.

## Source inventory

| Component | Evidence to audit |
|---|---|
| ZeroSideStratum | All-ratio RH implication; finite-support atomic index bound; tempered countermodel. |
| LiouvilleTwinSelectivity | Actual negative atomic witnesses above Robin–Euler threshold; narrow survival. |
| AKLT | Actual kernel/index, arithmetic invariance and prime-tower capstones named in the source review. |
| ASRP | Integrality lattice/exponent, deciding inputs, inversion and phase separation capstones. |
| CACT touching | Actual complete-Weil positivity capstone at touching. |
| ACS Haar prime edges | Complete form with Gamma reserve and signed prime-edge witnesses. |
| Loop spherical function | Actual K∩B=M and Borel equivariance, with Iwasawa dependencies. |

## Terminal audit inventory

The review's AKLT source closure consists of these eleven modules:
`CyclicSubgroupsDecideTheKreinLangerClass`,
`TowerFaithfulSpectraAreDecidedByAlmostEveryTower`,
`LocalConstituentsMeetOnlyAtTheIdentity`,
`TheTwistTowerCompletesTheUpperCount`,
`TheIndexIsContinuousOffTheDiscriminant`,
`TheParityFormOfTheGlobalLaw`,
`TheIndexIsTheNumberOfExceptionalWaves`, `CompressionsAreReceivers`,
`FineTowersDecideEveryOrbitKernel`, `LocalityIsTwinBlind`, and
`TheCollisionMassIsTheWaveNumber`. Terminal axiom commands now cover the
positive classifications, counterexamples, actual ζ equivalences and
multiplicity-sensitive collision law. Checks remain pending.

`ZeroSideStratum` has six terminal audits and `LiouvilleTwinSelectivity`
five. The CACT leaf
`OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching` has three.
`TheHaarPrimeEdgesRetainTheirGammaReserve` now has four covering the
retained divisor squares, exact full form, and strict prime-edge sign.
`HTGeometry/LoopEisenstein/RealSphericalFunction` now has five covering
the actual compact–Borel intersection, independence of chosen factors,
Borel equivariance, compact invariance and nonvanishing. Checks remain
pending. All these named modules already occur in their umbrellas.

The ASRP terminal closure has seven leaves:
`IntegerDirichletPolynomialsAtArithmeticPoints` (eight audits),
`CurvesCalibrateThePrecisionExponent` (four), `OneSignedPerturbations`
(seven), `SupNormCeilingsForceVanishingAtSmallRationals` (seven),
`TowerPositivityIsPrecisionExact` (six), `TheStirlingErrorSplits` (seven),
and `TwoPrimeTowersSeeEveryOrdinateDifference` (two). Their audits also
cover imported count-stabilizer, exact integrality, deciding-input and
monotone-inversion statements. Checks remain pending.

The integer Dirichlet-polynomial results concern integer evaluation
points and real-axis zero counts; they assert no general impossibility
of other arithmetic bounds at complex arguments. Concurrent later
extensions are preserved and are not silently included in this audit.
No full or umbrella build is part of this audit.

## Leaf checks

Each row uses `lake --old env lean GaloisForLFunctions/<module>.lean`
from `formal/`. The printed declarations cover their transitive dependencies.

| Leaf | Terminal audits | Result |
|---|---:|---|
| TM/ZeroSideStratum | 6 | Pending |
| TM/LiouvilleTwinSelectivity | 5 | Pending |
| CACT/OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching | 3 | Pending |
| ACS/TheHaarPrimeEdgesRetainTheirGammaReserve | 4 | Pending |
| HTGeometry/LoopEisenstein/RealSphericalFunction | 5 | Pending |
| AKLT/CyclicSubgroupsDecideTheKreinLangerClass | 4 | Pending |
| AKLT/TowerFaithfulSpectraAreDecidedByAlmostEveryTower | 4 | Pending |
| AKLT/LocalConstituentsMeetOnlyAtTheIdentity | 3 | Pending |
| AKLT/TheTwistTowerCompletesTheUpperCount | 2 | Pending |
| AKLT/TheIndexIsContinuousOffTheDiscriminant | 3 | Pending |
| AKLT/TheParityFormOfTheGlobalLaw | 2 | Pending |
| AKLT/TheIndexIsTheNumberOfExceptionalWaves | 2 | Pending |
| AKLT/CompressionsAreReceivers | 3 | Pending |
| AKLT/FineTowersDecideEveryOrbitKernel | 4 | Pending |
| AKLT/LocalityIsTwinBlind | 2 | Pending |
| AKLT/TheCollisionMassIsTheWaveNumber | 3 | Pending |
| ASRP/IntegerDirichletPolynomialsAtArithmeticPoints | 8 | Pending |
| ASRP/CurvesCalibrateThePrecisionExponent | 4 | Pending |
| ASRP/OneSignedPerturbations | 7 | Pending |
| ASRP/SupNormCeilingsForceVanishingAtSmallRationals | 7 | Pending |
| ASRP/TowerPositivityIsPrecisionExact | 6 | Pending |
| ASRP/TheStirlingErrorSplits | 7 | Pending |
| ASRP/TwoPrimeTowersSeeEveryOrdinateDifference | 2 | Pending |

Abbreviations: TM=`TransMetzlerWeilPositivity`, CACT=`CriticalArithmeticCorrelationTheory`,
ACS=`ArithmeticCastelnuovoSeveri`, AKLT=`ArithmeticKreinLangerTheory`,
ASRP=`ArithmeticOfSquareRootPrecision`.
