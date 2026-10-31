# Scale-Signed Incidence Criticality (SSIC)

Namespace `GaloisForLFunctions.ScaleSignedIncidenceCriticality`; umbrella
`ScaleSignedIncidenceCriticality.lean`; 19 modules. Entry module `TheResolutionLimitOfAReading.lean`.

## 1. Motivation

A proof never touches the arithmetic datum; it touches a list of observables (a certificate at one
aperture, magnitudes, moments, a node density, a rate). SSIC is an information theory of proposed
arguments: it computes, for each class of observables, the **exact best bound** any method reading
them can certify, and which observable must be added to decide RH. Every no-go of the corpus of the
form "two data share the observables but differ on the property" becomes one number.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Reading, shadow | `shadow r d` | $\{e : r\,e = r\,d\}$ |
| Resolution | `Resolves r P` | $P$ constant on shadows ⇔ $P$ factors through $r$ |
| Collapse | `Invisible r κ` | $r\circ\kappa = r$ |
| Limit / floor | `resolutionLimit`, `resolutionFloor`, `resolutionInterval` | sup / inf of invariant over shadow |
| Certification | `Certifies`, `CertifiesLower`, `Refutes` | bound on whole shadow; nothing in shadow satisfies $P$ |
| Faithful | `Faithful I r` | limit $= I$ |
| Order | `Refines`, `joinReading`, `familyReading` | finer readings, joins = shadow intersections |
| Zero data | `TemperedZeroConfig`, `width` | width $=\sup|\Re\rho-\tfrac12|\in[0,\tfrac12]$ |
| Aperture readings | `aperturePositivity`, `apertureGain`, `familyPositivity`, `fullPositivity` | Weil form $\ge0$ (or $\ge\eta\|f\|^2$) on tests in $[-a,a]$ |
| Lattice datum | `ScaleDepthDatum`, `sdScale`, `sdDepth`, `DepthDatum` | off-line lattice: scale $L$, depth $\delta$ |
| Deficit | `weilFloorThreshold`, `depthResolution`, `bandEnergy`, `bandDeficit` | $2L(\cosh\delta L-1)$; inverse $\operatorname{arcosh}(1+\eta/2L)/L$; index-$n$ ground energy |
| Rates | `deficitRateBelow`, `rateSet`, `GrowthProfile`, `rateBoundsOn` | exponential deficit growth; secant rates |
| Policies | `adaptiveReading`, `scaleAdaptiveReading`, `ScaleMatched`, `TransNyquistPolicy` | aperture/precision adapted to scale |
| Node face | `nodeScale`, `deleteNode`, `AsymptoticReading`, `membershipReading` | missing prime powers; density-type readings |
| Prime face | `radiusReading`, `weightAperturePositivity` | full Weil functional on aperture-$R$ tests |
| Pronic Gram | `crossScaleExponent`, `typeIIGramReading`, `rankTwoReadoutReading` | $\theta=2\log P/\log X\in[0,2]$ |
| Collapse fatality | `StrictlyFatalAt`, `NeutralAt` | $P\,d\wedge\neg P(\kappa d)$ |
| ζ ratios | `zetaTwoApertureRatio`, `primeWindowTwoApertureRatio` | $(\mu(A_0)-\mu(A))/\mu(A_0)$ |
| Comb datum | `CombPairingDatum`, `scalarCombEnergyReading`, `completedCombReading` | (mass, energy, charge) with CS |

## 3. Language

- **Blind**: limit = a priori maximum. **Informative**: interval proper. **Faithful**: interval a point.
- **Sub-/trans-Nyquist**: aperture $a\le L/2$ / $>L/2$ for lattice spacing $2\pi/L$; aliasing index $\lceil2a/L\rceil$.
- **Sign reading** (certificate holds or not) vs **magnitude reading** (value of a ground energy/deficit).
- **Cofinal** resource: data on an unbounded parameter set. **Bounded**: below a finite bound.
- **Gate**: a blindness theorem a method class must pass; passing is necessary, not an estimate.

## 4. Mechanisms

**A. Calculus (abstract).**
1. Collapse–resolution dichotomy (`not_resolves_of_separating_collapse`); resolution = factorization (`resolves_iff_exists_factorization`); one witness pair suffices (`not_resolves_of_pair`).
2. Floor theorem: a global maximizer in the shadow fixes the limit (`resolutionLimit_eq_of_mem_shadow_of_max`); limit = exact strength (`certifies_iff_resolutionLimit_le`).
3. Blindness is closed under post-processing, joins and families of any cardinality (`Invisible.familyReading`); faithful readings transfer to dominated invariants.

**B. Aperture face (signs).**
4. For every aperture $a$ an off-line lattice of width ½ (spacing $\pi/a$) passes the certificate: limit ½, floor 0 (on-line lattice), interval $[0,\tfrac12]$ (`resolutionInterval_width_aperturePositivity`). Same for any gap $\eta$ (`resolutionLimit_width_apertureGain`), any bounded family, any monotone unit (`theFloorIsUnitIndependent`). Unbounded certificate: limit 0 (`apertureResolutionJump`).
5. With scale free, one aperture resolves no depth (`resolutionLimit_sdDepth_scaleDepthReading`); depth is the complete dilation invariant (`dilationEquiv_iff_sdDepth_eq`).
6. Floor witnesses need infinitely many off-line zeros (`theFloorsNeedInfinitelyManyOffLineZeros`); a finite off-line set is refuted at an explicit aperture.

**C. Past Nyquist (magnitudes).**
7. Just above Nyquist the floor level is $2L(\cosh\delta L-1)\ge L^3\delta^2$: depth enters quadratically (`cube_mul_sq_le_weilFloorThreshold`); limit $\min(\tfrac12,\operatorname{arcosh}(1+\eta/2L)/L)\le\sqrt{\eta/L^3}$ (**square-root law**, `depthResolution_le_sqrt`); budget $\eta\le\beta^2L^3$ certifies depth $\beta$, sharp (`theDeficitBudgetLaw`).
8. Depth = half the exponential growth rate of the deficit; rate infimum is faithful and scale-free (`theRateReadingIsTheAnswer`); uniform deficit (one level for all apertures) separates on/off-line (`theGateIsPassedByNonGrowth`).
9. Two bands: $\delta=\operatorname{arcosh}(t_3/2t_2-1)(t_3-4t_2)/t_2^2$ exactly (`depthFromBands_eq`); three bands cancel unknown mass, $(t_4-t_3)/(t_3-t_2)=2\cosh\delta\ell$ (`threeBandsDefeatTheMass`); pair doubling $M(2a)/M(a)=2\cosh2\delta a$. Ratio precision $\eta$ ⇒ $\delta L\le\sqrt{2\eta}$.
10. Sign blind, magnitude pair faithful on the same family (`theDichotomyOfSignAndMagnitude`).

**D. Hiding laws.**
11. Single pair: $\delta\le\operatorname{arsinh}(M/|Q|+1)/v$ (log of local mass). Diluted lattice: $\ell e^{\delta(2a-\ell)}\le2L+2a+\ell$; reach $a\le\log((3L+\ell)/\ell)/2\delta+\ell/2$ (`theReachLaw`); aliasing free exactly below $\ell/2$ (`theFreeRegimeIsSharp`).
12. Band energy $=\ell\sum_j(\cosh(\delta\ell(2j-n+1))-1)$, strictly increasing in depth and index; diluted reading ⇔ one band inequality; dyadic comb teeth read $-2\,$bandDeficit at indices 2, 3.

**E. What must be verified.**
13. Monotone faces reduce to cofinal sets: positivity on any unbounded aperture/radius set ⇒ RH (`theReductionDichotomy`). Incidence face does not reduce: every prime power individually necessary.
14. Node face: prime powers are the least positive node set under RH (`isLeast_zeroPoleBlindPositiveOn`); asymptotic readings (densities, sieve levels) floor at ½ in node scale; deletion fatal ⇔ prime power.
15. Refutation finite, confirmation uniform: RH ⇔ no bounded-radius certificate refutes $\Lambda$ (`riemannHypothesis_iff_no_radiusReading_refutes`); one bit refutes a node set (`theNodeFaceAsymmetry`).
16. Rates are cofinal invariants (convex profiles, `theRateIsACofinalInvariant`; lattice face without convexity, `faithful_sdDepth_cofinalRateSet`); bounded aperture ranges certify no rate at all (`theRateDichotomyIsSharp`).

**F. Arithmetic instances.**
17. Pronic Gram: sign-blind Type-II and rank-two readout readings have limit 2, floor 0; smoothness order $K$ certifies $2K/(K+1)$; residue mass faithful for the Bernoulli main term; actual centred prime row bypasses the shadow on $7/6<\theta<2$ (`centredPrimeRow_bypasses_resolutionLimit_two`).
18. Parity collapses: even flip on $k\star o_\varepsilon$ strictly fatal ⇔ pole value 0 and even-part pole value ≠ 0; cubic moments pin odd sign orbits and reduce squarefree ones to the even flip; residue-class complementation neutral ⇔ unit density in $(\tfrac14,\tfrac34)$, subgroup index ≥ 4 fatal.
19. ζ band recipe: two-aperture ratio $R(A)$ with base $A_0\le21/200$; $R\le1+Ce^{2\sigma A}$ ⇒ width $\le\sigma$; near-top zero ⇒ $R>1$ beyond visibility lag; unconditional $R<1$ for $A\le21/200$.
20. ζ rates: lag, Chebyshev-deficit, band and receiver-damping rates = width unconditionally (`five_rate_currencies_of_zeta`); local off-line count is the exact missing datum (deficit alone floors width at 0; with count, explicit floor).
21. Policies at growing density: one sub-Nyquist scale ⇒ limit ½; scale-matched certify $\beta$ ⇔ $\eta(L)\le$ threshold; $\eta/L^3\to0$ suffices. Available ζ schedules are blind: single-height horizons sub-Nyquist; Chebyshev deficit $10+68e^L$ exceeds threshold.
22. Incidence ledger: prime side ≤ diagonal + first-power comb charge; scalar comb energy leaves charge in $[-\sqrt{ME},\sqrt{ME}]$, every ratio realized by dilated odd bumps; signed amplitude completes faithfully; coherent translation residual controls the charge.

## 5. Pillar theorems

| Theorem | Content |
|---|---|
| `not_resolves_of_separating_collapse`, `resolutionLimit_eq_of_mem_shadow_of_max` | dichotomy; floor theorem |
| `resolutionInterval_width_aperturePositivity`, `theFloorIsUnitIndependent` | aperture sign readings vacuous both ways |
| `dilationEquiv_iff_sdDepth_eq` | depth = complete dilation invariant |
| `theDeficitBudgetLaw`, `depthResolution_le_sqrt` | square-root precision law |
| `theDepthIsHalfTheDeficitGrowthRate`, `sInf_rateSet` | depth = rate |
| `depthFromBands_eq`, `threeBandsDefeatTheMass` | magnitudes invert depth |
| `theDichotomyOfSignAndMagnitude` | sign blind / magnitude faithful |
| `theReachLaw`, `theFreeRegimeIsSharp` | hiding prices |
| `riemannHypothesis_iff_no_radiusReading_refutes`, `theNodeFaceAsymmetry` | refutation finite, confirmation uniform |
| `theRateIsACofinalInvariant`, `theRateDichotomyIsSharp` | cofinal vs bounded rates |
| `resolutionLimit_typeIIGramReading_eq_two`, `centredPrimeRow_bypasses_resolutionLimit_two` | pronic Gram face |
| `five_rate_currencies_of_zeta` | ζ rates = width |
| `counterexample_primeSide_obstructions` | ζ cannot realize the hiding spec |

## 6. Tools

**Developed.** Resolution calculus (limit, floor, interval, refinement, joins, families, refutation,
fatality trichotomy); lattice deficit inversion (threshold, depth resolution, band energies,
cosh decomposition); band and doubling inversion formulas; rate readings (secant monotonicity,
cofinal sets); witness constructions (dense maximal datum, ramp profiles, coherent/anti-coherent
comb witnesses, dilated odd bumps).

**To build.** A scale-matched schedule for ζ ($L/2<A(L)\le L$, precision $o(L^3)$) from prime
estimates; rate readings for non-convex profiles; an exhaustive repair classification for a fixed
reading class; a bound on the coherent comb residual without archimedean subsidy.

## 7. Open questions

1. Which single-height prime estimate realizes a trans-Nyquist schedule with sub-cubic precision for ζ?
2. Is a local off-line count necessary for the physical-$L^2$ polar rate to equal the width?
3. Exact limit of the enriched actual-row pronic Gram reading at the endpoint $\theta=2$.
4. Rate readings for profile classes beyond convex/lattice; which tail regularity is necessary.
5. Fatality of Liouville twist, shifted pair, Beurling deformations as receiver collapses.
6. Complete list of repairs (added observables) for a specified reading class, each with its precision cost.

## 8. Traps

| Trap | Why |
|---|---|
| Strengthening a blind reading in its class | more bounded apertures, larger gap, monotone unit change: limit stays ½ |
| "Bounded aperture is weak because finite" | the operative obstruction is sub-Nyquist; trans-Nyquist bounded data is informative |
| First-order sensitivity to zero position | deficit is quadratic in depth: no first-order term |
| Rate claims on bounded aperture ranges | certify nothing (ramps) |
| Sparse sampling without structure | cofinality needs convexity or lattice structure |
| Density/asymptotic arguments on node face | invisible to one prime-power deletion |
| Reading "resolving ⇒ RH" | node gates read "resolving ⇒ ¬RH" (positivity holds only under RH) |
| Scalar comb energy | discards the signed charge; full CS interval open |
| RH-equivalent ratio criteria | `riemannHypothesis_iff_forall_zetaTwoApertureRatio_le_one` etc. are restatements |
| Faithful ≠ provable | a faithful reading names the deciding numbers, not their reachability |
| Mixing configuration classes | crystals vs finite sets vs single pairs have different prices |
| Unconditional ζ schedules | both available schedules (single-height, Chebyshev) are blind |

## 9. Context

| Programme | Relation (verified imports) |
|---|---|
| SquareRootThreshold | 24 imports: lattice models, Nyquist laws, visibility, hiding, width dictionary, incidence ledger grading |
| TransHorizonIncidenceMechanics | parity rows, cubic moments, quarter law, subgroup flips |
| BezoutValuationIncidence | cross-scale Gram, coherent block, readout barrier, centred prime row |
| ArithmeticOrientationTheory | two-way: SSIC uses oriented readings and even-flip modules; AOT imports resolution calculus, refutation, magnitude-pair, counterexample spec |
| ArithmeticCompensationTheory | prime comb translation, compensation coordinates, de la Vallée Poussin polar saving |
| ArithmeticIncidencePositivity | prime-tower ledger reduction |
| BiScaleUncertainty | prime-power node criticality |
| SmoothBernoulliPoleCalibration | even pole calibration, log-moment pinning |
| ArithmeticCriticalityTheory | ground-energy floors at small aperture (transitive) |

## 10. Big picture

SSIC says the RH problem is not short of positivity statements but of the right observable. Every
sign-type certificate at a bounded scale is exactly as informative as no certificate; every
magnitude above the Nyquist scale is exactly informative. The width lives at infinity or in a size,
and enters quadratically, so any argument must control a deficit to precision $\beta^2L^3$ at the
scale of the configuration, and must do so for every prime individually rather than on average. The
two available unconditional ζ schedules fall on the wrong side of this line — one below Nyquist,
one with an exponentially large deficit — which locates the missing input precisely: a
trans-Nyquist magnitude estimate with sub-cubic precision, equivalently control of the local
off-line count or of the signed first-power comb charge. For the RH programme this is a filter: a
route is worth building only if it names its reading, crosses Nyquist, reads magnitudes, and keeps
every prime's weight.
