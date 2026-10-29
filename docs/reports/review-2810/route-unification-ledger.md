# Route-unification ledger

**The 31 live routes and 18 candidate branches are faces of three core problems: the selective critical sign (U1), source-complete Weil positivity (U2) and independent faithful forcing (U3).** Four facts bind them:

1. **Selectivity is common to all three by theorem.** No twin-blind input reaches an RH-complete family. The one measured selective input, the margin \(2\log2\), separates \(\zeta\) from the Liouville twin but is shared at its maximum by single-prime flips \(p\ge11\).
2. **Precision is common to all three.** \(\Lambda\) and \(\Lambda+\varepsilon n^{-\eta}\) are never both tower-positive. Distribution statements stable under relative error \(o(1)\) cannot decide any of the three problems [S].
3. **Hecke towers join U1 and U2.** Along one prime's towers, U2 cross-level entries are U1 prime-error sequences, and tower positivity is RH for one fixed prime, at every generator size.
4. **The finite-support stratum crosses all clusters at the Lindelöf level.** Critical energy, subtracted lag, cosine defects, heat-flow nonreal counts, complete-form index and two-prime tower index all receive finite off-line support, which implies LH and a fixed strip [L].

[Route obstacles](route-obstacles.md) · [summary and priorities](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [frontier map](../rh-current-frontier-map.md). Evidence: corpus searches and Lean statements; **[K]** includes individual Lean and transitive-axiom checks. No full or umbrella builds. **[L]**/**[S]**/**[K]** as in the frontier map; **(inference)** = conclusion of this review, not a Lean theorem. [Working log](../../../logs/review-2810-v3-research-2026-10-28.md).

## What "the same problem" means

| Relation | Meaning | What it does not mean |
|---|---|---|
| **E — Endpoint equivalence** | Two stated conditions are both equivalent to RH, or to each other. | A usable estimate between the producers. |
| **T — Proved source transfer** | An identity, approximation or inequality carries the actual source from one formulation to another within its hypotheses. | Extension to growing supports, primes, degrees or another norm. |
| **S — Structural similarity** | Two approaches face the same kind of sign, exhaustion or faithfulness problem. | A theorem identifying their objects. |

At the E level all RH criteria are equivalent almost tautologically. Unification is meaningful only through T-bridges and a shared unproved producer.

## The three core problems

| Problem | The one missing statement | Faces (routes) | Wall |
|---|---|---|---|
| **U1 — Selective critical sign** | A bound on the actual signed prime/Möbius discrepancy at the critical scale, in some receiver currency. | WL, FU, RP, MC, LI, PM, JAS, CTF, PBM, RB; prime-error faces of HF/SRT/AIP. Via the Chebyshev identity, the off-diagonal of every U2 route. | 1 |
| **U2 — Source-complete positivity** | Positivity, or index zero, of the complete Weil form, with Gamma and both poles, on a source-complete family. | RW, TT, HF, CHMD, SZ, EWU, OWU, SRT, ACT, AIP, ACS; via sign receivers also PA, LA, TH, WD, HCF. | 1 and 3 |
| **U3 — Independent faithful forcing** | A source-built structure whose proved property supplies U1 or U2. | TG, RN, XN, BAG, GTA, all 17 candidates and PW-B; geometric faces of HF/ACS. | 14 |

Each core problem meets all three walls: Wall 1 asks for the estimate, Wall 3 for its transfer, Wall 14 for its source of force.

**Cross-cutting requirements on every producer.**

| Requirement | Status | Test object |
|---|---|---|
| **Selectivity** | Theorem [L] | Fail for the Liouville twin, scalings \(c\Lambda\), quadratic mixtures. |
| **Beyond the margin** | Theorem [L] for submaximal gaps, [S] at the maximum | Fail for single-prime flips \(\omega_p\), \(p\ge11\), which share the gap \(2\log2\). |
| **Parity** | Criterion (inference) | Majorant information \(|\lambda|\le\Lambda\) is consistent with the Liouville twin, as sieve information is consistent with the parity-twisted sequence. |
| **Precision** | Theorem [S] on towers | Fail for \(\Lambda+\varepsilon n^{-\eta}\), every \(\eta<\tfrac12\). |
| **Unbounded aperture** | Inference | Finite-aperture inequalities move continuously in \(\varepsilon\), so they cannot fail for every perturbation. |

[Selection](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/PositivityAtEveryRootSelectsTheVonMangoldtWeight.lean), [maximal flips](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/LargePrimeFlipsAttainTheMaximalGap.lean), [precision](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheDyadicSignIsRigid.lean).

## Strongest unifications

### A. U1 and U2 meet entry by entry (T)

For ordered tests (\(\operatorname{supp}f<b<\operatorname{supp}g\)) and every \(c\):
\[
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g).
\]
The Gamma tail decays like \(\pi e^{-2\,\mathrm{gap}}\), and on the pole hyperplane only the prime comb is left. So WL/FU/RP/PBM (prime-error histories) and HF/ACS/AIP/RW/OWU (complete form) ask for the same signed quantity in different test-function norms. The pole product, which alone grows across scales, is cancelled by the prime main term \(e^h\). That is where \(\Lambda\) differs from the Liouville twin (prime sum \(\approx-e^h\)) and from character twists (\(o(e^h)\)). [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean), [separated levels](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/SeparatedLevelsCoupleThroughTheChebyshevError.lean).

### B. One measured margin, two layers of selectivity (T)

RW, HF, ACS, AIP, OWU, EWU, SRT, SZ, CHMD and ACT all reduce, on atomic or complete sources, to the same form.

- Its pole hyperplane is the harmonic hyperplane \(\sum x_n/\sqrt n=0\).
- The prime form of \(\zeta\) has gap exactly \(2\log2\) there; the Liouville twin's gap is \(0\); every gauge's gap is at least \((2\log2)c_N^2\).
- At every width the atomic sign is the Markov gap on \(p=0\) plus one affine scalar.
- The sharp selective Gårding inequality turns the margin into a reserve \(c_0(2\log2-\eta)\) at narrow widths.

These routes share the quantified margin and a positive complete-matrix plateau theorem at each fixed separated width [S]. Their open transfer crosses touching and overlap ([Q1](obstacles-summary.md#q1)). The margin is only the first layer of selectivity: it is parity-selective (Liouville fails) but not \(\zeta\)-selective (\(\omega_p\), \(p\ge11\), share it). The second layer must see every prime's sign at square-root precision and unbounded aperture. That layer is RH-strength (inference).

[Margin](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheSelectiveMarginIsTwoLogTwo.lean), [harmonic correlation](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/HarmonicCorrelationPaysThePrimeGap.lean), [gap and scalar](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar.lean).

### C. Atomic families and the separated regime (T)

SRT, AIP, HF and ACS share one atomic receiver, valid at widths \((\log\log N)^\alpha/N\) for every \(\alpha>1\).

- The Markov form is negative under overlap growth unconditionally.
- The Liouville twin, scalings \(c\Lambda\) and quadratic mixtures are negative at every root.
- Arbitrary-shape narrow positivity holds up to a quarter of the Robin–Euler ratio.
- Exact bounded spectral counts identify the bottom of the complete matrix [S]. For each \(b<2-\log(2\pi)\), one smooth plateau has every eigenvalue at least \(b\), eventually at every fixed \(0<c<1\) [S]. The profile can retain nearly unit mass; the horizon depends on \(c\).

Strictly separated positivity has no uniform touching/overlap conclusion. The RH receivers require a source-complete limit, including the families with \((\log\log N)^{1+\varepsilon}\) overlap. A schedule approaching \(c=1\) from below is not itself such an exhaustion. The \(\alpha=1\) edge is a quasi-analyticity boundary of the stated synthesis (inference).

[Denjoy–Carleman](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDenjoyCarlemanProfiles.lean), [quarter](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheStabilityRegimeReachesAQuarterOfTheRobinEulerThreshold.lean), [splitting](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFullWeilMatrixSplitsAtTheSpacing.lean).

[Complete spectral counts](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum.lean), [full separated plateau sign](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive.lean) [S].

### D. Hecke towers, Toeplitz symbols and RH (T)

A quadratic form along the orbit of one Hecke dilation is a Toeplitz form. Its positivity is a statement about a spectral measure on the circle, and the corpus proves that this statement is RH.

| Face | Result |
|---|---|
| ACS one-prime tower law | Negative index on \(p\)-towers = number of distinct outer eigenvalues \(p^{\rho-1/2}\); RH iff positivity on all \(p\)-towers for one prime [L]. |
| SMAP pole-free generators | The same with generators supported in \([-\varepsilon,\varepsilon]\), any \(\varepsilon>0\) [S]. |
| ACS/SMAP self-similarity | \(C_{2a}+C_{2a+1}=T_{\log2}C_a\); every twisted Weil pairing is level-Toeplitz. |
| SAHT level matrix | Prime two is the unilateral shift on every generator chain. |
| SAHT whole-orbit projection | Every real lag has original-Gamma head error ≤\(96\Gamma/(1+\log A)\). Each fixed finite Euler family and the complete all-prime exponent≥3 sector cost their finite coefficient mass times this bound [K]. The higher-power estimate pays the sum of absolute termwise errors and every finite selection. All levels remain; no full-Weil transfer is implied. |
| SMAP level couplings | Pole rank two and removable; Gamma \(\pi4^{-(d-1)}\); touching uniform; prime part a Chebyshev sequence. |
| LI / ALG Cayley ladder | RH iff the Cayley–Li Toeplitz ladder is negative semidefinite on primitive vectors; couplings never decay [S]. |
| ACP Stepanov mechanism | \(1-T_p^N\) kills a zero symbol iff the zero is critical and on a height lattice. |
| HCF grids | One prime grid aliases a nonreal pair to a positive atom; two grids decide. |
| HKT | Positive kernel plus separated hyperbolic pairs: index exactly the number of pairs [S]. |

**Unifying statement.** Along a \(T_{\log p}\)-tower, the explicit formula writes the lag sequence as a sum over zeros of \(p^{d(\rho-1/2)}\). Off-line zeros are hyperbolic characters, and positivity is their absence. LI's ladder is the same statement in Li coordinates. HCF's aliasing and the Stepanov lattice criterion are the one-prime aliasing that a second prime removes. The finite-generator approximation is a proved transfer for L², fixed finite Euler correlations and the all-prime higher-power sector. A reduction of U2 still needs complete-form transfer and a sign theorem on the retained orbits; neither follows from their finite generator count.

[One prime](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OnePrimeSeesTheWholeDefectOfZeta.lean), [pole-free generators](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheDyadicSignOfAPoleFreeGeneratorIsRH.lean), [Cayley ladder](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RHIsReflectionPositivityOfTheCayleyLadder.lean), [Stepanov](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism.lean), [Krein–Langer](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/HyperbolicPairsAndTheIndexFormula.lean).

The shared approximation mechanism is [all-lag bound](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/EveryTranslationHasAnAllLevelGammaTailBound.lean), [complete finite Euler families](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/FiniteEulerFactorsHaveAllLevelGeneratorApproximation.lean) and [all-prime higher powers](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/AllHigherPrimePowersHaveAllLevelGeneratorApproximation.lean) [K]. They use the same projection and original Gamma reserve. The [coefficient threshold](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/CriticalEulerCoefficientMassStartsAtCubes.lean) [K] shows why the first-prime and square layers need a different payment mechanism. AID's one-level compensated square estimate is not the all-level source comparison. The common missing obligations are signed transfer with both poles and the full-form sign on the retained orbits, not higher-power coefficient summation.

### E. The finite-support stratum is Krein–Langer finiteness at the Lindelöf level (E + T)

Each face below is equivalent to finite off-line support, and finite support implies that the zeros approach the line, hence LH and \(\Theta<1\) [L].

| Face | Routes | Statement |
|---|---|---|
| Canonical critical energy | HF, SRT, ACS | \(\mathcal E_{\rm crit}<\infty\); bounded work; \(\Delta\mathcal W\to0\) |
| Complete-form index | HF, ACS, AIP | Uniformly bounded complete-cell negative index; last layer \(k=1\) of the finite-index chain |
| Two-prime tower index | ACS, HKT | Bounded index on the towers of two primes with incommensurable logarithms (W05) |
| Subtracted prime lag | WL | Lag minus finitely many exponentials bounded on one side |
| Xi cosine-shift defects | supporting | Uniformly bounded defects |
| Heat flow | WD, LA | Nonreal counts of \(H_t\) bounded as \(t\downarrow0\); the high part is the LH-level "zeros approach the line", the rest is the near-axis count [S] |

In Krein–Langer language every face says the same thing: the Weil kernel is positive-definite modulo finitely many exponential characters. A positive part never pays a hyperbolic pair, so no positive majorant can produce finiteness. An index ceiling must come from structure (inference from [S]). This is a T-bridge between U1 (lag), U2 (index, work) and the heat routes at the intermediate stratum.

[Lindelöf](../../../formal/GaloisForLFunctions/RHTower/LindelofCosineFiniteDefectDepth.lean), [index exit](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheIndexExit.lean), [subtracted lag](../../../formal/GaloisForLFunctions/RHTower/FiniteOffLineConverse.lean), [heat count](../../../formal/GaloisForLFunctions/RHTower/DeBruijnNonrealCountRightLimit.lean), [high collisions](../../../formal/GaloisForLFunctions/RHTower/DeBruijnHighCollisionsReadTheDepth.lean), [canonical energy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean).

### F. Width, rate, strip and work currencies (E + T)

Fixed-strip conditions \(\Theta\le\frac12+c\) have exact one-sided readings in escaped Möbius rates, all-test Hecke-defect caps, theta-prefix growth, \(\operatorname{Re}\xi'/\xi\ge0\) on half-planes, Vaughan power savings, the Möbius-divisor Abel moment and its quotient head at any cutoff, Suzuki finite-contact residuals, and terminal ceilings. Work and depth are stratified:
\[
\mathcal E_{\rm crit}\le Q_*\iff\mathrm{RH}\ \Longrightarrow\ \mathcal E_{\rm crit}<\infty\iff\text{finite support}\ \Longrightarrow\ \text{zeros approach the line}\ \Longrightarrow\ \text{LH}\wedge\Theta<1 .
\]
The thresholds \(2\), \(39/50\) and \(Q_*=1294047/2000\) belong to different normalizations. Density envelopes never cross into this ladder: they count and never exclude [L]. [Abscissa laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean), [Vaughan strips](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean), [terminal ceiling](../../../formal/GaloisForLFunctions/RenormalizedBiarithmeticGeometry/TheTerminalCeilingAndTheOneScaleBoundAreZeroFreeStrips.lean), [density no-go](../../../formal/GaloisForLFunctions/RHTower/DensityEnvelopeNoGo.lean).

### G. Counting faces (S)

These results locate zeros by counting rather than by positivity:

- over \(\mathbb F_q\), trickle-down on every Frobenius ladder is equivalent to the one-sided square-root count, proved for hyperelliptic curves by Stepanov;
- over \(\mathbb Z\), the one-sided \(\psi\) count \(\psi(x)-x\le C\sqrt x\log^2x\) is equivalent to RH (WL);
- the Alpöge–Furman inertia method counts critical zeros through Sylvester signatures, with exchange rate \(2-\phi(\lambda)\) beyond bandwidth one;
- canonical energy pays each off-line quartet a quantum (AID).

They share one structure: a count at square-root precision, or a signature count, replaces a sign. Only over \(\mathbb F_q\) is the count produced. Over \(\mathbb Z\) the census needs a two-sided coalescent prime-pair estimate, which is the counting form of the parity requirement (K).

[Count](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTrickleDownInequalityIsTheSquareRootCount.lean), [hyperelliptic RH](../../../formal/GaloisForLFunctions/RHTower/HyperellipticRiemannHypothesis.lean), [census](../../../formal/GaloisForLFunctions/RHTower/Zeta23SimpleCriticalDensity.lean), [exchange rate](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/NarrowStripClosePairEnergyAndExchangeRate.lean).

### H. Möbius admission, Haar approximation and chronological residuals (E + T)

MC, PM and CTF share actual Möbius arithmetic, and BVI supplies readout, pronic and rate identities. CTF's residual is \((1-\Lambda\text{-readout})^2\) plus centered energy; PM's criterion is positive gauge mass for every escape state. The common unpaid input is complete signed energy at small damping. [Visibility criterion](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean).

### I. Heat, Jensen, Ward, moment and seam formulations (E + T)

LA and WD share finite-head/heat coefficient geometry; TH and HCF expose moment/grid signs; PA exposes all-order passivity. HJ's reflection residual equals SEC's seam charge, and all-divisor vanishing matches HCF's two-grid sign. The heat flow links WD/LA to the finite-support stratum (E): its high collisions read the depth of the zeros and its near-axis collisions are its own content. The local cofactor \(\xi=P\cdot g\) and Gaussian averaging supply the comparison tools.

### J. Adjunction, prime modes and gauge finite parts (T)

RAPT links finite-prime adjunction to the actual prime matrix:

- the bounded spectrum equals the adjunction spectrum, with converging eigenlines [S];
- arithmetic modes have spacing-scale Weil energies \(\log(K_m/K)\), with the pole at the Robin–Euler ratio and the first excitation at four times it [S];
- the bounded complete spectrum equals the arithmetic spectrum [S], giving full separated plateau positivity at each fixed width [S];
- the \(\chi\)-twisted poles read \(2\operatorname{Re}(-L'/L(1,\chi))\), the object that governs MC/ACG character gauges.

The link to fixed separated full-matrix positivity is proved in source [S]. Q1 asks for the further complete-form transfer through touching and overlap. [Mode energies](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheWeilEnergiesOfTheArithmeticModes.lean), [complete spectral counts](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum.lean).

### K. Parity and precision are one obstruction in three coordinates (S)

| Coordinate | Where it appears | Statement |
|---|---|---|
| Weil positivity (U2) | Selection theorem | Twin-blind inputs cannot reach RH-complete families [L]. |
| Tower positivity (U1 ∩ U2) | Precision rigidity | \(n^{-\eta}\)-perturbed weights cannot both be positive [S]. |
| Census (counting) | Trans-threshold exchange rate | Coalescent prime pairs enter through a signed kernel; one-sided sieves give nothing [L], two-sided asymptotics are parity problems (inference). |

The walls of U1, U2 and the census coincide here. A producer for any one of them must be parity-breaking and square-root-precise. Analytic number theory has no input with both properties; finite-field geometry has several.

### L. Prime-free existence and the blind cone (E)

RH holds iff for every aperture some real weights, of any sign and growth, make the full Weil functional of \(\zeta\)'s archimedean datum nonnegative up to that aperture [L]. The primes do not occur: only the archimedean factor, the pole and the positions \(\log n\). Full-cone uniqueness forces the weight to be \(\Lambda\). By convex duality the obstruction is a blind test, which is EWU's attained blind minimum. EWU and the existence form are therefore one problem. Its certificate is \(\Lambda\) itself, so verifying it is RH. [Existence](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistenceDecidesRH.lean), [blind minima](../../../formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean).

## Complete live-route crosswalk

"Selective input" names where a \(\Lambda\)-specific property enters, or must enter, the route. "Stratum" gives the strongest intermediate the route exposes below its RH endpoint.

| Route | Core problem / cluster | Distinct producer obligation | Selective input | Stratum below RH |
|---|---|---|---|---|
| **WL** | U1; prime-error energy | Adverse cross-work | Main-term cancellation \(e^h-\psi(e^h)\) | Subtracted lag [FS] |
| **FU** | U1; Abel moment | Entire scheduled history | Signed prime channels | — |
| **RP** | U1; history floor | Linear floor against an unconditional linear escape | Signed hyperbola/LCM identities | — (knife edge at linear scale) |
| **MC** | U1; Möbius cancellation | Moving-scale \(\mu\) at every strict half-power | Actual \(\mu\) | Any power saving [≥QRH] |
| **LI** | U1 + D; prime–Gamma floor, Cayley ladder | Literal primitive; ladder sign | Signed clock | — |
| **PM** | U1; escape visibility | Positive gauge mass for every escape state | Actual Möbius cofactors | Exterior tightness [open] |
| **JAS** | U1; prime budget | Logarithmic to half-power budget | Prime-product sign | Quasi-RH plus dressed PSD at \(1\) |
| **CTF** | U1; approximation residual | Readout and centered energy together | \(-\mu_N\) readout alignment | — |
| **PBM** | U1; regularized series | Cancellation to \(\sigma>1/2\) | Actual coefficients | Fixed abscissa \(<1\) [≥QRH] |
| **RB** | U1; extremal remainder | Saturated extremizers | Divisor arithmetic | — |
| **RW** | U2; ground energy | Cumulative aperture relaxation | Margin on low/polar modes (B) | — |
| **TT** | U2; odd/covariance | Nonlocal reflected-prime correlation | Signed reflected primes | — |
| **HF** | U2 + U1 + U3 | Complete residual sign or work ceiling | Margin (B); main-term cancellation across levels (A, D) | Finite index, \(\mathcal E_{\rm crit}<\infty\) [FS]; touching/overlap transfer [open] |
| **CHMD** | U2; wave/Doob | Residual sign modulo the Weil radical | Primitive defect | — |
| **SZ** | U2; first variation | Sign on factorial/grid tent patterns | Must enter low modes | — |
| **EWU** | U2 + L; even blind minimum | All-aperture low/mixed payment | Weight rigidity | — |
| **OWU** | U2; odd weight | All-aperture odd sign | Radius-\(23/40\) witnesses (finite aperture) | Conductor/forcing [open] |
| **SRT** | U2 + U1 + D | All-generator tower sign or late-lag bound | Margin (B) | Touching/overlap transfer [open] |
| **ACT** | U2; one-shift | One shift paying every profile | Exterior primes | — |
| **AIP** | U2; allocation | Coarse/cross-level allocation | Margin (B); Chebyshev cross-level work | Separated step [open] |
| **ACS** | U2 + U3 + D | RI/height/chirality or complete index zero | Margin (B); one-prime towers | Finite index [FS] |
| **PA** | U2 (moment) | All-order/all-shift sign | Prime–archimedean trace | — |
| **LA** | U2 (heat) | All-height/all-degree heads | Xi coefficients | Uniform heat count [FS] |
| **TH** | U2 (moment) | Signed vectors at common time | Theta moments | — |
| **WD** | U2 (heat) | Cap extinction | Actual divisor | Uniform nonreal count [FS]; uniform high count [LH] |
| **HCF** | U2 (heat) + D | Both grids, all degrees | Two literal prime grids | — |
| **TG** | U3; trace cap | Positive residual and integer trace below one | Euler/Gaussian source | — |
| **RN** | U3; renewal | Directed boundary work | Theta renewal | — |
| **XN** | U3; Newton discs | Covering with paid curvature | Xi jets | — |
| **BAG** | U3; recurrence | Return at every right-strip point | Euler-product universality | — |
| **GTA** | U3; transverse decay | Rank-uniform decay | Theta Schur charge | — |

**Strongest shared programmes.**

- The U2 cluster (RW, HF, ACS, AIP, OWU, SRT, CHMD, SZ, EWU, ACT) shares a measured margin and fixed separated plateau positivity [S]; the open transfer concerns touching, overlap and source exhaustion (Q1).
- The finite-support stratum (HF, ACS, AIP, WL, WD, LA) is one Krein–Langer problem at the Lindelöf level.
- U1 supplies the prime-error sequences that are the cross-level couplings of U2, and the tower view (D) shows their positivity is RH.
- The census shares the parity coordinate with U1 and U2 (K).

## Candidate crosswalk

The 17 standalone candidates and PW-B are U3 producers whose landing is unproved. Each landing must fail for the full battery: Liouville, \(\omega_p\) with the maximal margin, and \(\Lambda+\varepsilon n^{-\eta}\).

| Candidate | Intended landing | What prevents merger into a live producer |
|---|---|---|
| **APF** | U3→U2; cycle-trace orientation | Fourier recovery is not divisor exhaustion with trace vanishing. |
| **BSH** | U3→U2; mate curvature | Calibrated vanishing equals criticality; forcing missing. |
| **CDC** | U3→U2; descending potential | Source-defined descent unconstructed. |
| **DR** | U3→zero-free endpoint | Cusp roots do not reach the strict-right domain. |
| **EGC** | U3→U1/U2; outer contour | Inner cancellation does not orient the outer contour. |
| **EWJ** | U3→U1; depth admission | Finite jets do not give norm exhaustion. |
| **FEL** | U3→U1; contrast balance | Entropy identities are nonselective. |
| **HJ** | U3→U2; SEC/HCF residual | Pre-divisor residual vanishing unpaid. |
| **IRK** | U3→U2; integral orientation | Completed relation is not the charged lift. |
| **MSC** | U3→U2; Sonin sign | Admission and divisor transport give no sign. |
| **PCS** | U3→U1; chronological energy | The co-shift defect survives. |
| **PTR** | U3→real-rooted Xi | No prime-faithful lossless port without zeros. |
| **RFHM** | U3→U1/U2; grade orientation | Support entropy forgets the grade. |
| **SC** | U3→U2; cross-fibre index | Wall value unselected; a finite cross-fibre index would land in the [FS] stratum (E). |
| **SEC** | U3→U2; seam sign | Asymptotic seam smallness is nonselective. |
| **W1C** | U3→real-rooted Xi | No arithmetic ferromagnetic limit; a Bohr-torus Lee–Yang lift is the natural landing. |
| **WBF** | U3→U2; certificates | No arithmetic coupling or uniform-depth landing. |
| **PW-B** | U3→U1; PM complete energy | Zero-indexed action; extinction chain unproved. |

## Unifications that are not valid

| Tempting identification | Correct distinction |
|---|---|
| Every RH receiver is one programme | Endpoint equivalence is E; producers differ. |
| \(W\), the collided form \(D\) and the prime-only form are interchangeable | \(D\) is positive but its invariance is the problem; prime-only forms omit Gamma and poles. |
| Twin-blind positive families can be completed to full positivity | Impossible on RH-complete families by the selection theorem. |
| The maximal margin \(2\log2\) selects \(\zeta\) among multiplicative twins | Single-prime flips \(p\ge11\) attain it and fail complete positivity [S]. |
| Short-interval prime statistics can decide tower or Weil positivity | Precision rigidity: \(\Lambda+\varepsilon n^{-\eta}\) shares them and fails [S]. |
| Narrow generator support shortens the tower problem | Tower positivity is RH at every generator size [S]. |
| Finite-part identification of \(\zeta\) is a positivity input | \(\zeta\) maximizes the matched finite part, which makes it the hardest member. |
| Finite-generator approximation proves the complete-form sign | The proved transfer covers L², fixed finite Euler families and all-prime higher powers. Complete-form transfer remains open; finite generator count retains infinitely many level directions. |
| Cross-level prime couplings are summable under a strong enough input | Under RH they are almost periodic and bounded, not decaying (inference). |
| Hyperbolicity of the atomic Gram is arithmetic | It holds for every completely multiplicative sign twin; only the Metzler sign is selective. |
| A positive correction can repair a finite index | A positive part never pays a hyperbolic pair [S]. |
| Finite negative index means RH | It means finite off-line support. |
| Finite off-line support is a sub-Lindelöf target | It implies that the zeros approach the line, hence LH and \(\Theta<1\) [L]. |
| The \(\alpha=1\) atomic receiver is a computation away | It needs compactly supported quasi-analytic profiles, which do not exist (inference). |
| The \(2/3\) census is a route to RH | Proportions do not exclude individual zeros. |
| Simple-zero theorems raise the critical-line census | Value moments cannot separate equal-valued reflected pairs from critical zeros, and the census extremal consists of simple zeros. |
| One-sided sieve bounds control pair correlation beyond \(\alpha=1\) | The trans-threshold kernel is signed; the Poisson term cancels only against the exact main term. |
| The shallow Cauchy bound \(hE_h=O(N)\) gives an on-line proportion | Its majorant counts all zeros; the constant is the open part. |
| Better density exponents yield a zero-free strip | A density envelope never drops below \(1\); a vanishing mechanism is needed. |
| Tensor amplification of \(\zeta\) is independent of WL | The tensor square of the prime error is WL's mean square (inference). |
| Regular integer counts force RH | Over-regular Beurling systems have off-line zeros; the functional equation excludes them. |
| \(A_Q\) is the Xi operator | Adjunction energies are prime-matrix eigenvalues, not Xi zeros. |
| Curves over finite fields can donate Weil positivity | The archimedean continuum cannot arise from finite places. |
| Simple zeros, Chowla and pair correlation are weaker than RH | Logical relations differ; some budgets force RH plus extra assertions. |

## How to organize research around the unification

1. **One selective-positivity programme** for the U2 cluster: full-form transfer through touching and overlap (Q1), tested against Liouville and the \(\omega_p\) flips.
2. **One parity programme** joining the census (two-sided coalescent pairs, Q2), the precision rigidity of towers and the selection theorem. Every proposed input is run through the full battery.
3. **One vanishing-mechanism programme** for fixed strips: the Chen–Gupta–Li detector threshold (Q3). Density work feeds it but cannot replace it.
4. **One Krein–Langer programme** at the Lindelöf level joining HF/ACS/AIP (first-layer compactness), WL (subtracted lag), WD/LA (heat counts) and HKT (index structure). Every result is checked against its implication LH \(\wedge\) \(\Theta<1\).
5. **One counting programme** over \(\mathbb Z\): a Stepanov-type auxiliary construction without a lattice spectrum.
6. **Independent-construction experiments** for U3, each tested against the battery and the parity and precision criteria.

No route is promoted because its final condition was renamed, and no candidate is retired because another route reaches the same endpoint.
