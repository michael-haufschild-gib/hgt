# Walls ledger

Status: 28 October 2026, corpus commit `389e3f1d10`. **Three core problem families remain: the selective critical sign (Wall 1), transfer and exhaustion (Wall 3), and independent realization or forcing (Wall 14).**

This edition records four structural changes:

- Selectivity moved from an inference about proof hypotheses to a Lean theorem, and its margin is measured: \(2\log2\) against \(0\).
- The prime-form gap closed.
- The atomic receiver reached \((\log\log N)^{1+\varepsilon}\).
- The complete-source picture split cleanly: Gamma, pole and touching couplings are paid; every prime layer except the first has uniform finite index; and the cross-level prime coupling is an almost-periodic Toeplitz sequence that no summable-cost argument can pay (inference).

[Route report](route-obstacles.md) · [summary and next questions](obstacles-summary.md) · [route unification](route-unification-ledger.md) · [scoped no-go catalogue](../rh-killed-routes.md). Evidence: corpus searches and Lean statements; no builds. **[S]** = working source as in the frontier map; **(inference)** = conclusion of this review, not a Lean theorem. [Working log](../../../logs/review-2810-v2-research-2026-10-28.md).

## The three families

| Family | Question | What would cross it |
|---|---|---|
| **Wall 1 — Selective critical sign** | What bounds the actual signed prime/Möbius source, the complete Weil form or a computed defect at the critical scale, using a property \(\Lambda\) has and its twins lack? | A new inequality meeting an existing receiver, false for the Liouville twin, with all tails and quantifiers intact. |
| **Wall 3 — Transfer and exhaustion** | Does an estimate survive the needed norm, source realization, shared reserve and simultaneous limit? | A source-faithful comparison in the right topology with the right uniformity. |
| **Wall 14 — Realization and forcing** | Which independently built structure forces the inequality? | A faithful object with a proved selective law, not a calibration or an assumed structure field. |

The families interlock:

- The selective margin of Wall 1 is proved only at narrow widths; carrying it to overlap is a Wall 3 problem.
- The cross-level prime couplings of Wall 3 are Wall 1 prime-error sequences.
- Over \(\mathbb F_q\) the Wall 14 forcing is a count; over \(\mathbb Z\) the corresponding count is a Wall 1 estimate.

The organizing identities:
\[
\operatorname{Re}W(f,f)=D(f,f)-\mathfrak d(f),\qquad
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g)\quad(\operatorname{supp}f<b<\operatorname{supp}g).
\]
Here \(W\) is the full Weil form, \(D\) the positive collided form and \(\mathfrak d\) the off-line defect. The diagonal carries the collided mass; the off-diagonal carries the prime error.

**Strata.** Inputs are classified by strength, from weakest to strongest:

1. **[open]** intermediate.
2. **[≥QRH]** implies a fixed zero-free strip \(\Theta<1\). Finite off-line support belongs here.
3. **[RH]** equivalent to RH.
4. **[RH+]** stronger than RH.

## Changes in this edition

| Face | Change | Current content |
|---|---|---|
| **1.18 Gauge selection** | **Margin closed; full sign open** | \(\zeta\)'s pole-hyperplane gap is exactly \(2\log2\) (sharp Poincaré constant of the multiplicative walk), Liouville's exactly \(0\), every sign gauge \(\le2\log2\). \(S_N^2=o(\log N)\) kills the gap; \(S_N/H_N\to1\) keeps it, so finite flips keep the maximal margin. |
| **1.24 Selectivity** | **Inference → theorem** | Atomic positivity of a bounded weight at a root iff RH and \(\lambda=\Lambda\). Twin-blind positivity on RH-complete atomic families is impossible. |
| **1.25 Parity form of selectivity** | **New (inference)** | Majorant information \(|\lambda|\le\Lambda\) is consistent with the Liouville twin, as sieve information is consistent with the parity-twisted sequence. Every crossing of Wall 1 needs a parity-breaking input. |
| **1.26 Finite support stratum** | **New, exact** | Finite off-line support forces \(\Theta<1\). Its receivers (critical energy, subtracted lag, cosine defects, heat nonreal counts, finite complete-form index) are all [≥QRH]. |
| **1.27 Critical-line census** | **New face** | Imported inertia theorem: \(\ge2/3\), \(\ge HD(1)\); IGP \(+10^{-8}\); off-line copies \(\le1-HD(1)\). The pair-correlation main term is capped by \(|\alpha|\le1\). |
| **1.28 Value-moment mimicry** | **New, closed [Lean]** | Mollified moments cannot separate equal-valued reflected pairs from critical zeros; the mollifier route to beyond \(2/3\) is falsified. |
| **1.0 Fixed strip** | Intake status | Quotient-head, Suzuki finite-contact and Möbius-divisor exponent laws added. The CGL \(7/8\) intake has no capstone. |
| **3.26 Complete overlap transfer** | **Extended** | RH iff eventual atomic positivity at widths \((\log\log N)^\alpha/N\), \(\alpha>1\). At every width: Markov gap on \(p=0\) plus one affine scalar on \(p=1\) [S]. |
| **3.37 Quasi-analytic boundary** | **New boundary (inference)** | \(\alpha=1\) would need compactly supported profiles of quasi-analytic class; Denjoy–Carleman excludes them. |
| **14.32 Narrow trickle-down** | **Extended** | \(K_\star\approx0.108\) spacing for plateau profiles, a quarter of the Robin–Euler threshold; arbitrary per-atom shapes [S]. With absolute pole costs the method stays below about half the threshold. |
| **3.28 / 14.31 Prime exhaustion** | **Gap closed; bulk open** | Sharp gap \(2\log2\) proved. Top spectrum exhausted by integers with \(\log m+d(m)<T\); counts equal adjunction counts; eigenlines converge [S]. Mode energies \(\log(K_m/K)\) for \(K<1/4\) [S]. |
| **3.31 Dyadic self-similarity** | **Reassessed** | Exact structure stands. Positivity on generator orbits is a Toeplitz-symbol statement about the zero measure on the circle (inference), so the reduction does not lower difficulty. |
| **3.32 Cross-level coupling** | **Split: three paid, one structural** | Pole: rank two, removed by \(\sum c_j2^{-j/2}=0\). Gamma: \(\pi4^{-(d-1)}\). Touching: uniform. Chebyshev part: almost periodic under RH, exponential otherwise, never summable (inference). |
| **3.35 Uniform finite-index chain** | **New; closed except \(k=1\)** | Gamma minus the all-prime \(k\ge3\) block, the whole prime-two source, or any fixed finite prime set has horizon-uniform finite index [S]. Open: the first prime layer over all primes, where \(\sum_p\log p/\sqrt p\) diverges [≥QRH]. |
| **3.36 Orbit approximation versus compactness** | **New boundary** | Finitely many full generator orbits approximate cell sources in \(L^2\); one Haar orbit is noncompact [S]. |
| **14.37 Local-to-global by counting** | **New, closed over \(\mathbb F_q\)** | Trickle-down on every Frobenius ladder iff one-sided square-root count; local Lorentzian input is local RH; hyperelliptic RH by counting. |
| **14.38 Blind hyperbolicity, selective sign** | **New** | The atomic Gram is hyperbolic for every completely multiplicative sign twin; the Metzler sign holds for \(\zeta\) and fails in every gauge for any prime-flipping twin. |
| **14.39 Heat-flow reality horizon** | **New** | Zeros of \(H_t\) beyond \(2\pi e^{(27/40+\varepsilon)/t}\) are real and simple, \(0<t\le1/8\). A uniform-in-\(t\) bounded count would give finite support [≥QRH]. |
| **14.40 Over-regular Beurling systems** | **New boundary** | Positive primes with integer-count error \(O(x^{-p})\) can have off-line zeros; the Riemann functional equation forbids such decaying count errors. |

"Closed" means the stated question is answered, never that a route is closed. "Open" means an input is missing. "Boundary" means a proved limitation with a positive survivor.

## Wall 1 — Selective critical sign

| Face | Status | Content and remaining obligation |
|---|---|---|
| **1.0 Fixed-strip first rung** | Open [≥QRH]; external claim | All strip dictionaries read \(\Theta\): escaped, Hecke-defect, theta-prefix, Vaughan, quotient-head at any cutoff, Suzuki finite contact. No local fixed power saving. CGL \(7/8\) claimed; intake partial. |
| **1.1 Critical signed cancellation** | Open [RH] | Lag, Abel, history, regularized-series and one-sided \(\psi\) receivers need the actual signed bound. |
| **1.2 Axis orientation** | Open [RH] | Ward caps, winding and Newton margins detect; extinction or all-disc orientation missing. |
| **1.3 Complete Weil positivity** | Open [RH] | High details, narrow sections and complete-cell realization known; index zero on the complete source not. |
| **1.4 Arithmetic cone membership** | Open [RH] | Identification and rigidity say what the source is, not that it is positive. |
| **1.5 Contrast equality** | Open [RH] | BSY/Jensen/Li identities keep a defect whose vanishing needs arithmetic. |
| **1.6 Required uniformity** | Open | Fixed rank/order/height and orthant positivity leave the simultaneous receiver unproved. |
| **1.7 Amplification bookkeeping** | Closed diagnostic | Amplification transfers a supplied cap; no rate gain. |
| **1.8 Critical pronic energy** | Open [RH] | Complete signed energy at small damping. |
| **1.9 Signed continuation** | Open | Integrated signed loss needs horizon-uniform control. |
| **1.10 Absolute compensation** | Open | Relative error \(\to0\) coexists with unbounded raw energy. |
| **1.11 Norm-specific rates** | Open in stated regimes | Norms are not interchangeable. |
| **1.12 Interior anti-alignment** | Open | Exterior field laws do not enter the strip. |
| **1.13 Aperture shell flux** | Open [RH] | Cumulative relaxation must not exceed the initial reserve. |
| **1.14 Actual divisor heat sign** | Open [RH] | Half-line Laguerre, Turán and positive tails leave all-height/all-degree signs. |
| **1.15 Depth homogeneity** | Boundary | Amplification pays at the scale it gains. |
| **1.16 Payment for actual zeros** | Open | Defect, field, inertia and index payments are lower laws; no source upper bound. |
| **1.17 Loss-rate improvement** | Open | A sublinear tensor loss must be proved. |
| **1.18 Arithmetic gauge selection** | Margin closed; sign open | Exact margins \(2\log2\)/\(0\); harmonic-correlation criteria; character finite parts \(2\operatorname{Re}(-L'/L(1,\chi))\); \(\zeta\) is the maximizer of the matched finite part, hence the hardest case on step profiles. Transfer to overlapping tests is missing (Q1). |
| **1.19 Budget strength** | Boundary | Some budgets are RH-equivalent; Abel/Mertens saturation also forces simple zeros [RH+]. |
| **1.20 Arithmetic-point completion** | Open | Periodic and finite-field counts keep their periods. |
| **1.21 Source reserve / work ceiling** | Open [RH] | Cofinal work \(\le2\) is RH-equivalent; no upper estimate. |
| **1.22 Finite versus zero exceptions** | Exact boundary | \(\mathcal E_{\rm crit}<\infty\) iff finite support; \(\mathcal E_{\rm crit}\le Q_*=1294047/2000\) iff RH; index \(k\) costs \(\ge\max\{(Q_*/2)k,50k^2-3k/2\}\). |
| **1.23 Ordered Chebyshev identity** | Exact identity; payment open | Separated couplings are the signed prime error against \(q'_{f,g}\). |
| **1.24 Selectivity** | **Theorem** | Selection at every root; twin-blind positivity impossible on RH-complete atomic families; Haar floor twin-blind. |
| **1.25 Parity form** | Criterion (inference) | Selectivity is the parity barrier in Weil-form language; required: a parity-breaking input. |
| **1.26 Finite support stratum** | Exact [≥QRH] | Finite support implies \(\Theta<1\) and excludes infinitely many near-line zeros, which density methods cannot do. |
| **1.27 Critical-line census** | Open beyond \(HD(1)\) | Inertia method with pair correlation on \(|\alpha|\le1\). Value moments of any weight cannot certify criticality (1.28). Open: a displacement-sensitive source estimate at depth \(1/\log T\) (Q3). |
| **1.28 Value-moment mimicry** | **Closed [Lean]** | An equal-valued reflected pair has every holomorphic value moment of two critical zeros. Survivor: \(|S_1|^2\le(\#\text{crit}+2\#\text{pairs})(\operatorname{Re}S_2+D)\). The Alpöge–Furman extremal consists of simple zeros, so no simplicity input moves the census. |

Evidence: [lag](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean), [abscissa laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean), [Vaughan strips](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean), [canonical energy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean), [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean), [selection](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/PositivityAtEveryRootSelectsTheVonMangoldtWeight.lean), [margin](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheSelectiveMarginIsTwoLogTwo.lean), [index exit](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheIndexExit.lean), [census](../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean), [mimicry](../../../formal/GaloisForLFunctions/RHTower/ValueMomentsCannotSeparateReflectedPairs.lean).

## Wall 3 — Transfer, norms and exhaustion

| Face | Status | Content and remaining obligation |
|---|---|---|
| **3.1 Information retained** | Boundary | Magnitudes, complete-period covariances and collided counts can lose orientation. |
| **3.2 Aperture escape** | Open | Finite windows admit hidden configurations. |
| **3.3 Norms and completions** | Scoped graph control closed | No global norm equivalence. |
| **3.4 Shared resources** | Open | A reserve cannot be spent on each block separately. |
| **3.5 Endpoint logarithms** | Open | Pole cancellation leaves Dini/log remainders. |
| **3.6 Moving horizons** | Open | No free below-half-damping interchange. |
| **3.7 Damping topology** | Open | Half-damped boundedness gives no sub-half trace-ideal control. |
| **3.8 Multiplicity and index** | Clarified boundary | Distinct index, copied energy and packet multiplicity differ. |
| **3.9 Observation cost** | Open | Finite-window coercivity has explicit horizon cost. |
| **3.10 Invertible filters** | Boundary | Repair needs non-unit arithmetic content. |
| **3.11 Coupled quantifiers** | Open | Degree, rank, height, time, damping and support limits do not commute. |
| **3.12 Residual reconstruction** | Open | Coordinate maps need not have bounded inverses. |
| **3.13 Joint orientation** | Open | One-channel signs do not orient the joint form. |
| **3.14 Averages to selected zeros** | Open | Proportions, Schur slack and large-value counts allow exceptions. |
| **3.15 Escape states** | Open [RH] | RH iff every escape state has positive gauge mass; record-minimum limits still allow zero mass. |
| **3.16 Prime to spectral sign** | Open | Prime-side margins must reach the full form with poles intact. |
| **3.17 Archimedean-line horizon** | Open | Near-incidence estimates have bandwidth limits. |
| **3.18 Localization** | Boundary | Positivity constrains a fibre only where the carrier localizes. |
| **3.19 Conductor versus forcing** | Open | No common aperture range for twisted positivity and companion forcing. |
| **3.20 Collided-form norm** | Closed locally | Fixed-aperture collided form \(\asymp\) log-weighted Fourier norm. |
| **3.21 Lattice to continuum** | Open | Lattice payment must keep the continuum remainder. |
| **3.22 Computed detection** | Closed diagnostic | Detection is not exclusion. |
| **3.23 Local to global Hodge** | Open | Hyperbolicity is not additive; dispersion must be paid. |
| **3.24 Horizon regulator** | Closed construction | Counterterms and finite parts explicit. |
| **3.25 Narrow spacing payment** | Closed | Archimedean self-energy and prime defect pay prime and pole terms at fixed fractions (\(c_\star\), \(K_\star\)). |
| **3.26 Complete overlap transfer** | Transfer closed to \((\log\log N)^{1+\varepsilon}\); sign open | Gap/scalar reduction at every width [S]. |
| **3.27 Complete residual** | Exact boundary | Bounded projection; residual radical = Weil radical; complete cells capture every finite index. |
| **3.28 All-prime/class exhaustion** | Gap closed; bulk open | Fixed packets and bounded spectrum realized [S]; growing conductors, complement and Gamma/pole coupling open. |
| **3.29 Valuation versus residue classes** | Exact boundary | Residue counterterm rank one; character finite parts \(-L'/L(1,\chi)\). |
| **3.30 Balanced Haar completion** | Details closed | Gamma pays details and a mean graph; twin-blind floor above index \(A\). |
| **3.31 Dyadic self-similarity** | Exact structure; reduction value reassessed | Complete cells are \(T_{\log2}\)-orbits of finitely many generators plus paid details. Orbit positivity is Toeplitz positivity of the zero measure on the circle (inference). |
| **3.32 Cross-level coupling** | Three parts closed; one structural | Pole hyperbolic and removable; Gamma \(\pi4^{-(d-1)}\); touching uniform. Chebyshev part almost periodic, never a summable cost (inference). |
| **3.33 Renormalization topology** | Boundary | No exponential amplitude renormalization gives uniform graph control. |
| **3.34 Gamma boundary rigidity** | Closed | Norm \(\pi/2\), exact square reserve, no maximizer, no uniform gap [S]. |
| **3.35 Uniform finite-index chain** | Closed except \(k=1\) | See changes table. The \(k=1\) layer is [≥QRH]. |
| **3.36 Orbit approximation versus compactness** | Boundary | \(L^2\) orbit approximation is not compactness and supplies no Weil sign [S]. |
| **3.37 Quasi-analytic boundary** | Boundary (inference) | \(\alpha=1\) is out of reach of compact-profile synthesis. |

Evidence: [Denjoy–Carleman](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDenjoyCarlemanProfiles.lean), [gap and scalar](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar.lean), [multiresolution](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheCompleteSourceIsADyadicMultiresolution.lean), [pole coupling](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/ThePoleCouplesTheLevelsHyperbolically.lean), [separated levels](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/SeparatedLevelsCoupleThroughTheChebyshevError.lean), [k≥3 index](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/AllHigherPrimePowerMixedFormsHaveUniformFiniteIndex.lean), [prime two](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheGammaMeanGraphPaysThePrimeTwoMixedBlock.lean), [noncompact orbit](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/CompactDetailsDoNotMakeTranslationOrbitsCompact.lean), [spectral counts](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum.lean), [escape visibility](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean).

## Wall 14 — Realization and forcing

| Face | Status | Content and remaining obligation |
|---|---|---|
| **14.1 Capacity and limits** | Open | A faithful limit must carry orientation. |
| **14.2 Algebra without orientation** | Boundary | Correspondence identities hold for impure data. |
| **14.3 Detector without producer** | Open | Calibrated vanishing laws are equivalent to criticality. |
| **14.4 Effectivity receiver** | Closed equivalence | Section/effectivity hypotheses are Hodge receivers. |
| **14.5 Pre-divisor weld** | Open | Prime and Gamma reservoirs need source-level compatibility. |
| **14.6 Section selectivity** | Open | Counts and positive sections do not give full-source RR/Hodge. |
| **14.7 Theta degree coupling** | Closed scoped law | Linear RR/count relation. |
| **14.8 Blind-carrier exhaustion** | Open | The maximal blind ideal is full only at RH. |
| **14.9 Positivity versus faithfulness** | Boundary | Strong invariant positivity may force RH plus simplicity. |
| **14.10 Invariant positive carriers** | Boundary | Off-line boosts force isotropy. |
| **14.11 Multiplicative forcing capacity** | Closed scoped boundary | Boundary forcing does not move interior zeros. |
| **14.12 Degree-one rigidity** | Closed scoped law | The simple-pole class is \(\mathbb R\cdot\zeta\); sign separate. |
| **14.13 Zero–pole budget** | Closed diagnostic | Inserted-zero bookkeeping is not \(\zeta\)'s budget. |
| **14.14 Amplification base** | Open | A fixed tensor loss can encode RH. |
| **14.15 Successor coupling** | Structure closed; sign open | Periodic successor holonomy is flat only at the Euler point. |
| **14.16 Correspondence ring** | Closed identity | Square identities hold without purity. |
| **14.17 Local representation type** | Closed diagnostic | No automatic conformal Frobenius. |
| **14.18 Arithmetic polarization** | Open | A form faithful, positive and equivariant at once. |
| **14.19 Zero contraction** | Closed scoped boundary | Contraction laws do not move nonreal quartets. |
| **14.20 Collision and conductor** | Closed obstruction | Finite carriers meet localization/conductor barriers. |
| **14.21 Collided polarization** | Open sign | \(D\) positive and computable; \(D=W\) needs zero defect. |
| **14.22 Central order** | Open forcing | Central-ceiling forcing missing. |
| **14.23 Polar-configuration criterion** | Closed receiver | Source sign unproved. |
| **14.24 Torsion renormalization** | Scoped bounds closed | Counterterm \(\varphi\log N+O(1)\); positive index \(\le N^{4/5+\varepsilon}\). |
| **14.25 Deformation** | Boundary | Deformation-stable properties need not select. |
| **14.26 Field and energy** | Open upper bound | Lower costs explicit; source ceiling missing. |
| **14.27 Coupled counterterm rank** | Closed scoped boundary | Partner-rank costs. |
| **14.28 Counterterm covariance** | Closed classification | Covariant diagonal finite parts are scalar. |
| **14.29 Arithmetic base across primes** | Construction boundary | Closure gives exactly nonnegative Lorentzian Hessians; Ramanujan local factors excluded; decaying isometric ladders carry no positive square. |
| **14.30 Zero moments** | Closed identification | Zero moments are Rosati-type pairings. |
| **14.31 Horizon finite part** | Local payment closed; gap closed | Raw threshold \(p\ge47\); valuation payment for every prime; sharp all-prime gap \(2\log2\). |
| **14.32 Actual trickle-down** | Narrow regime extended | \(K_\star\) up to a quarter of Robin–Euler; method cap about half; beyond Robin–Euler the open content is the gap on \(p=0\) plus one scalar. |
| **14.33 Conformal replacement** | Open beyond tested maps | Hecke dilation has factor one; power/successor maps are not conformal. |
| **14.34 Overlap frustration** | Obstruction | \(\rho<1\) Metzler; \(\rho>1\) frustrated; \(\rho=1\) open. |
| **14.35 Adjunction versus Xi** | Fidelity boundary | Adjunction energies are actual prime-matrix eigenvalues; not Xi zeros. |
| **14.36 Function-field approximation** | Boundary (inference) | Curve explicit-formula distributions reproduce the prime support, not the archimedean continuum. |
| **14.37 Local-to-global by counting** | Closed over \(\mathbb F_q\); open over \(\mathbb Z\) | Over \(\mathbb F_q\): TD iff square-root count, supplied by Stepanov. Over \(\mathbb Z\): sparse annihilators need a lattice spectrum; the analogous count is RH. |
| **14.38 Blind hyperbolicity, selective sign** | Exact boundary | Hodge index at proved scales carries no arithmetic; the Metzler sign does. |
| **14.39 Heat-flow reality horizon** | Scoped law; uniformity open | Horizon \(2\pi e^{(27/40+\varepsilon)/t}\); bounded nonreal counts as \(t\downarrow0\) iff finite support. |
| **14.40 Over-regular Beurling systems** | Boundary | Regular counts with positive primes do not force RH; the functional equation forbids decaying count errors. |

Evidence: [count](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTrickleDownInequalityIsTheSquareRootCount.lean), [local factor](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheLocalFactorTricklesDownByRamanujan.lean), [blind/selective](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/HyperbolicityIsBlindTheSignIsNot.lean), [quarter Robin–Euler](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheStabilityRegimeReachesAQuarterOfTheRobinEulerThreshold.lean), [Stepanov mechanism](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism.lean), [reality horizon](../../../formal/GaloisForLFunctions/RHTower/KiKimLeeInteriorLindelofHorizon.lean), [heat count](../../../formal/GaloisForLFunctions/RHTower/DeBruijnNonrealCountRightLimit.lean), [over-regular Beurling](../../../formal/GaloisForLFunctions/RHTower/BeurlingOverRegularIntegersOffLineZeros.lean), [count fluctuation](../../../formal/GaloisForLFunctions/RHTower/RiemannFunctionalEquationForcesCountFluctuation.lean), [torsion index](../../../formal/GaloisForLFunctions/ArithmeticIntersectionTheory/ThePositiveSquaresOfTheTorsionFormLiveBelowFourFifths.lean).

## Sharp obstructions and their positive survivors

| Excluded shortcut | Strongest survivor | Replacement question |
|---|---|---|
| Twin-blind positivity on RH-complete families | Selection theorem; exact margins \(2\log2\)/\(0\) | A parity-breaking input paying overlap (Q1). |
| Maximal margin as a unique selector | Finite flips keep \(2\log2\); \(S_N^2=o(\log N)\) kills it | Selectivity beyond the margin: Chebyshev main-term cancellation. |
| Pure Markov positivity beyond the spacing | Markov negative under overlap; RH iff pole-hyperplane Markov sign; gap/scalar reduction | The gap on \(p=0\) beyond Robin–Euler. |
| Absolute pole costs in narrow positivity | Quarter of Robin–Euler; method cap about half | A signed treatment of the pole term. |
| Summable cross-level costs on generator orbits | Gamma and touching costs summable; pole removable | Toeplitz-symbol positivity, which is RH-type (inference). |
| Finite-generator approximation as compactness | \(L^2\) approximation by orbits; compact fixed-level details | Signed control of infinite orbits. |
| Absolute payment of all prime layers | Uniform finite index for \(k\ge3\), prime two, finite \(P\) | First-layer relative compactness (Q2, [≥QRH]). |
| Same Metzler gauge through overlap | Narrow Hodge/TD; \(\rho\lessgtr1\) boundary | Signed/block methods. |
| Hyperbolicity as an arithmetic input | Blind for every sign twin; Metzler sign selective | Selective sign transfer. |
| \(\alpha=1\) or bounded-overlap receivers | \((\log\log N)^{1+\varepsilon}\) receiver; coverage bound | None needed; the boundary is quasi-analyticity. |
| Mollified value moments (CGG/BHB) as a criticality certificate | Mimicry; defect-repaired Cauchy–Schwarz counts simple zeros of either kind | A displacement-sensitive count at depth \(1/\log T\) (Q3). |
| Pair correlation beyond \(|\alpha|=1\), higher traces | \(HD(1)+10^{-8}\); \(k\lambda<2\) range | Same (Q3). |
| Regular counts as forcing | Over-regular Beurling systems with off-line zeros | Use the functional equation. |
| Stepanov over \(\mathbb Z\) by sparse annihilators | Exact lattice criterion; char-0 sparse root bound | A non-lattice auxiliary construction. |
| Function-field approximation as imported positivity | Curves reproduce exactly the prime support | An archimedean component of non-finite-field origin. |
| Detection or quantization as an upper bound | Canonical energy and thresholds | A virial-type upper estimate. |

## Consequences for priorities

- [Q1](obstacles-summary.md#q1) targets **1.18 / 1.24 / 3.26 / 14.32**: selective positivity past the Robin–Euler point.
- [Q2](obstacles-summary.md#q2) targets **3.35 / 1.26 / 1.22**: first-layer compactness and finite support.
- [Q3](obstacles-summary.md#q3) targets **1.27 / 1.28**: a displacement-sensitive source estimate beyond the census constant.

No route is declared dead by these priorities. Finite calculations, transfer instantiation and literature intake are listed as [just work](obstacles-summary.md#21-tasks-that-are-just-work).
