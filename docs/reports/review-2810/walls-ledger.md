# Walls ledger

Status: 28 October 2026, corpus commit `d47ab4b5d`. **Three core problem families remain: the selective critical sign, faithful transfer and exhaustion, and independent realization or forcing.** Several transfer walls closed or sharpened in this edition. In particular:

- the atomic RH receiver now holds at every polylog overlap;
- the narrow positive regime is located up to a constant;
- the complete source is a dyadic multiresolution of itself;
- the off-diagonal entries of the complete form are signed prime-error integrals.

Each closure exposes the same residual more precisely: a twin-selective inequality on the coarse and cross-level part of a complete source.

[Route report](route-obstacles.md) · [summary and next questions](obstacles-summary.md) · [route unification](route-unification-ledger.md) · [scoped no-go catalogue](../rh-killed-routes.md). Evidence: corpus searches and Lean statements; no builds. **[S]** = recent working source (committed on 28 October 2026, or unfinished); per-item status in the frontier map. [Working log](../../../logs/review-2810-refresh-2026-10-28.log).

## The three families

| Family | Question | What would cross it |
|---|---|---|
| **Wall 1 — Selective critical sign** | What bounds the actual signed prime/Möbius source, the complete Weil form or a computed defect at the critical scale, using a property \(\Lambda\) has and its twins lack? | A new arithmetic inequality meeting an existing receiver, false for the Liouville twin, with all tails and quantifiers intact. |
| **Wall 3 — Transfer and exhaustion** | Does an estimate survive the needed norm, source realization, shared reserve and simultaneous limit? | A source-faithful comparison in the right topology with the right uniformity. |
| **Wall 14 — Realization and forcing** | Which independently built structure forces the inequality? | A faithful object with a proved selective law, not a calibration or an assumed structure field. |

The families interlock. The complete source of Wall 3 now has an exact multiscale structure, and its cross entries are Wall 1 prime-error integrals. A finite-prime operator is a Wall 14 object whose all-prime comparison is a Wall 3 problem. They are not three independent conjectures.

The organizing identity stands:

\[
\operatorname{Re}W(f,f)=D(f,f)-\mathfrak d(f).
\]

Here \(W\) is the full Weil form, \(D\) the positive collided form and \(\mathfrak d\) the off-line defect. Its counterpart on ordered pairs is new:

\[
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,\Omega_{f,g}'(h)\,dh-\Gamma_{\rm tail}(f,g)\qquad(\operatorname{supp}f<b<\operatorname{supp}g).
\]

The diagonal carries the collided mass; the off-diagonal carries the prime error.

## Changes in this edition

| Face | Change | Current content |
|---|---|---|
| **3.26 Complete overlap transfer** | **Endpoint resolved** | RH iff eventual positivity on atomic families at overlap growth of any finite order. This covers widths \((\log N)^\alpha/N\) for every \(\alpha>0\) (smooth profiles), replacing \(\alpha>1/4\). The Markov form and the Liouville/scaling/quadratic twins are negative at every root. On the pole hyperplane, RH is Markov nonnegativity at every root [S]. |
| **14.32 Narrow trickle-down** | **Located up to constants** | \(W\ge0\) and Hodge on every atomic test at \(w\le K_\star(\varphi)\delta_N\); the prime defect pays the pole. The finite-part component of \(K_\star\) is within \(e^{2+2\varepsilon}\) of Robin–Euler Markov instability [S]. |
| **3.30 Balanced Haar completion** | **Detail payment closed** | Gamma pays \(\sum\log(a)h_a(u_a-v_a)^2\) on arbitrary complete cells, averages present, plus a far-end-weighted mean graph across interval pairs [S]. Coarse payment moves to new face 3.31. |
| **3.27 Complete residual** | Sharpened | Residual radical equals the Weil radical; translation keeps \(W\) and escapes every exponential graph bound; bounded-window transport has nonuniform constants [S]. |
| **1.18 Gauge selection** | Sharpened | Twisted poles read \(2\operatorname{Re}(-L'/L(1,\chi))\) for every nontrivial \(\chi\); twins are visible at every root. Among matched sign gauges with convergent Mertens error, \(\zeta\) uniquely maximizes the prime finite part (\(\ge4\log p/p\) per flipped prime), and Liouville uniquely minimizes the anti-matched one [S]. |
| **3.28 / 14.31 Prime exhaustion** | Sharpened | Valuation-chain gap \(2\log2\) for each finite prime set; the all-prime sharp gap is in progress; fixed conductor packets are realized by actual eigenvalues [S]. |
| **3.15 Escape states** | Sharpened | Record-minimum limits have \(K(p,p)\ge p^{2\varepsilon-2}\), still compatible with zero gauge mass \(\inf_dd\,K(d,d)\). |
| **1.0 Fixed strip** | Extended | \(\Theta<1\) iff a uniform power saving in the Vaughan convolution prefix iff a positive Vaughan decay index. |
| **1.23 Ordered Chebyshev identity** | **New** | Every separated mixed entry of the complete form is a centered prime-error integral plus a Gamma tail with nonnegative square reserve [S]. |
| **1.24 Selectivity localization** | **New** | All proved positive families are twin-blind, so the missing inequality must be selective on the coarse, low and cross-level residual. Inference from proof hypotheses. |
| **3.31 Dyadic self-similarity** | **New** | Average cells are \(\log2\)-translates; complete cells are \(T_{\log2}\)-orbits of finitely many generators plus paid high details. |
| **3.32 Cross-level coupling** | **New** | Cross-level blocks are Toeplitz in the level difference. Pole products grow like \(2^{\lvert j-k\rvert/2}\) and cancel only up to the prime error; one prime orientation vanishes, the other survives. |
| **3.33 Renormalization topology** | **New** | No exponential amplitude renormalization gives uniform graph control. |
| **3.34 Gamma boundary rigidity** | **New, closed** | Boundary norm \(\le\pi/2\) is an identity with an exact square reserve; equality only at zero; no uniform gap [S]. |
| **14.36 Function-field approximation** | **New boundary** | Curve explicit-formula distributions reproduce the prime support but not the archimedean continuum; Weil's positivity cannot be imported by weak approximation. |

"Closed" means the stated local or diagnostic question is answered, never that a route is closed. "Open" means a mathematical input is missing. "Boundary" means a proved limitation with a positive survivor.

## Wall 1 — Selective critical sign

| Face | Status | Content and remaining obligation |
|---|---|---|
| **1.0 Fixed-strip first rung** | Open; external claim | Escaped-endpoint, Hecke-defect, theta-prefix and Vaughan dictionaries all read \(\Theta\). An external \(7/8\) claim awaits intake. No local fixed power saving. |
| **1.1 Critical signed cancellation** | Open [RH] | Lag, Abel, history and regularized-series receivers need the actual signed bound at every slack. Absolute majorants and fixed periods lose the sign. |
| **1.2 Axis orientation** | Open [RH] | Ward caps, winding and Newton margins detect the defect; extinction or all-disc orientation is missing. |
| **1.3 Complete Weil positivity** | Open [RH] | High details, narrow sections and complete-cell realization are known; index zero on the complete source is not. |
| **1.4 Arithmetic cone membership** | Open [RH] | Identification and rigidity say what the source is, not that it lies in the positive cone. |
| **1.5 Contrast equality** | Open [RH] | BSY/Jensen/Li identities keep a signed or nonnegative defect whose vanishing needs arithmetic. |
| **1.6 Required uniformity** | Open | Fixed rank/order/height and orthant positivity leave the simultaneous signed receiver unproved. |
| **1.7 Amplification bookkeeping** | Closed diagnostic | Dyadic/tensor amplification transfers a supplied cap; it creates no rate gain. |
| **1.8 Critical pronic energy** | Open [RH] | Complete signed energy at small damping. |
| **1.9 Signed continuation** | Open | The integrated signed loss needs horizon-uniform control. |
| **1.10 Absolute compensation** | Open | Relative error \(\to0\) coexists with unbounded raw energy. |
| **1.11 Norm-specific rates** | Open in stated regimes | Physical L² full and polar ground rates agree; other norms are not interchangeable. |
| **1.12 Interior anti-alignment** | Open | Exterior (\(\sigma>1\)) field laws do not enter the strip. |
| **1.13 Aperture shell flux** | Open [RH] | Cumulative relaxation must not exceed the initial reserve. |
| **1.14 Actual divisor heat sign** | Open [RH] | Half-line Laguerre, Turán and positive tails leave all-height/all-degree signs. |
| **1.15 Depth homogeneity** | Boundary | Amplification pays at the scale it gains. |
| **1.16 Payment for actual zeros** | Open | Defect, field, inertia and index payments are lower laws; no source upper bound. |
| **1.17 Loss-rate improvement** | Open | A fixed tensor loss can encode RH; a sublinear loss must be proved. |
| **1.18 Arithmetic gauge selection** | Constrained margins closed; full sign open | Uniform prime gap on the pole hyperplane, where Liouville reaches the ceiling. Twisted poles read \(-L'/L(1,\chi)\); twins are visible at every root. Leading matching is blind to finite flips, but the finite part is not: \(\zeta\) is the unique maximizer among matched gauges, which identifies \(\zeta\) as the extremal, hardest member rather than a positive one. Transfer of a selective margin to the complete form is missing. |
| **1.19 Budget strength** | Boundary | Some budgets are RH-equivalent; Abel/Mertens saturation also forces simple zeros. |
| **1.20 Arithmetic-point completion** | Open | Periodic and finite-field counts keep their periods. |
| **1.21 Source reserve / work ceiling** | Open [RH] | Cofinal work \(\le2\) is RH-equivalent; no upper estimate. |
| **1.22 Finite versus zero exceptions** | Exact boundary | \(K(R)\uparrow\mathcal E_{\rm crit}\). \(\mathcal E_{\rm crit}<\infty\) iff finite off-line support; \(\mathcal E_{\rm crit}\le Q_*=1294047/2000\) iff RH. Finite index \(k\) costs \(\ge\max\{(Q_*/2)k,50k^2-3k/2\}\). |
| **1.23 Ordered Chebyshev identity** | Exact identity; payment open | \(W(f,g)=-\int(e^h-\psi(e^h)-c)\Omega'_{f,g}-\Gamma_{\rm tail}\) for ordered tests, with a Gamma square reserve. Separated couplings need the signed prime error, controlled in the dual norm of \(\Omega'\). |
| **1.24 Selectivity localization** | Structural boundary | The high-detail prime bound (Young/Schur, no sign condition), the Gamma payments (prime-free) and the narrow sign (shared by twins) all hold for every bounded twist. Since Liouville is not Weil-positive, any complete proof must use a \(\Lambda\)-specific input on the residual. Available selective inputs are prime-only or local. |

Evidence: [lag](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean), [aperture flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean), [Möbius](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean), [Vaughan strips](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean), [canonical energy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean), [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean), [Haar prime bound](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellPrimeBound.lean), [twisted pole](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheTwistedPoleReadsTheLogarithmicDerivative.lean), [gauge at every root](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheGaugeAtEveryRoot.lean).

## Wall 3 — Transfer, norms and exhaustion

| Face | Status | Content and remaining obligation |
|---|---|---|
| **3.1 Information retained** | Boundary | Magnitudes, complete-period covariances and collided counts can lose orientation or phase. |
| **3.2 Aperture escape** | Open | Finite windows admit hidden configurations and mimics. |
| **3.3 Norms and completions** | Scoped graph control closed | Fixed widths give arbitrary weighted floors and full-graph coercivity on finite prefixes; no global norm equivalence. |
| **3.4 Shared resources** | Open | A reserve cannot be spent on each edge or block separately. |
| **3.5 Endpoint logarithms** | Open | Pole cancellation leaves Dini/log remainders. |
| **3.6 Moving horizons** | Open | No free below-half-damping interchange. |
| **3.7 Damping topology** | Open | Half-damped boundedness gives no sub-half trace-ideal control. |
| **3.8 Multiplicity and index** | Clarified boundary | Distinct index, copied energy and packet multiplicity are different currencies. |
| **3.9 Observation cost** | Open | Finite-window coercivity has explicit horizon cost. |
| **3.10 Invertible filters** | Boundary | Unit filters preserve the classes; repair needs non-unit arithmetic content. |
| **3.11 Coupled quantifiers** | Open | Degree, rank, height, time, damping and support limits do not commute without uniform estimates. |
| **3.12 Residual reconstruction** | Open | Coordinate maps need not have bounded inverses. |
| **3.13 Joint orientation** | Open | One-channel signs do not orient the joint form. |
| **3.14 Averages to selected zeros** | Open | Proportions (\(\ge0.6725\) simple-critical), Schur slack and large-value counts allow exceptions. |
| **3.15 Escape states** | Open [RH] | RH iff every escape state has positive gauge mass. Record-minimum limits have positive diagonals that still allow zero mass; compact laws classify but do not exclude escape. |
| **3.16 Prime to spectral sign** | Open | Prime-side margins must reach the full spectral form with poles intact. |
| **3.17 Archimedean-line horizon** | Open | Near-incidence estimates have bandwidth/horizon limits. |
| **3.18 Localization** | Boundary | Positivity constrains a fibre only where the carrier localizes. |
| **3.19 Conductor versus forcing** | Open | No common aperture range for twisted positivity and companion forcing. |
| **3.20 Collided-form norm** | Closed locally | Fixed-aperture collided form \(\asymp\) log-weighted Fourier norm. |
| **3.21 Lattice to continuum** | Open | Lattice payment must keep the continuum signed/polar remainder. |
| **3.22 Computed detection** | Closed diagnostic | Detection is not exclusion. |
| **3.23 Local to global Hodge** | Open | Hyperbolicity is not additive; dispersion must be paid. |
| **3.24 Horizon regulator** | Closed construction | Polar/tensor counterterms and BV finite parts explicit; valuation rank grows, residue rank does not. |
| **3.25 Narrow spacing payment** | Closed | Archimedean self-energy pays prime and pole terms at fixed spacing fractions (\(c_\star\) tilted; \(K_\star\) defect-paid). |
| **3.26 Complete overlap transfer** | **Transfer closed at every root; sign open** | RH iff eventual atomic positivity at any unbounded polylog overlap. Bounded-overlap rows are explicit; coverage excludes fixed overlap as universal synthesis. |
| **3.27 Complete residual** | Exact boundary | Bounded projection on the proper unbounded carrier; residual radical equals the Weil radical; complete cells capture every finite index. Residual nonnegativity open. |
| **3.28 All-prime/class exhaustion** | Open transfer | Fixed packets realized; finite-\(Q\) gap \(2\log2\). Growing conductors, complement, class variation and Gamma/pole coupling open. |
| **3.29 Valuation versus residue classes** | Exact boundary | Residue counterterm rank one; character finite parts \(-L'/L(1,\chi)\) plus ramified term; twisted poles carry no divergence. |
| **3.30 Balanced Haar completion** | Details closed; coarse open | Unit full-form floor above index \(A\); Gamma pays all adjacent differences on complete cells. |
| **3.31 Dyadic self-similarity** | **New exact structure** | Average cell \(=T_{\log2}\)(cell). Complete cells are \(T_{\log2}\)-orbits of cell 1 and the low details \(a<A\), plus high details paid level by level. Positivity on the generator orbits is a one-prime orbit condition. |
| **3.32 Cross-level coupling** | **New open face** | Blocks Toeplitz in the level difference. Translated average→detail prime pairing vanishes; the reverse survives. Pole products grow like \(2^{\lvert j-k\rvert/2}\) and are cancelled only up to the Chebyshev error (1.23). |
| **3.33 Renormalization topology** | **New boundary** | Translation fixes \(W\) but every nonzero compact orbit's graph norm exceeds every exponential. Bounded windows and fixed translation ranges give bounded transport with nonuniform constants. |
| **3.34 Gamma boundary rigidity** | **New, closed** | Exact Schur weight; norm \(\le\pi/2\); exact square reserve; strict for nonzero profiles; no uniform gap. |

Evidence: [complete transfer](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteWeilSourceTransfer.lean), [every root](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheOverlapLawAtEveryRoot.lean), [rows](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheRowsAtBoundedOverlap.lean), [unbounded carrier](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheUnboundedCellCarrierHasAWeilProjection.lean), [radical](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TheSignedComplementRetainsExactlyTheWeilRadical.lean), [translation escape](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TranslationPreservesWeilEnergyButEscapesEveryExponentialGraphBound.lean), [Gamma payment](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellVariancePayment.lean), [self-similarity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellCoarseSplitting.lean), [Gamma reserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheGammaBoundaryReserveIsAnExactSquare.lean), [escape visibility](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean), [record minima](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean).

## Wall 14 — Realization and forcing

| Face | Status | Content and remaining obligation |
|---|---|---|
| **14.1 Capacity and limits** | Open | Growing/singular carriers survive fixed-capacity obstructions; a faithful limit must carry orientation. |
| **14.2 Algebra without orientation** | Boundary | Correspondence identities and count positivity hold for impure data. |
| **14.3 Detector without producer** | Open | Calibrated vanishing laws are equivalent to criticality; independent vanishing missing. |
| **14.4 Effectivity receiver** | Closed equivalence | Section/effectivity hypotheses are Hodge receivers. |
| **14.5 Pre-divisor weld** | Open | Prime and Gamma reservoirs need source-level compatibility. |
| **14.6 Section selectivity** | Open | Counts and positive sections do not give full-source RR/Hodge. |
| **14.7 Theta degree coupling** | Closed scoped law | Linear RR/count relation understood. |
| **14.8 Blind-carrier exhaustion** | Open | The maximal blind ideal is the full carrier only at RH. |
| **14.9 Positivity versus faithfulness** | Boundary | Strong invariant positivity may force RH plus simplicity. |
| **14.10 Invariant positive carriers** | Boundary | Off-line boosts force isotropy on the tested carriers. |
| **14.11 Multiplicative forcing capacity** | Closed scoped boundary | Boundary forcing and Fejér barriers do not move interior zeros. |
| **14.12 Degree-one rigidity** | Closed scoped law | The simple-pole class is \(\mathbb R\cdot\zeta\); sign separate. |
| **14.13 Zero–pole budget** | Closed diagnostic | Inserted-zero bookkeeping is not a budget for \(\zeta\)'s own zeros. |
| **14.14 Amplification base** | Open | A fixed tensor loss can encode RH. |
| **14.15 Successor coupling** | Structure closed; sign open | Successor carries an archimedean gauge connection. |
| **14.16 Correspondence ring** | Closed identity | Square identities hold without purity. |
| **14.17 Local representation type** | Closed diagnostic | No automatic conformal Frobenius. |
| **14.18 Arithmetic polarization** | Open | A form simultaneously faithful, positive and equivariant. |
| **14.19 Zero contraction** | Closed scoped boundary | Contraction laws do not move nonreal quartets. |
| **14.20 Collision and conductor** | Closed obstruction | Finite carriers meet localization/conductor barriers. |
| **14.21 Collided polarization** | Open sign | \(D\) positive and computable; its equality with \(W\) needs zero defect. |
| **14.22 Central order** | Open forcing | Central-ceiling forcing missing. |
| **14.23 Polar-configuration criterion** | Closed receiver | Source sign unproved. |
| **14.24 Torsion renormalization** | Scoped bounds closed | Counterterm \(\varphi\log N+O(1)\); positive index \(\le N^{4/5+\varepsilon}\). Not Weil indices. |
| **14.25 Deformation** | Boundary | Deformation-stable properties need not select the source. |
| **14.26 Field and energy** | Open upper bound | Lower costs explicit; source upper ceiling missing. |
| **14.27 Coupled counterterm rank** | Closed scoped boundary | Partner-rank costs for positive torsion blocks. |
| **14.28 Counterterm covariance** | Closed classification | Covariant diagonal finite parts are scalar. |
| **14.29 Arithmetic base across primes** | Construction boundary | Closure gives exactly nonnegative Lorentzian Hessians; Ramanujan local factors excluded; decaying isometric ladders carry no single positive square. |
| **14.30 Zero moments** | Closed identification | Zero moments are Rosati-type pairings. |
| **14.31 Horizon finite part** | Local payment closed; exhaustion open | Raw threshold \(p\ge47\); valuation payment for every prime; finite-\(Q\) gap \(2\log2\). The all-prime Poincaré constant \(2\log2\) is stated in Lean with an unfinished proof. |
| **14.32 Actual trickle-down** | **Narrow regime located up to constants** | Hodge/TD at \(c_\star\) (tilted) and \(K_\star\) (defect-paid); Robin–Euler bounds the Markov mechanism within \(e^{2+2\varepsilon}\). |
| **14.33 Conformal replacement** | Open beyond tested maps | Hecke dilation has factor one; power/successor maps are not conformal. |
| **14.34 Overlap frustration** | Obstruction | \(\rho<1\) Metzler; every \(\rho>1\) frustrated; \(\rho=1\) open; full sign not refuted. |
| **14.35 Adjunction versus Xi** | Fidelity boundary | Adjunction energies are realized as actual prime-matrix eigenvalues for fixed packets; not a Xi spectral identification. A paper-stage exhaustion card awaits formalization. |
| **14.36 Function-field approximation** | **New boundary (this review, not formalized)** | In the natural log-norm normalization, nonnegative combinations of curve explicit-formula distributions over finite fields are supported on \(\{\pm\log(\text{prime powers})\}\cup\{0\}\). \(\zeta\)'s zero-side distribution has a nonzero continuous part on \((0,\log2)\) (pole minus archimedean density), so Weil's positivity for curves cannot be imported by weak approximation. Dilating the curves removes the support obstruction, but their atoms then no longer sit at \(\log(\text{prime powers})\). The approximation becomes one of \(\zeta\)'s zero side, which is circular as a producer. |

Evidence: [adjunction](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSieveOperatorHasTheAdjunctionEigenbasis.lean), [spectral packets](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFullPrimeMatrixRealizesFiniteAdjunctionPackets.lean), [finite-Q gap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheValuationChainOfFinitelyManyPrimesHasGapTwoLogTwo.lean), [pole defect](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/ThePoleDefectPaysThePole.lean), [Robin–Euler](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheStabilityRegimeEndsAtTheRobinEulerThreshold.lean), [Metzler threshold](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheMetzlerThresholdOfTheOverlapRatioIsOne.lean), [closure class](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheClosureProducesExactlyTheLorentzianForms.lean), [ladders](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/AnIsometricLadderCarriesNoPositiveSquare.lean), [torsion index](../../../formal/GaloisForLFunctions/ArithmeticIntersectionTheory/ThePositiveSquaresOfTheTorsionFormLiveBelowFourFifths.lean), [Stepanov mechanism](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism.lean).

## Sharp obstructions and their positive survivors

| Excluded shortcut | Strongest survivor | Replacement question |
|---|---|---|
| Pure Markov positivity at separated widths | Markov fails at every root unconditionally; full form positive at \(K_\star\); pole-hyperplane RH criterion | Full pole-paid sign at unbounded polylog overlap. |
| Same diagonal Metzler gauge through overlap | Narrow Hodge/TD at \(K_\star\); sharp \(\rho\lessgtr1\) boundary | Signed/block methods without that gauge. |
| Shrinking or translating positive sections | Bounded projection; Weil radical; translation escape | Residual nonnegativity respecting the radical and the graph topology. |
| Twin-blind positive families as complete positivity | High-detail floor; Gamma payment of all details | A selective inequality on the coarse/low residual (Q2). |
| Pole products across levels as summable | Chebyshev identity: main-term cancellation | Signed prime-error control in the dual norm of \(\Omega'\). |
| Fixed-prime positivity as all-prime positivity | Valuation payment; finite-\(Q\) gap \(2\log2\); fixed packets | Sharp all-prime gap; growing conductors. |
| Leading polar matching as gauge selection | Pole-hyperplane gap; finite parts; twisted poles \(-L'/L(1,\chi)\) | Transfer of constrained margins to the complete form. |
| Detection/quantization as an upper bound | Canonical monotone energy and exact thresholds | An arithmetic upper estimate keeping exterior rows. |
| Lorentzian closure / Euler closure as global Hodge | Exact closure class; half-line Laguerre; finite-field Gram polarization | A faithful signed/block identification. |
| Hecke/power/successor maps as Frobenius | Factor-one Hecke isometries; Stepanov needs a lattice spectrum | A different faithful correspondence. |
| Function-field approximation as imported positivity | Curve distributions reproduce exactly the prime support | An archimedean component of non-finite-field origin. |
| Proportions as zero exclusion | Simple-critical \(\ge0.6725\); Schur slack | Force each exceptional zero into an impossible event. |

## Consequences for priorities

- [Q1](obstacles-summary.md#q1) targets **3.31 / 3.32 / 3.27 / 1.3**: reduce complete positivity to finitely many \(\log2\)-orbits plus a paid cross-scale coupling.
- [Q2](obstacles-summary.md#q2) targets **1.24 / 1.18 / 3.28 / 14.31**: the selective input on those orbits.
- [Q3](obstacles-summary.md#q3) targets **1.21 / 1.22 / 14.26**: an upper bound on canonical critical energy.

No route is declared dead by these priorities. Finite calculations, transfer instantiation and literature intake are listed as [just work](obstacles-summary.md#21-tasks-that-are-just-work).
