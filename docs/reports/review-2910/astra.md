# RH research: opportunities, limits, and a programme for new tools

29 October 2026. Mathematical synthesis of the requested reports and local Lean corpus.

**Best opportunity: turn the newly explicit complete-source spectrum into a signed estimate that survives touching and overlapping atoms. Best quantitative target: the specific prime-pair surplus already known to imply 75% simple critical zeros. I found no defensible new mechanism escaping all three broad walls.** Finite off-line support and improved fixed strips remain meaningful targets, but neither follows from the available density or heat estimates.

There is also a concrete, smaller opportunity: an explicit polynomial profile appears to turn the existing bounded spectral law into eventual full-Weil positivity at **every fixed strictly separated width ratio**. This is a proposed corollary, with rational calculations below, **not a newly formalized result**. It sharpens where the next difficult question begins.

## Scope and status

Read [frontier map](../rh-current-frontier-map.md), [killed routes](../rh-killed-routes.md), [unification](route-unification-ledger.md), [obstacles](route-obstacles.md), [28 October walls](../review-2810/walls-ledger.md), and [programme list](../research-programmes.md), then the programme READMEs named in that list, oldest to newest. Repeated entries were treated as revisits. The final `ShallowCauchyPrimeEnergy` entry has no README; its mathematics was examined through corpus searches and Lean source. No linked ancillary Markdown was followed.

Existing results below are statements found in the reports and checked against relevant Lean declarations. **[S]** marks working-source developments, including statements newer than the ledgers. **Proposal** denotes an unproved research target or an unformalized deduction in this report. No builds, web searches, or proof-integrity audit. Searches identify local evidence; they do not establish worldwide novelty or absence of other mathematics. [Research log](../../../logs/astra-rh-research-2026-10-29.txt) and [search records](../../../logs/astra-rh-research/) preserve findings.

## What the programme sequence has taught us

The historical movement matters more than the number of route names. In the order supplied:

| Programme sequence | Mathematical gain | Remaining lesson |
|---|---|---|
| Arithmetic positivity → BiScale → TransHorizon → Bézout–valuation | Exact signed sources, critical energies, half-damping thresholds, rate dictionaries | Admission and cancellation are separate. Changing norm or horizon has a real price. |
| Arithmetic criticality → SquareRootThreshold → incidence → continuation → scale-signed criticality → compensation | All-test variation criteria, small-width visibility, common-reserve allocation, aperture flow, depth reconstruction | A small detector can see deep zeros through a long orbit. Small support does not make the global estimate local. |
| Castelnuovo–Severi → signed energy incidence → trans-threshold correlation | Effectivity receivers, signed path payment, quantitative census targets | Positive counts need quadratic compatibility; pairwise absolute payment can lose valid global positivity. |
| Orientation theory/geometry → local divisor geometry → successor arithmetic → defect rigidity | Width/index dictionaries, heat barriers, exact shift floors, escape classifications | Reconstruction and lower costs do not supply an upper bound on the actual defect. |
| Biarithmetic → multiplicative positivity → positive duality → StripBochner → correlation geometry → Künneth | Source rigidity, affine representations, gauge classification, almost-everywhere cancellation, tensor count laws | Identification is not positivity; typical gauges do not select the actual one; tensorization can preserve the original obstruction. |
| Correspondence positivity → polarization → effectivity → gauge geometry → conjugate diagonal → selective thresholds | Exact section-count/sign equivalences, collided defect, height receivers, successor holonomy, selective local witnesses | Arithmetic compatibility must yield an inequality, not merely identify the Euler point. |
| Electrostatics → intersection → renormalized potential/biarithmetic, with correlation and potential revisits | Quantized defect energies, local prime towers, counterterms, Ramanujan spectrum | Local positivity cannot be summed freely; finite parts retain indispensable signed information. |
| Spacing-scale → Lorentzian → Gabor pinching | Near-spacing positivity, overlapping-family receivers, pole-complement reduction, improved critical-line census | Separation, overlap, and microscopic horizontal displacement are distinct thresholds. |
| Index descent → signed Hodge → selective multiscale → counting positivity → Hecke–Krein–Toeplitz → shallow Cauchy energy | Large paid source blocks, exact selection tests, conductor measures, full index laws, critical-scale collision budgets | The remaining problem is increasingly specific: actual first-prime and mixed correlations, with sufficient precision and simultaneous uniformity. |

This is substantial progress. It has removed ambiguity about what must be proved and exposed statements that would accidentally demand more than RH. It has not yet produced the decisive arithmetic estimate.

The unification can be compressed into three mathematical obligations:

| Core problem | What is missing | Relevant wall |
|---|---|---|
| U1: selective critical sign | A signed estimate using a property of the actual prime/Möbius source that the failing comparison sources lack | Wall 1 |
| U2: complete Weil positivity | Control of the original form, including Gamma, both poles, cross terms, and simultaneous exhaustion | Walls 1 and 3 |
| U3: independent producer | An arithmetic construction that proves the required estimate or index bound | Wall 14 |

Three distinctions should govern the next programme.

**An equivalence is not a producer.** The identity between ordered Weil entries and centered Chebyshev integrals is stronger than two independent RH criteria: it identifies the same unpaid source entry by entry. Rephrasing that entry as an index, current, height, or covariance does not change its arithmetic content. See [ordered Chebyshev source](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean).

**The broad walls are obligations, not universal impossibility theorems.** Selectivity, faithful passage to limits, and an independent construction must be supplied somehow. The individual no-go results exclude specified mechanisms. They do not prove that all possible mathematics lacks the required tools. Likewise, finite support implying Lindelöf means a successful argument would prove Lindelöf too; it does not mean Lindelöf must first be assumed.

**Different targets require different information.** A 75% census may tolerate finitely many exceptional zeros and need much less than a sign theorem deciding every zero. RH-level precision obstructions should not automatically be imposed on every statistical intermediate result.

In particular, finite off-line support would already give a critical-line proportion tending to one, though it says nothing comparable about simplicity. It also gives some fixed strip, without selecting a numerical endpoint such as \(5/6\): the remaining low exceptions could determine that endpoint. Conversely, a fixed strip or a 75% census alone leaves room for infinitely many off-line zeros. These are different kinds of partial progress.

## 1. Opportunities to cross a wall

### A concrete opening inside strict separation

The current complete-Weil spectral theorem is stronger than convergence of individual Ramanujan trial vectors. For fixed profile \(\varphi\), fixed \(0<c<1\), and threshold \(b\) outside the arithmetic spectrum, it identifies **the entire count of eigenvalues below \(b\)** for all sufficiently large horizons. Thus low eigenvalues cannot hide in conductors omitted from a fixed trial calculation. [Bounded spectral counts, S](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum.lean).

Write

\[
M_\varphi=\int\varphi^2,\qquad
B_\varphi=\frac{\operatorname{bumpRobin}(\varphi,1)}{M_\varphi},\qquad
q_\varphi=\frac{(\int\varphi)^2}{M_\varphi}.
\]

The limiting lowest energy is

\[
e_1(c)=B_\varphi-\log(2\pi c)+c q_\varphi.
\]

Every other conductor has strictly higher energy for \(c<1\). This uses the complete archimedean and polar correction: the \(+c q_\varphi\) term is part of the original source. [Energy formula and ordering](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheCompleteWeilTrialEnergiesAreSimpleAndProper.lean).

**Proposed corollary to formalize.** Use

\[
\varphi(x)=
\begin{cases}
x^3(1-x)^3,&0\le x\le1,\\
0,&\text{otherwise}.
\end{cases}
\]

This profile is \(C^2\). Exact rational autocorrelation calculations give

\[
M_\varphi=\frac1{12012},\qquad
\int\varphi=\frac1{140},\qquad
B_\varphi=\frac{48233}{36036},\qquad
q_\varphi=\frac{429}{700}.
\]

The scalar margin is

\[
B_\varphi+q_\varphi-\log(2\pi)
=\frac{439487}{225225}-\log(2\pi)
\approx0.11344716>0.
\]

Since \(q_\varphi<1\), the displayed \(e_1(c)\) decreases on \((0,1)\) toward this positive value. The proposed composition is therefore: certify these profile integrals and the positive scalar margin; apply the existing spectral count theorem at a positive threshold below that margin; obtain eventual positive definiteness of the complete matrices for this profile at each fixed \(c<1\). The calculation uses the corpus's [Robin normalization](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheRobinConstantOfAnAtom.lean); [rational scratch record](../../../logs/astra-rh-research/polynomial-robin-check.txt) is not a Lean certificate.

**Why this matters:** the older “past Robin–Euler” question has a concrete completion candidate for a fixed profile. The full polar correction can preserve positivity after the Markov-only scalar loses its sign. Treating poles by absolute values would miss that mechanism.

**Exact limits:** this would not prove arbitrary-profile positivity, positivity at \(c=1\), a horizon bound uniform as \(c\uparrow1\), overlapping-family positivity, or RH. The existing coercivity coefficient is \((1-c)/4\), so the current control degenerates precisely at touching. Positive limiting scalar energies alone do not prevent new modes entering there. [Coercivity, S](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheCompleteWeilEnergyControlsThePrimeDefect.lean).

The next serious problem should therefore examine the **full signed operator at touching and overlap**, rather than repeatedly extend a narrow absolute-value estimate.

### Exact elimination of paid directions

Schur and Kron reductions already belong to the programmes; the abstract mechanism is not new. Their next use should be an arithmetic estimate for the remaining block of the original complete form. In a finite source family, write

\[
W=\begin{pmatrix}A&B\\B^*&D\end{pmatrix}.
\]

Where the paid detail block \(D\) is positive definite, its exact remaining cost is \(BD^{-1}B^*\), and the unresolved form is

\[
S=A-BD^{-1}B^*.
\]

This retains correlations and spends the detail reserve once. The mathematical proposal is to control this particular \(S\) using actual prime incidence and the two pole moments. A generic norm estimate on \(B\) is likely to reproduce the losses already catalogued. The gap and affine floor must both survive. [Complete pole-complement reduction](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar.lean).

There is a current source-level example of the right kind of transfer. Whole dyadic generator-orbit cutoffs commute with every power of the actual clock, giving

\[
|\mathcal P_2(f)-\mathcal P_2(P_Af)|
\le \frac{64\log2}{\sqrt2-1}\,
\frac{\Gamma(f)}{1+\log A}
\]

for the complete prime-two Euler contribution of the source's cell component, with one original-source reserve. Here \(P_A\) abbreviates the whole-generator-orbit projection on those cell coordinates. This is an all-level error estimate, not merely convergence at each fixed lag. [Dyadic Euler tail, S](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/OneGammaReserveControlsTheDyadicEulerTail.lean).

The opportunity is to develop analogous **joint signed** estimates for interacting prime actions. Summing fixed-prime absolute bounds will not work: the first-power costs over all primes diverge. Also, a head of finitely many generators still contains infinitely many translation levels. This result does not make that head compact or give a finite index bound.

The paid block is now larger than the square layer alone. Odd prime powers of exponent at least three can be paid jointly with the even-power refinement, leaving a uniform coarse/detail reserve after removing a fixed detail head. The remaining coarse odd-power source and first-prime terms must still be combined with the full completion. These results should be used together; adding independently proved estimates can spend the same Gamma reserve twice. [Joint refinement reserve, S](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/CompleteCellAveragesAreBoundedInGammaEnergy.lean), [odd higher-power payment](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/OddHigherPrimePowersPayTheirWholeDetailBlock.lean).

Another advance is uniform full prime–polar cancellation on compact BV profiles:

\[
|\mathcal P(f)-(2C(f)^2-2S(f)^2)|
\le \varepsilon e^R\bigl(\Gamma(f)+\|f\|_2^2\bigr)
\quad(R\ge R_0(\varepsilon)),
\]

where \(\operatorname{supp}f\subseteq[-R,R]\), and \(C,S\) are the original half-exponential cosh/sinh moments. This removes a derivative-norm restriction and retains every prime power and both poles. It does **not** improve the aperture exponent: \(\varepsilon e^R\) is not a small relative form bound as \(R\to\infty\). [Full Gamma-norm bound, S](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheFullPrimePolarSourceCancelsInGammaNorm.lean).

### Selectivity must enter the estimate itself

The gap \(2\log2\) is insufficient: remote prime flips attain it. The exact dyadic-response test proves that additional response information can select the untwisted source within finite flips. That is useful evidence for studying a response function rather than one scalar gap. It does not yet connect selection to the sign of the overlapping complete form. [Two-gap selection](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/OneDyadicProbeSelectsTheFinitePrimeSource.lean).

Newer working sources also go beyond the older ledger: every prime pattern now has an actual resolvent limit in the physical first gap, and positive Euler density transfers the exact finite-cutoff gap to the infinite pattern. Positive density retains full conductor mass; at zero density the resolvent reading vanishes through mass escape. These provide concrete comparison objects and distinguish a lost limit from a small positive operator. They remain statements about the prime matrix. [All-pattern resolvent](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/EveryPrimePatternHasItsFullArithmeticResolvent.lean), [positive-density gap transfer](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/PositiveDensityTransfersTheExactCutoffGap.lean).

**Verdict:** a plausible way to cross part of Wall 3 exists: exact spectral exhaustion plus signed elimination of paid blocks. Crossing Wall 1 still requires an arithmetic inequality for the remaining block. No current result supplies it automatically.

## 2. A wildly different RH route that avoids every existing wall?

**I do not see a defensible one in the evidence examined.** Calling an operator, geometric object, or probability model “new” would not justify that claim. The corpus already covers an unusually broad range of such constructions.

Several tempting departures are already constrained:

- Affine arithmetic dynamics and Bost–Connes-type positive states are not unexplored. Under the precise integer-successor hypotheses, the dilation spectral measure gives zero mass to the archimedean character line. A positive affine representation is therefore not automatically the required faithful carrier. [Successor spectral obstruction](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheIntegerSuccessorForcesAKroneckerNullDilationSpectrum.lean).
- Infinite-symmetry continuation is not a fresh escape. The updated unification report records its failed calibration. The local polynomial result shows why moment growth can hide a fixed number of off-line pairs: inserting a reciprocal-depth pair changes the depth product and circle maximum by degree-independent factors. [Moment/depth boundary](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MomentBoundsCapTheOffLineDepth.lean).
- Independent lossless, Lee–Yang, Hodge, or section-count constructions still owe their exact identification with the arithmetic source. That is the content of their candidate status, not an incidental implementation step.

There is no theorem here saying a future proof must use the present test families. A different producer could bypass their particular failures. Wall 14 is broad enough, however, to include the need to connect a new construction to the actual zeta function. Avoiding all existing carriers would still leave that identification and forcing theorem to prove.

The conceptual departure I would encourage is **arithmetic exclusion or propagation**: identify an exact integer-specific law that an off-line mode would violate, or would force to replicate into too many independent arithmetic obstructions. Its first deliverable must be such a law on an actual source-defined family. Merely tensoring a zero configuration, adjoining more shifts, or counting the same exceptional zero in many auxiliary objects does not supply it. I do not have that law, so I would label this exploratory research, not another standalone route.

## 3. Could there be only finitely many off-line zeros?

This remains a coherent intermediate target. The wording “if any exist, only finitely many exist” is logically the finite-support assertion itself: when none exist, finiteness is automatic.

The corpus has already identified its exact content:

\[
\begin{aligned}
\text{finite off-line support}
&\Longleftrightarrow\kappa(K_\zeta)<\infty\\
&\Longleftrightarrow\sup_{t>0}N_{\rm nonreal}(H_t)<\infty\\
&\Longleftrightarrow\exists T_0\ \forall\rho:
\ |\Im\rho|>T_0\Rightarrow\Re\rho=\tfrac12.
\end{aligned}
\]

The index can already be read on a two-prime lattice. It counts distinct right zeros; the heat count retains multiplicity. Finiteness implies Lindelöf and some fixed zero-free half-plane. The actual zeta kernel already has the finite-stratum structure theorem; proving an abstract Krein–Langer classification would not itself establish that zeta belongs to that stratum. [Finite stratum, S](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean).

There is an especially sharp source-work target. Set \(\mathscr W(R)=\texttt{xiDampedSourceWork}(R)\) and

\[
\Delta_R\mathscr W=\mathscr W(2R)-\mathscr W(R).
\]

This is the completed work of the arithmetic Laurent source fields, with multiplicity and every exterior field retained. The displacement weights use
\(h_R(t)=R^4/(R^2+t^2)^2\). Critical-line reflection makes the completed pair increments nonnegative. The current theorems give

\[
\begin{aligned}
\text{finite off-line support}
&\Longleftrightarrow
\Delta_R\mathscr W\le\frac{39}{50}\quad\text{for all sufficiently large }R,\\
\mathrm{RH}
&\Longleftrightarrow
\Delta_R\mathscr W\le\frac{39}{50}\quad\text{for every }R\ge4.
\end{aligned}
\]

Each off-line quartet at height \(|\gamma|\) forces
\(\Delta_{|\gamma|}\mathscr W>39/50\), however small its horizontal depth. This gives a particularly clear separation between excluding high exceptions and excluding all exceptions. [Strict scale quantum, S](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/EveryOffLineQuartetCostsAStrictScaleQuantum.lean).

**My preferred finite-support opportunity is an arithmetic upper estimate on this difference.** Differencing the damping removes the constant contribution of any fixed low zero; it costs \(O(\gamma^2/R^2)\) there, while retaining a fixed charge for a new quartet at height \(R\). An estimate \(\Delta_R\mathscr W=o(1)\) would suffice. The missing work is to control the signed source expression before its zero-side symmetrization, using actual arithmetic. Its existing identification with Laurent residues is not such an upper bound. [Completed source identity](../../../formal/GaloisForLFunctions/ArithmeticElectrostatics/TheSelbergWorkExhaustsTheTransverseEnergy.lean).

Two exact classifications help calibrate that proposal:

- For distinct zeros with unit charges,
  \[
  \mathcal E_\perp=\frac12\sum_{\rho\ne\sigma}
  \frac{(\Re\rho-\Re\sigma)^2}{|\rho-\sigma|^2}<\infty
  \quad\Longleftrightarrow\quad\text{finite off-line support}.
  \]
  Reflection supplies a depth-independent quantum. A decay estimate on horizontal depths alone cannot pay it. This energy counts distinct zeros, unlike the copied source work. [Transverse energy](../../../formal/GaloisForLFunctions/ArithmeticElectrostatics/TheTransverseEnergyOfTheZeroDivisor.lean).
- Boundedness of \(R^2\Delta_R\mathscr W\) is also equivalent to finite support. Its exact trichotomy is zero under RH, convergence to a positive finite source moment for finitely many exceptions, and divergence to infinity for infinitely many exceptions. The finite moment retains all exterior interactions; its finite-sum formula cannot be used before finiteness is proved. [Critical-rate classification, S](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalRateClassifiesAllOffLineSupport.lean).

Two complementary programmes remain plausible, with missing inputs:

1. **A finite-index theorem for the remaining complete source.** Much of the detail/even/nonfirst source has a uniform negative-dimension bound with the original poles retained. Finish the first-prime/coarse remainder with a bound independent of aperture and prime cutoff. Finiteness permits a large constant; RH would require index zero. This relaxation is useful, but it does not remove the need to control infinitely many potential negative directions. [Paid source and its two scalar costs](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheEntireSquareSourceSharesTheFullDetailReserve.lean).
2. **An arithmetic bound on total small-time collision production.** The heat programme now has local zero motion, exterior forces, collision continuity, and forward simplicity. A localized evolution estimate with a uniformly bounded total incoming contribution as \(t\downarrow0\) could supply the required count. The unproved part is that uniform global budget, including zeros arriving from arbitrarily high ordinates. Local evolution identities alone cannot bound it. [Local heat evolution source](../../../formal/GaloisForLFunctions/RHTower/Heat/HeatLocalizedEnergyEvolution.lean).

A compact perturbation argument needs particular care. A compact negative perturbation of a positive operator whose spectrum approaches zero can still create infinitely many negative eigenvalues. “Compact remainder” alone is insufficient; one needs coercivity on the relevant complement or a stronger structural index theorem. The corpus's noncompact translation orbits and vanishing aperture floors make this distinction material.

Likewise, \(N(t)<\infty\) separately for every positive \(t\), or even a prospective polynomial bound \(N(t)\ll t^{-a}\), does not prove a uniform bound. Density zero is also consistent with infinitely many exceptional zeros, including depths tending to zero extremely rapidly.

**Assessment:** finite support might be easier in constants than RH, but it still needs a qualitative global theorem. Nothing currently establishes it. Its implication of Lindelöf is a strength diagnostic, not a reason to prohibit research on it.

## 4. Improved quasi-RH beyond the reported 1/8–7/8 strip

The requested reports describe the Chen–Gupta–Li \(7/8\) statement as external, with detector/density components but no local zero-free capstone. This review neither validates nor refutes that manuscript. The claimed strip cannot serve as an established local starting theorem.

The most precise local guide is the exact exponent dictionary. Let \(\Theta\) be the supremum of real parts of nontrivial zeros. For integer \(M\), define the corpus's normalized Chebyshev Cesàro sum and energy by

\[
C(M)=\sum_{2\le n<M}\frac{\psi(n)-n}{\sqrt n},\qquad
E_C(N)=\sum_{2\le k\le N}\left(\frac{C(k)}k\right)^2.
\]

Its infimal admissible power exponent is \(2\Theta\). Consequently the following are meaningful arithmetic targets:

| Desired closed strip | Mean-square target, for every \(\varepsilon>0\) | Alternative sufficient one-sided bound on \(C(M)/M\) |
|---|---|---|
| \([1/8,7/8]\) | \(E_C(N)\ll_\varepsilon N^{7/4+\varepsilon}\) | \(O(M^{3/8})\) upper bound |
| \([1/6,5/6]\) | \(E_C(N)\ll_\varepsilon N^{5/3+\varepsilon}\) | \(O(M^{1/3})\) upper bound |
| \([1/4,3/4]\) | \(E_C(N)\ll_\varepsilon N^{3/2+\varepsilon}\) | \(O(M^{1/4})\) upper bound |
| Critical line | \(E_C(N)\ll_\varepsilon N^{1+\varepsilon}\) | Every positive power suffices |

The one-sided bound can even be imposed on any fixed integer-power mesh, with the exact additive constants in the source theorem. These are established translations, **not established estimates**. Closed endpoint confinement does not by itself exclude zeros on the endpoints. [Strip and energy laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw.lean).

I see two research opportunities:

- Extract the complete parameter dependence of an **individual-zero detector**, including contour continuation and every error term. Find which inequality sets the claimed threshold and whether it admits a positive exclusion margin at some \(\sigma_0<7/8\). Only then optimize it. There is no justified improved numerical value to announce before that calculation is closed.
- Seek a signed estimate for \(C(M)/M\) on a sparse power mesh. The existing theorem makes that sufficient without first proving pointwise bounds at every integer. This reduces the requested input, although it does not produce cancellation or evade its critical scale.

The Guth–Maynard density exponent and short-interval prime asymptotics do not give the missing implication. A bound for the number of zeros with a right-hand side remaining above one cannot exclude a single zero. Nor should improving the standard CGL packet estimates be advertised as an RH endpoint: the actual horizontal-collision no-go has a floor of \(288\) against quantum \(2\), and the packet merges reflected points with the same ordinate. That obstruction is scoped to this merger, not to the external fixed-strip claim. [Collision obstruction](../../../formal/GaloisForLFunctions/RHTower/ChenGuptaLiHorizontalCollisionNoGo.lean).

**Assessment:** \(5/6\) is a clean next target, \(3/4\) a stronger one. Neither value follows from current bounds. The opportunity is a vanishing mechanism or signed power saving; a better density exponent alone does not supply it.

## 5. At least 75% on the critical line

**This has the clearest quantitative path among the requested intermediate targets.** The local baseline is already at least \(0.67250071-\varepsilon\) simple critical zeros, using the imported Zeta23 framework and local extension. The actual declaration is [simple_critical_proportion_ge_67250071](../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean). I use that baseline, not older training-data proportions.

The most direct target is `PrimeSurplusFourThirds`. At bandwidth \(4/3\), the already controlled contribution is \(43/36\). The remaining normalized prime surplus must be at most \(1/18+o(1)\), because

\[
\frac{43}{36}+\frac1{18}=\frac54,
\qquad 2-\frac54=\frac34.
\]

The source theorem gives **75% simple and critical**, asymptotically with every \(\varepsilon>0\), from precisely that hypothesis. The surplus includes off-diagonal prime pairs, sum frequencies, and the grid end correction. The prime–pole cross term is already \(O(T^{5/6}\log^2T)\). [Exact receiver](../../../formal/GaloisForLFunctions/RHTower/ZetaThreeQuartersOfPrimeSurplus.lean).

The best approach is to prove this **one signed weighted functional**, with its own normalization, rather than demand a full Hardy–Littlewood asymptotic for every prime pair. Organize the calculation so the Poisson/main-term cancellation occurs before absolute values. A one-sided upper sieve bound does not control a kernel with both signs. A different test profile is legitimate only after deriving its own census receiver and all end corrections; profiles from distinct certificates cannot be mixed.

The trans-threshold programme makes this more concrete. At sufficiently small coalescent aperture, actual contributing primes are odd and their shifts are even. The exact decomposition is

\[
S_{\rm actual}=S_{\rm parity\text{-}stabilizer,Q}
+D_{\rm centered,Q}.
\]

The Ramanujan model already retains the negative Ward–Mertens repulsion. The open arithmetic input is the **signed centered discrepancy on actual prime pairs**, together with the errors transferring the model's additive-shift calculation to the logarithmic weights and taper of the census. Modulus two is locked to the Poisson baseline, so treating it as an independently oscillating mode loses the actual structure. This is a more precise research object than “better pair correlation.” It is not yet a bound for the complete bandwidth-\(4/3\) surplus. [Parity-sensitive transfer and exact discrepancy](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/ParitySensitiveRamanujanStabilizerTransfer.lean).

The smaller \(70\%\) target, \(E(1/9)\le4\), is a useful first demonstration of such arithmetic control. It would establish an actual gain across bandwidth one. It is not automatically the \(75\%\) input. [Exchange rate](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/NarrowStripClosePairEnergyAndExchangeRate.lean).

There is a second, complementary route through horizontal displacement. In a common height window write

\[
N=N_0+2(R_{\rm shallow}+R_{\rm deep}).
\]

With the exact multiplicities and shifted Cauchy energy retained, \(R_{\rm shallow}\le hE_h\). A budget

\[
hE_h+R_{\rm deep}\le N/8
\]

would give \(N_0\ge3N/4\). The corresponding \(70\%\) budget is \(3N/20\). Present results give \(O(N)\), not these constants. Increasing the shallow depth reduces the deep tail but increases the prefactor \(h\); the tradeoff must be optimized jointly. [Shallow-energy implications](../../../formal/GaloisForLFunctions/ShallowCauchyPrimeEnergy/ShallowCauchyImplications.lean), [census algebra](../../../formal/GaloisForLFunctions/RHTower/XiWardSourceWindowMultiplicity.lean).

A promising new observable would retain a **confluent horizontal channel**: reflection divided differences or horizontal jets before reflected pairs are merged into one ordinate. Such an observable must have an arithmetic upper bound and a price for each remaining off-line pair. Taking more ordinary value moments does not repair the documented mimicry. Normalizing a divided difference by an arbitrarily small displacement may itself be expensive; that price is part of the research problem.

The quartic \(16/21\) model gives another potential mechanism, but actual wider-frequency signed Gram moments and column normalization are missing. It should remain a parallel target, not be cited as a zeta proportion. Near-line \(75\%\), simple-or-critical \(88.76\%\), and critical-line \(75\%\) are three different statements.

## 6. Three open questions to prioritize

### Q1. What is the full signed low-energy operator when atoms begin to overlap?

First formalize the fixed-profile separated corollary proposed above. Then derive a source-faithful Schur complement at touching and at a fixed ratio \(c>1\), keeping the actual prime term, Gamma contribution, and both pole moments.

**First success:** a uniform positive bound on the relevant remaining block for an explicitly specified overlapping family, or an exact classification of the new low-energy modes. **RH objective:** extend a valid sign mechanism to a family known to exhaust the source, such as the existing growing-overlap receiver. **Failure criterion:** the argument merely retains the prime-only margin, changes the form by a positive correction, or proves convergence separately for each fixed conductor.

This question directly feeds RW, HF, ACS, AIP, SRT, CHMD, and their shared machinery. It makes use of the newest spectrum results rather than restarting the narrow-window calculation.

### Q2. Can one microscopic signed prime-pair functional be bounded with the census constant?

Target \(E(1/9)\le4\) as the first crossing, and the complete bandwidth-\(4/3\) prime surplus \(\le1/18+o(1)\) as the \(75\%\) goal. Keep horizontal displacement visible when translating between zero and prime sides.

Use the parity-adjusted stabilizer decomposition to isolate the arithmetic discrepancy. **First success:** a signed estimate for the selected weighted correlation with the required one-sided census constant. A two-sided error estimate would suffice but is not logically necessary. **Failure criterion:** an unsigned majorant, a near-line count, or moments of an abstract sine-kernel model are substituted for that actual functional.

This target is weaker than excluding every exceptional zero and has an exact, substantial numerical payoff. It is also a testing ground for the signed correlation tools needed elsewhere.

### Q3. Can arithmetic bound the annular source-work increment below its quartet quantum?

The precise target is

\[
\mathscr W(2R)-\mathscr W(R)\le\frac{39}{50}
\quad\text{for all sufficiently large }R.
\]

The receiver and depth-independent lower quantum are already proved. The question is whether the difference of the two damped Laurent-source sums admits an arithmetic upper bound, retaining Gamma corrections, multiplicity, and exterior fields. Subtract at the source level before estimating; separate estimates for the two large work terms would erase the gain being sought.

**First success:** a bound for this actual annular source expression that improves the present growing majorant, with explicit dependence on \(R\) and uniform removal of the outer height taper. **Breakthrough:** an eventual bound by \(39/50\), proving finite support and hence Lindelöf; a bound at every \(R\ge4\) would prove RH. **Failure criterion:** the upper estimate assumes finite support, drops the exterior field, or only controls zeros whose horizontal depth exceeds a fixed cutoff.

This is an exclusion question that remains sensitive to arbitrarily shallow exceptions. It gives the finite-support programme a specific analytic task instead of another equivalence to prove. Uniform heat counts and the remaining full-index bound are alternative ways to supply the same conclusion.

These priorities have different payoffs: Q1 attacks the full sign, Q2 offers the clearest measurable proportion gain, and Q3 attacks finiteness without requiring index zero. The fixed-strip detector in §4 remains worthwhile, but its improved exclusion exponent must first be extracted from an actual arithmetic estimate. Stepanov is a model of the independent producer all these questions need: arithmetic creates a count, then a general theorem converts it into spectral control.

## 7. What new field could supply the tools?

**Working name: critical arithmetic correlation theory.** The name is incidental. Much of its foundation already exists in these programmes. Its missing subject would be **rigidity of signed arithmetic correlations at the exact resolution where a nonunitary zero mode becomes visible**.

The central change of viewpoint is to study the arithmetic source and its incompatible-looking structures together. Multiplication gives prime valuations and Euler factors; addition gives residue classes, successor relations, and short differences; the archimedean completion gives a continuum and a functional-equation reflection. Each structure separately admits the wrong models. The desired theorem must use their joint compatibility to force a signed estimate.

This would not be founded by postulating a positive arithmetic Hodge object. That would assume the intended conclusion. Positivity, finite index, or an exclusion exponent must emerge as theorems from independently constructed objects.

The programmes have already built much of the proposed language. The positive collided form can already be recovered uniformly on growing normalized test families from finite arithmetic theta prefixes; its comparison with the off-line defect is missing. [Polynomial-prefix metric](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/PolynomialThetaMetric.lean). On the Möbius gauge orbit the half-power law holds Haar-almost everywhere, while its exceptional set is null and comeager. Genericity does not identify the actual gauge. [Exceptional-set theorem](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheMoebiusExceptionalSetIsComeagerAndNull.lean).

Ordinary integral auxiliary polynomials already produce baseline Chebyshev control. [Stepanov method over the integers](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheStepanovMethodOverZ.lean). An advance in this branch would supply a characteristic-zero replacement for the coefficient-flatness mechanism of Frobenius and prove the resulting quadratic count. This is a proposed source of new tools, not a theorem that every RH proof must use it. Rebuilding existing receivers under a new name would not fill the gap.

### Questions defining the subject

1. **Rigidity:** which exact mixed additive–multiplicative identities distinguish the actual arithmetic source at increasing resolution, beyond identifying it up to a prime gauge?
2. **Signed comparison:** how can those identities bound an indefinite correlation form without discarding the cancellation between primes, Gamma, and poles?
3. **Critical limits:** what topology retains sign, negative index, and escape mass while aperture, conductor, rank, and damping vary together?
4. **Microscopic geometry:** which observable distinguishes a displaced reflected pair from two critical zeros when the displacement is \(O(1/\log T)\), or smaller?
5. **Count production:** what characteristic-zero arithmetic construction supplies a genuine exclusion or count estimate, rather than receiving one?

### Objects and language

| Object | Data it must retain |
|---|---|
| Complete explicit-formula source | Von Mangoldt prime-power coefficients, the Gamma distribution, and both polar functionals, with the corpus's exact normalization |
| Arithmetic correspondence system | Actual integer maps \(n\mapsto an+b\), valuation and residue data, and their compatibility; not arbitrary abstract actions satisfying only ring identities |
| Signed correlation packet | A finite Gram family together with its actual source, test norm, support, conductor, and error terms |
| Pole and conductor coordinates | Distinguished low modes, constraint coordinates, and charge; enough information to distinguish sources with the same scalar gap |
| Remaining source form | The exact form after eliminating paid blocks, preferably as a Schur complement with an explicit common reserve |
| Microscopic divisor data | \((\Re\rho-1/2)\log T\), ordinate differences times \(\log T\), exact multiplicities, and confluent jets when points coalesce |
| Arithmetic escape state | A limit retaining signed correlations and missing mass, rather than only its positive covariance or fixed-coordinate shadow |
| Annular arithmetic work | The difference of two completed source sums, including full exterior fields and its depth-independent quartet charge |

The natural language combines quadratic forms, relative spectra, Mellin/Fourier transforms, arithmetic correspondences, and scale-dependent estimates. One should be able to say precisely whether a theorem controls a scalar trace, an entire quadratic form, a negative index, or only a positive proportion. Those statements have different logical strengths.

### Foundational principles

**Exact source first.** Every transformation carries the original arithmetic coefficients and completion. A corrected positive form is useful only if its correction is identified and paid in the original problem.

**Signed interactions before majorants.** Separate main-term cancellation and reflected contributions before using absolute values. The current census and first-prime remainder show why the order matters.

**One reserve per source.** A comparison theorem records a joint budget for all blocks and scales. Exact commuting projections and Schur complements are promising models; independent blockwise bounds may spend the same Gamma energy repeatedly.

**Rigidity must have quantitative consequences.** Proving that only zeta has certain identities identifies the source. A second theorem must turn those identities into the required estimate. Source uniqueness alone is not a positivity principle.

**Precision has a scale.** A fixed response tolerance can miss a sufficiently remote prime flip. An effective rigidity theorem must specify how its error depends on conductor and aperture, and carry that error into the signed form estimate. Neither exact source identification without an estimate nor a fixed numerical tolerance closes this step.

**Limits must carry the intended invariant.** Pointwise kernel convergence can retain a uniform index bound; arbitrary \(L^2\) convergence of tests need not retain the Weil form. A suitable form-domain or kernel topology must include poles, tails, and escape. The correct compactness statement may be compactness modulo explicit noncompact profiles, not ordinary compactness.

**Resolve tiny defects without assuming a gap.** Off-line depths might approach zero arbitrarily fast. A finiteness or RH theorem cannot depend on a uniform positive horizontal displacement. Statistical results can instead price a depth distribution, provided the remaining shallow mass is retained.

**Produce the estimate from arithmetic.** Integer divisibility, valuation, successor, and functional-equation identities are legitimate starting data. A positive form, bounded index, or square-root count is a desired theorem. The subject must explain how the former force the latter. Its distinctive foundational theorem would be a signed comparison principle using addition and multiplication together, with a quantified remainder absorbable in the original completed source.

**Keep calibration classes honest.** Finite-field curves, prime-sign twins, and Beurling systems test different subsets of the axioms. An impure curve with a curve functional equation is not a counterexample with Riemann's exact degree-one functional equation. Each failed calibration identifies the precise missing condition.

### Research topics with falsifiable milestones

| Topic | First useful theorem | What would be insufficient |
|---|---|---|
| Arithmetic overlap analysis | Identify and control the complete low-energy operator across touching | Positive separated trial vectors alone |
| Mixed prime-action estimates | Joint signed tail bound with one reserve, including commutator errors | Sum of divergent fixed-prime absolute costs |
| Confluent reflection calculus | Arithmetic upper bound for a displacement-sensitive packet that survives coalescence | More ordinary value moments |
| Signed short-difference correlations | Bound the census's actual weighted prime surplus | One-sided sieve majorants or unnormalized model moments |
| Relative spectral response | Transfer source-selective conductor/probe information into a complete-form inequality | Another classification of prime-only gaps |
| Escape and defect compactness | Decomposition with quantified remainder carrying all negative directions | Fixed-coordinate convergence with lost mass |
| Arithmetic exclusion theory | An individual-zero detector with a positive vanishing exponent | A density envelope remaining above one |
| Characteristic-zero count production | A source-built auxiliary object with a proved counting inequality | Assuming quadratic RR/Bézout as a structure field |
| Finite-index dynamics | Uniform total collision flux or a structural bound on the full kernel's negative index | Finiteness at each fixed heat time or aperture |
| Annular source estimates | Arithmetic upper control of \(\mathscr W(2R)-\mathscr W(R)\), eventually below \(39/50\) | A positive pair-kernel identity or an upper estimate assuming finite support |

For a theorem intended to imply RH, the calibration battery should include Liouville, remote prime flips with maximal gap, appropriate small weight perturbations, and the relevant impure models. Its hypotheses must fail somewhere on each applicable countermodel. For a theorem intended only to improve a proportion, demanding that it reject every finite exceptional configuration would be unnecessary.

**The field earns its name by producing estimates.** A convincing first result would be a new signed overlapping-family bound, the \(70\%\) correlation input, or an arithmetic improvement in annular work or fixed-strip exclusion. Another general equivalence between positivity and RH would add organization, but would not supply the missing tool.
