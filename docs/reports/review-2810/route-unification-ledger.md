# Route-unification ledger

Status: 28 October 2026, corpus commit `d47ab4b5d`. **The 31 live routes and 18 candidate branches are faces of three core problems: the selective critical sign (U1), source-complete Weil positivity (U2) and independent faithful forcing (U3).** New this edition: U1 and U2 are joined entry by entry. Every separated off-diagonal entry of the complete Weil form is a centered prime-error integral, so U1 is the off-diagonal of U2. In addition, several routes turn out to be faces of one problem — positivity on Hecke-translation orbits.

[Route obstacles](route-obstacles.md) · [summary and priorities](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [frontier map](../rh-current-frontier-map.md). Evidence: corpus searches and Lean statements; no builds. **[S]** = recent working source (committed on 28 October 2026, or unfinished); per-item status in the frontier map. [Working log](../../../logs/review-2810-refresh-2026-10-28.log).

## What "the same problem" means

| Relation | Meaning | What it does not mean |
|---|---|---|
| **E — Endpoint equivalence** | Two stated conditions are both equivalent to RH, or to each other, in source. | A usable estimate or construction between the producers. |
| **T — Proved source transfer** | An identity, approximation or inequality carries the actual source from one formulation to another, within its hypotheses. | Extension to growing supports, primes, degrees or another norm. |
| **S — Structural similarity** | Two approaches face the same kind of sign, exhaustion or faithfulness problem. | A theorem identifying their objects. |

At the E level all RH criteria are equivalent almost tautologically. Unification is meaningful only through T-bridges and a shared unproved producer.

## The three core problems

| Problem | The one missing statement | Faces (routes) | Wall |
|---|---|---|---|
| **U1 — Selective critical sign** | A bound on the actual signed prime/Möbius discrepancy at the critical scale, in some receiver currency. | WL, FU, RP, MC, LI, PM, JAS, CTF, PBM, RB; work faces of HF/SRT. Via the Chebyshev identity, also the off-diagonal of every U2 route. | 1 |
| **U2 — Source-complete positivity** | Positivity, or index zero, of the complete Weil form, with Gamma and both poles, on a source-complete family. | RW, TT, HF, CHMD, SZ, EWU, OWU, SRT, ACT, AIP, ACS; through exact sign receivers also PA, LA, TH, WD, HCF. | 1 and 3 |
| **U3 — Independent faithful forcing** | A source-built structure whose proved property supplies U1 or U2. | TG, RN, XN, BAG, GTA, all 17 candidates and PW-B; geometric faces of HF/ACS. | 14 |

The walls ask different questions of the same problems: Wall 1 the estimate, Wall 3 its transfer, Wall 14 its source of force. Each core problem meets all three walls.

**One cross-cutting requirement binds all three: selectivity.** Every proved positive family on the complete or atomic source is twin-blind — it also holds for bounded twists \(|\lambda|\le\Lambda\) — while the Liouville twin is not Weil-positive. A producer for any core problem must therefore use a property \(\Lambda\) has and its twins lack. Grouping routes by *where* their selective input enters is the most informative unification.

## Strongest unifications

### A. U1 and U2 meet entry by entry (T, new)

For ordered tests (\(\operatorname{supp}f<b<\operatorname{supp}g\)) and every \(c\) [S]:

\[
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,\Omega'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g),\qquad\Omega_{f,g}(h)=e^{-h/2}\mathrm{corr}_{f,g}(h).
\]

The Gamma tail contains a nonnegative square reserve. The diagonal of the complete form carries Gamma and pole reserves; its separated off-diagonal is the Chebyshev error \(e^h-\psi(e^h)\) tested against correlation derivatives. Hence:

- WL/FU/RP/PBM (prime-error histories) and HF/ACS/AIP/RW/OWU (complete form) ask for the **same signed quantity**, in different test-function norms.
- The pole product, which alone grows across scales, is cancelled exactly by the prime main term. This is the place where \(\Lambda\) differs from the Liouville twin (prime sum \(\approx -e^h\)) and from character twists (\(o(e^h)\)). Finite prime flips keep the main term. They are identified by the prime finite part, where \(\zeta\) is the unique matched maximizer, and they fail positivity only through local witnesses.

[Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean), [square reserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceRetainsItsGammaSquareReserve.lean).

### B. Full Weil sign, parity, incidence, Hodge and effectivity share one complete source (E + T)

RW minimizes the full form; SZ obtains it as a first variation; EWU/OWU are even/odd weight-uniqueness forms; AIP is its joint allocation; ACT reaches its odd sign from one shift; HF/ACS phrase it as Hodge/effectivity/index; TT/CHMD give theta/Doob/wave coordinates. All are E-equivalent, and they share one T-carrier:

- complete logarithmic cells recover every mixed entry;
- smoothing preserves both pole moments;
- complete cells capture every finite index.

That carrier is now a dyadic multiresolution of itself [S]. Average cells are \(\log2\)-translates; Gamma pays every adjacent difference; high details carry a horizon-uniform floor. The common residual is therefore the \(T_{\log2}\)-orbits of finitely many generators (cell 1 and low details) plus cross-level couplings. [Complete transfer](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteWeilSourceTransfer.lean), [Gamma payment](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellVariancePayment.lean), [self-similarity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellCoarseSplitting.lean), [floor](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean).

Pole neutrality, mean zero, oddness and a generic codimension-one constraint remain different conditions. A sign on one hyperplane does not transfer to another by dropping the pole.

### C. Atomic families at every root (T)

SRT, AIP, HF and ACS share one atomic receiver. RH holds iff the full form is eventually nonnegative on atomic families at any overlap growth of finite order — widths \((\log N)^\alpha/N\) for any \(\alpha>0\) [S]. The same transfer law applies to every "stable form". The Markov form is negative at every root unconditionally, and on the pole hyperplane its nonnegativity at every root is RH. The Liouville twin, scalings \(c\Lambda\) and quadratic mixtures are negative at every root. Narrow positivity holds at \(K_\star\delta_N\), where the prime-form defect pays the pole [S]. The proved and the needed regimes are now separated only by bounded versus unbounded polylog overlap. [Every root](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheOverlapLawAtEveryRoot.lean), [gauge](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheGaugeAtEveryRoot.lean), [pole defect](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/ThePoleDefectPaysThePole.lean).

### D. Hecke-translation orbits (S, new)

Six results describe one phenomenon: the behaviour of the Weil form along orbits of a single Hecke dilation \(T_{\log p}\).

| Face | Result |
|---|---|
| ACS self-similarity | Average cell \(=T_{\log2}\)(cell); complete cells are orbits of finitely many generators. |
| SAHT translation escape | \(W\) is constant along every orbit, while the graph norm exceeds every exponential. |
| ALG isometric ladders | Decaying Toeplitz ladders are hyperbolic at all depths iff every finite form is nonpositive; a positive block repeats. |
| ACP Stepanov mechanism | \(1-T_p^N\) annihilates a zero symbol iff the zero is critical and on a height lattice. Sparse auxiliaries vanish to order below their term count. |
| PL / one-prime receivers | One-shift similitude and one-prime strip criteria are RH-type. |
| RAPT one-prime towers | Primitive gap \(p\log p/(p-1)\), equal to \(2\log2\) at \(p=2\) — the conjectured sharp all-prime gap. |

On a single orbit, cross entries are Toeplitz in the orbit index. Their positivity is a one-prime orbit condition, and off-line zeros make the entries grow exponentially. Q1 of the [summary](obstacles-summary.md#q1) asks whether the complete source reduces to finitely many such orbits. This is an S-level unification; the identification theorems belong to the individual modules. [Ladders](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/AnIsometricLadderCarriesNoPositiveSquare.lean), [translation escape](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TranslationPreservesWeilEnergyButEscapesEveryExponentialGraphBound.lean), [Stepanov mechanism](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism.lean).

### E. Möbius admission, Haar approximation and chronological residuals (E + T)

MC, PM and CTF share actual Möbius arithmetic; BVI supplies readout, pronic and rate identities. CTF's residual is \((1-\Lambda\text{-readout})^2+\text{centered energy}\). PM's criterion is positive gauge mass \(\inf_dd\,K(d,d)\) for every escape state. The common unpaid input is complete signed energy at small damping. Record-minimum escape limits have positive diagonals but may still have zero gauge mass. [Visibility criterion](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean), [record minima](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean).

### F. Width, rate, field and work currencies (E + T)

Fixed-strip conditions \(\Theta\le1-\theta\) have many exact readings: escaped Möbius rates, all-test Hecke-defect caps, theta-prefix growth, \(\operatorname{Re}\xi'/\xi\ge0\) on half-planes, and (for \(\Theta<1\)) Vaughan convolution power savings. Source work is stratified:

\[
\text{bounded work}\iff\Delta\mathcal W\to0\iff\mathcal E_{\rm crit}<\infty\iff\text{finite off-line support};\qquad\mathcal E_{\rm crit}\le Q_*\iff\mathrm{RH}.
\]

A finite index \(k\) costs \(\mathcal E_{\rm crit}\ge\max\{I_*k,50k^2-3k/2\}\), a quantitative T-bridge between U1 work and U2 index. The thresholds \(2\), \(39/50\) and \(Q_*=1294047/2000\) belong to different normalizations and are not interchangeable. [Vaughan strips](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean), [canonical energy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean).

### G. Heat, Jensen, Ward, moment and seam formulations (E + T)

LA and WD share finite-head/heat coefficient geometry; TH and HCF expose moment/grid signs; PA exposes all-order passivity. HJ's reflection residual equals SEC's seam charge, and all-divisor vanishing matches HCF's two-grid sign. The Xi Jensen family satisfies Laguerre on \(s\ge0\); Lorentzian closure is exactly the nonnegative-Hessian class. None of this supplies all-degree real-rootedness. [HJ/SEC](../../../formal/GaloisForLFunctions/RHTower/PrimeTailSeedHurwitzReflection.lean), [two grids](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean).

### H. Adjunction, prime modes and gauge finite parts (T)

RAPT links finite-prime adjunction to the actual prime matrix:

- Ramanujan profiles are quasimodes at \(\log N-E_m\), and fixed packets are actual eigenvalues.
- The prime form has a uniform gap on the pole hyperplane, where Liouville reaches the ceiling.
- Each finite prime set has gap \(2\log2\).
- \(\chi\)-twisted poles read \(2\operatorname{Re}(-L'/L(1,\chi))\) [S]. This ties RAPT's horizon finite parts to the value of \(L'/L\) at \(s=1\), the same object that governs MC/ACG character gauges.
- Among matched sign gauges with convergent Mertens error, \(\zeta\) uniquely maximizes the finite part [S]. This is a selectivity classification of gauges, with \(\zeta\) as the extremal case.

The link to complete-cell positivity stays S until Gamma, both continuous poles and the mode complement are paid. [Spectral packets](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFullPrimeMatrixRealizesFiniteAdjunctionPackets.lean), [twisted pole](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheTwistedPoleReadsTheLogarithmicDerivative.lean).

## Complete live-route crosswalk

"Selective input" names where a \(\Lambda\)-specific property enters, or must enter, the route.

| Route | Core problem / cluster | Distinct producer obligation | Selective input |
|---|---|---|---|
| **WL** | U1; prime-error energy | Adverse cross-work; keep RH apart from genus saturation | Signed \(\psi(x)-x\) (main-term cancellation) |
| **FU** | U1; Abel moment | Entire scheduled history | Signed prime channels |
| **RP** | U1; history floor | High-LCM/moving-core debt | Signed hyperbola/LCM identities |
| **MC** | U1; Möbius cancellation | Moving-scale \(\mu\) at every strict half-power | Actual \(\mu\), not typical gauges |
| **LI** | U1; prime–Gamma floor | Literal primitive with outside terms | Signed clock |
| **PM** | U1; escape visibility | Positive gauge mass for every escape state | Actual Möbius cofactors |
| **JAS** | U1; prime budget | Logarithmic to half-power budget | Prime-product sign |
| **CTF** | U1; approximation residual | Readout and centered energy together | \(-\mu_N\) readout alignment |
| **PBM** | U1; regularized series | Pole-subtracted cancellation to \(\sigma>1/2\) | Actual coefficients |
| **RB** | U1; extremal remainder | Saturated extremizers | Divisor arithmetic |
| **RW** | U2; ground energy | Cumulative aperture relaxation | Must enter the low/polar modes |
| **TT** | U2; odd/covariance | Nonlocal reflected-prime correlation | Signed reflected primes |
| **HF** | U2 + U1 work + U3 geometry | Complete residual sign or work ceiling | Must enter the generator orbits (Q1/Q2) |
| **CHMD** | U2; wave/Doob | Residual sign modulo the Weil radical | Primitive defect |
| **SZ** | U2; first variation | Low/mixed modes on a complete family | Must enter the low modes |
| **EWU** | U2; even blind minimum | All-aperture low/mixed payment | Weight rigidity (\(\lambda=\Lambda\)) |
| **OWU** | U2; odd weight | All-aperture odd sign | Small-radius witnesses; twisted poles |
| **SRT** | U2 + U1 bridge | Sign at any unbounded polylog overlap, or work ceiling | Twins negative at every root; must be used |
| **ACT** | U2; one-shift | One shift paying every profile | Must enter the exterior primes |
| **AIP** | U2; joint allocation | Coarse/cross-level allocation | Must enter the low/cross-level residual |
| **ACS** | U2 + U3 effectivity | RI/height/chirality or complete index zero | Must enter the coarse residual |
| **PA** | U2 (moment); passivity | All-order/all-shift sign | Prime–archimedean trace |
| **LA** | U2 (heat); coefficient signs | All-height/all-degree heads | Xi coefficients |
| **TH** | U2 (moment); Hankel | Signed vectors at common time | Theta moments |
| **WD** | U2 (heat); caps | Cap extinction as heat shrinks | Actual divisor |
| **HCF** | U2 (heat); two grids | Both grids, all degrees | Literal \(\log2\)/\(\log3\) grids |
| **TG** | U3; trace cap | Positive residual and integer trace below one | Euler/Gaussian source |
| **RN** | U3; renewal | Directed boundary work | Theta renewal |
| **XN** | U3; Newton discs | Covering with paid curvature | Xi jets |
| **BAG** | U3; recurrence | Return at every right-strip point | Euler product universality |
| **GTA** | U3; transverse decay | Rank-uniform decay | Theta Schur charge |

**Strongest shared programmes.**

- The U2 complete-source cluster (RW, HF, ACS, AIP, OWU, SRT, CHMD, SZ, EWU) now has one concrete target: the generator orbits and cross-level couplings of the multiresolution.
- The U1 cluster (WL, FU, RP, PBM, MC, PM, CTF) supplies exactly the signed quantity that pays those couplings.
- Heat/moment routes (LA, TH, WD, HCF, PA) keep separate quantifiers and are not reducible to the complete-cell problem without a T-bridge.

## Candidate crosswalk

The 17 standalone candidates and PW-B are U3 producers whose landing is unproved; their family membership is S until a source landing exists.

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
| **SC** | U3→U2; cross-fibre index | Wall value unselected. |
| **SEC** | U3→U2; seam sign | Asymptotic seam smallness is nonselective. |
| **W1C** | U3→real-rooted Xi | No arithmetic ferromagnetic limit. |
| **WBF** | U3→U2; certificates | No arithmetic coupling or uniform-depth landing. |
| **PW-B** | U3→U1; PM complete energy | Zero-indexed action; extinction chain unproved. |

## Unifications that are not valid

| Tempting identification | Correct distinction |
|---|---|
| Every RH receiver is one programme | Endpoint equivalence is E; producers differ. |
| \(W\), the collided form \(D\) and the prime-only form are interchangeable | \(D\) is positive but its invariance is the problem; prime-only forms omit Gamma/poles. |
| Twin-blind positive families can be completed to full positivity | They hold for the Liouville twin, which is not Weil-positive; a selective input is required. |
| Finite-part identification of \(\zeta\) is a positivity input | \(\zeta\) is the unique *maximizer* of the matched prime finite part, hence the hardest member on step profiles. |
| The Chebyshev identity makes U2 easier than U1 | It shows they are the same signed quantity in different norms. |
| Pole products across scales are harmless | They grow like \(2^{\lvert j-k\rvert/2}\) and are cancelled only by the prime main term. |
| Finite negative index means RH | Bounded index means finite off-line support. |
| Vanishing work increments mean no exceptions | A finite exceptional set also has vanishing increments. |
| \(A_Q\) is the Xi operator | Fixed packets are actual prime-matrix eigenvalues, not Xi zeros. |
| All Hodge/TD formulations share one input | Overlap frustrates gauges; Lorentzian closure has an exact restricted scope. |
| Local hyperbolic pieces sum to global hyperbolicity | Mixed terms and polar dispersion must be paid. |
| Narrow sections, complete cells and atomic families are one exhaustion | Narrow sections are positive but non-dense; complete cells capture every index; atomic families are RH-complete only at unbounded overlap. |
| The every-root receiver lowers the difficulty to bounded overlap | Positivity at any fixed overlap ratio is not RH-complete; the receiver needs unbounded (polylog) overlap. |
| Curves over finite fields can donate Weil positivity | The archimedean continuum cannot arise from finite places (walls 14.36). |
| Simple zeros, Chowla and pair correlation are weaker than RH | Logical relations differ; some budgets force RH plus extra assertions. |

## How to organize research around the unification

1. **One complete-source programme** for RW/HF/ACS/AIP/OWU/SRT/CHMD/SZ/EWU, built in multiresolution coordinates (Q1).
2. **One selective-input programme** joining the U1 cluster (signed prime error, Möbius) with RAPT's constrained margins (pole-hyperplane gap, twisted poles) to pay the generator orbits (Q2).
3. **One energy programme** for an upper bound on \(\mathcal E_{\rm crit}\) (Q3).
4. **Independent-construction experiments** for U3, sharing fidelity and selectivity tests without premature identification.

No route is promoted because its final condition was renamed, and no candidate is retired because another route reaches the same endpoint.
