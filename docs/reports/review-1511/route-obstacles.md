# RH routes: current mathematics and closure obstacles

The corpus has one seed — no zero of \`ζ\`, of any Dirichlet \`L\`-function or of any finite-order Hecke \`L\`-function of \`ℚ(ω)\` in \`Re s > 7/8\` [SEEDZETA] [MMD_DIR] [HECKESEED] — and a dense set of exact readings of the zero width \`w = Θ − ½\`, of the number \`κ\` of zeros right of the line, and of the tail of the zero configuration. No unconditional RH closure exists. Every route endpoint needs one of three things: a lever on \`w\` (or a better seed), a uniform exclusion of the finite and shallow off-line configurations, or a faithful realization that uses the Euler product, the exact functional equation, the unit size of the Euler parameters and the integrality of the primes together.

**Scope.** 38 route formulations, 12 candidates and the supporting programmes listed in the frontier map. **Evidence.** Lean statements read in source at checkpoint \`3699ff3a33\` with the working tree of 15 Nov 2026; [S] marks modules the frontier map tags unintegrated, [W] untracked working-tree files, [D] a deduction of this report. Every cited declaration was opened and its statement read ([fact log](../../../logs/review-1511-frontier-facts.md)). No build, compile or axiom audit was run.

**A — work**: an application, assembly, normalization or finite certificate with a known method; it contains no unproved sign, rate or uniformity. **B — open**: no proof in the corpus and no known method. **Excluded**: a stated construction class carries a proved obstruction.

## Shared frontier

**Width (face W).** \`w ≤ 3/8\` is the seed [MMD_STRIP]. The seed is read exactly by many rulers: zero abscissa, Möbius prefix at one height, one unit window, zeros of \`M_X\`, zeta-kernel signal, two-end state [RULERS] [WD] [SIGNAL-WIDTH]; the Weil floor in the logarithmic energy [LOGENERGY]; the neutral-window margin and its doubling factor (best factor \`2^w\`) at polynomial block size [MARGINSINF] [DOUBLING]; the slope loss of the long moments (least loss \`2w\`, loss \`3/4\` unconditional) [SLOPE] [SLOPE34]; the squarefree quotient \`((s−1)ζ)^m/ζ(2s)\` on \`[½, 9/16)\` [SQFRULER]; Weil-lag, prime-log-window, regularized-series and long-moment dictionaries [WL] [SRT] [PBM] [WD-LONG]; the AdS strip [ADS]. A lever on one ruler is a lever on all [MEASURING] [LEVERTRANSPORT]. No lever for \`ζ\` is proved.

**Index (face I).** Some neutral window has \`r\` negative squares iff \`r ≤ 1 + κ\` [INDEXLAW]; real packets attain \`κ\` exactly [INDEX]. Bounded margins ⇔ RH [ACS]; a gap at each cutoff ⇔ RH [GAPRH]. A constant level law, a doubling law with factor one, and the margin law at every positive rate are each RH, and no intermediate growth exists: bounded loss or a positive rate [DOUBLINGONE] [LOSSDICHOT].

**Tail (face T).** AAL fails exactly at a finite top layer [AAL-LAYER]; RH ⇔ ZAL ∧ \`FiniteOffLine → RH\` ∧ Landing [THREEATOMS]. Off AAL the prime-number-theorem error is a finite trigonometric oscillation attained on every late window [FINOSC]; non-attainment on arbitrarily late windows of one ratio gives AAL [NONATTAIN].

**Selection (all faces).** Five world classes each satisfy all but one structure of \`ζ\` and defeat every mechanism that does not use the missing one: Euler worlds without functional equation (no lever bites below \`2/3\`) [EULERWORLD] [TWOTHIRDSWORLD]; cosh models without Dirichlet series (no lever bites) [COSH]; two-sided prime edits with a count rate (the seed fails) [EDIT]; shifted pairs \`ζ(s−a)ζ(s+a)\` with Euler product and exact functional equation but without the Ramanujan bound (no lever bites in \`[Θ, Θ+½) ⊇ [7/8, 1)\`) [PAIRSABS] [PAIRSNOBITE] [PAIRS] [TEMPERED]; prime-2 deformations with Euler product, exact functional equation, passivity and axis unitarity, whose Euler factor at 2 has parameters off the unit circle [P2FACTOR] [ADS-NOGO]. The compact Selberg zeta functions have Euler product and functional equation, and their off-line zeros are exactly the small eigenvalues — archimedean non-temperedness [SMALLEIG]. A local Euler column has its zeros on the line iff it is tempered [EULERCOLUMN]. [D] Every Euler–FE countermodel of the corpus is non-tempered at some place.

## The 38 routes

### Width rulers and receivers

| Route | Available mathematics | A — work | B — closure obstacle |
|---|---|---|---|
| **WL — Weil lag** | For \`0 ≤ σ < ½\`, \`w ≤ σ\` ⇔ each of five deficit, primitive, energy, cross-work and lag bounds at rate \`σ\` [WL]; RH ⇔ the prime lag is positive definite on \`ℝ\` [PRIMELAG]; the seed gives rate \`3/8\`. | Transport an independently proved rate through the five forms. | A rate below \`3/8\`, ultimately \`0\` (P1, P8). |
| **FU — signed scheduling** | RH ⇔ the Möbius-divisor Abel moment is bounded above on any power-gap sampling set [FU]. | Insert a supplied schedule. | A signed bound across advancing windows. |
| **CFC — first clock** | Eventual lower bound of the published first-clock source ⇔ RH [CFC]. | — | The lower bound with prime, archimedean and endpoint terms. |
| **RP — history floor** | RH ⇔ linear floor \`−B(K+2)\` of the head-matched variance defect [RP]. | Head/tail accounting. | A uniform signed defect in the history length. |
| **PA/HJ — Hausdorff** | A calibrated Hausdorff certificate at any positive radius implies RH [PA]. | Finite-height entries. | All-order sign. |
| **MC — Möbius cancellation** | Möbius Hilbert form subpolynomial ⇔ RH [MC]; the zeta-kernel signal is a smoothed Möbius sum and a ruler [SIGNAL] [SIGNAL-WIDTH]; \`M(n) = O(n^β)\` for \`β > 7/8\` [MERTENS78]; logarithmic two-point Chowla [CHOWLA]. | Transfer an estimate between Möbius observables. | Half-power cancellation. The producer class stops at frame centre \`3/5\` [GAUSS] [WALLGEN] and its estimates at the vertex \`7/8\` [VERTEXPOS]; a lever must use the coefficient size [PAIRS]. |
| **SQF — squarefree count** | One-sided \`O_ε(t^{−1/4−ε})\` error for every \`ε\` ⇔ RH [SQF]; pole-freeness of \`((s−1)ζ)^m/ζ(2s)\` on \`Re s > β/2\` ⇔ \`Θ ≤ β\` for \`β ∈ [½, 9/16)\` [SQFRULER]. | — | The sharp one-sided bound, equivalently pole-freeness on \`Re s > 1/4\`; Witt, Brauer and shifted-convolution identities do not supply it [WITTORD] [BRAUERCANCEL] [SHIFTMARGIN]. |
| **TT — Wold covariance** | Bounded directed covariance plus half-diagonal at every \`0 < t < ½\` ⇔ RH [TT]. | Assemble supplied bounds. | Bounds at each fixed \`t\`. |
| **CHMD — prime wave** | Prime wave bounded below ⇔ RH [CHMD]. | Wave/source identities. | Boundedness of the unnormalized wave. |
| **LI — paired Li** | Subexponential lower bound at every rate ⇔ RH [LI]. | Finite Li signs from verified heights. | Uniformity in \`n\`. |
| **PBM — regularized abscissa** | \`Σ(1_P(n) − 1/log n)n^{−σ}\` convergent on \`σ > ½\` ⇔ RH [PBM]. | Seed reading at \`3/8\` [D]. | Convergence on \`σ > ½\`. |
| **RB — Robin** | Eventual Robin inequality on colossally abundant \`n\` ⇔ RH [RB]. | Reductions. | The eventual inequality. |
| **SRT — prime-log windows** | \`Re ρ ≤ ½ + α\` for all zeros ⇔ a one-sided cubic prime-trace floor \`−Kp^α\` on cofinal windows [SRT]; two fixed primes on \`√T\` windows suffice for RH [TWOPRIME]; prime-window non-attainment gives AAL [NONATTAIN]. | Seed reading at \`3/8\` [D]. | The floor at \`α = 0\`. |
| **WD — long moments** | Width read at one height [WD]; two-sided long-moment slope with a common \`K\` [WD-LONG]; the least slope loss of a stage map \`θ ↦ 2θ\` is \`2w\`, loss \`3/4\` holds, loss \`0\` is RH [SLOPE] [SLOPE34]; depth ladder [DEPTHLADDER]; necessary mollifier length [NECLEN]. | Transfer supplied bounds with the exact quantifiers. | A slope loss below \`3/4\`, i.e. a better seed; RH needs loss \`0\` with \`θ\` unbounded. |
| **JAS — joint ancestry** | Dressed PSD at level one ⇔ RH [JAS]; a signal bound \`O(Z^b)\` gives level \`b + ½ + ε\` [SIGNAL-JAS]; ancestry abscissa is \`0\` or \`≥ 1 +\` the largest depth [RULERS]. | Insert supplied bounds. | Level-one sign or half-power signal (P1, P2, P9). |
| **CTF — chronological rows** | RH ⇔ unit-bounded rows reach every tolerance [CTF]; RH ⇔ \`∫ log|ζ(½+it)| dt/(¼+t²) = 0\` [BSY]. | Row/norm identities. | Vanishing-error rows. |
| **PM — physical model** | Strip width \`δ\` of the two-boundary correlator ⇔ zeros in \`Re ρ ≤ 1 − 2δ\`; \`δ = 1/16\` from the seed [ADS]; Bianchi analogue [BIANCHI]; ZAL and AAL as Euler-filtered horocycle rates [HOROZAL] [HOROAAL]. Excluded: causal, Euler, FE, passive, axis-unitary prime-2 deformations, with decay thresholds \`→ 0\` [ADS-NOGO]; such a deformation keeps the \`10⁻¹³\` floor at aperture \`½log 2\` for every \`α\` and stays Weil-positive at aperture \`log 2\` for \`α\` near \`½\` while carrying off-line zeros [P2NYQ] [P2LOG2] [S]. | Transport the seed to every observable. | \`δ > 1/16\` is a better seed, \`δ = 1/4\` is RH; a physical principle must see the non-tempered gate. |

### Complete forms, windows and thresholds (index face)

| Route | Available mathematics | A — work | B — closure obstacle |
|---|---|---|---|
| **RW — restricted Weil** | RH ⇔ canonical potential locally bounded [RW]; the Weil floor in the logarithmic energy is a ruler, rate \`0\` ⇔ RH [LOGENERGY] [LOGENERGY0]; floor \`10⁻¹³\` at \`log 2\` [FLOORLOG2] [S]; step samples carry Weil's form [STEPS]. | Certificates at further apertures. | Every aperture; a finite aperture never separates \`ζ\` from prime-2 deformations [P2LOG2] [S]. |
| **HF — critical half-line state** | RH ⇔ the bare half-line energy is nonnegative ⇔ the Legendre intercept is nonnegative ⇔ the vacuum is the unique occupation-ball minimizer at every \`R\` [HPEQUIV] [S]; off RH an exact first-order Hawking–Page transition at \`W₀ = inf_A windowThreshold(A)\` with a positive latent jump [HPTRANS] [S]; the state is unique up to sign, outer, cyclic, Laplace zero-free on the closed right half-plane [HF] [HF-OUTER] [HF-CYCLIC] [HF-BOUNDARY]; at every \`R\` the minimizer has a positive transverse gap and is Hessian-stable [TRANSGAP] [SADDLE] [S]; whole-space threshold = polar threshold [POLAR]. Excluded: stability, outerness, cyclicity and zero-pressure endpoint competition (the weak endpoint wins with or without RH) as exclusion mechanisms [WEAKEND] [LEGENDRE] [S]. | Domain and weak-equation lemmas. | The sign of the bare energy on the domain (RH). |
| **HAT-C — clocked energy** | Corrected energy + jump tail = Weil form [HATC]. | Keep the jump-tail normalization. | All-aperture lower bound. |
| **TH — theta flag** | The full Hermite flag implies RH [TH]. | Certified finite ranks. | Unbounded degree with signed adaptive heads. |
| **RN — renewal** | RH ⇔ Gamma/polar ≤ prime scaling energy on theta ground profiles [RN]. | — | That inequality. |
| **SZ — Suzuki** | RH ⇔ eventually bounded aligned Gamma-completed energy [SZ]. | Completion identities. | Bounded completed energy. |
| **EWU — even sector** | Even floor \`10⁻¹³\` at \`log 2\` [EVENLOG2] [S]; an explicit degree-14 Gamma comparison is negative [UPPERLOG2] [S]. | Reuse the certificate. | Even sign at every aperture. |
| **OWU — odd sector** | Odd floor \`10⁻¹⁰\` at \`log 2\` [ODDLOG2] [S]. | Parity transfers. | Odd sign at every aperture. |
| **GTA — quartic charge** | Uniform decay of positive quartic charge ⇔ RH [GTA]. | Charge/flag conversion. | Quartic decay. |
| **ACT — one shift** | At any fixed shift, the pole-free variation inequality on even \`C²_c\` profiles ⇔ RH [ACT]. | Fix one shift. | All profiles. |
| **AIP — compensated incidence** | Subexponential compensated cost at every rate ⇔ RH [AIP]. | Keep prime, pole, reflection terms. | Subexponential cost at every rate. |
| **SC — two-prime cone** | Bounded Gaussian-damped coupling on one two-prime cone ⇔ RH [SC]; undamped coupling or prime towers give AAL, and under AAL RH ⇔ ZAL [AKLT]. | Apply the receivers. | The coupling bound. |
| **ACS — arithmetic index** | Margin bounded ⇔ RH [ACS]; gap ⇔ RH [GAPRH] [GAP]; index law [INDEXLAW]; margin rate at polynomial block size = \`w\` [MARGINSINF]; doubling factor best \`2^w\` [DOUBLING]; RH ⇔ doubling factor one [DOUBLINGONE]; a factor in \`(1, 2^{3/8})\` exists iff \`w < 3/8\` [DOUBLING38IFF] [S]; every bounded contact-weight model has the factor \`√2\` [SQRT2] [S]; ratio ladder \`≤ 3\` (\`Q ≥ 2\`), \`< 4\` (\`Q ≥ 3\`) [LOGLADDER] [S]; the first step separates \`ζ\` from the sign twin through the dipole [TWIN] [DIPOLE]. Excluded: gluing data alone — a sub-Euler model agrees with the true window up to any certified cutoff, on every dyadic middle and on both half-windows, and has best factor exactly \`√2\` [SUBEULER] [S]; fixed-rank absolute gluing [RANK-WALL]; bare dilation gap [TREE-GAP]. | Decide the \`Q = 2\` fourth step [FOURTHRED] [S]. | A factor below \`√2\` needs a negative fresh-octave form of order \`√K\` on the obstructing direction [TOPOCTAVE] [TOPJUMP] [S]; that form reads primes in \`(3K, 6K]\`, i.e. the width (P10). |
| **ECP — endpoint characters** | Actual character Grams PSD at every rank ⇔ RH [ECP]. | Finite shapes. | All ranks. |

### Zero geometry, heat, approximation

| Route | Available mathematics | A — work | B — closure obstacle |
|---|---|---|---|
| **LA — Jensen anchor** | Infinitely many real-rooted degrees ⇔ RH [LA]; real-rooted through degree \`31922\` [JENSEN]; \`N_d\` increases to the off-line multiplicity [JENSENCOUNT]; \`N_d ≤ 300√(d log d)\` for \`log d ≥ 6.1·10⁶\` [JENSENBOUND]. | Larger rungs from larger verified heights (computation). | Unbounded degree without heat shift. |
| **ZCG — heat geometry** | RH ⇔ mirror transport at every positive nonbranch time [ZCG]; \`Λ ≤ 9/128\` [NEWMAN]; finite arithmetic actions are heat monodromies [HEAT-FINITE]; whole fibres excluded [HEAT-NOGO]; a proper \`G₊\` forces \`8 | N(t)\` [HEAT-EIGHT]; one isolated double collision off the centre gives \`G₊ = W\` [DOUBLECOLL]; a forward multiple zero off the centre exists [OFFCENTRE]; \`N(t) ≤ 1\` at times accumulating at \`0\` gives RH [HEATUNIT]. Excluded: a heat ruler in the width alone (cosine models of width \`δ\` have heat time \`→ 0\`) [HEATSPACING]. | Exact order two and isolation of one off-centre collision (A3). | No collision at \`0 < t ≤ 9/128\`; a heat ruler using the zero density. |
| **TG — topological gate** | Sub-unit cubic trace norm on every rectangle ⇔ RH [TG]. | Integer winding. | The sub-unit bound. |
| **PTR — cosine shifts** | No exceptional points ⇔ RH [PTR]; strict Laguerre on \`½ < Re s < 1\` ⇔ RH [STRICTLAG]. | Collision detector. | Exceptional points below the Vinogradov–Korobov boundary. |
| **HCF — heat sampling** | Two prime-log grids at fixed offsets ⇔ RH [HCF]. | Certified finite degrees. | Every degree. |
| **XN — Newton discs** | Self-mapping line-centred discs covering every zero ⇔ RH [XN]. | Self-map conclusion. | The discs. |
| **BAG — self-return** | Cutoff-uniform head-target density on every disc ⇔ RH [BAG]; power-many separated self-returns exclude a zero at the disc centre [GRADEDRET]. | Target identities. | Target recurrence. |

## The 12 candidates

| Candidate | Available mathematics | A — work | B — obstacle |
|---|---|---|---|
| **SEC** | Time-one Gamma-jet Fock boundedness on the divisor ⇔ RH [SEC]. | Finite jet identities. | A \`ζ\`-selective bound. |
| **CDC/BSH** | A nonescaping priced dark history places a zero on the line [CDC]. | Check a supplied history. | One arithmetic history. |
| **S3** | The return transfer ⇔ RH with no premise [RETURNRH] [S3COND]. | — | No content beyond RH. |
| **APF** | \`Ξ\` zeros at real labels ⇔ vanishing cap-grade traces [APF]. | Finite reconstruction. | Exhaust the complex divisor. |
| **EGC** | Contour count error \`≤ 32ε² log T/T\` [EGC]. | Horizon choice. | A horizontal locator. |
| **EWJ** | Norm exhaustion iff \`c = 0\` or \`−a + b + 2d = 0\` [EWJ]. | Depth compression. | A norm-exhausting source. |
| **FEL** | Bounded theta-history information [FEL]. | Entropy transfer. | An arithmetic conclusion. |
| **IRK** | Finite free resolution of the \`ξ\` clock [IRK]; the Steinberg quotient is two square-zero sectors [STEINBERG]; the scalar regulator kernel is classified [REGULATOR]; inverse-unit cycles vanish and positive pairs span only the diagonal [CYCLICSOURCE]. | Finite modules and jets. | Projectivity or descent; analytic trace = Chern charge [LOCAL-GLOBAL]. |
| **MSC** | Squarefree partition has \`ξ\`'s order on \`½ < Re s < 1\` [MSC]. | Divisor bridge. | Normality or sign. |
| **RFHM** | Excluded: all-prime reversible sewing [RFHM]. | — | A nonreversible law. |
| **W1C** | RH ⇔ \`ξ\` is a limit of real entire functions with \`≤ 1\` right zero [W1C]; a realization of the right zeros with a form positive on a hyperplane gives RH [INDEXONE]. | Limit theorem. | Independent approximants. |
| **WBF** | Determinants are coefficient-blind; Grams recover magnitudes [WBF]. | Magnitude recovery. | Phases. |

## Supporting programmes

| Programme | Established | Open |
|---|---|---|
| **MMD / FCT / CRF (producer)** | The seed [SEEDZETA] [MMD_DIR] [HECKESEED]; the degree-two Artin character of \`ℚ(∛2)\` carries it [ARTINSEED] [S]. Estimate ladder: the published geometry is a vertex at \`7/8\` [VERTEXPOS]; rescaled scales \`(17/48, 479/1000, 1001/6000)\` have budget boundary \`20999/24000\` with every high-side exponent negative, and the true vertex of the budget lies in \`(40535/46328, 20999/24000]\` [TRUEVERTEX] [FARKAS] [S]; low probe, reflected energy and principal comparison exist at these scales [LOWPROBE] [REFLENERGY] [PRINCCOMP] [S]; the design floor is \`13/15\`, reached with the count \`U^{1−δ}\` in every bin [VERTEXFLOOR] [BALANCED]; Cauchy–Schwarz models have floor \`5/6\`, a pre-Cauchy–Schwarz saving \`s\` gives \`5/6 − s\` [SAVING] [LOWBARRIER]; low estimates through the twists return the zero [TWISTRETURN]; every rung \`13/15, 5/6, 3/4, 2/3, ½\` transfers to \`ζ\` and all Dirichlet \`L\` [LADDERTRANSFER]. Excluded: rank-two (\`A₂\`) multiple Dirichlet series in convexity, Perron, Kubota-pole and squared-row forms, all boundaries \`> 7/8\` [A2CHAIN] [A2REJECT] [A2DOUBLE]. Frame ladder: completed Gauss pairings \`≥ 3/5\` [GAUSS] [MIXED] [WALLGEN]; the Möbius sign prices a monomial at \`k/2\` at some place, short monomials exactly at \`k/2\`, and towers on that line have values in \`(½, K/(2(K−1))]\` [SIGNCOST] [SIGNPRICE] [SIGNLINE] [PRICEABOVE]; the cubic frame is a ruler \`Θ_corr = (3 + Θ_rung)/6\` [RUNG] [RUNG3148]. Extraction: averaging kills the target [AVERAGE]; a nonprincipal filter recovers it at mean-square cost \`1 + ‖Y‖²\` [TARGETFILTER] [ROWTARGET] [W]. | Closure at \`20999/24000\` (nonprincipal high-side transport, common probe, zero exclusion); the count \`U^{1−δ}\`; a pre-Cauchy–Schwarz saving; a completion on the sign line at period \`≥ 7\`. |
| **EDCS (exponent dynamics)** | Rulers, levers, walls, worlds as Lean objects; margin, doubling, slope, log-energy, frame and squarefree rulers; five world classes [RULERS] [MARGINSINF] [DOUBLING] [SLOPE] [LOGENERGY] [RUNG] [PAIRS] [COSH] [EULERWORLD] [EDIT]. | Any lever. |
| **ZeroForcingCalculus** | An off-line zero forces exactly its quartet [QUARTETFORCE]; quartet-symmetric, real-zero-free configurations closed under right-zero descent or right doubling lie on the line [DESCENT] [RDOUBLE]; left doubling admits a finite off-line defect at \`Re ρ = 3/4\` [LEFTDOUBLE]; rational Euler identities, Brauer relations and shifted convolutions force nothing [WITTORD] [BRAUERCANCEL] [SHIFTMARGIN]; band-forcing and covering-lever receivers [BANDFORCE] [COVERLEVERS]. | A forcing law for \`ζ\` without coincidence. |
| **AAL / ELT / FFA / WZC** | Finite top layer; three atoms; landing TFAE; cofactor reduction; finite oscillation and non-attainment receivers; world-I edit; fake-edit defects do not decay [AAL-LAYER] [THREEATOMS] [LANDING-TFAE] [COFACTORS] [FINOSC] [UNITGAPAAL] [WORLDI] [EDITDEFECT]. | ZAL, \`FiniteOffLine → RH\`, Landing; prime-weighted cofactors. |
| **ACS / AGZ / GCW / WTZ / MAFT** | Index law, gap and margin criteria, ladder, Green calculus, top-octave locality: contacts \`k ≥ 3K+2\` act only on the end-to-end block of a doubled window [TOPLOCAL] [S]; floor-map operator norm \`2Λ(k)/√k\` [FLOORNORM] [S]; an \`O(√K)\` shift kills every negative square of every bounded-weight window [SHIFTKILL] [S]; pole capacity [POLECAP]. | \`Q = 2\` fourth step; the fresh-octave form. |
| **AHD / CACT** | Hawking–Page phase law, stability, Legendre intercept [HPTRANS] [SADDLE] [LEGENDRE] [S]; thresholds and critical multiple [POLAR] [CRITICAL-SMALL]. | The sign of the bare energy. |
| **GTZ (Galois theory of zeros)** | Fields, orbits, quartet/width/ordinate criteria, reflection lift ⇔ purity, square-class parity, finite-window heat comparison [REFLECTION] [QUARTET] [CONJCENTRAL] [SQREL] [HEAT-FINITE]; isolated off-line quartet: radicand negative at every prime, square-class ⇔ no partial flip, trace factorization with the swap \`a ↔ it\`, Klein action when a critical zero shares the ordinate [REGIMEA] [PARTIALFLIP] [TRACEFACTOR] [KLEIN]. | Sign of \`G₊\`; a restriction on conjugation. |
| **F₁ / Kummer calibration** | Contact conductors, Witt boundary, logarithmic self-pairings [CONTACT] [WITT] [DIAGONAL]; Kummer function fields: parity classification, maximal count \`#C = Q² + 1 + 2Qg\`, Cartier vanishing after one constant-field period [KUMMERPARITY] [KUMMERMAX] [KUMMERCARTIER] [S]; Artin completions, Brauer induction [ARTIN] [BRAUER]. | A \`ζ\`-compatible positivity transfer; global index theorem. |
| **AdS / thermodynamics** | Dictionary, prime-2 no-go, finite-aperture nonseparation [ADS] [ADS-NOGO] [P2LOG2] [S]; thermofield realization [THERMOFIELD]; endpoint competition [THERMO]. | A principle that sees gate temperedness. |
| **Census / density** | \`0.67250071\` simple critical [CENSUS]; positive proportion of odd-multiplicity critical ordinates [ODDPROP]; runs of five simple critical zeros [FIVERUN]; multiplicity envelope from the seed [MULT]; density \`30/13\` [DENSITY]; positivity cannot certify \`70%\` [SEVENTY]. | Pair correlation beyond bandwidth one. |
| **Heat / off-line constraints** | An off-line zero gives \`Λ ≥ δ²/(200 log γ)\` above \`e^{1600}\` [NEWMANLOW], flattens \`ζ\` at the centre [FLATTEN]; a positive heat threshold places an off-line zero below an explicit height [HEATLOC]; RH ⇔ integer lag inequality for every \`n ≥ 2\` [INTLAG]. | A structural lower bound for any gap quantity. |

Walls: [wall ledger](walls-ledger.md). Faces and bridges: [unification ledger](route-unification-ledger.md). Tasks, research questions and programmes: [summary](obstacles-summary.md).

<!-- source references -->
[A2CHAIN]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L504
[A2DOUBLE]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L779
[A2REJECT]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L696
[AAL-LAYER]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33
[ACS]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis.lean#L505
[ACT]: ../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/SingleShiftCompleteness.lean#L177
[ADS]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheEternalAdSPrimeMarkedDictionary.lean#L884
[ADS-NOGO]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L1600
[AIP]: ../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheCompensatedRemainderOfTheFullLedger.lean#L878
[AKLT]: ../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/PrimeTowersAndConeCouplingProduceAsymptoticAbscissaLaw.lean#L306
[APF]: ../../../formal/GaloisForLFunctions/RHTower/PaperPrimeFredholmReconstruction.lean#L39
[ARTIN]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/EveryArtinLFunctionHasACompletionWithAFunctionalEquation.lean
[ARTINSEED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheArtinFunctionOfTheCubeRootsOfTwoCarriesTheSeed.lean#L147
[AVERAGE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheAverageRowIsBlindToTheTarget.lean#L148
[BAG]: ../../../formal/GaloisForLFunctions/RHTower/ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip.lean#L294
[BALANCED]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L541
[BANDFORCE]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/ExpandingForcingLawsRulersAndTheRiemannHypothesis.lean#L154
[BIANCHI]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/EternalBianchiBoundaryDictionaryAndWardObstruction.lean#L469
[BRAUER]: ../../../formal/GaloisForLFunctions/RHTower/Artin/ArtinBrauerInductionTheorem.lean#L206
[BRAUERCANCEL]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L497
[BSY]: ../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorCriterionEquivalence.lean#L217
[CDC]: ../../../formal/GaloisForLFunctions/RHTower/XiSourceHistoryPriceEscape.lean#L140
[CENSUS]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean#L1042
[CFC]: ../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockTailLowerBoundCompleteness.lean#L1089
[CHMD]: ../../../formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L385
[CHOWLA]: ../../../formal/GaloisForLFunctions/LogarithmicChowla/LogarithmicChowlaTheorem.lean#L90
[COFACTORS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheGrowingFilterReachesPolynomiallyManyCofactors.lean#L1
[CONJCENTRAL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ConjugationIsCentralAtAZeroIffItsOrdinateValueLiesInThePrimeTraceField.lean#L279
[CONTACT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheConductorOfTwoGraphsIsTheirContact.lean#L22
[COSH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L142
[COVERLEVERS]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/ExpandingForcingLawsRulersAndTheRiemannHypothesis.lean#L352
[CRITICAL-SMALL]: ../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveAtACriticalMultiple.lean#L145
[CTF]: ../../../formal/GaloisForLFunctions/RHTower/ChronologicalRiemannEquivalence.lean#L414
[CYCLICSOURCE]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerCyclicSourceClasses.lean
[DENSITY]: ../../../formal/GaloisForLFunctions/RHTower/PrimeShortIntervalsSeventeenThirtiethsUnconditional.lean#L25
[DEPTHLADDER]: ../../../formal/GaloisForLFunctions/SelectiveArithmetic/TheCancellationAndDepthLadder.lean#L67
[DESCENT]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/TheClosedConfigurationsOfHalvingAndDoubling.lean#L431
[DIAGONAL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean#L268
[DIPOLE]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheDipoleOfWeilsGreenMatrixCarriesTheFirstOverlapStep.lean#L364
[DOUBLECOLL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L162
[DOUBLING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L217
[DOUBLING38IFF]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L772
[DOUBLINGONE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheLossOfTheMarginIsBoundedOrPolynomial.lean#L81
[ECP]: ../../../formal/GaloisForLFunctions/RHTower/Representation/EndpointCharacterCriterion.lean#L62
[EDIT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L186
[EDITDEFECT]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/TheWorldOneScenarioTable.lean#L38
[EGC]: ../../../formal/GaloisForLFunctions/SquareRootThreshold/EffectiveHorizons/TheEGCContourIsExplicit.lean#L139
[EULERCOLUMN]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/RamanujanIsRealityOfAnEulerColumn.lean#L91
[EULERWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L81
[EVENLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtApertureLogTwo.lean#L4149
[EWJ]: ../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthCompression.lean#L48
[FARKAS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheTrueVertexBelowSevenEighths.lean#L328
[FEL]: ../../../formal/GaloisForLFunctions/RHTower/PaperThetaObservationHistory.lean#L1
[FINOSC]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/ThePrimeNumberTheoremIsNotAttainedOnWindows.lean#L68
[FIVERUN]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/ConsecutiveSimpleCriticalZeros.lean#L350
[FLATTEN]: ../../../formal/GaloisForLFunctions/ArithmeticDiscreteness/TheDepthOfAnFEPairIsReadOnTheLine.lean#L113
[FLOORLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize.lean#L48
[FLOORNORM]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean#L97
[FOURTHRED]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L310
[FU]: ../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorOneSidedPowerGapBootstrap.lean#L596
[GAP]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheBoundRangeEndsOnlyWhereTheGapOfTheBoundWindowsCloses.lean#L308
[GAPRH]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheGroundEnergyOfAnApertureIsAGapOfEveryWindowInsideIt.lean#L408
[GAUSS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L595
[GRADEDRET]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/Recurrence/GradedSelfRecurrence.lean#L151
[GTA]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean#L293
[HATC]: ../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheJumpTailFloorNeedsTheFullArithmeticNormalization.lean#L38
[HCF]: ../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean#L123
[HEAT-EIGHT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation.lean#L165
[HEAT-FINITE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupActsOnContinuedWindowsOfZerosAsHeatMonodromy.lean#L81
[HEAT-NOGO]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupIsAHeatMonodromyOnFiniteWindowsButNotOnAFibre.lean#L62
[HEATLOC]: ../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatThresholdVerificationHeight.lean#L94
[HEATSPACING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeatTimeIsTheWidthTimesTheSpacing.lean#L109
[HEATUNIT]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheHeatFlowHasTheCountOfItsLimit.lean#L60
[HECKESEED]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L602
[HF]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L96
[HF-BOUNDARY]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoBoundaryLaplaceZero.lean#L149
[HF-CYCLIC]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateIsCyclic.lean#L59
[HF-OUTER]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineLaplaceMultiplierIsOuter.lean#L45
[HOROAAL]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheOptimalHorocycleExponentAndEulerAnnihilators.lean#L1107
[HOROZAL]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheOptimalHorocycleExponentAndEulerAnnihilators.lean#L1090
[HPEQUIV]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L352
[HPTRANS]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L440
[INDEX]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheFiniteStratumIsThePacketIndexDichotomy.lean#L85
[INDEXLAW]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheIndexOfTheNeutralPartIsOnePlusTheNumberOfZerosRightOfTheLine.lean#L166
[INDEXONE]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/AnIndexOneRealizationIsAUnitGap.lean#L93
[INTLAG]: ../../../formal/GaloisForLFunctions/RHTower/WeilLagFunctionInteger.lean#L541
[IRK]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPrimeRotationResolution.lean#L25
[JAS]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean#L35
[JENSEN]: ../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenPolynomialsThroughDegree31922AreRealRooted.lean#L21
[JENSENBOUND]: ../../../formal/GaloisForLFunctions/FiniteFreeProbability/NonRealJensenCountBound.lean#L674
[JENSENCOUNT]: ../../../formal/GaloisForLFunctions/FiniteFreeProbability/JensenCountsOffLineZeros.lean
[KLEIN]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L445
[KUMMERCARTIER]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FunctionField/KummerCartierConstantPeriod.lean
[KUMMERMAX]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FunctionField/KummerMaximalCount.lean
[KUMMERPARITY]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FunctionField/KummerParityClassification.lean
[LA]: ../../../formal/GaloisForLFunctions/FiniteFreeProbability/FiniteFreeDeBruijnNewman.lean#L466
[LADDERTRANSFER]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicCoverSpecializationOfTheBindingBin.lean#L344
[LANDING-TFAE]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L145
[LEFTDOUBLE]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/TheClosedConfigurationsOfHalvingAndDoubling.lean#L869
[LEGENDRE]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L212
[LEVERTRANSPORT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L85
[LI]: ../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean#L165
[LOCAL-GLOBAL]: ../../../formal/GaloisForLFunctions/RepresentationLifting/PrimePlaneLocalSplitting.lean#L1
[LOGENERGY]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L428
[LOGENERGY0]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L441
[LOGLADDER]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L322
[LOSSDICHOT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheLossOfTheMarginIsBoundedOrPolynomial.lean#L106
[LOWBARRIER]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L802
[LOWPROBE]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsLowProbe.lean#L1142
[MARGINSINF]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L804
[MC]: ../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean#L219
[MEASURING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L79
[MERTENS78]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L169
[MIXED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L419
[MSC]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmGammaSewnSquarefreeXiConormalBridge.lean#L87
[MULT]: ../../../formal/GaloisForLFunctions/SquareRootThreshold/SechMultiplicityEnvelope.lean#L91
[NECLEN]: ../../../formal/GaloisForLFunctions/ArithmeticProduction/TheNecessaryLengthOfAMollifier.lean#L716
[NEWMAN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L155
[NEWMANLOW]: ../../../formal/GaloisForLFunctions/RHTower/Heat/TheHeatDetectionRateIsQuadraticInTheDepth.lean#L520
[NONATTAIN]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/ThePrimeNumberTheoremIsNotAttainedOnWindows.lean#L151
[ODDLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheOddWeilFormHasAFloorAtApertureLogTwo.lean#L3966
[ODDPROP]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheTwistedMomentGivesAPositiveCriticalProportion.lean#L109
[OFFCENTRE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ACollisionAwayFromTheCentreExistsAtAForwardTime.lean#L625
[P2FACTOR]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L95
[P2LOG2]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L278
[P2NYQ]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L169
[PA]: ../../../formal/GaloisForLFunctions/RHTower/PrimeArchEndpointCalibratedHausdorffRH.lean#L92
[PAIRS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L295
[PAIRSABS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L259
[PAIRSNOBITE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L267
[PARTIALFLIP]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L308
[PBM]: ../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean#L402
[POLAR]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/WholeSpaceCriticalThresholdEqualsPolarThreshold.lean#L256
[POLECAP]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheBindingEnergyOfAWindowIsAtMostItsPoleCapacity.lean#L251
[PRICEABOVE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheGaussPairingsArePricedAboveTheSign.lean#L126
[PRIMELAG]: ../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/ThePrimeLagIsPositiveDefiniteExactlyUnderRH.lean#L52
[PRINCCOMP]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsPrincipalComparison.lean#L3008
[PTR]: ../../../formal/GaloisForLFunctions/RHTower/XiCosineShiftExceptionalPointCriterion.lean#L510
[QUARTET]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheOrbitOfAZeroLiesInItsQuartetIffItsWidthAndOrdinateValuesSolveAQuadraticOverThePrimeTraceField.lean#L281
[QUARTETFORCE]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/TheClosedConfigurationsOfHalvingAndDoubling.lean#L120
[RANK-WALL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize.lean#L929
[RB]: ../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean#L132
[RDOUBLE]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/TheClosedConfigurationsOfHalvingAndDoubling.lean#L549
[REFLECTION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField.lean#L55
[REFLENERGY]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Reflection/SubSevenEighthsReflectedEnergy.lean#L2012
[REGIMEA]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L247
[REGULATOR]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerRegulatorKernel.lean
[RETURNRH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L254
[RFHM]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryAllPrimeReversibleRFHMSewingNoGo.lean#L37
[RN]: ../../../formal/GaloisForLFunctions/RHTower/CCM/CCMThetaGroundRHCriterion.lean#L49
[ROWTARGET]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/PhaseExtraction/TheNonprincipalRowRetainsTheTarget.lean#L46
[RP]: ../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean#L478
[RULERS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L55
[RUNG]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L126
[RUNG3148]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L167
[RW]: ../../../formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/ThePotentialIsLocallyBoundedIffRH.lean#L115
[S3COND]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheReturnTransferIsTheRiemannHypothesisUnderAStrip.lean#L44
[SADDLE]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L660
[SAVING]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L830
[SC]: ../../../formal/GaloisForLFunctions/ArithmeticCouplingTheory/ConeBoundary/GaussianConeKernel.lean#L231
[SEC]: ../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean#L461
[SEEDZETA]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L631
[SEVENTY]: ../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/TotientGridGaussianRegularization.lean#L637
[SHIFTKILL]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean#L542
[SHIFTMARGIN]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L426
[SIGNAL]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalOfTheZetaKernelIsAMoebiusSum.lean#L1
[SIGNAL-JAS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsThePositivityLevel.lean#L165
[SIGNAL-WIDTH]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsTheZeroAbscissa.lean#L212
[SIGNCOST]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMoebiusSignCostsHalfAUnitAtSomePlace.lean#L188
[SIGNLINE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L139
[SIGNPRICE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L97
[SLOPE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L110
[SLOPE34]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L95
[SMALLEIG]: ../../../formal/GaloisForLFunctions/CompactHyperbolicSurfaces/SmallEigenvalueZeta.lean#L25
[SQF]: ../../../formal/GaloisForLFunctions/RHTower/SquarefreeExponentialOneSided.lean#L605
[SQFRULER]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L268
[SQREL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ASquareRelationAmongHeightRadicandsHasAnEvenNumberOfCriticalHeights.lean#L33
[SQRT2]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L149
[SRT]: ../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/PrimeLogarithmicWindows.lean#L145
[STEINBERG]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerPrimeSteinbergObstruction.lean
[STEPS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/StepSamplesCarryWeilsFormOfALipschitzPacket.lean
[STRICTLAG]: ../../../formal/GaloisForLFunctions/RHTower/XiCosineShiftStrictLaguerre.lean#L360
[SUBEULER]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L320
[SZ]: ../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTransitionCoreAlignedGammaCompletion.lean#L380
[TARGETFILTER]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheNonprincipalFilterRecoversTheTarget.lean#L161
[TEMPERED]: ../../../formal/GaloisForLFunctions/RHTower/NonTemperedShiftedZetaPairCountermodel.lean
[TG]: ../../../formal/GaloisForLFunctions/RHTower/FormationAnchoredCubicEndpoint.lean#L220
[TH]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaHermiteTraceFlag.lean#L250
[THERMO]: ../../../formal/GaloisForLFunctions/HTGeometry/Thermodynamics/EndpointSourceSwitch.lean
[THERMOFIELD]: ../../../formal/GaloisForLFunctions/HTGeometry/Thermofield/PrimeLogApplications.lean
[THREEATOMS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68
[TOPJUMP]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L473
[TOPLOCAL]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean#L650
[TOPOCTAVE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L664
[TRACEFACTOR]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L372
[TRANSGAP]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningGlobalTransverseGapAndResponse.lean#L284
[TREE-GAP]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheDilationProcessHasNoGap.lean#L174
[TRUEVERTEX]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheTrueVertexBelowSevenEighths.lean#L109
[TT]: ../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean#L182
[TWIN]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFirstOverlapStepOfWeilsFormFailsForTheSignTwin.lean#L744
[TWISTRETURN]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L780
[TWOPRIME]: ../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/TwoPrimeLocalWindows.lean#L21
[TWOTHIRDSWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L95
[UNITGAPAAL]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/NonAttainmentGivesTheAbscissaLaw.lean#L117
[UPPERLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtApertureLogTwo.lean#L5579
[VERTEXFLOOR]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L499
[VERTEXPOS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L333
[W1C]: ../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/TheIndexIsSemicontinuous.lean#L96
[WALLGEN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L525
[WBF]: ../../../formal/GaloisForLFunctions/HTGeometry/PaperGenealogyFredholmRecovery.lean#L50
[WD]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheWidthIsReadInOneWindow.lean#L85
[WD-LONG]: ../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean#L659
[WEAKEND]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L182
[WITT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/Witt/RaynaudOperatorBoundary.lean#L19
[WITTORD]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L182
[WL]: ../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean#L868
[WORLDI]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerCanBeEditedAway.lean#L136
[XN]: ../../../formal/GaloisForLFunctions/RHTower/XiNewtonDiscSourceMargin.lean#L219
[ZCG]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros.lean#L186
