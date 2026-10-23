# RH obstacles: routine work, open mathematics, and a possible new research programme

**Status at 2026-10-23:** 30 live routes, 18 standalone candidates, and PM's embedded PW-B candidate. No reviewed route has a source-derived closing estimate whose remaining proof is routine. Many exact reductions, local inequalities and classification problems are solved. The outstanding task is to prove an arithmetic estimate or construct an arithmetic object that actually satisfies one of those reductions.

Companions: [complete route and programme report](hard-obstacles.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: the six specified reports, searched and inspected Lean sources, targeted dependency checks, and primary external sources. No other existing Markdown was read. Detailed evidence limits appear in the complete report.

## 1. What “nobody has a solution” can mean here

**B-RH:** a target proved sufficient for RH, often equivalent. RH remains an [unsolved Millennium Problem](https://www.claymath.org/millennium/riemann-hypothesis/), so no accepted unconditional solution is known for these closing targets.

**B-C:** an auxiliary construction or estimate unresolved in the reviewed research. Repository absence does not establish worldwide novelty. Some such questions could yield to existing methods, some need new mathematics, and some will turn out false. They belong in a research list, not a list of internationally certified open problems.

**Just work:** a proof method and its inputs are already available; what remains is a specialization, explicit regularity derivation, supplied-certificate verification, or integration of an existing proof. Explicit formulas, numerical evidence and finite support do not make an unknown inequality routine. A theorem of the form “if this positive realization exists, then RH” is not such a realization.

## 2. All identified “just work” tasks

These tasks improve usable mathematics and proof certification. None is presently a routine last step to RH.

| ID | Task and concrete deliverable | Existing input | What remains outside this category |
|---|---|---|---|
| **J1 — Integrate existing proof sources** | Check leaf imports and transitive axioms; expose completed supporting results through their intended interfaces. Includes the existing odd narrow-bump calibration, signed-gauge, compensation, ACS and SAEI leaves where integration is outstanding. | Proof declarations already present; source hashes and inspection records in the review log. | Completing a missing estimate, treating an uncompiled proof as certified, or assuming a candidate capstone. |
| **J2 — Discharge concrete analytic premises** | For a specified compact smooth source, prove Fourier decay, integrability, collar support and derivative bounds needed by an existing theorem. Record aperture-dependent constants. | Integration by parts, compact support, existing weighted-floor and compactification theorems. | Replacing a logarithmic Fourier or derivative norm by unrestricted `L²` mass, or making constants uniform over an unknown family. |
| **J3 — Apply exact dictionaries** | Translate a specified source/clock/history/row through the proved receiver, allocation, block-energy, index, ghost or fixed-shift identities. Retain all pole, Gamma, boundary and centering terms. | The linked capstones in every route entry; completed RW/SZ sign transfer; CHMD fixed-aperture graph comparison; signed continuation; ACS index. | An unproved converse, global source sign, new density statement, quotient surjectivity, or change of limit order. |
| **J4 — Verify a supplied finite certificate** | Check a concrete rational matrix, path packing, strip budget, moment/Jensen instance, finite graph, Frobenius Gram or coefficient block. Record whether it succeeds. | Exact finite object and a known verification method. | Discovering a successful certificate, promising positivity, or paying its infinite tail. |
| **J5 — Package established damping dynamics** | Integrate the existing real-spectrum draft; connect strong continuity and residue derivatives to uses on their proved domains. | Dense residue span, compact semigroup, source proof of real spectrum `{0}∪{d^(−η):d≥2}`, and formal strong continuity/unbounded-generator results. | A graph-core theorem not checked here, Schauder basis, bounded projections, backward stability, or pronic norm control. |
| **J6 — Evaluate known constants and ranges** | Compute thresholds for a chosen APT window, probe, collar, recovery experiment or actual-row estimate. Include the `17/30` centered-prime range and all its slack/support requirements. | Existing explicit estimates, blind one-tower formulas, finite-shift cost and fixed-support negativity. | Balanced-scale cancellation, sharper cell extrema, larger positivity windows or cutoff-independent recovery. |
| **J7 — Transfer the stronger odd-window constant** | Derive the matching lag corollary at `181/500=0.362` from the proved odd-form theorem and its norm bridge. | The odd positivity theorem; the named lag corollary inspected still uses `0.353`. | An even/all-test theorem at `0.362`, a larger radius, or positivity at all apertures. |

J5's spectrum source is a [Lean draft](../../drafts/pipeline/1-in-progress/thim-bvi-250/pending-lean/ArithmeticDampingCenteredSpectrum.lean), inspected directly, not a paper-proof claim inferred from an unread card. Strong continuity is in [DampingIsStronglyContinuousWithUnboundedGenerator](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/DampingIsStronglyContinuousWithUnboundedGenerator.lean). J7 uses [SchurLendingOddWindowThreeHundredSixtyTwoThousandths](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/SchurLendingOddWindowThreeHundredSixtyTwoThousandths.lean).

Routine work applies across the inventory as follows: finite source/trace/jet candidates use J3–J4; positive-form routes use J1–J4 and J7; cancellation/approximation routes use J1–J3, J5–J6; geometric ACS uses J1, J3–J4. “No route-specific routine task” means the next mathematical obstruction is genuinely unproved, not that more algebra must be manufactured first.

## 3. Solved boundaries that must not be reopened

| Achieved result | Exact scope | Remaining problem |
|---|---|---|
| Explicit universal spline probe and packet receiver | A single specified probe detects all zeros; critical band bound is RH-equivalent. | Bound its actual arithmetic packet. |
| Compact-packet mean-square limit | Under RH/blindness, limit equals the `m²`-weighted energy; optimal packet/Weil comparison equals maximal critical multiplicity. | Raw-field asymptotics and quantitative tails; simplicity is a separate stronger issue. |
| APT critical prime kernel and positive families | Negative limiting prime kernel; fixed-support finite-scale negativity; high blocks, polynomial windows and sufficiently lacunary unions are positive. | Dense adjacent scales, growing-support prime-channel control and a complete-family norm transfer. |
| Physical periodic-signal recovery | Fifth/sixth translated moments; sixth-root stability with cutoff-dependent constant. | Nonperiodic pronic energy and quantitative observation costs. |
| THIM prefix defects and BVI outer compensation | Eventual all-prefix sign; compensated diagonal and predecessor terms bounded at fixed positive damping. | Signed compensated interior energy. |
| Actual arithmetic rows | Fixed-modulus Möbius cancellation; centered-prime unbalanced range up to `Q≤P^(30/17−δ)`; restricted dual-norm savings. | Balanced scales, growing moduli, mass and higher-order tails. |
| Relative compensation | Super-logarithmic relative decay and summable dyadic projection motion. | Absolute critical energy and signed cross-scale payment. |
| Positive-interval core debt | Exact zeta-log-ratio limit, bounded on `0<a≤c`. | Complete signed loss, including covariance and flux. |
| Half-damping kernel law | Exact logarithmic energy of partial pole sums; sharp square-root-log sufficient class. | Other signed sources and actual cofinal small-damping admission. |
| Multiplicative phase diagrams | Constant-prime family, quarter-density negative side, subgroup flips, and oscillatory prime amplitudes have exact stated laws. | General spectra; prime signs/density alone do not decide admission. |
| Damping topology | Dense `c₀` residue span; strong continuity but no norm continuity at zero; unbounded generator; exact receiver first column. | Source-specific pronic estimates; full operator bounds are stronger. |
| Small Weil windows | All tests through `0.3`; odd tests through `0.362`. Joint 2/3 strip costs through `0.575`. | All apertures. The `0.575` result is not complete positivity. |
| Form transfer | RW/SZ completed sign equivalence; CHMD graph/Weil norm equivalence on fixed aperture. | Actual sign; quotient lower bound and whole-quotient landing. |
| Odd bump calibration | Full-energy finite-error theorem on the specified no-axis integer-log lattice. | Origin/axis extension, requested self-energy asymptotic and general continuum transfer. |
| Signed incidence classification | Balanced holonomy characterizes universally lossless local payment; nonlocal paths pay frustrated cycles. | Construct actual arithmetic supersolutions and packed paths. |
| Geometric defect | ACS Hodge defect (excess positive index) equals distinct right-zero count; finite-curve defect equals distinct outer-eigenvalue count. | Independent arithmetic effectivity and zero defect. |
| EGC, MSC, RFHM, PW-B admission | Inner contour cancellation; unweighted squarefree Hilbert source; full-support forward creation; positive-damping action/response. | Exterior sign, positive transport, orientation law, and pre-divisor zero-damping landing respectively. |

These scopes are established by the linked source dossiers in the [complete report](hard-obstacles.md). Solving one of these subproblems does not solve its remaining column.

## 4. Open research, without counting the same receiver repeatedly

### O1 — Critical cancellation of the actual prime and divisor source

**B-RH targets:** a one-sided universal lag/packet bound at every positive exponential slack; linear critical-band energy; a completed Abel-moment upper bound; the literal full-history linear floor; regularized prime-series convergence throughout `Re s>1/2`; the required eventual Robin inequality; or LI's subexponential actual-clock lower floor.

The exact observable and its RH receiver exist. The missing input is signed cancellation after all prime, inherited-history, off-diagonal and endpoint terms are included. PNT savings do not remove the positive exponential rate. Prime-minus-polar compensation now has an explicit `exp(−c√S)` saving but still carries `exp(S/2)` in the translated-source bound. [ThePrimePolarResidualHasTheDeLaValleePoussinSaving](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/ThePrimePolarResidualHasTheDeLaValleePoussinSaving.lean).

**Routes:** WL, FU, RP, PA, LI, JAS, PBM, RB; HF's prime-window branch and EGC's exterior branch. Positive-width improvements are meaningful B-C/partial results. They are not all equivalent numerically: LI measures reciprocal depth, while HF's ceiling exponent is only pinched by the proved width inequalities.

### O2 — Actual critical pronic energy and signed continuation

For actual Möbius energy,

`Eε(T)=Σ_{n≤T} Aε(n)²/[n(n+1)]`, `∂εEε(T)=2Wε(T)`.

The exact continuation budget is

`∫_a^c −2Wε(T)/(1+Eε(T)) dε = log(1+Ea(T))−log(1+Ec(T))`.

For an admitted `c`, an upper bound uniform in `T` is equivalent to admission at `a`. Constants may depend on `a>0`; a uniform bound as `a→0` is not required. Cofinal admitted `a↓0` is **B-RH**. Equivalent concrete fronts are BVI's compensated interior contraction, PM's global Haar approximation and the appropriate CTF approximation limit. [TheAveragedBudgetIsExactlyAdmission](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheAveragedBudgetIsExactlyAdmission.lean); [UniformRenormalizedInteriorEnergyRemainder](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformRenormalizedInteriorEnergyRemainder.lean).

**Unpaid:** the complete signed covariance/flux, an independently constructed comparable adapted energy, and actual-source control of moving tails. Relative projection alignment is already strong; its normalization does not pay absolute energy. Global `W≥0` is false, positive-part loss is unnecessarily stronger, arbitrary drifting origins do not preserve admission, and generic below-half cutoff interchange fails.

**Routes:** MC, PM, CTF; THIM/BVI/ACCE/ACCC/SAEI provide the detailed mechanisms.

### O3 — Growing arithmetic moduli beyond generic dispersion estimates

**B-C:** prove actual-row savings with all conditional means, centering, block masses and higher-order tails at balanced or otherwise uncovered scales. **B-RH** when those estimates pay O1 or O2.

Fixed-modulus cancellation is solved. The centered-prime range is wider than the older `12/7` range, using the `17/30` short-interval input, but still excludes balanced `Q≈P`. Generic Type-II and pronic-window counterexamples use different coefficient classes and different definitions of their exponent parameter. They do not refute additional cancellation of literal Möbius/prime rows. [TheSeventeenThirtiethsWindowWidensTheCentredPrimeRowRange](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheSeventeenThirtiethsWindowWidensTheCentredPrimeRowRange.lean); [Guth–Maynard](https://arxiv.org/abs/2405.20552).

A useful result must say which arithmetic feature beats the generic bound and how its gain survives the modulus/horizon limit. Small improvements inside an already admitted range should not be advertised as critical closure.

### O4 — Complete positivity with one shared signed budget

**B-RH:** all-aperture full Weil positivity, full odd capacity, ACT's all-profile fixed-shift inequality, or AIP's complete shared allocation. **B-C:** a larger finite window, a new sign-changing profile class, or an effective nonlocal certificate.

The remaining problem is to pay all adverse prime interactions, polar terms and signed remainder simultaneously. Local certificates can spend the same favorable mass; signed collars move charges but conserve the complete autocorrelation ledger. A frustrated incidence pattern can be globally positive while no pairwise allocation works. The surviving nonlocal method requires a positive signed supersolution and packed resistance budgets. Constructing those for actual arithmetic, then passing to the complete continuum form, is open. [FrustrationIsPaidAlongCanonicalPaths](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/FrustrationIsPaidAlongCanonicalPaths.lean).

**Routes:** RW, SZ, CHMD, OWU, ACT, AIP, EWU, HF and TT. APT's large positive families help only after a norm-controlled complete-family transfer. Neither repeated finite windows nor unconditional uniqueness of `Λ` establishes its full positivity.

### O5 — Signed sampling, width, clustering and the correct norm

**B-C:** derive an unrestricted mass-normalized floor from width, or prove a signed replacement using on-line compensation. Currently width controls derivative-normalized and logarithmic Fourier-energy floors. Uniform local squared-depth mass gives the sharp plain-`L²` exponent; the available unconditional local estimate still has a height logarithm. The stronger local **count** assumption is not necessary for the proved weighted-depth version. [TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster.lean).

Polynomial interpolation supplies a concrete survivor: on-line companion values pay a depth-weighted derivative at an explicit Lagrange price, with a smooth-source Taylor remainder. Actual ζ requires companion placement, approximation control and summable errors at growing height/aperture. Fixed-aperture compact negativity prevents disappearance of adverse weak limits but gives no aperture-uniform positivity. [OnLineCompanionsPayOffLineDepth](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/OnLineCompanionsPayOffLineDepth.lean).

Even an exact positive-width dictionary would not prove that width is zero. Likewise, multiplicity comparison and zero simplicity must not be smuggled into a packet/Weil norm identification. **Routes:** RW/SRT/ACS, with BiScale and SAEI.

### O6 — Uniformity across rank, degree, height, aperture and damping

**B-RH** at the complete LA/TH/HCF/PA/GTA/JAS receiver; **B-C** for quantitative detection, a larger rank-window regime or sharper finite-precision costs.

The open quantifier is specific: fixed-degree Jensen asymptotics do not control every degree; all ranks in a positive coefficient orthant do not control arbitrary signed vectors; a fixed heat-rank horizon does not detect every possible high zero; per-order moment thresholds need not have a common threshold; one sparse-shell receiver has its precise cofinal conditions. These are distinct failures of uniformity, not one generic “take the limit” task.

Synthetic bounded-aperture positive configurations can have any allowed depth. This proves blindness for that reading on that class. It neither constructs off-line ζ zeros nor forbids an arithmetic argument that excludes those configurations. Source-realizable height/depth/precision bounds remain the central B-C task. **Programmes:** APT, BiScale, SRT, SSIC.

### O7 — A positive carrier with faithful arithmetic landing

**B-C construction; B-RH once its stated landing is proved:** a centered ferromagnetic sequence whose characteristic functions converge to `Ξ/Ξ(0)`; a prime-defined lossless nonlocal product port landing exactly on Ξ; a positive arithmetic Hodge/Sonin realization; or a singular trace/determinant comparison retaining the actual divisor.

Finite positivity is available. W1C's receiver already upgrades compact-real characteristic-function convergence to complex convergence using Lee–Yang/Montel; no extra off-real growth hypothesis needs to be invented. PTR's lossless-product equivalence has a converse built from zeros under RH; it does not supply a prime-defined producer. Trace-class transport conflicts with the source's trace-ideal capacity; `det₂` is the surviving language. Positive Poisson transport is exact but does not preserve real zeros for arbitrary inputs. [IsingLawConvergenceRH](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean); [PhotonicLosslessProductPortRH](../../../formal/GaloisForLFunctions/RHTower/PhotonicLosslessProductPortRH.lean).

**Routes/candidates:** HF, RN, TG, MSC, PTR, W1C, WBF, and parts of EWJ/IRK/SC. Changed architecture must retain arithmetic source data, not just a desired spectral output.

### O8 — Independent orientation of a divisor-sensitive diagnostic

Several exact expressions vanish precisely on the line: SEC's seam/Fock diagnostic, HJ's prime-2 reflection residual, BSH's radial curvature, CDC's calibrated descent. Others reconstruct the right-zero count, Ward cap, Fourier cycle traces or source index. Their diagnostics are solved.

**B-C producer; B-RH at complete forcing:** prove their required vanishing, contractivity, descent or sub-unit budget from data defined independently of the unknown zero positions. Evaluating a formula at an actual zero is legitimate and does not assume RH. Circularity enters only if the desired line property is inserted into the proposed producer's hypotheses or carrier definition.

**Routes/candidates:** WD, TG, APF, BSH, CDC, HJ, SEC, IRK, SC, RFHM, PCS, EWJ, PW-B and WBF. These share a construction requirement; no theorem identifies all their missing producers with one another.

### O9 — Recurrence, root continuation and complete contrast balance

**B-RH:** actual ζ self-return on every required right-strip compact, global strict-right root continuation, or the complete zero-sensitive Jensen/contrast equality. **B-C:** the particular arithmetic tail, monodromy, likelihood or head-to-tail coupling needed to produce it.

BAG local recurrence is already equivalent to nonvanishing at the base point. Nonvanishing-target universality and recurrence after removing the local divisor do not cross that obstruction. DR has genuine all-level dyadic roots on a symmetric zero-free cusp, but the cusp boundary tends toward `Re s=1`, not `1/2`. FEL's entropy/reveal accounting is correct without forcing its residual to vanish. [ZetaRecurrenceAtEveryPointModuloItsZeros](../../../formal/GaloisForLFunctions/RHTower/ZetaRecurrenceAtEveryPointModuloItsZeros.lean); [XiSymmetricLittlewoodZeroFreeCuspDyadicRoots](../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean).

### O10 — Arithmetic effectivity producing the Hodge inequality

**B-RH:** construct RR-compatible ample/Bézout effectivity for the actual ACS scaling surface. The exact intersection/Weil identity and Hodge-index receiver are established. Merely asserting the needed effectivity structure restates the endpoint.

**B-C:** discover a coupled pole/test incidence geometry with an independent RR mechanism. Positive graph cones fail RR; Witt integrality, functional equation and positive integral Euler data coexist with impure golden Beurling spectra. A universal subshift ceiling is also incompatible with the stated nontrivial unitary spectrum class. [TheScalingSurface](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheScalingSurface.lean); [BezoutEffectivityAndTheBeurlingObstruction](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BezoutEffectivityAndTheBeurlingObstruction.lean).

This is a sharply formulated arithmetic-geometry construction problem. It may eventually produce O4; no checked theorem currently turns a nonlocal path budget into RR effectivity or vice versa.

### Programme-task crosswalk

The [complete report](hard-obstacles.md) retains every programme task individually. This table groups them without erasing auxiliary questions.

| Topic | Programme task IDs |
|---|---|
| O1 | BS-1/6; SR-1/4/5; AI-6; ACCC-5; source signs in WL/FU/RP/PA/LI/JAS/PBM/RB/EGC |
| O2 | THIM-1; BV-1/3/4; CE-1/2/3/4; ACCC-1/2/3; SAEI-4 |
| O3 | BV-2/6; ACCC-5; THIM-4/7 where actual-row asymptotics are required |
| O4 | APT-1/2/3/4/6; THIM-3; AC-1/2/3/4/6/7; AI-1/2/3/4/5; CE-5; ACCC-4; SAEI-1/2; SCG-1; SI-4 |
| O5 | BS-2/7; CE-6; SR-3; SAEI-3/5; BV-5; SI-5 |
| O6 | APT-5/7/8; BS-3/4/5; THIM-2/4/5/6/7; AC-5; SR-2/4/5; SI-1/2/3/5/6; LA/TH/HCF/GTA uniformity |
| O7 | Positive carrier constructions in HF/RN/TG/MSC/PTR/W1C/WBF; relevant EWJ/IRK/SC landing |
| O8 | Pre-divisor producers and exact vanishing budgets in the candidates listed above |
| O9 | BAG/DR/FEL; arithmetic recurrence tail and contrast/monodromy tasks |
| O10 | ACS-1/2/3, and their proposed bridges to O4/O5 |

Not every item must be solved to prove RH. One complete B-RH producer suffices. Conversely, solving all routine J tasks does not discharge a B-RH estimate.

## 5. Would this require a new field of mathematics?

**No such necessity is established.** The walls rule out specified mechanisms or expose missing estimates; they do not prove that existing analysis, analytic number theory, spectral theory or arithmetic geometry cannot provide them. Established approaches already demonstrate how different languages can encode RH: the [Báez–Duarte approximation criterion](https://arxiv.org/abs/math/0202141) and [Suzuki's screw-function criteria](https://arxiv.org/abs/2206.03682) are examples. More equivalent languages alone would not resolve the source estimate.

The corpus nevertheless suggests a coherent possible programme: **arithmetic compensation geometry**. This is a proposed research direction, not an established discipline or a claim of novelty. Its purpose would be to explain how arithmetic correlations pay signed spectral defects across scales while preserving the exact norm, source and limiting process. Its analytic and geometric branches could develop separately; no current theorem says they form one theory.

### 5.1 Objects and language

| Object | Data the theory must retain | Question it enables |
|---|---|---|
| Arithmetic incidence complex | Divisibility edges, prime powers, shared residues, horizon and logarithmic scale; signed couplings and cycle holonomy. | Which nonlocal arithmetic paths can pay frustrated interactions without reusing the same energy? |
| Compensated source state | Actual centered prefix, pole density, Gamma contribution, boundary flux, projection coefficient and transverse residual. | When does excellent relative alignment yield bounded absolute critical energy? |
| Comparable energy family | `Hε(T)` comparable to `1+Eε(T)` with a source-defined corrector and signed integrated work. | Which arithmetic correction cancels adverse excursions without concealing them in an unrelated norm? |
| Filtered form/index object | Complete Weil form, aperture, negative index, local squared-depth mass, and distinct/multiplicity-weighted spectra kept separate. | What can a certificate detect, at what aperture, and what information does it discard? |
| Observation map with priced error | Exact domain, map, compatible fibre, precision and cutoff-dependent stability constant. | Does added information improve a receiver estimate, or merely reconstruct a periodic signal? |
| Arithmetic effectivity structure | Pole plane and test cycles coupled by actual incidence; independent RR/ampleness/Bézout laws. | What source geometry produces Hodge positivity rather than assumes it? |
| Faithful realization | Maps between the arithmetic source and Hilbert/operator/geometric carriers, with explicit norm and divisor transport. | Which positive structures survive landing on the original Ξ/Weil object? |

This language must distinguish three kinds of statement: an identity, a reconstruction theorem, and a bound. It must also expose whether a result is finite, uniform in horizon, cofinal in aperture, or uniform only after fixing damping. Those distinctions are mathematical content, not administrative labels.

### 5.2 Mechanisms and tools worth developing

1. **Nonlocal signed Dirichlet methods.** Extend the sharp frustrated-cycle payment to arithmetic graphs with overlapping paths. Seek source-defined positive supersolutions, effective resistances and packing estimates. The target is a complete form inequality; a generic finite path certificate is only the starting tool.
2. **Compensated energy transport.** Construct correctors from the actual divisor/prime dynamics, using signed work rather than total variation. Prove comparability and endpoint bounds together. The positive-interval core law and dyadic alignment provide explicit pieces; the remaining covariance must be estimated.
3. **Arithmetic short-interval incidence estimates.** Exploit relationships among coefficients unavailable to arbitrary Type-II rows. Retain prime bias, floor jumps and shared residues, then prove estimates uniform in the growing parameters used by the receiver.
4. **Signed sampling and companion interpolation.** Combine on-line positive samples with off-line derivative costs, instead of bounding negative mass in isolation. Develop Paley–Wiener approximation bounds whose errors survive summation over actual zero heights.
5. **Aperture-dependent concentration analysis.** Fixed-aperture compactness is available. A stronger theory should classify how an adverse profile could move, oscillate or concentrate as aperture grows, and price each behavior against arithmetic structure. It must allow positive floors to decay at the required doubly exponential rate.
6. **Spectral arithmetic beyond sign density.** Build a calculus for multiplicative prime patterns that retains amplitudes, frequencies, residues and endpoint logarithmic energy. Constant-sign and one-frequency phase diagrams are calibration cases; the actual Möbius source requires more than fitting one probe.
7. **Effectivity from incidence.** Seek an RR mechanism tied to prime/pole/Gamma correspondences, perhaps through exact sequences or intersection inequalities. Any proposal must explain why graph-cone positivity and integral Euler data are insufficient and what extra arithmetic relation repairs that failure.
8. **Source-preserving limits.** Develop singular or gapless realization tools that preserve the original defect through completion. Strong convergence alone must not be used as trace-norm convergence; a positive integral kernel must not be assumed to preserve real zeros.

These are candidate mechanisms, not predicted theorems. A successful tool may arise entirely within an existing field.

### 5.3 Questions the programme must answer

- What exact relation among actual Möbius/prime coefficients supplies a signed gain unavailable to the known positive twins and arbitrary coefficient rows?
- Which part of the compensated interior energy is controlled by local incidence, and which requires genuinely global arithmetic?
- Can one construct a comparable corrected energy whose integrated loss remains bounded for each fixed smaller damping, cofinally approaching zero?
- Can prime-induced frustration be paid nonlocally with a single conserved budget at every aperture?
- Can on-line companion geometry replace the unproved uniform off-line depth-mass bound without assuming RH or simplicity?
- Which adverse profile types remain compatible with the full prime, Gamma and pole source after all known identities are imposed?
- What additional structure distinguishes a genuine arithmetic effectivity cone from an impure Beurling datum with the same easy axioms?
- Which new information has a quantitatively bounded observation cost, and how does that cost enter the closing inequality?
- Can a positive carrier be constructed before the unknown divisor is used, and can its exact landing be proved in the receiver's topology?

### 5.4 Acceptance criteria

A contribution should identify its precise source, domain, norm, constants and quantifiers; prove rather than package its positivity/cancellation premise; preserve the complete Gamma/polar/prime accounting; and state the arrow into a receiver. A claimed universal theorem must survive the countermodels within its actual hypothesis class. An actual-ζ theorem need not extend to every Beurling system, but it must identify the arithmetic hypothesis excluding an applicable counterexample.

It should distinguish absolute control from normalized control, signed budgets from positive-part budgets, generic operator estimates from one-orbit admission, and zero counting from multiplicity-weighted energy. A proposed geometry should recover finite-curve calibration without declaring arbitrary curve data pure. Lean integration must expose dependencies and contain no unproved analytic input hidden in a structure or typeclass.

Useful milestones short of RH include a new balanced actual-row estimate with a receiver-relevant gain; a nonlocal full-form certificate beyond the current window; a signed mass-floor theorem for a broader explicitly defined configuration class; a source-specific moving-tail estimate; or an independently constructed effectivity structure on a nontrivial arithmetic subcategory. Each needs a theorem describing its exact improvement. Another equivalence, a larger finite computation, or a new name for the same uncontrolled term does not by itself meet that standard.
