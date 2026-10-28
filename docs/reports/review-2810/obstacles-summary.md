# Research frontier: work, open problems and next questions

Status: 28 October 2026. **The main gap is an arithmetic sign or upper bound on a complete source.** Complete-cell transfer, closed positive-section projection, fixed-prime adjunction and sharp overlap obstructions make that gap substantially more concrete. They do not close an RH route.

This summary combines all 31 live routes, 17 standalone candidates and PW-B. [Route-by-route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md). Evidence comes from corpus searches and direct Lean-source inspection; no builds or fresh kernel certification. [Working evidence](../../../logs/review-2810-research.log).

## What the corpus now establishes

There are three principal destinations, not fifty unrelated final problems:

1. **Critical arithmetic bounds:** actual signed prime/Möbius histories, approximation energies, rates, or source-work ceilings.
2. **Complete Weil sign:** full, even, odd, incidence, Hodge, effectivity and atomic formulations, with exact source terms and quantifiers.
3. **Independent forcing constructions:** an arithmetic geometry, operator, dynamics or source law whose independently proved structure supplies one of the first two destinations.

The first two have many exact RH-equivalent receivers. The third has useful objects and exact diagnostics, but no complete independent forcing mechanism. An equivalence between destinations does not construct a bridge between proposed producers.

Five facts determine the current priorities:

- **Source-complete approximation is closed at fixed support.** Complete logarithmic cells and pole-preserving smoothing recover all mixed Weil entries. Their sign remains open. [Transfer](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteWeilSourceTransfer.lean).
- **Signed Haar blocks offer a concrete prime gain.** Working source compresses adjacent-cell interactions to odd-boundary divisibility and bounds prime energy with logarithmic coefficient 1/√2<1 for arbitrary real coefficients. Full archimedean/smoothing, polar and coarse/mixed-scale payment is still missing. [Haar prime bound](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellPrimeBound.lean).
- **Narrow Hodge structure is real but not exhaustive.** Actual narrow-spacing Grams satisfy Hodge/TD with polar payment. Shrinking cells remove vanishing energy; recentered high bands decouple from fixed tests. Beyond spacing, the natural atomic basis has frustrated triangles, ruling out every diagonal nonnegative phase gauge in the stated profile class. [Narrow Hodge](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing.lean), [decoupling](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/MovingArithmeticBandsDecoupleFromFixedTests.lean), [gauge obstruction](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheMetzlerThresholdOfTheOverlapRatioIsOne.lean).
- **Renormalization now has a concrete finite-prime operator.** Its source finite part, complete eigenbasis and compact shifted inverse are known. Fixed-prime valuation potentials pay small-prime tower deficits. Growing-prime/class exhaustion and full Gamma/pole sign remain unpaid. [Adjunction](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSieveOperatorHasTheAdjunctionEigenbasis.lean), [tower payment](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheArchimedeanPlacePaysTheTowerDeficit.lean).
- **Work thresholds distinguish finite exceptions from no exceptions.** Vanishing work increments characterize finite off-line support; a quadratically scaled cofinal bound detects even one remaining exception. No sufficient arithmetic upper estimate is known in the corpus. [Finite support](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/VanishingScaleIncrementsCharacterizeFiniteSupport.lean), [quadratic threshold](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheQuadraticScaleWorkDetectsEveryException.lean).

Working source further classifies the quadratic increment exactly: zero under RH, a finite limit greater than 48 for finite nonempty off-line support, and divergence for infinite support. A finite Weil negative index k forces this quantity eventually above every b<24k. This sharpens the target; it still supplies only classification and lower payment. [Critical-rate trichotomy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalRateClassifiesAllOffLineSupport.lean), [index payment](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalRatePaysEveryNegativeSquare.lean).

## 2.1 Work with established mathematical ingredients

“Just work” means the task can be executed using available mathematics. For a finite sign problem, the guaranteed deliverable is a rigorous enclosure or conditional certificate, not a guarantee that the desired sign is true. No item below includes an unproved uniform extrapolation.

| ID | Concrete task / deliverable | Routes or frameworks served | Boundary of the task |
|---|---|---|---|
| W01 | Build finite complete-cell mixed Grams, including all active prime translations, Gamma, mass and two pole coordinates. | HF, ACS, AIP, RW, SRT | Fixed support and finite probe family; positivity is a separate result. |
| W02 | Instantiate pole-preserving smoothing and explicit L²/L¹/Lévy errors for specified tests. | ACS, HF, AIP, SZ, CHMD | Existing fixed-support transfer, not a uniform growing-aperture estimate. |
| W03 | Compute finite section projections, Schur residuals, radicals and source-kernel cost bounds. | AID, HF, ACS, CHMD | A positive block can be removed exactly; the complement retains negative directions. |
| W04 | Produce a finite width/profile/gauge table distinguishing pure Markov, full Weil, corrected-twist and pole-hyperplane forms. | SSHA, ALG, SRT, OWU, AIP | Certified finite statements; no universal critical ratio inferred from experiments. |
| W05 | Evaluate finite-prime/class counterterms, mixed horizons, Blaschke modes and adjunction energies. | RAPT, ACS, HF | Prime set and class depth fixed; constants retain those dependencies. |
| W06 | Apply sharp prime ceiling, Dirichlet-defect and golden torsion estimates to prescribed finite vectors. | RAPT, AIT, ALG | Prime-only and torsion forms remain distinct from full Weil energy. |
| W07 | Assemble complete seed/drift/history/cross-block/endpoint ledgers for specified schedules. | FU, RP, LI, TT, PA | Exact signed accounting; no claim of cofinal cancellation. |
| W08 | Compute finite Möbius, pronic and Báez–Duarte rows with readout and centered energy reported separately. | MC, PM, CTF, BVI, JAS | Finite-row optimization; no unproved small-damping/global tail bound. |
| W09 | Instantiate known fixed-modulus, below-diagonal, low-LCM and finite-prime dispersion estimates. | MC, RP, PM, CTF, arithmetic compensation | Preserve the allowed parameter range and all endpoint costs. |
| W10 | Translate supplied width/strip/rate estimates between existing receivers, with normalizations stated. | MC, WL, SRT, HF, BVI, AOT | Transport a supplied bound; producing a better bound is research. |
| W11 | Evaluate fixed compact cofactor Grams, effective pole orders and residue costs. | PM, WL, MC | Compact-window classification; no exterior tightness or simplicity assertion. |
| W12 | Certify finite-aperture ground-energy, blind-minimum and shell-relaxation bounds. | RW, EWU, OWU, ACT | A finite window does not decide all apertures. |
| W13 | Extend finite prime-collar and joint allocation bookkeeping with favorable terms and shared reserves retained. | AIP, OWU, ACT, TT | A finite collar calculation may leave an explicit unpaid remainder. |
| W14 | Compute selected heat/Jensen/Hankel heads and both Gaussian prime-log grids; propagate established tail bounds. | LA, TH, WD, HCF | No exchange of degree, height and heat quantifiers; keep ordinary and factorial-normalized coefficients distinct. |
| W15 | Evaluate finite Newton-disc margins, Ward caps, renewal resolvents and projection/transgression traces. | XN, WD, RN, TG | Local certificates, not a covering, all-disc or extinction theorem. |
| W16 | Calculate finite-rank Schur charges and fixed compact recurrence approximations. | GTA, BAG | Rank dependence and possible target-zero exceptions remain explicit. |
| W17 | Enumerate finite Robin/Nicolas extremal ranges and apply established fixed-valuation-defect margins. | RB | No conclusion about increasingly prime-saturated extremizers. |
| W18 | Evaluate theta-prefix zero/defect readings and finite source-work integrals with explicit truncation errors. | CDG, AES, AID, HF, SRT | Detection is computable; its required upper bound is not thereby proved. |
| W19 | Transport exact residual identities among HJ, SEC and HCF; compute finite jets, fibres and seams. | HJ, SEC, HCF | No assumed residual vanishing or all-order Fock boundedness. |
| W20 | Calculate finite cycle traces, framed curvatures, repair defects, rotation-algebra jets and cross-fibre coordinates. | APF, BSH, CDC, IRK, SC | Test proposed source identifications; do not treat calibration as forcing. |
| W21 | Glue roots on established zero-free charts; evaluate corrected contours, finite jet histories and predeclared likelihood contrasts. | DR, EGC, EWJ, FEL | Global continuation, outer orientation and cofinal balance remain research. |
| W22 | Calculate source evaluations, co-shift defects and phase/grade observables in the admitted carriers. | MSC, PCS, RFHM | Preserve the discarded defect; no false intertwining with invertible dilation. |
| W23 | Analyze proposed finite photonic/Ising realizations, certificate streams and admitted cusp actions. | PTR, W1C, WBF, PW-B | Exact finite transfer data; independent Xi landing and uniform-depth limits remain research. |
| W24 | Use known finite-net/cycle recovery and tolerant-incidence bounds on specified energy/support classes. | EWU, HF, BVI, PM, CTF | Keep source-dependent inverse costs; finite injectivity is not uniform coercivity. |
| W25 | Reconcile external theorems/announcements with local statements and constants; identify exact missing imports. | MC, ACG, LA, pair correlation, shared | Literature intake can be completed; acceptance or formalization of a new claimed proof is not assumed. |
| W26 | Instantiate the balanced Haar prime matrix and its signed bound; retain explicit coarse and polar coordinates in finite examples. | ACS, AIP, HF | Prime-only compression is established in working source; uniform full-form payment is research. |
| W27 | Compute fixed-modulus residue/class-function counterterms and their absolute-profile errors. | RAPT, ACG | Unit-residue leading rank is one; no actual-mass bound or growing-modulus uniformity follows. |

Several former work items are already mathematically closed and should not remain on the open queue: compact-support summability in the non-ratio-lag calculation; complete mixed-entry cell transfer; bounded closed-section projection; finite attainment of completed residual index; sufficient shrinking-width atomic synthesis; actual fixed-spacing Hodge/TD and polar payment; sharp golden torsion growth; fixed-prime valuation payment; finite-sieve adjunction construction. Their stronger uniform extensions are listed below.

In particular, **derive interior short-prime alignment from a zero's reserve** is not routine explicit-formula bookkeeping. The known exterior estimate lives at \(\sigma>1\); moving it into the strip requires a new argument retaining poles, zeros and signs.

## 2.2 Open mathematical obstacles and research topics

The table distinguishes RH-equivalent endpoints from intermediate project problems. “Open” describes the current mathematical input, not a claim that an exhaustive search of all mathematics has proved its absence.

| ID | Missing mathematical result | Why existing work stops short | Status / affected routes |
|---|---|---|---|
| O01 | Actual critical-rate signed prime/Möbius cancellation: complete histories, regularized series, pronic energy, or extremal divisor remainder. | Absolute values, fixed periods and separate diagonal estimates retain too much mass or discard cancellation. VK decay does not reach every positive power. | RH-equivalent endpoints; WL, FU, RP, MC, LI, PBM, RB, JAS. |
| O02 | Complete full/even/odd Weil positivity, or source-complete residual/index-zero bound. | Known positive sections leave a complement; source completeness captures negative directions as well as positive ones. | RH-equivalent; RW, HF, SZ, EWU, OWU, AIP, ACS, TT, CHMD, ACT, SRT. |
| O03 | Simultaneous all-degree/all-height sign with the required common heat/shift parameter. | Fixed-order positivity, orthant positivity and positive tails leave arbitrary signed low/head sectors uncontrolled. | RH-sufficient/equivalent receivers; PA, LA, TH, HCF, WD, SEC. |
| O04 | Cofinal admission, tightness or vanishing global approximation error as damping tends to zero. | Local completeness and compact residue laws allow mass to escape to the origin, high height or growing order. | RH-equivalent endpoints; PM, CTF, MC, EWJ, PCS. |
| O05 | Uniform all-prime/class finite-part control in a source-compatible exhaustion, including Gamma and both poles. | Fixed-Q spectra and fixed-class asymptotics do not control changing carriers, mixed terms or growing constants. | Project research problem; a successful full-sign version would close HF/ACS/AIP. |
| O06 | A signed overlap mechanism beyond the narrow stability regime. | Pure Markov positivity already fails within part of the separated regime; beyond-spacing diagonal Metzler gauges are impossible. | Intermediate full-Weil bounds are unresolved; sufficiently complete all-coefficient positivity is RH-equivalent. |
| O07 | Arithmetic upper bounds on work/index/field at a sufficient threshold. | Quantization proves a lower cost of exceptions; computing that cost does not bound total work above. | Bounded work or vanishing increments would prove finite off-line support; stronger stated thresholds prove RH. HF, ACS, SRT. |
| O08 | Selection of actual arithmetic signs from gauge-sensitive data, with usable moving-scale correlation estimates. | Typical-gauge cancellation, coefficient norms and leading polar matching admit other gauges. Polynomial charged-cell counts do not control the full signed form. | Project research; MC, PM, CTF, AIP, RAPT, ACG. Fixed-form Chowla has a separate external claim. |
| O09 | A source-side mechanism controlling the particular ordinates of possible off-line zeros. | Density/proportion results and power-saving alignment counts still permit exceptions; the current conductor horizon misses the forcing range. | Project research leading to RH/strip bounds; HF, WL, SRT, OWU, pair-correlation programmes. |
| O10 | Independent arithmetic effectivity, polarization, orientation or pre-divisor descent. | Counts and identities can hold for impure models; calibrated descent or invariant positive forms can encode the desired conclusion. | Unconstructed producer; ACS, HF, TG, BSH, CDC, APF, IRK, SC, WBF. |
| O11 | A faithful spectral/physical/dynamical realization with an independently proved forcing property. | Existing finite carriers have capacity/gap obstructions; some converses use unknown Xi zeros; positivity may not imply real spectrum. | Unconstructed producer; RN, XN, PTR, W1C, RFHM, PW-B, MSC, PCS. |
| O12 | Rank-uniform transverse decay or actual all-point self-recurrence. | Fixed-rank convergence and zero-free-target recurrence leave the exact exceptional directions untreated. | RH-equivalent endpoints; GTA, BAG. |
| O13 | Stronger auxiliary conjectures: full simplicity, certain residue-summability budgets, matching-profile signed pair surplus and stronger uniform correlations. | These assertions are not supplied by RH alone or by current proportions; their exact strength differs. | Separate research. Use only when their benefit justifies a stronger target. |

These are shared obligations. A new name for O02, O04 or O10 does not constitute a new route unless it provides a different arithmetic producer.

### External status that changes the queue

RH remains [unsolved](https://www.claymath.org/millennium/Riemann-Hypothesis/). However, the September 2026 [quasi-RH manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) claims the Dirichlet zero-free half-plane \(\Re s>7/8\). This is an external claimed proof, not a local theorem or a result verified by this review. The fixed \(7/8\) target belongs in literature reconciliation; moving all the way to \(1/2\) remains the RH frontier.

The September 2026 [ordinary two-point manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) claims logarithmically saving **ordinary fixed-affine-form** Liouville correlations. Its stated constants need not be uniform for growing forms. Thus “natural two-point Chowla has no proposed solution” is inaccurate, while the moving-profile, modulus and horizon estimates needed here remain unpaid. The established [logarithmic theorem](https://arxiv.org/abs/1509.05422) is a different input.

Published [Lorentzian theory](https://arxiv.org/abs/1902.03719), the [0.22 de Bruijn–Newman upper bound](https://arxiv.org/abs/1904.12438), and [simple-critical-zero proportion results](https://arxiv.org/abs/2609.02882) should likewise be separated from local formalization coverage and from stronger desired consequences. None licenses a silent upgrade to all-degree real-rootedness or zero exceptions.

## 2.3 The three questions to answer next

<a id="q1"></a>
### Q1. What arithmetic inequality makes the complete-cell residual nonnegative beyond narrow spacing?

**Exact object:** the original full Weil form after projection onto an already positive narrow section, or the corresponding Schur residual in a complete logarithmic-cell Gram. The projection and mixed-entry approximation exist. The remaining sign is exposed rather than hidden in a domain problem.

**First useful answer:** a genuinely new, coefficient-uniform full-Weil bound on a specified family crossing the narrow regime, with an explicit remainder paid by actual arithmetic data. State exactly how the tested family grows and whether it approaches an RH-complete schedule. A finite computed example, positivity of a different repaired form, or a new sufficient conditional criterion is not this answer.

**Concrete starting point:** the working Haar inequality bounds prime energy by \(\sum_a(16+\log(2a+1)/\sqrt2)h_a c_a^2\). Determine whether its logarithmic gain survives the actual Gamma/Lévy smoothing cost and both poles, then identify the coarse and mixed-scale residual. The balanced blocks alone omit source directions; their ordinary mean-zero condition is not a pole constraint. This is a specific candidate input, not an already complete positive family. [Compression](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellPrimeCompression.lean), [bound](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellPrimeBound.lean).

**Required mechanism:** retain signed overlap, successor interactions, Gamma and both pole moments. It may use blocks, Schur complements or nonuniform reserves. It cannot require a diagonal Metzler gauge throughout \(w/\delta_N>1\): that route is obstructed. It also cannot demand unconditional positivity of the pure Markov form.

**Why first:** it uses the most complete existing source realization and gives a common target for RW/HF/ACS/AIP/OWU/SRT. Even a sharply delimited positive extension would identify which genuinely arithmetic term can survive the known local obstructions. [Complete residual](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheClosedSectionHasABoundedWeilProjection.lean), [complete index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean), [overlap obstruction](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheMetzlerThresholdOfTheOverlapRatioIsOne.lean).

<a id="q2"></a>
### Q2. Can finite-sieve adjunction be exhausted in the original source while retaining its positive energy and exact pole/Gamma terms?

**Exact object:** the family \(A_Q\) on \(Q\)-supported integers, together with its source-horizon quadratic form, class polar counterterm and explicit spectral basis. A fixed-Q operator is already constructed; another abstract self-adjoint model would add little.

**First useful answer:** source-compatible maps for growing finite prime sets and class supports, with explicit mixed-form comparison and error bounds on one nontrivial signed source class. Establish what happens to domains, ground modes, polar coordinates and constants. A stronger sufficient answer would control a dense complete-cell class with no unaccounted residual.

**Required mechanism:** prove compatibility; identical-looking eigenvalue labels do not prove it. Pay errors using actual signed mass/energy, not the absolute coefficient budget alone. Fixed-prime valuation payment closes the local deficit, but all-prime exhaustion is a new problem.

The choice of class decomposition matters: working source gives growing-rank valuation counterterms but rank-one unit-residue counterterms at fixed modulus. The latter read only a class function's mean and annihilate the leading term of every nonprincipal character. Removing this leading divergence leaves a signed finite-part problem, not an automatic coercive norm. [Residue law](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheHorizonSeesOnlyTheMeanOfAClassFunction.lean).

**Why second:** this is the strongest concrete arithmetic spectral construction currently available and a plausible source of the inequality sought in Q1. A precise obstruction would also be valuable: it would reveal which part of the original source is lost in the finite-prime model. [Adjunction basis](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSieveOperatorHasTheAdjunctionEigenbasis.lean), [source finite part](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSieveHorizonDefectIsTheAdjunctionOperator.lean), [fixed-prime payment](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheArchimedeanPlacePaysTheTowerDeficit.lean).

<a id="q3"></a>
### Q3. What prime/theta estimate gives an upper bound on scale work strong enough to force finite support, then eliminate the last exception?

**Exact object:** \(\Delta\mathcal W(R)=\mathcal W(2R)-\mathcal W(R)\), computed from the source with all multiplicities and counterterms retained.

**First useful answer:** prove \(\Delta\mathcal W(R)\to0\), bounded total work, or eventual \(\Delta\mathcal W\le39/50\). Each would establish finite off-line support, a substantial intermediate result. It would not prove RH.

An eventual finite upper bound on \(R^2\Delta\mathcal W(R)\) is another exact finite-support criterion. For finite nonempty support its limit is a source height-square moment strictly greater than 48, so the residual finite-exception problem has an explicit nonzero target rather than an unspecified tail.

**RH endpoint:** cofinally \(R^2\Delta\mathcal W(R)\le48\), or cofinally \(\mathcal W(R)\le2\), or the all-scale increment bound. A finite exceptional set escapes the unscaled limit but not the quadratic test.

**Required mechanism:** an upper estimate from actual arithmetic structure. Per-zero lower costs, rarity of large prime polynomials, exterior anti-alignment and a detector that identifies a zero do not provide it. An interior reserve-to-alignment theorem is one possible new research input, not an existing routine transfer.

**Why third:** it offers a distinct route to progress without proving every finite Weil matrix positive directly, and makes the intermediate/terminal distinction exact. [Finite support criterion](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/VanishingScaleIncrementsCharacterizeFiniteSupport.lean), [quantum](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/EveryOffLineQuartetCostsAStrictScaleQuantum.lean), [quadratic endpoint](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheQuadraticScaleWorkDetectsEveryException.lean).

The questions are alternative producers, with Q2 potentially feeding Q1. They are not three jointly necessary lemmas, and none is presented as easier merely because its statement is short.

## 2.4 Would a new field of mathematics be needed?

**No result here proves that a new field is necessary.** A sufficiently sharp arithmetic estimate inside existing analytic number theory could close a receiver. Classical operator theory, Hodge theory, Lorentzian polynomials, renormalization and harmonic analysis already explain much of the corpus. The difficulty is their faithful combination on this particular signed arithmetic source.

A coherent new programme would nevertheless be justified: **signed arithmetic Hodge theory with source-compatible renormalization**. This is a proposed research language, not an established field or theorem. Its subject would be how arithmetic incidence, archimedean singular energy and polar constraints jointly create—or fail to create—an index bound under infinite exhaustion.

### Objects and language

The primary objects should be actual logarithmic-cell, balanced Haar, valuation-class and residue-class source spaces, complete Weil mixed forms, Gamma/Lévy energies and the two pole coordinates. Alongside them belong finite-prime adjunction operators, source-graph domains, signed overlap blocks, successor connections, closed-section residuals and scale-dependent source work. Class decompositions must retain their different counterterm ranks and error norms.

A useful statement would specify five pieces together: **source, form, domain, exhaustion and error currency**. For example, a finite-Q spectral gap is attached to its actual class embedding and full mixed-form comparison, not quoted as an abstract gap. A residual is attached to the projection that produced it. A positivity statement names the pole constraint and coefficient class. This prevents a positive surrogate from silently replacing the original form.

Morphisms should preserve the relevant mixed pairings and pole coordinates, with any failure recorded as an explicit defect. They need not all be isometries or positive maps. The point is to control the defect, not erase it by definition. Arithmetic Hecke dilation, successor transport, refinement and sieve enlargement are distinct operations and should not be conflated.

### Mechanisms worth developing

| Proposed tool | Mathematical purpose | Test against current obstacles |
|---|---|---|
| Signed block Hodge inequalities | Bound negative index without demanding entrywise nonnegative atomic gauges. | Must handle the beyond-spacing frustrated triangle and retain the original Weil form. |
| Source-compatible Schur/adjunction calculus | Pass from positive finite-prime or narrow blocks to a controlled complete residual. | Must pay polar dispersion and nonlinear mixed terms; local hyperbolicity is not additive. |
| Uniform renormalized form convergence | Compare growing prime sets, class depth and horizons in a fixed source topology. | Must prevent ground-mode/domain escape and retain both pole moments. |
| Arithmetic gauge selection | Use successor/non-ratio/finite-part information that coefficient norms and polar density forget. | Must distinguish the relevant competing gauges where a global selector is claimed. |
| Defect-to-work inequalities | Turn arithmetic interaction bounds into upper work/index control. | Must add an upper estimate; quantized lower costs alone are already known. |
| Selective localization | Couple local probes to actual exceptional ordinates without losing the signed source. | Must overcome the conductor/forcing gap or replace that detector. |

### Questions such a theory must answer

- Which signed overlap patterns admit an arithmetic index bound even when every diagonal Metzler gauge fails?
- Which finite-prime spectral structures survive enlargement of the prime set in the actual source, and what residual measures the failure?
- How do successor transport and non-ratio lags distinguish gauges at the level of a full form rather than at the level of a coefficient defect?
- What joint inequality pays prime interactions, archimedean self-energy and pole dispersion exactly once?
- What arithmetic monotonicity, conservation or compactness law yields an **upper** bound on source work?
- Can a local estimate be made exhaustive without shrinking away its coupling to each fixed source?

### Criteria for mathematical success

1. **Independent construction.** Start with arithmetic data, not a zero-indexed object whose desired positivity is a premise.
2. **Full fidelity.** Recover actual mixed Weil/prime-theta quantities, including poles, Gamma terms and multiplicities. Clearly separate prime-only, collided and complete forms.
3. **A new inequality.** Supply a paid sign, residual bound, index ceiling or work upper bound. Another identity or equivalent criterion is not sufficient.
4. **Correct exhaustion.** State and prove uniformity in exactly the variables that grow; fixed-Q and fixed-test results are not a substitute.
5. **Selectivity in the claimed domain.** Explain why an impure golden curve, sign twin, synthetic hidden cluster or escaped source cannot satisfy the proposed sufficient hypotheses. Models outside those hypotheses need not be excluded.
6. **Compatibility with known limits.** Recover finite-field polarization and established narrow-spacing/valuation results without demanding the false all-overlap gauge or pure-Markov sign.
7. **Unconditional formal closure.** Any proposed theorem must eventually be formalized with its actual inputs discharged; an assumption binder or interface cannot hide the new mathematics.

The first evidence of a successful theory would be a theorem answering a substantive part of Q1, Q2 or Q3. A new vocabulary, an elegant operator with the wrong source, or a larger catalogue of equivalent RH criteria would not establish it.
