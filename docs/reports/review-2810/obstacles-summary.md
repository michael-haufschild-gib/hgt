# Research frontier: work, open problems and next questions

Status: 28 October 2026. **The main gap is an arithmetic sign or upper bound on a complete source.** Complete-cell transfer, closed positive-section projection, fixed-prime adjunction and sharp overlap obstructions make that gap substantially more concrete. They do not close an RH route.

This summary combines all 31 live routes, 17 standalone candidates and PW-B. [Route-by-route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md). Evidence comes from corpus searches and direct Lean-source inspection; no builds or fresh kernel certification. [Working evidence](../../../logs/review-2810-research.log).

## What the corpus establishes

There are three principal destinations, not fifty unrelated final problems:

1. **Critical arithmetic bounds:** actual signed prime/Möbius histories, approximation energies, rates, or source-work ceilings.
2. **Complete Weil sign:** full, even, odd, incidence, Hodge, effectivity and atomic formulations, with exact source terms and quantifiers.
3. **Independent forcing constructions:** an arithmetic geometry, operator, dynamics or source law whose independently proved structure supplies one of the first two destinations.

The first two have many exact RH-equivalent receivers. The third has useful objects and exact diagnostics, but no complete independent forcing mechanism. An equivalence between destinations does not construct a bridge between proposed producers.

The following results determine the priorities:

- **Complete transfer and a proper projected carrier are available.** Complete cells recover every mixed Weil entry. Fixed widths control the full source graph; the chosen unbounded carrier has a bounded projection, is proper and leaves an infinite null radical in its complement. Residual nonnegativity remains open. [Projection and scope](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheUnboundedCellCarrierHasAWeilProjection.lean).
- **High Haar sections have full-form positivity.** Prime logarithmic cost \(1/\sqrt2\), Gamma coefficient 1 and bounded pole loss give one fixed lower index above which every finite signed Haar section has a unit rough-Weil floor, independent of upper horizon. Coarse and mixed-scale completion remains research. [Full Haar floor](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean).
- **Synthesis and local obstacles are explicit.** Second-order transfer reaches \(w_N=(\log N)^\alpha/N\), \(\alpha>1/4\). Bounded-overlap rows, coverage deficits, Robin–Euler instability and beyond-spacing gauge frustration constrain extensions. [Synthesis](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheSecondOrderSynthesis.lean), [rows](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheRowsAtBoundedOverlap.lean), [stability](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheStabilityRegimeEndsAtTheRobinEulerThreshold.lean).
- **Adjunction has an actual fixed-mode prime bridge.** Ramanujan profiles have asymptotically orthonormal Gram and quasimode energy \(\log N-E_m\), with distinct \(E_m=\gamma+\log m+\operatorname{tameDifferent}(m)\). The assembled declarations are working source. Growing-mode control, complementary energy and full Gamma/pole coupling remain open. [Quasimodes](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanPoleProfilesArePrimeQuasimodes.lean), [distinct energies](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanAdjunctionEnergiesAreDistinct.lean).
- **Constrained prime selectivity is established.** A uniform gap separates Euler/Liouville on the same harmonic pole hyperplane. Their step-profile finite parts also differ by an explicit positive main term, with absolute-profile errors. Neither supplies complete continuous Weil sign. [Uniform gap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin.lean), [finite parts](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFinitePartSeparatesZetaFromItsLiouvilleTwin.lean).
- **Critical work has a canonical monotone limit.** \(K(R)=R^2(\mathcal W(2R)-\mathcal W(R))\uparrow\mathcal E_{\rm crit}\). Finite energy is equivalent to finite off-line support; \(\mathcal E_{\rm crit}\le Q_*=1294047/2000\) is equivalent to RH. Finite Weil index \(k\) costs at least \(\max\{I_*k,50k^2-3k/2\}\), \(I_*=Q_*/2\). Arithmetic upper control is missing. [Canonical energy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean).
- **Generic Lorentzian closure has a precise scope.** It produces exactly entrywise-nonnegative Lorentzian Hessians; the stated prime Ramanujan local factors cannot supply its inputs. Xi Jensen Laguerre inequalities hold on the nonnegative half-line, without full real-rootedness. [Closure](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheClosureProducesExactlyTheLorentzianForms.lean), [local factors](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RamanujanAndLorentzianMeetOnlyAtTheWeilBound.lean), [Xi half-line](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheJensenPolynomialsOfXiSatisfyLaguerreOnTheHalfLine.lean).

## 2.1 Work with established mathematical ingredients

“Just work” means the task can be executed using available mathematics. For a finite sign problem, the guaranteed deliverable is a rigorous enclosure or conditional certificate, not a guarantee that the desired sign is true. No item below includes an unproved uniform extrapolation.

| ID | Concrete task / deliverable | Routes or frameworks served | Boundary of the task |
|---|---|---|---|
| W01 | Build finite complete-cell mixed Grams, including all active prime translations, Gamma, mass and two pole coordinates. | HF, ACS, AIP, RW, SRT | Fixed support and finite probe family; positivity is a separate result. |
| W02 | Instantiate pole-preserving smoothing and explicit L²/L¹/Lévy errors for specified tests. | ACS, HF, AIP, SZ, CHMD | Existing fixed-support transfer, not a uniform growing-aperture estimate. |
| W03 | Compute finite section projections, Schur residuals, radicals and source-kernel cost bounds. | AID, HF, ACS, CHMD | A positive block can be removed exactly; the complement retains negative directions. |
| W04 | Evaluate the explicit bounded-overlap Schur rows and finite profile/gauge Grams, distinguishing Markov, full Weil, corrected-twist and pole-hyperplane forms. | SSHA, ALG, SRT, OWU, AIP | Row control is established; a growing-overlap signed margin is not. |
| W05 | Evaluate finite-prime/class adjunction modes and the fourteen raw tower deficits at primes≤43. | RAPT, ACS, HF | Valuation payment is proved for every fixed prime; all raw tower finite parts are nonnegative exactly at primes≥47. |
| W06 | Apply sharp prime ceiling, Dirichlet-defect and golden torsion estimates to prescribed finite vectors. | RAPT, AIT, ALG | Prime-only and torsion forms remain distinct from full Weil energy. |
| W07 | Assemble complete seed/drift/history/cross-block/endpoint ledgers for specified schedules. | FU, RP, LI, TT, PA | Exact signed accounting; no claim of cofinal cancellation. |
| W08 | Compute finite Möbius, pronic and Báez–Duarte rows with readout and centered energy reported separately. | MC, PM, CTF, BVI, JAS | Finite-row optimization; no unproved small-damping/global tail bound. |
| W09 | Instantiate known fixed-modulus, below-diagonal, low-LCM and finite-prime dispersion estimates. | MC, RP, PM, CTF, arithmetic compensation | Preserve the allowed parameter range and all endpoint costs. |
| W10 | Translate supplied width/strip/rate estimates between existing receivers, with normalizations stated. | MC, WL, SRT, HF, BVI, AOT | Transport a supplied bound; producing a better bound is research. |
| W11 | Evaluate fixed compact cofactor Grams, effective pole orders and residue costs. | PM, WL, MC | Compact-window classification; no exterior tightness or simplicity assertion. |
| W12 | Certify finite-aperture ground-energy, blind-minimum and shell-relaxation bounds. | RW, EWU, OWU, ACT | A finite window does not decide all apertures. |
| W13 | Extend finite prime-collar and joint allocation bookkeeping with favorable terms and shared reserves retained. | AIP, OWU, ACT, TT | A finite collar calculation may leave an explicit unpaid remainder. |
| W14 | Compute finite heat/Jensen/Hankel heads and both Gaussian grids; apply the actual Xi half-line Laguerre inequality and established tail bounds. | LA, TH, WD, HCF | No negative-half-line or all-degree real-rootedness inference; preserve coefficient normalization and common-time quantifiers. |
| W15 | Evaluate finite Newton-disc margins, Ward caps, renewal resolvents and projection/transgression traces. | XN, WD, RN, TG | Local certificates, not a covering, all-disc or extinction theorem. |
| W16 | Calculate finite-rank Schur charges and fixed compact recurrence approximations. | GTA, BAG | Rank dependence and possible target-zero exceptions remain explicit. |
| W17 | Enumerate finite Robin/Nicolas extremal ranges and apply established fixed-valuation-defect margins. | RB | No conclusion about increasingly prime-saturated extremizers. |
| W18 | Evaluate theta-prefix readings, finite source-work integrals and finite canonical pair-energy lower sums with explicit truncation scope. | CDG, AES, AID, HF, SRT | Critical exterior rows belong to the full energy; finite lower sums do not enclose its unknown upper tail. |
| W19 | Transport exact residual identities among HJ, SEC and HCF; compute finite jets, fibres and seams. | HJ, SEC, HCF | No assumed residual vanishing or all-order Fock boundedness. |
| W20 | Calculate finite cycle traces, framed curvatures, repair defects, rotation-algebra jets and cross-fibre coordinates. | APF, BSH, CDC, IRK, SC | Test proposed source identifications; do not treat calibration as forcing. |
| W21 | Glue roots on established zero-free charts; evaluate corrected contours, finite jet histories and predeclared likelihood contrasts. | DR, EGC, EWJ, FEL | Global continuation, outer orientation and cofinal balance remain research. |
| W22 | Calculate source evaluations, co-shift defects and phase/grade observables in the admitted carriers. | MSC, PCS, RFHM | Preserve the discarded defect; no false intertwining with invertible dilation. |
| W23 | Analyze proposed finite photonic/Ising realizations, certificate streams and admitted cusp actions. | PTR, W1C, WBF, PW-B | Exact finite transfer data; independent Xi landing and uniform-depth limits remain research. |
| W24 | Use known finite-net/cycle recovery and tolerant-incidence bounds on specified energy/support classes. | EWU, HF, BVI, PM, CTF | Keep source-dependent inverse costs; finite injectivity is not uniform coercivity. |
| W25 | Reconcile external theorems/announcements with local statements and constants; identify exact missing imports. | MC, ACG, LA, pair correlation, shared | Literature intake can be completed; acceptance or formalization of a new claimed proof is not assumed. |
| W26 | Evaluate a numerical lower-index threshold for the proved Haar full-form floor and instantiate fixed-family pole-preserving smoothing. | ACS, AIP, HF | Rough floor is uniform in upper horizon; complete coarse/mixed-scale positivity remains research. |
| W27 | Calculate fixed-modulus residue/character finite parts and fixed-BV horizon errors using variation budgets and −L′/L(1,χ). | RAPT, ACG | Formula and fixed-profile asymptotics exist; growing modulus/variation and uniform signed mass control remain unpaid. |
| W28 | Instantiate the Ramanujan residual and Gram estimates for a specified finite conductor set; apply the Hermitian residual-to-eigenvalue lemma. | RAPT, HF, ACS | Fixed-mode landing is supplied; no growing-conductor completeness or full-Weil spectral interpretation. |
| W29 | Instantiate fixed-width graph-coercive sections and the unbounded-carrier projection/cost identity on specified sources. | AID, CHMD, HF, ACS | Carrier is proper; its complementary infinite radical prevents a strict residual floor. |
| W30 | Apply the pole-hyperplane prime gap and its Liouville separation to finite source comparisons. | RAPT, AIP, OWU | The discrete harmonic constraint is not automatically the continuous full-Weil pole constraint. |

Established ingredients include complete mixed-entry transfer, fixed-support pole-preserving smoothing, bounded section projection, fixed-width full-graph coercivity, finite index capture, second-order synthesis, bounded-overlap Schur rows, coherent mean-zero Gamma and Haar pole payment, a horizon-uniform high-Haar full-form floor, finite-sieve adjunction, fixed-mode prime transfer, prime pole-gap selectivity, BV/character finite-part laws, and canonical critical-energy monotonicity. Their stated uniformity limits determine the research queue.

In particular, **derive interior short-prime alignment from a zero's reserve** is not routine explicit-formula bookkeeping. The known exterior estimate lives at \(\sigma>1\); moving it into the strip requires a new argument retaining poles, zeros and signs.

## 2.2 Open mathematical obstacles and research topics

The table distinguishes RH-equivalent endpoints from intermediate project problems. “Open” describes the current mathematical input, not a claim that an exhaustive search of all mathematics has proved its absence.

| ID | Missing mathematical result | Why existing work stops short | Status / affected routes |
|---|---|---|---|
| O01 | Actual critical-rate signed prime/Möbius cancellation: complete histories, regularized series, pronic energy, or extremal divisor remainder. | Absolute values, fixed periods and separate diagonal estimates retain too much mass or discard cancellation. VK decay does not reach every positive power. | RH-equivalent endpoints; WL, FU, RP, MC, LI, PBM, RB, JAS. |
| O02 | Complete full/even/odd Weil positivity, or source-complete residual/index-zero bound. | Known positive sections leave a complement; source completeness captures negative directions as well as positive ones. | RH-equivalent; RW, HF, SZ, EWU, OWU, AIP, ACS, TT, CHMD, ACT, SRT. |
| O03 | Simultaneous all-degree/all-height sign with the required common heat/shift parameter. | Half-line Xi Laguerre and generic Lorentzian closure leave the negative-half-line, low/head and arbitrary signed sectors uncontrolled. | RH-sufficient/equivalent receivers; PA, LA, TH, HCF, WD, SEC. |
| O04 | Cofinal admission, tightness or vanishing global approximation error as damping tends to zero. | Local completeness and compact residue laws allow mass to escape to the origin, high height or growing order. | RH-equivalent endpoints; PM, CTF, MC, EWJ, PCS. |
| O05 | Growing-conductor/modal-complement control and full-source convergence, including Gamma and both poles. | Fixed-mode full-prime quasimodes, finite-Q spectra and BV finite parts do not control jointly growing carriers, variation or errors. | Project research; a complete positive version would close HF/ACS/AIP. |
| O06 | Coarse and mixed-scale signed residual payment reaching a complete source or overlap family. | High Haar full-form floors and bounded-overlap rows are proved; coverage, gauge frustration and a proper projected carrier prevent a free exhaustion. | Intermediate extensions unresolved; complete all-coefficient sign is RH-equivalent. |
| O07 | Arithmetic upper bounds on canonical critical energy or other sufficient source-work/index currencies. | Monotone convergence and linear/quadratic index costs are lower-payment laws. Critical exterior rows remain in the energy. | Finite energy gives finite off-line support; energy≤1294047/2000 gives RH. HF, ACS, SRT. |
| O08 | Extend constrained arithmetic gauge selectivity to the source-complete signed form and moving-scale correlations. | The prime pole gap separates Euler/Liouville; leading matching still admits finite flips, and no complete continuous sign follows. | Project research; MC, PM, CTF, AIP, RAPT, ACG. Fixed-form Chowla has a separate external claim. |
| O09 | A source-side mechanism controlling the particular ordinates of possible off-line zeros. | Density/proportion results and power-saving alignment counts still permit exceptions; the current conductor horizon misses the forcing range. | Project research leading to RH/strip bounds; HF, WL, SRT, OWU, pair-correlation programmes. |
| O10 | Independent arithmetic effectivity, polarization, orientation or pre-divisor descent. | Counts and identities can hold for impure models; calibrated descent or invariant positive forms can encode the desired conclusion. | Unconstructed producer; ACS, HF, TG, BSH, CDC, APF, IRK, SC, WBF. |
| O11 | A faithful spectral/physical/dynamical realization with an independently proved forcing property. | Existing finite carriers have capacity/gap obstructions; some converses use unknown Xi zeros; positivity may not imply real spectrum. | Unconstructed producer; RN, XN, PTR, W1C, RFHM, PW-B, MSC, PCS. |
| O12 | Rank-uniform transverse decay or actual all-point self-recurrence. | Fixed-rank convergence and zero-free-target recurrence leave the exact exceptional directions untreated. | RH-equivalent endpoints; GTA, BAG. |
| O13 | Stronger auxiliary conjectures: full simplicity, certain residue-summability budgets, matching-profile signed pair surplus and stronger uniform correlations. | These assertions are not supplied by RH alone or by current proportions; their exact strength differs. | Separate research. Use only when their benefit justifies a stronger target. |

These are shared obligations. A new name for O02, O04 or O10 does not constitute a new route unless it provides a different arithmetic producer.

### External mathematical status

RH remains [unsolved](https://www.claymath.org/millennium/Riemann-Hypothesis/). However, the September 2026 [quasi-RH manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) claims the Dirichlet zero-free half-plane \(\Re s>7/8\). This is an external claimed proof, not a local theorem or a result verified by this review. The fixed \(7/8\) target belongs in literature reconciliation; moving all the way to \(1/2\) remains the RH frontier.

The September 2026 [ordinary two-point manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) claims logarithmically saving **ordinary fixed-affine-form** Liouville correlations. Its stated constants need not be uniform for growing forms. Thus “natural two-point Chowla has no proposed solution” is inaccurate, while the moving-profile, modulus and horizon estimates needed here remain unpaid. The established [logarithmic theorem](https://arxiv.org/abs/1509.05422) is a different input.

Published [Lorentzian theory](https://arxiv.org/abs/1902.03719), the [0.22 de Bruijn–Newman upper bound](https://arxiv.org/abs/1904.12438), and [simple-critical-zero proportion results](https://arxiv.org/abs/2609.02882) should likewise be separated from local formalization coverage and from stronger desired consequences. None licenses a silent upgrade to all-degree real-rootedness or zero exceptions.

## 2.3 The three questions to answer next

<a id="q1"></a>
### Q1. Can the positive high-Haar family control the coarse and mixed-scale residual on a complete source?

**Exact object:** the original full Weil form after removing a paid high Haar block or projected positive section, retaining every mixed entry, Gamma reserve and both poles. The high-Haar rough-Weil floor is uniform in upper horizon. The fixed unbounded carrier has a bounded projection but is proper; its complement includes an infinite radical.

**First useful answer:** a quantitative mixed-block/Schur inequality for an enlarging family that pays cross-scale interactions without spending Gamma reserve twice. Identify the remaining coarse source and treat null directions explicitly. A stronger sufficient answer would prove nonnegative residual on complete cells or a synthesis schedule \((\log N)^\alpha/N\), \(\alpha>1/4\). Strict positivity of the entire graph complement is not a valid target.

**Required mechanism:** retain signed overlap and full poles. Schur rows price a cost to beat; small fixed overlap lacks universal coverage. Beyond-spacing diagonal Metzler gauges and universal all-twist positivity are obstructed. Ordinary mean-zero and exact pole neutrality remain different constraints.

**Why first:** it puts an established full-form positive family against the shared unpaid residual of RW/HF/ACS/AIP/OWU/SRT. Another local Gamma or pole payment does not cross that boundary. [Haar floor](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean), [projection and radical](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheUnboundedCellCarrierHasAWeilProjection.lean), [rows](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheRowsAtBoundedOverlap.lean).

<a id="q2"></a>
### Q2. Can growing Ramanujan mode families and the pole gap yield a full-Weil comparison with a controlled complement?

**Exact object:** \(v_m(n)=c_m(n)/\sqrt{\phi(m)n}\) in the actual finite prime matrix, with energy \(\log N-E_m\), \(E_m=\gamma+\log m+\operatorname{tameDifferent}(m)\). Completed rows, fixed-conductor tails, asymptotic orthonormality, quasimode residuals and distinct energy labels are available.

**First useful answer:** quantitative Gram and residual estimates for an explicit growing conductor set \(m\le M(N)\), plus an upper bound on complementary source energy in the needed norm. Couple conductor growth, class variation and horizon, then compare Gamma and both continuous pole moments on the same vectors. A slowly growing diagonal schedule alone follows from fixed-mode limits; sufficient coverage and a paid complement are the research target.

**Required mechanism:** retain the prime gap's exact harmonic pole constraint. Its Euler/Liouville separation and the explicit finite-part difference have different error norms. BV/character finite parts retain variation/modulus costs. Raw tower sign is nonnegative exactly at primes \(p\ge47\), and valuation potential pays all smaller primes; fixed-prime payment is closed.

**Why second:** actual arithmetic modes offer a spectral producer for Q1. Distinct trial energies are not a complete spectrum, and a growing finite set is not source exhaustion. [Quasimodes](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanPoleProfilesArePrimeQuasimodes.lean), [Gram limits](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanPoleProfilesAreAsymptoticallyOrthonormal.lean), [gap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePrimeFormHasASpectralGapBelowItsPole.lean), [BV laws](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheHorizonLawsHoldForProfilesOfBoundedVariation.lean).

<a id="q3"></a>
### Q3. What arithmetic upper estimate controls canonical critical energy, including its critical exterior rows?

**Exact object:** \(K(R)=R^2(\mathcal W(2R)-\mathcal W(R))\uparrow\mathcal E_{\rm crit}\in[0,\infty]\). Its nonnegative pair-energy representation includes off-line/critical interactions. Entrywise nonnegativity is not a PSD-kernel theorem; the alternative finite-support source moment has signed summands.

**First useful answer:** a finite upper bound on \(K\), equivalently \(\mathcal E_{\rm crit}<\infty\), would prove finite off-line support. Bounded unscaled work, vanishing increments or eventual \(\Delta\mathcal W\le39/50\) also give that intermediate conclusion. None removes a finite exceptional set.

**RH endpoint:** \(\mathcal E_{\rm crit}\le Q_*=1294047/2000\), equivalently cofinally \(K\le Q_*\). Finite nonempty support gives a limit strictly above \(Q_*\); infinite support gives infinity. Other exact endpoints include cofinal \(\mathcal W\le2\) and the all-scale increment bound.

**Required mechanism:** an upper estimate from actual prime/theta structure retaining the complete source and counterterms. Lower costs \(I_*k\) and \(50k^2-3k/2\), \(I_*=Q_*/2\), convert such a bound into an index ceiling but do not produce it. Monotonicity and the canonical limit are established. Interior reserve-to-alignment remains an unproved input.

**Why third:** this is a distinct route to a substantial intermediate theorem, with an exact threshold for excluding the last exception. [Canonical energy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean), [quadratic cost](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSourceBudgetMakesTheIndexCostQuadratic.lean), [classification](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalRateClassifiesAllOffLineSupport.lean).

These are alternative producers: Q2 can feed Q1; Q3 targets a different arithmetic upper bound.

## 2.4 Would a new field of mathematics be needed?

**No result here proves that a new field is necessary.** A sufficiently sharp arithmetic estimate inside existing analytic number theory could close a receiver. Classical operator theory, Hodge theory, Lorentzian polynomials, renormalization and harmonic analysis already explain much of the corpus. The difficulty is their faithful combination on this particular signed arithmetic source.

A coherent new programme would nevertheless be justified: **signed arithmetic Hodge theory with source-compatible renormalization**. This is a proposed research language, not an established field or theorem. Its subject would be how arithmetic incidence, archimedean singular energy and polar constraints jointly create—or fail to create—an index bound under infinite exhaustion.

### Objects and language

The primary objects should be actual logarithmic-cell, balanced Haar, valuation-class and residue-class source spaces, complete Weil mixed forms, Gamma/Lévy energies and the two pole coordinates. Alongside them belong finite-prime adjunction operators, actual Ramanujan pole quasimodes and their complements, fixed pole hyperplanes, source-graph domains, signed overlap blocks, successor connections, closed-section residuals and canonical critical energy. Its off-line/critical exterior interactions are part of the object. Class decompositions must retain their different counterterm ranks and error norms.

A useful statement would specify five pieces together: **source, form, domain, exhaustion and error currency**. For example, a fixed-conductor quasimode carries its actual residual and Gram error; a growing-mode claim must also control its complement. A pole-gap statement names the fixed hyperplane and the Gamma/pole comparison still required. A residual is attached to the projection that produced it. A positivity statement names the pole constraint and coefficient class. This prevents a positive surrogate from silently replacing the original form.

Morphisms should preserve the relevant mixed pairings and pole coordinates, with any failure recorded as an explicit defect. They need not all be isometries or positive maps. The point is to control the defect, not erase it by definition. Null radicals must be retained or quotiented through a proved form-preserving map; they cannot be treated as negative energy or forced into a false strict floor. Arithmetic Hecke dilation, successor transport, refinement and sieve enlargement are distinct operations and should not be conflated.

### Mechanisms worth developing

| Proposed tool | Mathematical purpose | Test against current obstacles |
|---|---|---|
| Signed block Hodge inequalities | Combine paid Haar/Gamma blocks with coarse and mixed-scale residuals. | Must allocate shared reserve once and handle frustrated overlap in the original Weil form. |
| Source-compatible Schur/adjunction calculus | Compare actual Ramanujan modes, finite-prime adjunction and complete residuals. | Must control growing-mode Gram/residual errors, modal complements and polar dispersion. |
| Uniform renormalized form convergence | Compare growing prime sets, class depth and horizons in a fixed source topology. | Must prevent ground-mode/domain escape and retain both pole moments. |
| Arithmetic gauge selection | Extend the fixed pole-hyperplane prime gap to full signed-source control. | Must preserve the established Euler/Liouville separation while addressing other gauges and continuous pole constraints. |
| Defect-to-work inequalities | Bound canonical critical energy above from arithmetic. | Must retain critical exterior rows and add upper control beyond known monotonicity and index lower costs. |
| Selective localization | Couple local probes to actual exceptional ordinates without losing the signed source. | Must overcome the conductor/forcing gap or replace that detector. |

### Questions such a theory must answer

- Which signed overlap patterns admit an arithmetic index bound even when every diagonal Metzler gauge fails?
- Which growing families of actual Ramanujan quasimodes control a complete source, and what energy remains in their complement?
- How do successor transport and non-ratio lags distinguish gauges at the level of a full form rather than at the level of a coefficient defect?
- What joint inequality pays prime interactions, archimedean self-energy and pole dispersion exactly once?
- Which arithmetic conservation, cancellation or compactness law bounds the established monotone critical energy **above**, including its critical exterior rows?
- Can a local estimate be made exhaustive without shrinking away its coupling to each fixed source?

Generic Lorentzian closure alone cannot be this theory: its Hessian class is already exactly characterized, and the stated Ramanujan local polynomials are inadmissible inputs. A useful arithmetic construction must supply signed/block geometry or a faithful change of coordinates with its defects paid. The actual half-line Xi Laguerre law is a consistency check, not the missing all-degree real-rootedness theorem.

### Criteria for mathematical success

1. **Independent construction.** Start with arithmetic data, not a zero-indexed object whose desired positivity is a premise.
2. **Full fidelity.** Recover actual mixed Weil/prime-theta quantities, including poles, Gamma terms and multiplicities. Clearly separate prime-only, collided and complete forms.
3. **A new inequality.** Supply a paid sign, residual bound, index ceiling or work upper bound. Another identity or equivalent criterion is not sufficient.
4. **Correct exhaustion.** State and prove uniformity in exactly the variables that grow; fixed-Q and fixed-test results are not a substitute.
5. **Selectivity in the claimed domain.** Explain why an impure golden curve, sign twin, synthetic hidden cluster or escaped source cannot satisfy the proposed sufficient hypotheses. Models outside those hypotheses need not be excluded.
6. **Compatibility with known limits.** Recover finite-field Gram polarization, paid Haar/Gamma estimates, the fixed prime pole gap and established narrow-spacing/valuation results without demanding the false all-overlap gauge or pure-Markov sign.
7. **Unconditional formal closure.** Any proposed theorem must eventually be formalized with its actual inputs discharged; an assumption binder or interface cannot hide the new mathematics.

The first evidence of a successful theory would be a theorem answering a substantive part of Q1, Q2 or Q3. A new vocabulary, an elegant operator with the wrong source, or a larger catalogue of equivalent RH criteria would not establish it.
