# RH routes: mathematical status and closure obstacles

The corpus contains many exact RH criteria, substantial arithmetic production, and quantitative finite-window theorems. It contains no unconditional RH closure identified by this research. The main distinction is between **constructing an arithmetic input** and **proving that this input would imply RH**. Most routes have the second theorem.

This report covers 38 named routes, 12 candidates, and supporting programmes. “Proved” refers to Lean declarations inspected for their statements, binders and relevant dependency interfaces; no fresh compilation or exhaustive transitive kernel audit is claimed. Evidence is recorded in [the fact log](../../../logs/review-1411-facts.txt), [corpus search records](../../../logs/review-1411-evidence.jsonl), and [source declarations](../../../logs/review-1411-source-declarations.jsonl). Existing reports supply route names, not mathematical authority.

**Classification.** **A — work:** applications of available theorems, exact finite algebra, normalization, or a specified classical construction with no new estimate. **B — research:** an unavailable arithmetic estimate, uniformity theorem, exclusion principle, or source realization. An RH-equivalent condition belongs to B. An unproved finite-window estimate also belongs to B until its proof is known. “Open” means unresolved in the audited corpus; for RH-equivalent targets, RH remains an established open problem. It does not assert an exhaustive survey of every unpublished result. [Clay's RH status](https://www.claymath.org/millennium/Riemann-Hypothesis/)

## Shared mathematical frontier

### Arithmetic production

The MMD detector supplies an unconditional source theorem excluding ζ zeros in `Re s > 7/8`, hence placing nontrivial zeros in `1/8 ≤ Re s ≤ 7/8`. Its family results cover Dirichlet characters and the specified cubic Eisenstein Hecke family; they are not an arbitrary-number-field GRH theorem. This is an input available to routes requiring a fixed strip strictly narrower than the critical strip. [MMD]

For the formalized Möbius-signed Gauss-monomial pairing class, uncoupled constructions stop at `2/3`; coupled constructions stop at `3/5`. The coupled optimum is attained at completion order three and probe order six, with the reduced equality case classified. Changing monomial order or arity within this class is not an open escape route. This is a restriction on that producer architecture, not a universal lower bound for arithmetic cancellation. [GAUSS]

Decompletion is a concrete survivor: for every `σ > 1/2`, a sufficiently large finite prime cutoff makes the uncompleted correction holomorphic and nonzero on `Re s > σ`. The missing input is a usable reflection/reciprocity law with a controlled boundary defect, followed by an actual signed estimate. Nonvanishing of this correction is not the missing theorem. Averaging that removes the target and reciprocal target does not supply such an estimate. [DECOMPLETE] [PHASE-WALL] [AVERAGE]

Logarithmic two-point Chowla is also available: for each fixed integer `h>0`, `(1/log x)Σ_{n≤x}λ(n)λ(n+h)/n→0`. This gives genuine signed correlation cancellation, but its statement supplies neither a square-root prefix rate nor uniformity over growing shifts. It cannot be substituted for MC's critical estimate or JAS's full family of shell bounds. [CHOWLA] [MC] [JAS]

### Windows, charges and overlap

For every real even C² test supported in `[-1881/5000,1881/5000]`, Weil's form has floor `(1/50000)∫F²`. Parity splitting and complexification give the full complex floor, the corresponding closed ground-energy floor, and every block size at window ratio at most `10609/5000 = 2.1218`, for cutoff `Q ≥ 2`. This is an all-block-size theorem, not a finite matrix check. [FLOOR] [BLOCK-FLOOR]

The first overlap Schur excess vanishes, the dressed middle has one negative square, and the first ladder level is zero. The proof transfers the fixed-aperture floor to overlap matrices; it is not an independently established Green contraction that can simply be iterated. The ratio ladder starts at `103/50`, sends `r` to `r²/2`, and reaches beyond ratio three after four steps. Vanishing of the remaining levels would close that finite ladder. A global bounded-level theorem, with the stated binding-energy ceiling, would imply RH. Neither further zero excess nor a global level budget is supplied by the first step. [GREEN-FIRST] [GREEN-LADDER] [GREEN-GLOBAL]

The actual neutral-matrix margin has an exact boundedness criterion for RH. A uniform matrix shift of size `C K^θ` implies zero width at most `θ`, for `0 ≤ θ < 1/2`; a general converse at positive `θ` is not established by that receiver. Uniform strictly positive margins at every aperture are the wrong target: under RH the long-window continuum margin tends to zero. [ACS] [MARGIN-RATE] [MARGIN-DECAY]

Finite Legendre-charge gaps and Gamma comparisons retaining charges and higher lags already exist. Their existence does not certify a larger full Weil floor. Coupling cannot be replaced by a uniformly fixed-rank model with the prescribed lowering budget at ratio four; the necessary rank grows with block size. Full jets/contact operators with finitely many *additional* charges are not excluded by that theorem. [CHARGES] [GAMMA-CHARGES] [GAMMA-LAGS] [RANK-WALL]

### Half-line states, zeros and arithmetic Galois theory

Closed soft-logarithmic energy attains its infimum. Confining minimizers have exponential barriers. A critical half-line state, if the positive critical threshold occurs, is unique up to sign, outer, causally cyclic and free of Laplace zeros on the closed right half-plane. The corpus derives such a state as an alternative to RH. These are structural properties of the possible obstruction, not its exclusion. The soft-logarithmic minimizer and critical half-line state must not be identified without a comparison theorem. [SOFT] [HF-BARRIER] [HF] [HF-OUTER] [HF-CYCLIC] [HF-BOUNDARY]

Forward heat monodromy is transitive and large: its finitary signed permutation subgroup has index at most two in the ambient signed group. The heat cover has no global continuous monic factor of fixed positive degree selecting its zeros. Analytic relations on the connected configuration covers hold identically or only at discrete parameter sets. None of these facts proves algebraic independence at a fixed fibre or reality at time zero. One isolated off-centre double collision gives an explicit pair exchange and then every finitary signed permutation at every forward base. Existence of such a collision remains a hypothesis. [MONODROMY] [HEAT-FACTOR] [HEAT-RELATION] [HEAT-TURN]

There is also an actual arithmetic Galois theory: the prime-value extension over the mixed prime-trace field is algebraic and normal, acts faithfully on zeros, and preserves absolute ordinate. A zero's orbit is contained in its conjugate pair exactly when its prime weight belongs to the trace field. This membership is prime-independent; it does not force real part `1/2`. Functional reflection has a precise square-class obstruction to lifting. These field automorphisms are different objects from heat monodromy. [TRACE-FIELD] [WEIGHT-ORBIT] [REFLECTION]

### Finite exceptions

Write `Θ` for the rightmost zero abscissa and `Θ∞` for the tail abscissa. AAL is `Θ∞ = Θ`. Its failure is a finite nonempty exceptional layer above a narrower infinite tail. RH requires both tail approach to the critical line and elimination of exceptional zeros. One off-line zero does not by itself falsify AAL. [AAL] [AAL-LAYER] [AAL-HIERARCHY]

Integer-norm edit models can retain counting estimates and prescribed finite layers. Compact Selberg models can have genuine finitely many off-line zeros from small eigenvalues. The latter have their own Gamma factor and functional equation; they are not counterexamples with the exact Riemann completion. These models test the sufficiency of proposed axiom packages. [EDIT] [EDIT-REMOVE] [SELBERG]

## Named routes

The A column lists useful routine assembly only where identifiable. `—` means no independent routine task removes the closure obstruction; the available receiver can already accept its missing input.

### Arithmetic growth, scheduling and cancellation

| Route | Established receiver or boundary | A — work | B — hard closure obstacle |
|---|---|---|---|
| **WL — Weil lag** | Exact closed-rate dictionary between zero width, the critical deficit, Chebyshev primitive and coprime cross-work. [WL] | Transport a proved rate between these normalizations. | Establish the critical arithmetic deficit bound. A change of observable does not improve its rate. |
| **FU — signed prime scheduling** | One-sided bounds for the normalized Abel quantity on backward power gaps give RH; the criterion retains its gap exponent. [FU] | Apply the existing gap-bootstrap theorem to an independently supplied schedule. | Obtain the signed one-sided bound on those actual gaps. Absolute estimates lose the required cancellation. |
| **CFC — first-clock lower bound** | An eventual floor for the actual first-clock tail implies RH. [CFC] | — | Prove that floor with all completion and tail terms retained. The receiver is a sufficient theorem; no converse is asserted here. |
| **RP — history floor** | A linear floor `−B(K+2)` for the actual head-matched variance defect is equivalent to RH. [RP] | Exact head/tail normalization is available. | Bound the signed defect, uniformly in history length. Positivity of an unrelated variance is insufficient. |
| **PA/HJ — prime–archimedean passivity** | Calibrated Hausdorff finite-difference inequalities at all orders characterize RH. [PA] | Use the established calibrated sequence and radius. | Control all difference orders together. A result at each fixed order eventually is not the universal assertion. |
| **MC — Möbius cancellation** | Subpower growth of the specified Möbius Hilbert form is equivalent to RH. [MC] | Transfer an actual cancellation bound through the Hilbert-form identity. | Produce critical signed cancellation uniformly over the required lengths and dampings. Changing norm or basis does not produce it. |
| **SQF — weighted squarefree count** | The one-sided weighted exponential-count error at exponent `1/4+ε`, for every `ε>0`, is an RH criterion. [SQF] | — | Prove the arithmetic one-sided error, including the endpoint quantifier over ε. |
| **TT — theta tail/Wold** | The directed covariance plus half-diagonal bound for every `0<t<1/2` characterizes RH. [TT] | Assemble the open-parameter bounds if supplied. | Uniform arithmetic control through that parameter family. The natural `t=1/2` target is not a substitute. |
| **CHMD — causal hyperbolic–modular duality** | Boundedness above, below or in absolute value of the actual prime wave characterizes RH. [CHMD] | Carry a proved source bound through the existing wave dictionary. | Bound the arithmetic wave; a causal representation alone does not bound it. |
| **LI — paired Li/prime–Gamma balances** | The actual response has the required lower floor at every positive exponential rate iff RH. [LI] | Exact response and clock identities are available. | Control prime–Gamma cancellation at arbitrarily small rates; a finite coefficient calculation cannot do this. |
| **PBM — regularized abscissa** | Convergence of the regularized prime-coefficient object throughout `Re s>1/2` is equivalent to RH. [PBM] | — | Prove continuation/convergence at the critical abscissa from arithmetic, rather than naming the desired continuation. |
| **RB — Robin/Nicolas** | Colossally-abundant reduction and an eventual lcm formulation give exact arithmetic RH criteria. [RB] [RB-LCM] | Carry a proved inequality through these reductions; exact finite initial ranges are separate work. | Establish the infinite eventual inequality with the sharp constant. Finite verification supplies no tail proof. |

### Forms, windows and arithmetic energy

| Route | Established receiver or boundary | A — work | B — hard closure obstacle |
|---|---|---|---|
| **RW — restricted Weil ground energy** | Local boundedness of the canonical potential on its precontact domain iff RH. Finite-aperture floors are available. [RW] [BLOCK-FLOOR] | Transfer certified floors among the existing closed-form and matrix interfaces. | Prevent loss at every aperture/contact. Local compactness does not supply the global bound. |
| **HF — Hodge/critical half-line state** | Under failure of RH a unique-up-to-sign critical state exists with strong regularity and reflection structure. [HF] [HF-WALL] | Apply the attained minimizer and barrier theorems in their stated domains. | Exclude this particular arithmetic state, or force its critical threshold to vanish. Existence, uniqueness, outerness and cyclicity are not missing inputs. |
| **HAT-C — arithmetic-clock Green energy** | Corrected energy plus the jump tail is exactly Weil's form; the full family floor characterizes RH. [HATC] | Preserve the exact jump-tail normalization in transfers. | Bound the corrected energy over all test functions and apertures. Dropping the jump tail changes the problem. |
| **TH — theta moment positivity** | The actual arithmetic Hermite trace flag implies RH. [TH] | Finite flag identities and conversions are available. | Establish the whole flag for the arithmetic source. A model with a positive moment sequence need not be that source. |
| **RN — theta renewal** | The exact Gamma-polar versus prime-ground scaling-energy inequality is equivalent to RH. [RN] | — | Prove that inequality. A renewal denominator without divisor identification cannot replace ξ. |
| **SZ — Suzuki screw** | Eventual boundedness of the aligned Gamma-completed energy iff RH. [SZ] | Keep the established completion and source-welding terms together. | Bound the completed arithmetic energy; an uncompleted or differently aligned energy is not the criterion. |
| **EWU — even sector** | Even Weil floor `1/50000` at aperture `1881/5000`. [FLOOR] | Exact reuse of the retained-charge certificate at smaller apertures. | Extend to unbounded apertures, including new prime contacts and their cross terms. |
| **OWU — odd sector** | Odd/even splitting yields the full first-overlap floor. [BLOCK-FLOOR] | Complexification and matrix transfer are already proved. | Control the odd sector at all apertures alongside the even sector. A result for one parity is not the full criterion. |
| **GTA — Schur charge** | Uniform quartic-charge decay is equivalent to RH. [GTA] | Use the exact charge/flag conversion. | Produce this decay for the arithmetic charge. Ordinary skew-energy bounds do not control the quartic observable. |
| **ACT — single shift** | For any fixed positive shift, the full reflected-difference inequality over all compact even C² profiles iff RH. [ACT] | No need to introduce more shifts. | Prove the universal profile inequality at that shift; “single shift” does not mean finitely many tests. |
| **AIP — incidence/compensation** | A subexponential bound for the compensated full prime-polar ledger, for every positive rate, iff RH. [AIP] | Exact compensation identities are available. | Bound the retained signed remainder. Omitting a ledger term destroys the implication. |
| **SC — Stokes/Witt–Krein** | Bounded Gaussian-damped two-prime cone coupling at every index pair iff RH. [SC] | Use the damped criterion with its fixed positive damping. | Bound the actual full coupling. Undamped tail information must separately pay for finite exceptional zeros. |
| **ACS — Castelnuovo–Severi on degree points** | A uniform lower bound on neutral-window margins iff RH; first-overlap matrices have an explicit positive floor. [ACS] [GREEN-FIRST] | Propagate proved finite floors and evaluate exact ladder recurrences. | Control signed Schur losses or an equivalent margin at all scales. Contact-only gaps and fixed-rank gluing do not suffice. [RANK-WALL] [TREE-GAP] |
| **ECP — endpoint character positivity** | Positive semidefiniteness of every finite arithmetic endpoint-character Gram iff RH. [ECP] | Finite-rank identities can use existing character formulas. | Establish positivity of the actual character at every rank. Projecting to a positive character without source equality does not close ECP. |

### Zero geometry, heat, topology and realization

| Route | Established receiver or boundary | A — work | B — hard closure obstacle |
|---|---|---|---|
| **LA — Jensen line anchor** | Real-rooted unshifted Jensen polynomials in unbounded degree characterize RH. Verified-height/width rungs give finite degrees. [LA] [JENSEN-RUNG] | Combine the `3/8` width bound with the height-67 rung: the stated inequality permits degree `31922`; this is a corollary to formalize, not a theorem located under that number. | Reach unbounded degree with no heat shift. Almost all roots real is insufficient. |
| **ZCG — zero-configuration geometry/heat descent** | At every positive real nonbranch base, equality of loop and conjugate-loop transport iff RH. Large monodromy and local collision laws are proved. [ZCG] [MONODROMY] [HEAT-TURN] | Compose established local transports on specified finite paths. | Prove the arithmetic conjugation compatibility, or exclude positive-time nonreal configurations and control descent to time zero. A large permutation group supplies no reality theorem. |
| **TG — topological sub-unit gate** | Every formation rectangle admits the specified anchor with cubic trace-norm defect `<1` iff RH. [TG] | The integer-winding/sub-unit deduction is available. | Produce the strict arithmetic sub-unit bound on every required rectangle. Topology converts the bound; it does not establish it. |
| **WD — Ward/collision/long moments** | Subpower fixed-window moments iff RH. Alternatively: a fixed height exponent `K`, arbitrarily large length exponents `θ`, and cofinal-height bounds `C_θ T^K` suffice and characterize RH. [WD] [WD-COFINAL] | Transfer a proved bound through the receivers with the exact length/height quantifiers. | Obtain signed long-mollifier control with `K` independent of `θ`. Short-mollifier asymptotics and finite block factorization do not reach this range. A near-unit target has its own obstruction. [WD-SHORT] [WD-BLOCK] [LONG-MOMENT] |
| **PM — physical model** | Modular/Bianchi scattering receivers translate zero abscissae into pulse decay. Bianchi uses `ζL(χ₋₃)`; its quarter-rate criterion concerns the corresponding Dedekind RH. The strip gives rates `1/16−ε` in the pulse normalization. [PM] [RINGDOWN] | Transfer an improved strip through the established decay dictionaries. | Prove the sharp arithmetic decay and complete visibility of the relevant divisor. An AdS interpretation adds a separate, unconstructed dictionary. |
| **PTR — cosine source** | Membership of every positive cosine shift in the Laguerre–Pólya class iff RH. [PTR] | Use established shifted bounds within their range. | Reach all arbitrarily small positive shifts. A fixed safe shift cannot be sent to zero without uniform control. |
| **JAS — joint ancestry** | RH iff no off-line chain plus cofinal small-shell positivity at every positive exponent. The subcritical-strip variant still needs window and shell positivity. [JAS] [JAS-STRIP] | Insert the MMD strip into the strip-dependent receiver. | Establish the remaining arithmetic shell/window bounds and the required chain/tail control. Do not discard one conjunct because another is available. |
| **CTF — chronological tail/Báez–Duarte** | Approximation to one by the specified real unit-bounded chronological rows iff RH. [CTF] | Use the existing row construction and norm identities. | Prove approximation for rows tied to the actual Möbius arithmetic. The failed sharp full-sequence target is not repaired by arbitrary coefficients. |
| **HCF — heat trace** | Nonnegativity for all polynomial degrees on two distinct prime-log sampling grids iff RH. [HCF] | Grid/trace conversion is available. | Prove the arithmetic inequalities in every degree. Two grids reduce sampling locations, not polynomial complexity. |
| **XN — Newton discs** | Every zero lies in a line-centred Newton self-map disc iff RH. [XN] | Once a disc and its exact margin are supplied, the contraction conclusion is standard. | Construct those discs with the required margins from arithmetic. Subharmonicity alone supplies no minimum principle of the required sign. |
| **BAG — self-return** | The specified cutoff-uniform head-target density on every closed disc of the strip iff RH. [BAG] | Existing recurrence identities give the target to test. | Prove target-faithful uniform recurrence. Generic recurrence and S3 identity returns have different targets. |
| **SRT — lag localization** | Cofinal prime-logarithmic windows of radius `32 log(T+2)` with the stated one-sided cubic-trace floor characterize a bound on zero width. [SRT] | Apply the existing localization theorem to an independently supplied arithmetic floor. | Prove the floor with its prime, window and cofinality quantifiers. A mean or density estimate does not automatically bound each required local trace. |

## Route candidates

Candidate status means the receiver is mathematically meaningful but its arithmetic source is not supplied. A finite algebraic identity or a generic realization is not promoted to a producer.

| Candidate | Established content | A — work | B — source or exclusion problem |
|---|---|---|---|
| **SEC** | Factorial-Fock boundedness detects criticality exactly. [SEC] | Evaluate the finite jet identities. | Derive a ζ-selective Fock bound from the actual source, or prove the needed edge compactness. |
| **CDC/BSH** | A nondivergent positive-priced dark history forces criticality under the stated price/response conditions. [CDC] | Verify the accounting for a given history. | Construct an arithmetic history satisfying all conditions independently of criticality. |
| **S3** | A strip of width `<1/2` excludes heavy identity returns; a suitable homogeneous-return transfer gives strip collapse. [S3] | Supply the available MMD strip. | Prove the transfer from the relevant target to identity returns. BAG recurrence does not provide it automatically. |
| **APF** | Prime/grade/cap traces reconstruct the specified real critical labels. [APF] | Assemble finite traces and countable-span reconstructions. | Exhaust the entire ξ divisor, including a hypothetical off-line zero; reconstruction on the real-labelled subspace does not do so. |
| **EGC** | Explicit contour scheduling makes the tail count error smaller than `1/(n+1)`. [EGC] | Substitute the explicit schedule and perform the integer-error deduction where its hypotheses hold. | Isolate the correct height fibre and prove outer landing. Small contour error alone does not select that fibre. |
| **EWJ** | Norm exhaustion has an exact endpoint-blind exceptional lane. [EWJ] | Use the proved depth reporter identities. | Construct endpoint-faithful admission outside the blind lane; norm exhaustion itself is too weak. |
| **FEL** | Theta observation histories satisfy exact information/KL accounting. [FEL] | Apply the finite chain rule to a specified history. | Choose and calibrate a source-determined history forcing the needed BSY sign. Information inequalities alone do not supply that sign. |
| **IRK** | The prime-rotation construction has an exact finite free resolution. [IRK] | Finite resolution algebra is available. | Produce an integral/projective arithmetic realization identifying its trace with the required Chern charge and full divisor. |
| **MSC** | Gamma-sewn squarefree source has an exact conormal/ζ bridge. [MSC] | Preserve the completion and nonvanishing-unit factors. | Prove the Sonin/Weil sign for the actual source; the physical Hilbert realization does not settle it. |
| **RFHM** | Literal all-prime reversible sewing is impossible. [RFHM] | Extract usable local phase/grade identities. | Find a different source-faithful phase/depth law with the required wall orientation. Support and admission alone are insufficient. |
| **W1C** | Locally uniform index-one approximants to ξ characterize RH. [W1C] | Transfer a genuinely constructed approximating family through the convergence theorem. | Construct that family arithmetically without assuming its index. A prescribed zero operator is not an independent construction. |
| **WBF** | Genealogy Gram determinants recover magnitudes and the associated phase-gauge information. [WBF] | Exact determinant reconstruction is available. | Obtain an arithmetic certificate stream and prove ξ landing; recovered magnitudes do not determine the missing source phases. |

## Supporting programmes and their remaining mathematics

| Programme | Available result | Actual frontier |
|---|---|---|
| **AGZ / arithmetic square / F₁** | Frobenius contacts, jets, planar ideals and planar Bézout are explicit. Hodge-compatible self-pairings require logarithmic negative geometric diagonals. [CONTACT] [CONTACT-JET] [BEZOUT] [SELF-PAIRING] | A source-independent global intersection/index theorem with the actual archimedean counterterm. Perfecting away the contacts loses the arithmetic. [PERFECT] |
| **Green calculus / MAFT** | Exact overlap Schur formulas, additive loss, refinement and bounded-margin RH criterion. [GREEN-LOSS] [ACS] | Bound the actual signed losses at every scale. Contact-process gap and curvature shortcuts fail. [TREE-GAP] [TREE-CURVATURE] |
| **Arithmetic Galois theory** | Complete-fibre equations, normal extensions, faithful zero actions and an exact reflection-lift obstruction. [FIBRE-FIELD] [TRACE-FIELD] [REFLECTION] | Derive restrictive prime-field relations independently; construct and constrain the reflection lift. Rational real part gives a small orbit, not criticality. [WEIGHT-ORBIT] |
| **AAL / exceptional-layer theory / edit worlds** | Finite-layer, transport and finite-oscillation characterizations; explicit edited countermodels. [AAL-LAYER] [AAL-TRANSPORT] [AAL-OSCILLATION] [EDIT] | Identify an arithmetic invariant that forces height transport or prohibits a finite top layer for ζ itself. Tail estimates cannot replace it. |
| **Artin/Hecke transfer** | Primitive Hecke identification, Brauer meromorphic completion, unit functional equation and signed divisor/index accounting. [ARTIN] | Pole cancellation for general Artin holomorphy; critical-line exclusion for the factors. The cubic Eisenstein producer does not automatically extend to arbitrary number fields. |
| **Compact hyperbolic geometry** | Genuine small-eigenvalue Selberg countermodels and exact Bergman identities. [SELBERG] [BERGMAN] | Distinguish the Riemann arithmetic source from generic geometric models admitting exceptional eigenvalues. |
| **Census / IGP / cameras** | The pole perturbation of the fourth trace is `O(d/L²)`; second/fourth moments can be ambiguous; reflected cubic interference can be negative. [CENSUS] [CENSUS-AMBIGUITY] [GRAM-SIGN] | An actual arithmetic fourth/higher correlation bound or a different invariant that controls the desired census. Second-moment evidence cannot be promoted to that bound. |
| **Multiplicity / near-line geometry** | Sech envelope on the `1/8..7/8` strip; large critical multiplicity forces nearby off-line mass. [SECH] [COMPENSATION] | Exclude that compensating configuration. Boundary multiplicity is sublogarithmic; the critical-line envelope alone is not. |
| **Modular/cubic horizon** | Arithmetic scattering normalization, unconditional strip-derived decay and the weight-half three-term calibration. [RINGDOWN] [LEWIS] | Sharp complete-observable decay. A functional equation or a calibrated period identity is not a decay estimate. |
| **HFP — fixed-part/comb geometry** | Paired Li coefficients are limits of explicit comb-tail sequences. [HFP] | A sign or rate for the actual tails. A limit representation does not prove the sign of its limit. |
| **HAT — adelic Green support** | The critical inverse has no bounded operator realization; Green damping identifies the logarithmic energy domain. [HAT-INVERSE] [HAT-DOMAIN] | Work with the correct unbounded/form-domain object and prove the remaining arithmetic inequality; a bounded inverse is an excluded target. |
| **TTPO / prime-orbit return support** | Heavy prime subsets cannot return in the stated Vinogradov–Korobov height range. [RETURNS] | A stronger source-sensitive return theorem and the required return-to-zero transport. Fixed-height recurrence or a prime-label statement alone is insufficient. |
| **MZF — short-mollifier arithmetic** | The exponent-`13/50` Levinson construction proves an explicit positive critical odd-fibre proportion. [MZF-PROPORTION] | All-zero exclusion or the unbounded-length bounds needed by WD. This census proportion differs from WD's low-set proportion criterion. |

## What closes a route

There are three shared requirements: **arithmetic production**, **global exclusion with the correct quantifiers**, and **faithful realization/transport**. A route can fail at more than one. The finite-exception coordinate must remain visible through all three. The [wall ledger](walls-ledger.md) makes these requirements explicit; the [unification ledger](route-unification-ledger.md) separates actual common observables from routes that merely have equivalent terminal propositions.

<!-- source references -->
[MMD]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L1
[GAUSS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L586
[DECOMPLETE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheWallIsThePriceOfCompletion.lean#L211
[PHASE-WALL]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheWallOfTheFrameIsAPhaseLFunction.lean#L371
[AVERAGE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheAverageRowIsBlindToTheTarget.lean#L1
[CHOWLA]: ../../../formal/GaloisForLFunctions/LogarithmicChowla/LogarithmicChowlaTheorem.lean#L90
[MC]: ../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean#L219
[JAS]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryShellAmplitudeAbscissaDuality.lean#L213
[FLOOR]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtAperture1881Over5000.lean#L340
[BLOCK-FLOOR]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheFirstOverlapWindowHasAPositiveWeilFloorAtEveryBlockSize.lean#L1
[GREEN-FIRST]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFirstOverlapStepHoldsAtEveryBlockSize.lean#L1
[GREEN-LADDER]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree.lean#L1957
[GREEN-GLOBAL]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree.lean#L2178
[ACS]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis.lean#L505
[MARGIN-RATE]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheRateOfTheMarginOfTheWindowMatricesBoundsTheAbscissaOfTheZeros.lean#L724
[MARGIN-DECAY]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/UnderTheRiemannHypothesisTheMarginOfALongWindowTendsToZero.lean#L442
[CHARGES]: ../../../formal/GaloisForLFunctions/LatticeSectionTheory/WindowJumpCounts/RegionalLogarithmicChargedGaps.lean#L1
[GAMMA-CHARGES]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheGammaComparisonRetainsItsChargesThroughRadiusTwo.lean#L1
[GAMMA-LAGS]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheGammaRemainderRetainsHigherLagsThroughRadiusTwo.lean#L1
[RANK-WALL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize.lean#L929
[SOFT]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/SoftLogarithmicClosedAttainment.lean#L27
[HF-BARRIER]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningMinimizerExponentialBarriers.lean#L1
[HF]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L96
[HF-OUTER]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineLaplaceMultiplierIsOuter.lean#L45
[HF-CYCLIC]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateIsCyclic.lean#L59
[HF-BOUNDARY]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoBoundaryLaplaceZero.lean#L149
[MONODROMY]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyGroupHasIndexAtMostTwoInTheSignedPermutationsOfFiniteSupport.lean#L1
[HEAT-FACTOR]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheHeatCoverOverTheForwardTimesIsConnectedAndHasNoPolynomialFactor.lean#L125
[HEAT-RELATION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnAnalyticRelationAmongZerosInDistinctPairsHoldsOnEveryConfigurationOrOnADiscreteSet.lean#L1
[HEAT-TURN]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L131
[TRACE-FIELD]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ThePrimeTraceGaloisGroupOfTheZeros.lean#L850
[WEIGHT-ORBIT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheOrbitOfAZeroIsItsConjugatePairIffItsWeightLiesInThePrimeTraceField.lean#L1
[REFLECTION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ThePrimeReflectionKernelOfTheZeros.lean#L455
[AAL]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean#L158
[AAL-LAYER]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33
[AAL-HIERARCHY]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheLinearAbscissaLawAndItsHierarchy.lean#L233
[EDIT]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerWithATailOverTheRationalPrimes.lean#L488
[EDIT-REMOVE]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerCanBeEditedAway.lean#L48
[SELBERG]: ../../../formal/GaloisForLFunctions/CompactHyperbolicSurfaces/SmallEigenvalueZeta.lean#L113
[WL]: ../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean#L868
[FU]: ../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorOneSidedPowerGapBootstrap.lean#L596
[CFC]: ../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockTailLowerBoundCompleteness.lean#L1066
[RP]: ../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean#L478
[PA]: ../../../formal/GaloisForLFunctions/RHTower/PrimeArchEndpointCalibratedHausdorffRH.lean#L92
[SQF]: ../../../formal/GaloisForLFunctions/RHTower/SquarefreeExponentialOneSided.lean#L605
[TT]: ../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean#L182
[CHMD]: ../../../formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L385
[LI]: ../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean#L165
[PBM]: ../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean#L402
[RB]: ../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean#L132
[RB-LCM]: ../../../formal/GaloisForLFunctions/RHTower/RobinLcmRiemannCriterion.lean#L458
[RW]: ../../../formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/ThePotentialIsLocallyBoundedIffRH.lean#L115
[HF-WALL]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/CriticalTerminalWallEnergy.lean#L131
[HATC]: ../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheJumpTailFloorNeedsTheFullArithmeticNormalization.lean#L38
[TH]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaHermiteTraceFlag.lean#L250
[RN]: ../../../formal/GaloisForLFunctions/RHTower/CCM/CCMThetaGroundRHCriterion.lean#L49
[SZ]: ../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTransitionCoreAlignedGammaCompletion.lean#L380
[GTA]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean#L293
[ACT]: ../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/SingleShiftCompleteness.lean#L177
[AIP]: ../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheCompensatedRemainderOfTheFullLedger.lean#L878
[SC]: ../../../formal/GaloisForLFunctions/ArithmeticCouplingTheory/ConeBoundary/GaussianConeKernel.lean#L231
[TREE-GAP]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheDilationProcessHasNoGap.lean#L174
[ECP]: ../../../formal/GaloisForLFunctions/RHTower/Representation/EndpointCharacterCriterion.lean#L62
[LA]: ../../../formal/GaloisForLFunctions/FiniteFreeProbability/FiniteFreeDeBruijnNewman.lean#L466
[JENSEN-RUNG]: ../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenRungAtTheSaddleScale.lean#L117
[ZCG]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros.lean#L186
[TG]: ../../../formal/GaloisForLFunctions/RHTower/FormationAnchoredCubicEndpoint.lean#L220
[WD]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheWidthIsReadInOneWindow.lean#L485
[WD-COFINAL]: ../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean#L704
[WD-SHORT]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TwistedSecondMomentsBelowSquareRoot.lean#L128
[WD-BLOCK]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheTwistedMomentFactorsOverBlocks.lean#L585
[LONG-MOMENT]: ../../../formal/GaloisForLFunctions/ArithmeticProduction/LongMollifiersImplyCriticalClustering.lean#L422
[PM]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/BianchiHorizonRingdownEquivalence.lean#L1
[RINGDOWN]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/UnconditionalScatteringResonanceBounds.lean#L1
[PTR]: ../../../formal/GaloisForLFunctions/RHTower/DeBruijnNewmanCosineShift.lean#L415
[JAS-STRIP]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryDoubleExpWindowsDyadicShells.lean#L26
[CTF]: ../../../formal/GaloisForLFunctions/RHTower/ChronologicalRiemannEquivalence.lean#L414
[HCF]: ../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean#L123
[XN]: ../../../formal/GaloisForLFunctions/RHTower/XiNewtonDiscSourceMargin.lean#L219
[BAG]: ../../../formal/GaloisForLFunctions/RHTower/ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip.lean#L294
[SRT]: ../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/PrimeLogarithmicWindows.lean#L145
[SEC]: ../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean#L398
[CDC]: ../../../formal/GaloisForLFunctions/RHTower/XiSourceHistoryPriceEscape.lean#L140
[S3]: ../../../formal/GaloisForLFunctions/SignFreePurityMechanisms/HomogeneousReturnTransferImpliesStripCollapse.lean#L35
[APF]: ../../../formal/GaloisForLFunctions/RHTower/PaperPrimeFredholmReconstruction.lean#L39
[EGC]: ../../../formal/GaloisForLFunctions/SquareRootThreshold/EffectiveHorizons/TheEGCContourIsExplicit.lean#L139
[EWJ]: ../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthCompression.lean#L48
[FEL]: ../../../formal/GaloisForLFunctions/RHTower/PaperThetaObservationHistory.lean#L52
[IRK]: ../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPrimeRotationResolution.lean#L25
[MSC]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmGammaSewnSquarefreeXiConormalBridge.lean#L53
[RFHM]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryAllPrimeReversibleRFHMSewingNoGo.lean#L132
[W1C]: ../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/TheIndexIsSemicontinuous.lean#L96
[WBF]: ../../../formal/GaloisForLFunctions/HTGeometry/PaperGenealogyFredholmRecovery.lean#L107
[CONTACT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheFrobeniusGraphsMeetInThePrimes.lean#L98
[CONTACT-JET]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/WeilsOffDiagonalIsContactsPlusJets.lean#L125
[BEZOUT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/BezoutIsAnEqualityOnThePlanarSquare.lean#L124
[SELF-PAIRING]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean#L268
[PERFECT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/APerfectSquareKeepsNoContact.lean#L81
[GREEN-LOSS]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle.lean#L568
[TREE-CURVATURE]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheFloorTreesHaveCurvatureZero.lean#L1
[FIBRE-FIELD]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheFieldOfCompleteFibreTraces.lean#L409
[AAL-TRANSPORT]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheAbscissaLawsOfAZeroConfiguration.lean#L106
[AAL-OSCILLATION]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/TheOneOffsAreFiniteOscillationsOfThePrimeError.lean#L736
[ARTIN]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/EveryArtinLFunctionHasACompletionWithAFunctionalEquation.lean#L220
[BERGMAN]: ../../../formal/GaloisForLFunctions/CompactHyperbolicSurfaces/BergmanKernel.lean#L1
[CENSUS]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ZetaSamplingPrimePoleFourth.lean#L262
[CENSUS-AMBIGUITY]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/SplitBandMomentAmbiguity.lean#L1
[GRAM-SIGN]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/ReflectedExponentialCubicInterference.lean#L304
[SECH]: ../../../formal/GaloisForLFunctions/SquareRootThreshold/SechMultiplicityEnvelope.lean#L91
[COMPENSATION]: ../../../formal/GaloisForLFunctions/SquareRootThreshold/GaussianLocalCompensation.lean#L110
[LEWIS]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/TheWeightHalfThreeTermCalibration.lean#L1338
[HFP]: ../../../formal/GaloisForLFunctions/HodgeTheoryOfAFixedPart/TheLiCoefficientsAreLimitsOfCombTails.lean#L360
[HAT-INVERSE]: ../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheCriticalAdelicGreenInverseIsUnbounded.lean#L94
[HAT-DOMAIN]: ../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheGreenDampingDetectsTheCompleteWeilFormDomain.lean#L169
[RETURNS]: ../../../formal/GaloisForLFunctions/TranscendenceTheoryOfThePrimeOrbit/HeavySubsetsDoNotReturnBeforeTheVinogradovKorobovHeight.lean#L147
[MZF-PROPORTION]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheTwistedMomentGivesAPositiveCriticalProportion.lean#L109
