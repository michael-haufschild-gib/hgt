# Hard obstacles: routine work, open mathematics and research directions

19 October 2026. Individual assessments: [all routes and candidates](hard-obstacles-1910.md).

**Every current route requires new mathematics. None can be closed by routine calculations or formalization alone.** Existing results provide exact criteria, source identities, finite constructions and sharp constraints. The missing input is an independent arithmetic estimate or a faithful construction strong enough to satisfy a complete RH criterion.

This summary covers **27 routes, 19 named candidates, PM's PW-B candidate branch and 15 shared walls**. These approaches overlap: solving RH through one route need not solve every candidate construction.

RH remains [unsolved](https://www.claymath.org/millennium/riemann-hypothesis/). **B-RH** denotes an open target sufficient for RH; **B-C** denotes an unproved construction or transfer whose truth and usefulness are themselves research questions. An individually proposed construction is not automatically a recognized worldwide open problem.

## 1. Tasks that are “just work”

These tasks use supplied mathematics. They can support a chosen research attack, but **none supplies a missing RH-closing sign or bound**. Finite input ranges, tolerances and theorem hypotheses must be specified before execution. A statement quantified over every rank, aperture, height or vanishing damping is outside this routine list.

| Task | Available method | Scope and concrete result |
|---|---|---|
| **Apply exact identities and receiver implications.** | Trace/source dictionaries, pronic and cell transfers, moment identities, Abel summation, extremal reductions. | All routes with established receivers, including WL, RW, PA, CHMD, PM, BVI, JAS, PBM and RB. Express a proposed bound in the exact normalization and list its unproved premises. Identifying different completed spaces or norms requires a separate theorem. |
| **Evaluate a specified finite problem with rigorous error.** | Finite Gram matrices, moments, traces, contour heads, coefficient formulas and certified arithmetic. | PA, LA, TH, HCF, XN, CTF, RB, APF, IRK and finite stages of the other candidates. Produce a certified sign, norm or error for the stated finite range. The result does not extend automatically to unbounded ranges. |
| **Specialize finite reconstruction and graph-error bounds.** | Prime-anchor inversion, known taper coefficients, complete signed-energy error `K²+2K‖F_ref‖`. | BiScale/BVI and finite FU/PM applications. Verify a live anchor and calculate cutoff, amplitude and inverse losses. Produce an explicit finite error budget. Making that budget vanish in a changing-cutoff regime remains research. |
| **Instantiate source constructions within their proved domains.** | Finite prime scheduling, fixed-damping admission, full-support Gamma–theta source formulas, renewal determinants, squarefree `L²` admission and finite Lee–Yang constructions. | FU, PM, JAS/RFHM, SZ, RN, MSC, W1C and PW-B. Construct the specified source or model and verify its existing hypotheses. Small-damping control, complete positivity and identification of a different arithmetic limit are excluded. |
| **Apply established obstruction and repair formulas.** | Local mass corrections, fixed-cutoff amplitude compactness, exact defect identities, sharp moment cones and explicit carrier obstructions. | THIM, BiScale, ACT, BVI, RP, EGC and PCS. Determine whether a specified proposal meets the known boundary and calculate the retained defect. Bounding that defect in the full RH regime is a new mathematical problem. |

### Established supporting results and their limits

| Programme | Established result | Remaining mathematical obstacle |
|---|---|---|
| **BVI/PM** | Finite source recovery; complete five-component Vaughan expansion with all 25 ordered pairings; summable active-boundary difference; energy bound for `ε≥1/2`. | Complete horizon-uniform energy bounds for damping arbitrarily close to zero. |
| **BiScale** | Live prime-anchor recovery and complete finite graph-error control. Fixed cutoff plus bounded total amplitude gives compactness. | Observation accuracy sufficient to pay the growing inverse losses and preserve the complete receiving form. Bounded graph norm plus vanishing diagonal cost alone does not imply compactness. |
| **THIM** | Universal cosh-by-sinh absorption fails. Exact minimal local correction and nonzero primitive families with complete absolute energy `O((n+1)⁻²)` are available. | Domination of the correction for arbitrary tests, or a sufficiently rich independently nonnegative family. Small energy alone gives neither sign nor density. |
| **APT** | Explicit negative complete prime singleton; joint complete-form approximation for growing finite translated-tent patterns; detection of a specified off-line model. | Actual-zeta positivity or exclusion, together with sufficient separation; a separate direct critical-tail full-form estimate. The prime channel is subtracted in the Weil form, so its negativity is not a negative complete Weil witness. |
| **ACT** | A single shifted theta profile fails as a folded supersolution. Exact nonnegative-remainder minus reflected-collar identity. | Remainder domination on an admissible class and coverage of the full odd receiving class. A classification of all positive odd profiles is not established by the single-shift theorem. |
| **PCS** | Shift-plus-defect formulas; kernel/surjectivity obstruction to the full-carrier chronological-dilation isometry. | A source-natural restricted or defect-preserving construction that retains the required RH information. |
| **CHMD** | One-signed odd eigenstates above `1/2` are excluded; the threshold radical and its mass obstruction are identified. | Exclude sign-changing eigenstates above `1/2`. Finite multiplicity does not empty the entire band, and source mass does not descend through the radical. |
| **SRT** | Fixed-profile eventual positivity and fixed-resolution invisibility examples. | Joint resolution/height/aperture control capable of excluding every off-line configuration. |

The [supporting-programme analysis](hard-obstacles-1910.md#6-supporting-programmes-established-results-and-open-gaps) gives the exact bounds and domains.

## 2. Open mathematical obstacles, deduplicated

The eight families below organize the gap. They are **not proved irreducible or independent**, and a single successful route could bypass many optional constructions. **B-RH** marks a target sufficient for RH; **B-C** marks an unproved construction/transfer whose truth and ultimate usefulness still require testing.

### O1. Critical arithmetic cancellation and complete weighted energy

**Entries:** WL, MC, PM/FZZ-P, CTF, PBM, RB and JAS; BVI supplies an interface. FU/RP/LI share related history versions listed in O4.

Classical targets include `M(x)=O_η(x^(1/2+η))` for every `η>0`, the square-root-with-logarithms Chebyshev criterion, regularized-series convergence for every `σ>1/2`, or vanishing Nyman/Báez–Duarte approximation error. Each is an unproved **B-RH** target.

A precise current BVI/PM sufficient target is

\[
\forall\delta>0\;\exists\varepsilon\in(0,\delta)\;\exists B_\varepsilon<\infty\;
\forall T\ge1:\quad
\mathcal I_\varepsilon(T)=\sum_{n=1}^{T}
\frac{I_\varepsilon(n)^2}{n(n+1)}\le B_\varepsilon,
\]

with the literal `I_ε=pmBezoutInteriorPrefix ε`. The [receiver](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean) already gives the unconditional range `ε≥1/2`. The missing range is cofinal towards zero, with constants allowed to depend on damping.

The complete Vaughan expansion has five components and 25 ordered Gram terms. Its existing logarithmic source saving produces an energy majorant `n^(−2ε)/(log n)^8`, nonsummable below half damping. This is a failure of that upper-bound method, not proof that the true energy diverges. A concrete research target is a source-derived bound on the **mixed signed sum relative to the diagonal**, leaving summable dyadic losses. Such an estimate must retain density centering, active drift, covariance and endpoints. [Complete Vaughan identity](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CompletePronicVaughanCalibration.lean).

An intermediate bound at one fixed sub-half damping would be meaningful even without reaching RH. It must not be relabelled a complete solution of the cofinal criterion.

### O2. Nonnegativity of the complete arithmetic Weil form

**Entries:** RW, EWU, OWU, CHMD, HF, TT and related PA/SZ formulations; ACT attempts a producer, MSC a transport.

The central **B-RH** target is nonnegative complete form for every test in the receiving class, at every aperture. One exact odd-sector version is

\[
E_{\rm arch}(v)+E_{\rm prime}(v)
\ge \operatorname{phiDoobCoshMass}(v^2)
\qquad(v\text{ odd},\ v\in C_c^2(\mathbb R)).
\]

This is the corpus's [full odd Doob criterion](../../../formal/GaloisForLFunctions/RHTower/WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean), not positivity of one summand. In spectral coordinates it excludes the whole sign-changing odd bound-state band above `1/2`. The full-domain theorem, not finite multiplicity or one-signed exclusion, is missing.

Concrete possible mechanisms remain research: pay the reflected low-prime diagonal/collar by the complete jump remainder; establish a sharp capacity inequality; or construct a source-derived factorization on the actual domain. The single-shift ACT supersolution and uniform THIM absorption shortcuts fail. The survivor is an explicit defect comparison, with admissibility and full-class coverage still required. Near-null families forbid some positive-gap ambitions while leaving semidefinite positivity possible.

### O3. All-order moment, phase and critical-parameter control

**Entries:** TH, HCF, PA, LA, JAS; HJ and SEC expose related divisor/jet tests.

**B-RH:** prove every required Hankel/Bezoutian/heat-grid form positive at a common admissible parameter; all Hausdorff orders at their residual shifts; or the actual critical phase/current condition. A fixed order with its own eventual threshold is not a common all-order theorem. A finite power window with endpoints moving to infinity is not finite work.

HCF already has two prime-log grid criteria after polar cancellation; their arithmetic signs remain open. A single complete grid has aliases. Two-grid positivity and reconstruction of arbitrary packets are distinct problems. Forward heat evolution and positive shifted kernels do not control the original unshifted object. The known [Jensen hyperbolicity results](https://arxiv.org/abs/1902.07321) and [de Bruijn–Newman lower bound](https://arxiv.org/abs/1801.05914) illustrate established progress without supplying the missing quantifiers.

### O4. Complete history bounds and global signed transport

**Entries:** FU, RP, LI, TG, WD, GTA, SZ; APF, EGC and FEL have candidate versions.

**B-RH** for the established receivers: bounded completed Abel moments; a full-history linear floor; paired-Li lower floors on growing windows; a nonnegative residual plus sub-unit integral trace; vanishing Ward cap; rank-uniform transverse decay; or a complete moving-boundary Wronskian sign. These are different observable-specific targets, not one proved interchangeable estimate.

The missing mechanism must pay prior history, newly admitted blocks, moving core, high-LCM terms, cross covariance, residue/Gamma corrections and endpoint drift. A decrease at selected cutoffs, a small difference of two large energies, or strong convergence of every fixed packet is insufficient. Candidate contour/trace/likelihood schemes additionally need a faithful arithmetic landing (**B-C**).

### O5. Deterministic recurrence with conditioned tails

**Entry:** BAG.

**B-RH:** find common physical return heights for actual zeta on each required right-strip disc by controlling the centered tail on finite-head return events. The exact recurrence formulation is a sufficient corpus theorem; its converse is not asserted here.

Unconditioned mean square is already established. Conditioning on density `κ` can cost `1/κ`; the head length, tolerance, event density and tail cutoff are coupled. A valid next theorem must bound this actual conditional mean or otherwise prove common-height recurrence. An arbitrary polynomial or doubly exponential cutoff prescription has no authority without derivation from those parameters.

### O6. Independent arithmetic realizations and source-to-receiver constructions

**Entries:** geometric parts of HF/TG/RN and ACT, APF, BSH, CDC, DR, EWJ, FEL, HJ, IRK, MSC, PCS, PTR, RFHM, SC, SEC, W1C, WBF and PW-B.

These are **B-C** tasks until the proposed object and landing are fixed: positive arithmetic cohomology with the correct trace; a mate or descending potential; a globally compatible root; an integral projective lift; a faithful Sonin transport; a defect-preserving shift model; a continuum port; an arithmetic Lee–Yang limit; or a depth-uniform certificate stream. Their desired full packages would be RH-sufficient where the associated receiver is proved.

None follows from constructing an arbitrary self-adjoint operator, positive finite spin model, formal determinant or scalar genealogy. Prove literal arithmetic coefficients, completion/poles, domain, multiplicity and converse spectral identification where needed. Zero-based proofs remain permitted; what cannot be assumed is the positive/location property the argument is meant to establish.

### O7. Quantitative approximation and limits in the complete receiving form

**Programmes:** APT, BiScale, BVI, THIM; applications across RW/EWU/OWU/HF, PM/CTF, SZ, RN and several candidates.

**B-C:** construct a family whose complete-form approximation error tends to zero in the same regime where it detects a hypothetical negative direction. Track growing support, coefficients, anchor size, height, damping, origin concentration and polar escape. If the resulting family is separating/dense and independently nonnegative, its full theorem becomes **B-RH**.

BiScale's error `K²+2K‖F_ref‖` makes the needed accuracy explicit; it does not make `K` small. APT supplies a joint complete-form smoothing error for arbitrary growing finite translated-tent patterns, and the same family detects an explicit off-line model. **The remaining steps are actual arithmetic sign and sufficient actual-zeta separation/coverage.** Its direct critical-tail analysis is a separate unfinished route. THIM's primitive near-null family is not a density theorem. A candidate compactness theorem must survive the actual-prime escaping packet counterexample, and must preserve the complete form, not only unweighted `L²` mass.

### O8. Every-height exclusion and residual exceptions

**Entries:** LA, XN, WD, HCF, JAS and any localization proposal; SRT is the diagnostic.

**B-RH:** prove that every possible off-line configuration is excluded, including clusters, near-double pairs and a finite residual exceptional set. The corpus's exact diagnostic split is approach-to-line plus the asymptotic abscissa law; it is not a mandated proof format.

A localization mechanism needs joint profile/height/aperture bounds strong enough to reveal the displacement it claims to exclude. SRT shows fixed-profile eventual positivity can hold without this selectivity. XN needs interior disc margins, not just boundary sign. Global zero density and arbitrary finite-height checks do not by themselves remove residual exceptions. A theorem controlling an entire cluster could avoid separately counting its members.

## 3. Does this require a new field of mathematics?

**There is no evidence proving that a new field is necessary.** An independent estimate in existing analytic number theory, an unexpected factorization, or a new arithmetic realization could suffice. Conversely, adding more equivalences or naming an umbrella “positivity theory” does not create the missing mathematics.

Several familiar theories already address parts of the problem: explicit formulas and sieve/correlation methods; harmonic analysis and uncertainty; moment problems and de Branges spaces; nonlocal Dirichlet forms and ground-state transforms; spectral/perturbation theory; and concentration/compactness methods. For example, nonlocal ground-state transforms and Allegretto–Piepenbrink-type results are established parent mathematics, with precise hypotheses. [Frank–Lenz–Wingert](https://authors.library.caltech.edu/records/5ke56-ymh17). ACT must check those hypotheses for its folded arithmetic form; a finite matrix theorem does not transport itself to that form.

The strongest case for a broader programme is that the same combination repeatedly resists these methods: **literal arithmetic correlations, an indefinite complete energy, and several parameters tending to their limits together**. A useful theory would explain when this combination admits a sign or a quantitatively controlled defect. Its novelty would be a theorem accomplishing that, not a new name for the combination.

### 3.1 A possible unifying programme: arithmetic energy across scales

This is a proposed research direction, not an established new discipline or a claim of priority. It should initially be pursued through existing BVI, BiScale, THIM, APT and ACT interfaces. A new umbrella is justified only if a new theorem actually unifies them.

**Objects and language.** Work with the literal coefficient row (`μ`, a specified taper, or `Λ`), its arithmetic clock/cutoff, and the complete quadratic form together. An object must retain its mean, diagonal, signed mixed terms, prime-power incidence, Gamma contribution and polar charges. A transformation carries an explicit domain, error bound and parameter dependence. Distinguish an observation of the source from the source itself, and an exact identity from an upper/lower bound.

**Mechanism sought.** Arithmetic relations between different pieces should pay a negative or divergent term before absolute values erase the cancellation. A successful mechanism would produce either a summable signed remainder, a complete-form domination inequality, or a controlled passage to a sufficiently rich test family. It would also explain precisely when this is impossible and what correction restores a valid theorem.

**Possible tools.** Signed Gram estimates for moving floor kernels; exact divisor/successor incidence; multiscale decompositions retaining cross-depth terms; quantitative observation inverses in the receiving graph norm; constrained ground-state identities; and defect measures recording energy lost at the origin or infinity. Each has an existing mathematical parent. Their arithmetic application and a useful combined theorem would be the contribution.

**First falsifiable targets, rather than a promise to solve everything:**

| Track | Question to answer | Concrete target | Immediate failure test |
|---|---|---|---|
| **Signed arithmetic transport** | Can the literal mixed terms beat the available unsigned bound at a scale the receiver uses? | At one specified `0<ε₀<1/2`, bound the complete dyadic Vaughan energy by a summable sequence; subsequently seek a cofinal range of dampings. | Retain all 25 ordered Gram entries, actual coefficient products and moving floor endpoints. A nonsummable positive majorant or a conservation identity cancelling the target is no improvement. |
| **Arithmetic form domination** | Which exact arithmetic relation pays the reflected collar and pole potential? | For one fixed admitted ACT profile, prove the remainder-versus-collar inequality on an explicitly stated growing test class; separately prove full-class coverage if claiming RH. | Single-shift pointwise supersolution is already false. Localization defeats every fixed universal THIM mass-absorption constant. A replacement must retain the compensating remainder. |
| **Limits with complete energy control** | What additional data prevent loss of the sign-relevant energy? | A decomposition or quantitative approximation theorem retaining origin concentration, polar escape and coefficient/cutoff growth, followed by a proved separating-family statement. | Apply it to actual-prime escaping packets and repaired factorial families. Any theorem excluding these without an additional hypothesis is false; any theorem compatible with them must explain why the target family differs. |
| **Arithmetic realization** | Can a source-defined operator or geometry enforce the required sign without importing it? | Construct an explicit domain/form/trace model and prove the exact Xi landing, including poles, Gamma data and multiplicities. | Test shifted-zeta/Beurling examples under exactly shared hypotheses, arbitrary diagonal self-adjoint models and zero-indexed constructions. Generic spectral reality is not enough. |

The first track is a specific BVI/PM problem. The second is an actual odd-Weil problem. **There is no proved theorem making them the same task.** A unification would itself have to identify the sources, domains and complete energies quantitatively. Clock-to-prime-chain identities alone do not do that.

### 3.2 A separate possible theory of conditioned arithmetic recurrence

BAG deserves its own mechanism rather than forced inclusion in a quadratic-form slogan. Its objects are finite-prime return events, centered tails of the actual zeta function, conditional measures and analytic norms on a whole disc. Its key question is whether arithmetic tail cancellation survives the rare event that aligns the head.

A useful tool would give an explicit estimate for a conditional tail norm in terms of head size, tolerance, event density, strip position and cutoff, strong enough to choose one common return height. It must beat or exploit the generic `1/κ` conditioning loss and control the order of limits. A first result could cover a stated parameter range without giving RH. Independent random phases are a comparison model, not a proof for the actual deterministic function.

This requires stronger conditional correlation control; there is no established necessity for an entirely new field. It is also not established that BVI observability alone supplies these conditional estimates.

### 3.3 Geometric/physical alternatives remain optional

A cohomological trace with positivity, an arithmetic Hilbert–Pólya construction, or a prime-faithful Lee–Yang limit could reorganize the problem dramatically. Such a programme would need objects carrying exact arithmetic operations, an appropriate duality or involution, a domain supporting the required trace, and a theorem forcing the spectrum/zero support to the line.

Its central questions are concrete: what object produces the prime powers? Where do Gamma and the poles live? Which trace recovers the explicit formula? Why is the complete form positive? Does the model include every zero with its multiplicity? What convergence preserves the divisor? These questions distinguish a mathematical construction from attaching zeta zeros to an arbitrary real spectrum.

No theorem here requires an `F₁` geometry, forbids all compact-resolvent models, or says a valid proof must be nonlinear. Those are hypotheses about future architecture, not consequences of the current no-go results.

## 4. Criteria a successful programme must meet

1. **Exact target and strength.** Give a quantified theorem, its source class and the proved implication it would use. Label a fixed-parameter improvement separately from RH closure.
2. **Independent arithmetic input.** Identify the first new inequality or construction. Do not hide positivity, a global norm bound, zero-free convergence or source faithfulness inside a definition or admission premise.
3. **Complete accounting.** Retain mean, diagonal, cross terms, polar/Gamma charges, residues, endpoint errors and inherited history. A positive component or small contrast does not sign the full form.
4. **Correct limits.** State dependence on every changing parameter. Prove the topology and norm the receiver actually consumes; pointwise, strong, trace-norm and graph convergence are different claims.
5. **Selectivity.** Prove that a hypothetical off-line configuration violates the target, or prove the family is dense/separating in the needed sense. Detection without exclusion and asymptotic blindness without normalization are both incomplete.
6. **Scoped falsification.** Test actual counterexamples and extremizers. Keep their exact hypotheses. Reflection-even squared displacement can be useful; arbitrary generic positivity cannot locate support.
7. **Sharp scope.** Specify the strongest proved boundary, classification, decomposition or replacement hypothesis when a mechanism fails. Failure of a construction does not establish failure of its entire route.
8. **A complete mathematical theorem.** Every claimed advance must have a dependency-closed proof and an exact comparison with existing results. Formal correctness and scientific novelty are separate requirements.

## 5. Existing inputs and concrete research targets

The literature provides substantial intermediate results without the closing quantifiers. Fixed-degree eventual Jensen hyperbolicity leaves common all-degree positivity unresolved; the nonnegative de Bruijn–Newman constant leaves the opposite bound required by RH unresolved. [Jensen hyperbolicity](https://arxiv.org/abs/1902.07321), [de Bruijn–Newman lower bound](https://arxiv.org/abs/1801.05914).

Two quasi-RH preprints claim zero-free half-planes above `7/8` and `11/12`. These are **unverified preprint claims**, not established inputs here. Even if valid, neither reaches `1/2`. A separate correlation preprint claims fixed-affine Liouville logarithmic savings and qualitative ordinary correlations in its stated class, explicitly without growing-affine-coefficient uniformity. That statement does not supply the complete moving-weight BVI estimate. [Quasi-RH at `7/8`](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf), [quasi-RH at `11/12`](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf), [ordinary correlations](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf).

The principal research targets are:

| Approach | Concrete next theorem | What would remain after that theorem |
|---|---|---|
| **Cancellation** | A complete signed-source energy bound at one explicit damping `0<ε₀<1/2`, retaining all mixed terms. | Bounds cofinal towards zero, or another proved implication reaching RH. |
| **Odd Weil positivity** | A compensated remainder/collar inequality on a specified admissible class. | Coverage of every odd test required by the receiver. |
| **Approximation** | Complete-form error control and separation of the relevant actual-zeta negative directions by the same family. | Independent arithmetic nonnegativity on that family. |
| **Conditional recurrence** | A centered-tail bound on the actual finite-head return event, with explicit joint parameter dependence. | Strength sufficient to obtain common physical returns on every required disc. |
| **Arithmetic realization** | An explicit source-defined object with exact coefficients, domain, trace/completion and a proved positivity mechanism. | Faithful identification with the full Xi divisor, including multiplicity and any limiting passage. |

These are alternative research attacks. No theorem guarantees that any proposed intermediate construction exists or is easier than RH. A successful programme must supply an independent bound or construction with the precise strength its route requires.
