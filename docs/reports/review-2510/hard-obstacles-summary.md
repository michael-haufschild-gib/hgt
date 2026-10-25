# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-25. This summary covers all 31 routes, 17 candidates, PW-B and the supporting programmes in the [complete report](hard-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: Lean corpus search and source reading, recorded in `logs/review-2510/`. Nothing was compiled.

## 0. The frontier in five statements

1. **Every unconditional positivity theorem is a blindness theorem.** The corpus proves positivity only on carriers that cannot see off-line zeros: low-grid-blind tests, bounded Meyer orbits, positive Hermitian degrees, jointly blind families, large-height heated heads, small apertures, and frequency averages. RH is the statement that the actual arithmetic source is itself blind. No route yet contains a **forcing law** that places the actual source in the closure of its blind carrier.
2. **Cancellation routes have no rung between Vinogradov–Korobov and quasi-RH.** WL, PBM, JAS, the balanced Möbius statistic, the centred-prime band, short-window Möbius saving, the Vaughan empty leg, and graded RW/ACS floors are all formal equivalences. In each, the first gain beyond Vinogradov–Korobov is a fixed zero-free strip ([L]).
3. **Positivity is proved on average beyond the square-root threshold.** Averaged Weil positivity holds unconditionally at aperture `κ₀ log Γ`. Subpower averaged coercivity holds up to prime support `Γ^{4/3}` ([L]). The remaining wall is **selection**: control at individual heights, in particular at zero ordinates.
4. **Faithfulness costs simplicity.** On the genuine Meyer surface:
   - ordinary trace positivity is equivalent to RH;
   - every faithful, jet-retaining positivity is equivalent to RH plus simple zeros;
   - every positive Hermitian degree is blind, seeing only critical values.

   A route that proves RH through a faithful realization proves more than RH.
5. **The routes are no longer short of criteria.** They are short of producers: a signed estimate (cancellation family), a sign on a complete class (positivity family), or an independently constructed, oriented object (realization family). Each of these is an instance of the forcing problem.

## 1. Just work

These obstacles can be removed with existing mathematics. Each stops before any unknown estimate. "Just work" does not mean small; W7 in particular requires certified numerics.

| ID | Task | Concrete content | Completion criterion |
|---|---|---|---|
| **W1** | **Integration** | Wire the 18 committed modules that no umbrella reaches: thirteen ACS modules (the Meyer chain, majorant cone geometry, smooth reading kernels), AOT active cosets, the THIM Dini law and threshold, APT `CriticalPrimeChannelBeyondLinearWindows`, and the Landau formula. Commit the umbrella imports for the prime-shell ladder, `MeyerSourceIntersectionSurface` and the global majorants. After a file check, integrate the 11 working-tree modules, including the bounded Meyer surface and the ground-rate equality. `ZetaSmoothedLandauFormula` now contains the assembled estimate `exists_smoothedLandau_le` in working source, sorry-free; it needs integration only. | Each module is checked with `lake --old env lean` and imported. Labels move from [S] to [L]. |
| **W2** | **Certificate replacement** | Replace `native_decide` in `RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean:749` (PA order-24 quadrature) with kernel-checked rational arithmetic. The same applies to the non-route use in `HTGeometry/MilnorKTwoSteinbergSurjective.lean:138`. | No forbidden tactic remains in the project corpus. No `sorry`, `axiom`, `opaque` or `unsafe` is present. |
| **W3** | **Status-record corrections** (needs the user's permission) | The frontier map and killed-routes catalogue still report summation-scope defects in BVI and APT. They do not exist: Mathlib parses `∑ x ∈ s, f x - c` as `(∑ …) - c`. The balanced Möbius and centred-prime band equivalences with `Θ < 1` should be relabelled [L]. Filtered coercivity is complete. Integration labels need updating. | The status documents agree with the source. |
| **W4** | **Finite identities and certificates** | Gram matrices, Hausdorff and Hankel blocks, Jensen and heat-Hankel ranks, finite divisor heat transforms, finite schedules and histories, finite incidence ledgers, finite Robin and Li checks, and finite budgets for JAS and Vaughan packets. | Every finite term and error is certified. None of this gives a cofinal theorem. |
| **W5** | **Premise checks for specified sources** | Regularity, support, integrability, cutoff, real-lag decay and domain membership for a named test or family (the SZ moving and noncompact limits, CHMD domains, candidate sources). | The exact hypotheses of an available transfer are discharged. Unknown uniform family bounds are not hidden here. |
| **W6** | **Transport of proved inputs** | Push proved estimates through exact dictionaries: the width functor, RW↔SZ↔CHMD, HF→AIP, the Weil-margin→heat window, and the graded Sobolev floors. Damping, aperture, rank, degree, height and horizon quantifiers are all kept. | Each conclusion is stated at its true strength. |
| **W7** | **Certified finite extensions and explicit constants** | Push the pointwise positivity windows beyond full `3/10`, odd `181/500` and primitive `(log 2+1/50)/2` toward the next prime thresholds, using the known Yoshida/Bombieri-type low-sector method with certified numerics. Make explicit the constants `κ₀, c₀, C₀, Γ₀` of averaged positivity, and `R₀, T(λ)` of the radius-head theorem. | Certified finite-aperture theorems. They are not uniform in aperture. |
| **W8** | **Corollary assembly from new theorems** | (i) Merge the RW, SRT and ACS rate dictionaries through `groundRate = polarRate`. (ii) Averaged RR and graded-cone statements on ACS from filtered positivity. (iii) The explicit residual region `{|t| ≤ T(λ), λ ≤ λ₀}` for LA/WD, from the radius-head and KKL results. (iv) Restate ACS effectivity as a bounded-carrier exhaustion criterion. (v) An averaged bounded-energy statement for WL from the high-zero tail and the filtered deficit law. | Each statement is proved from existing theorems. None closes a route. |
| **W9** | **Dependency and axiom audit** after W1/W2 | Run `#print axioms` on route receivers and new capstones. This needs an authorized compile pass; reviews do not compile. | The audit is clean, or each finding is recorded. |

These tasks open no route. Their value is accuracy: after W1–W3 the [L]/[S] labels match the source, and W7/W8 supply the explicit regions that any new mechanism must cover.

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

Each is equivalent to RH or stronger. Statements in different routes that share a receiver are listed once. Solving any one closes every route that uses its receiver.

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit energy, one-sided lag or Abel moment, history floor, regularized abscissa `1/2`, JAS half-power budget, Mertens at square root, late-lag sign. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Cofinal admission as `ε ↓ 0`, equivalently Báez–Duarte residual → 0, signed interior Vaughan energy, or exclusion of cofactor escape. | PM, CTF, BVI, PW-B |
| **B1.3** | **Complete Weil positivity at every aperture.** Low and mixed sectors, Gamma and both polar terms, one shared budget. Equivalently: the nodal inequality, positive Suzuki first variation, odd capacity, one-shift reflected collar, global allocation, the ceiling `O(L)`, Bézout on the exact source cone. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS |
| **B1.4** | **Selection.** From averaged or almost-all-height statements to control at every height, in particular at zero ordinates. | Shared by B1.1 and B1.3. Faces in WL, SRT, ACS, APT. |
| **B1.5** | **Critical-endpoint heat and moment sign.** Coefficient positivity on the bounded-height × small-heat residual region, i.e. the de Bruijn–Newman constant `Λ ≤ 0`. All-rank Hankel positivity at one time. Both literal heat grids at every degree. Rank-uniform Schur decay. The Newton interior margin. Order-uniform passivity. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization.** The Ward cap vanishes. The integer trace residual is a nonnegative sub-unit. Renewal boundary orientation. An effectivity source on the exact cone. A global stabilization weld. Pre-divisor compactness. A descending potential. A centered Ising limit. A nonlocal lossless port. An arithmetic certificate stream. | TG, RN, WD, ACS and all 17 candidates with PW-B |
| **B1.7** | **Single-currency endpoints.** Cofinal contrast equality; subexponential Li floor; eventual Robin tail; recurrence near every possible zero; global index `D < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **Stronger than RH: RH with all zeros simple.** A faithful positive Meyer degree; RR for the Hilbert–Schmidt reserve; exhaustion of the bounded Meyer carrier. | ACS/Meyer faithful branch |


### 2.2 Tier B2: classical open problems weaker than RH

Mathematics has no solution to these either. Each is a first rung or a partial target of the routes.

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | **Quasi-RH**: a fixed zero-free strip, `Θ < 1`. | First rung of WL, PBM, JAS, MC/BVI (balanced band, centred-prime band, short windows), Vaughan empty leg, RW/ACS graded floors, DR. Formally equivalent in these receivers [L]. |
| **B2.2** | **Finite off-line index**: all sufficiently high zeros are critical. | HF/AOG index exit, WD collision masses, uniform heat counts. Stronger than B2.1, weaker than RH. |
| **B2.3** | **Simplicity of the zeros.** | Every faithful realization (B1.8). Meyer numerical = principal. Hilbert–Schmidt reserve RR. |
| **B2.4** | **Density hypothesis / large values beyond Guth–Maynard.** | Extending averaged positivity beyond `α = 2/3`; the zero-side census `HD(1)`; the filtered deficit exponents. |
| **B2.5** | **At least 3/4 of the zeros on the critical line.** | TTPC/ACS certificate: signed coalescent surplus `β ≤ 1/18`. |
| **B2.6** | **Power-saving sign correlations of μ and λ** (Chowla/Elliott with rates). | MC interior anti-alignment, SSA successor constants, BVI balanced rows. |
| **B2.7** | **Hardy–Littlewood prime-pair correlations, uniform near the square-root band.** | TTPC surplus, the selective square-root band, short-window selection (Q1). |
| **B2.8** | **Subconvexity and Lindelöf improvements.** | The KKL horizon constant `27/40`, and so the size of the LA/WD residual region. |
| **B2.9** | **Better upper bounds for the de Bruijn–Newman constant.** | Shrinks the B1.5 residual region. `Λ = 0` is RH. |

### 2.3 Tier B3: open problems isolated by this research

No solution is known, and none is proved RH-equivalent. Several are plausible research targets.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | **Rate equality** `polarGroundEnergyRate = Δ`. | `Δ ≤ polarRate = groundRate ≤ 1/2` [S]. Bounded local depth mass suffices. Failure needs collapsed clusters at doubly exponential height. |
| **B3.2** | **Escape-state classification** of cofactor limits. Equality of the paid ideal with the annihilator, and of the hull with the obstruction hull. Compatibility with the moving boundary. | Inclusions are proved [L]. White noise satisfies PSD, dilation and antipodality. Finite index equals joint multiplicity, and Möbius and Liouville modules are unit-equivalent [S]. |
| **B3.3** | **Quantitative coercivity** of residual/trace reconstruction in the receiver norm. | Only algebraic injectivity is known. The dilation commutator is bounded. |
| **B3.4** | **A jet-retaining completion of Meyer cohomology with tail control**, and source-defined positive carriers beyond the blind carrier. | The origin-L² completion is ruled out. Finite projectors split positive energy with a nonnegative complement [S]. |
| **B3.5** | **Surface section law**: couple the base theta `h⁰` to test components so that it supplies effectivity. | Base `h⁰` RR and Mellin identities [L]. Boolean section counts and finite readings cannot pay. |
| **B3.6** | **Signed shell flux** along the moving prime-threshold ladder. | Birth jumps vanish. The collar bound is `e^{−a}[ψ(e^{2c}) − ψ(e^{2a})]·mass`. Permanently frozen finite prime families fail. |
| **B3.7** | **Short-window averaged positivity.** Find the smallest `H(Γ)` for which averaged Weil positivity holds on `[Γ, Γ + H]`. | `H = Γ` is proved. `H ≍ 1/log Γ` would amount to selection, which is RH-strength. |
| **B3.8** | **A nonlocal shared-budget calculus** for frustrated arithmetic incidence; quantitative cofinal two-tower saving. | Frustration and descent laws are exact; fixed-box gaps are proved. |
| **B3.9** | **Arithmetic input on the residual heat region**; source-selective cofactor repair of the actual heated head. | The model geometry is complete. No universal positive multiplier exists. |
| **B3.10** | **Compatible oriented families** and quantitative bounds on the global index. | Common-endpoint classification; finite-target law. |
| **B3.11** | **Sub-half-damping signed control** of the size-cutoff forward interior; the signed prime-divisor endpoint at `ε = 1/2`. | Exterior paid; `ε = 1/2` paid for the size cutoff; prime-subset cutoffs diverge. |
| **B3.12** | **Order-uniform PA thresholds**; decoupling rank from time for TH and HCF. | Fixed-order thresholds exist; Weil margins give coupled windows. |
| **B3.13** | **Sharp successor constants**: complex floor in `[−1/2, −1/3]`; classification of zero-defect signs. | Odd shifts `1/3` and lag 2 `1/4` are exact; the `f(2)=1` branch is settled. |

## 3. The three questions to answer next

Selection criteria:

1. Each question is weaker than RH, so it can actually be answered.
2. Either answer changes the frontier: a positive answer creates a forcing or selection mechanism; a negative answer is a sharp no-go that names the missing arithmetic input.
3. Together the three cover the three route families, each in its own currency.

Quasi-RH (B2.1) and the de Bruijn–Newman core (B1.5) are not on the list. Both are classical problems on which this corpus has no new leverage beyond restating them.

### Q1. Selection: how short can the averaging window be?

> *What is the shortest frequency window `[Γ, Γ + H(Γ)]` on which unconditional averaged positivity of the complete Weil form at logarithmic aperture holds? Can its exceptional set be shown to avoid zero ordinates in short windows?*

- **Why this question.** Averaged positivity is proved at `H = Γ` with prime support beyond the Nyquist aperture. Pointwise positivity at every aperture is RH. Shrinking `H` is a graded path from the proved statement toward the open one. Every intermediate `H` gives a new kind of partial result, positivity at almost all heights in short windows, which cannot be expressed as a zero-free strip.
- **Known tools.** Zero density in short intervals; Guth–Maynard large values; the all-length Heath–Brown estimate; the phase-selective single-height law; the high-zero tail law.
- **The obstruction to beat.** The syndetic phase obstruction: bad heights recur. The question is whether they can coincide with zero ordinates in short windows.
- **Possible outcomes.** A threshold theorem stating that no `H` below some explicit bound follows from density inputs alone would identify the missing input precisely, namely short-window prime-pair correlation (B2.7). A positive result supplies the missing selection step (B1.4) to RW, SZ, CHMD, EWU, OWU, ACT, AIP, HF, ACS, SRT and WL at once.

### Q2. Forcing in geometry: can the positivity argument behind classical zero-free regions be expressed as carrier positivity?

> *Is there a sharp-stable source carrier, defined without reference to Ξ zeros, that strictly contains the blind (bounded critical) carrier, carries provable trace positivity, and makes every off-line zero in an explicit region produce a negative element? Calibration: does it reproduce the de la Vallée Poussin region?*

- **Why this question.** The geometric programmes (ACS, Meyer, AOG, HF) now have genuine Riemann–Roch, exact Hodge-index equivalences and a complete classification of positive degrees. All of it is blindness. The only unconditional forcing argument in the subject is the de la Vallée Poussin positivity `3 + 4cos θ + cos 2θ ≥ 0`, applied to Euler-product coefficients. That argument does exclude zeros, in a region of logarithmic width.
- **What a positive answer gives.** If that argument can be realized as positivity on a source-defined carrier larger than the blind one, the geometric framework contains forcing. Widening the carrier then becomes a geometric problem; the Vinogradov–Korobov region would be the next calibration.
- **What a negative answer gives.** A maximality theorem would show that every source-defined positive carrier lies inside the blind carrier. Geometric positivity could then never force anything without input from outside the carrier, and that input would have to be named. This retires carrier exhaustion as a mechanism.
- **Known tools.** The Meyer finite-jet and projector algebras; the Hermitian-part theorem; the quasi-inverse radical; the Hilbert–Schmidt reserve identity; the origin-mass no-go, which fixes which completions are excluded.
- **Routes fed.** ACS, HF, AOG, TG, RN, WD and every candidate.

### Q3. Escape: which abstract escape states survive all proved constraints?

> *Classify the cyclic critical-Wiener modules compatible with every proved constraint on actual cofactor limits: unit receiver mass, sharp dilation contraction, PSD finite packets, antipodality, the signed Gram collapse, full paid-ideal annihilation, and the moving forcing boundary with its absolute word tail. Does white noise, or any model, survive the last two?*

- **Why this question.** Cancellation routes have no rung below quasi-RH. Their only non-averaged handle is the escape alternative: either admission or escape, with escape carrying a rigid module structure. Classifying the escape states is a problem about an explicitly defined abstract class, so it is weaker than RH.
- **What a positive answer gives.** If no model passes every constraint, escape is impossible and the small-damping energy problem B1.2 is solved.
- **What a negative answer gives.** An explicit surviving model is a sharp no-go. Its structure states exactly which arithmetic input (ideal equality, coercivity, moving-boundary cost) the actual Möbius source must supply. B3.2 and B3.3 become concrete.
- **Known tools.** Paid-ideal annihilation; the common-limit Wiener module; finite index as joint multiplicity; unit transport; quantile antipodality; the bounded dilation commutator; the power-subtracted forcing.
- **Routes fed.** PM, CTF, BVI, MC, FU, RP, JAS, PW-B.

The three questions are the forcing problem in each family's own currency: selection by height (Q1), carrier exhaustion (Q2) and escape exclusion (Q3).

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows that a new field is necessary. The corpus nevertheless shows a consistent pattern across several hundred tested mechanisms in the [killed-routes catalogue](../rh-killed-routes.md):

- **Every unconditional result is a dominance or blindness result.** The archimedean term pays above a horizon; heat pays above a height; averages pay above a density threshold; bounded carriers are blind by construction.
- **Every failed mechanism fails on a countermodel that satisfies its axioms without RH.** The battery includes:
  - golden Beurling curves (integral Euler data, functional equation, positive counts);
  - planted Euler factors;
  - shifted pairs `ζ(s−a)ζ(s+a)`;
  - Wolff configurations;
  - white-noise cofactor kernels;
  - magnitude and parity twins;
  - Euler-blind Gaussian-cosine sources;
  - `Γ_R^d` functional-equation abundance.
- **The known forcing mechanisms do not transfer.** Weil's proof for curves forces through the geometry of `C × C` (sections, ampleness, Frobenius graph). No such surface exists over `Spec ℤ`: the corpus builds scaling and Meyer surfaces whose Hodge index is equivalent to RH, but has no independent source of ampleness. The de la Vallée Poussin positivity forces, but only up to regions of Vinogradov–Korobov type.

The missing ingredient, **a forcing law that is selective for ζ, quantitative across limits and independent of the conclusion**, has no counterpart in any existing toolkit over number fields. If such a law exists, it will probably look like a new field: a theory that treats estimates, positivity and geometry as three readings of one structure, rather than a new estimate inside one existing discipline.

### 4.2 Working name and subject

**Arithmetic forcing theory** (alternatively: *critical arithmetic positivity*). Subject: how the multiplicative and additive structure of an arithmetic source forces its spectral readings into blind carriers, with every loss priced across scale, limit and completion.

- **The phenomenon to explain.** Arithmetic sources sit exactly on the critical boundary between dominance (provable) and cancellation (unproved). The theory should explain why actual ζ, and not its countermodels, stays blind as the controlling parameter crosses that boundary. The parameter can be rate `σ → 0`, aperture `A → ∞`, heat `λ → 0`, damping `ε → 0`, window length `H → 0`, or carrier → everything.
- **Its character.** Closer to a **renormalization theory of positivity** than to a single estimate:
  - flows in aperture, damping and heat, with arithmetic beta functions (the prime-shell flux is the first one already computed);
  - fixed points (blind carriers);
  - relevant directions (off-line zeros);
  - a forcing law stating that arithmetic makes those directions irrelevant.

  It merges Arakelov-style intersection theory (sections, `h⁰`, Riemann–Roch), the spectral analysis of quadratic forms and their completions, and sieve-style selection.

### 4.3 Criteria it must meet

| Criterion | Test against the corpus |
|---|---|
| **Selectivity** | Distinguishes ζ from the whole countermodel battery. It must use more than functional equation, positivity, integrality, Euler form, finite readings or local collars. It must survive every single-node perturbation `Λ + δ·δ_m`. |
| **Non-circularity** | No interface field, structure or premise contains the conclusion. The object is constructed before its sign, and the sign proof does not read zeros. |
| **Uniformity across limits** | Tails are paid in a jet-retaining topology, not the origin-L² completion. Aperture, height, rank, damping and window length are controlled together. |
| **Positivity–faithfulness separation** | RH follows from non-faithful (trace) data. Simplicity is a separate output, never a hidden input. |
| **Calibration** | Reproduces Weil's proof for curves and explains why the golden datum fails it. Reproduces the de la Vallée Poussin, Vinogradov–Korobov and Ki–Kim–Lee results as dominance-regime special cases. |
| **New partial results** | Produces results that are not zero-free strips, for example positivity at almost all heights in short windows, geometric zero-free regions, or an escape classification. This is evidence that the theory adds mechanism rather than criteria. |

### 4.4 Questions it must answer

1. **What arithmetic invariant separates ζ from Beurling systems that share its functional equation, Euler form and positivity?** Integrality (Witt), λ-ring and Rosati structure, and positive counts are all shown not to be it.
2. **How does blindness propagate under the flows?** What is the sign of the arithmetic beta function (shell flux, collar correlation), and what keeps the ground energy above zero across the prime-threshold ladder?
3. **What is the right completion?** Which topology on arithmetic sources keeps every jet, makes trace energy lower semicontinuous, and controls actual tails? The origin-L² completion is excluded.
4. **How does an average become a point?** What selection principle passes from height averages to zero ordinates despite syndetic phase recurrence?
5. **What replaces the ample class and Frobenius graph of `C × C`?** That is, what surface-level `h⁰` with independent Riemann–Roch would yield effectivity?
6. **How can quantization force vanishing?** The corpus has many integer phenomena: even collision masses, two-scale deficits equal to four times a count, quotient index finite or continuum, winding numbers, a char-zero Stepanov argument. Which arithmetic inequality pushes an integer charge below one?
7. **How are shared resources paid?** What nonlocal allocation calculus pays frustrated prime incidences from one budget?

### 4.5 Tools it would develop

- An **arithmetic beta-function calculus**: signed flux formulas for the aperture, damping and heat flows, with sign criteria computable from source data.
- **Jet-retaining completions** with lower-semicontinuity and tail theorems for Meyer-type cohomology and cofactor modules.
- **Short-window selection lemmas** turning density information into control at individual heights, with explicit exceptional sets.
- **Carrier-positivity constructions** generalizing de la Vallée Poussin positivity from trigonometric polynomials in `log p` to sharp-stable source carriers.
- **Escape-state classification** for cyclic critical-Wiener modules under source constraints.
- An **arithmetic Stepanov method**: auxiliary polynomials or sections over `ℤ` whose forced vanishing multiplicity bounds spectral counts. A char-zero shifted-subgroup Stepanov lemma already exists in `HTGeometry`.
- A **nonlocal budget calculus** for frustrated signed incidence, with canonical-path packing and a single shared reserve.

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | Arithmetic sources: prime and Möbius rows with Gamma and pole completion. Receivers. Carriers, and blind carriers among them. Readings. Flows and their beta functions. Shells and collars. Cofactor modules with paid ideals, hulls and escape states. Meyer cohomology with its jets, sharp involution and positive degrees. Scaling surfaces with sections and `h⁰`. Orbits, families and indices. |
| **Language** | It must distinguish: equality, receiver equivalence and directional transfer; source and receiver; signed energy and absolute majorants; blind and faithful; finite, countable and uniform limits; distinct zeros, multiplicity and multiplicity squared; algebraic and bounded inverses; dominance regime and critical regime. |
| **Mechanisms to discover** | A **forcing law**: arithmetic places the source in the closure of a blind carrier. A **selection law**: averages become points. A **quantization law**: integer charge with a sub-unit bound gives zero. A **payment law**: one nonlocal budget pays every frustrated cost. |
| **First milestones** | (1) Recover the de la Vallée Poussin region as carrier positivity (Q2). (2) Averaged positivity on windows `H = Γ^θ`, `θ < 1` (Q1). (3) A classification of escape states with the moving boundary included (Q3). (4) A surface `h⁰` with independently proved RR on a nontrivial test class. (5) The sign of the shell flux on one ladder step beyond `3/10`, from a structural argument rather than a certified computation. |

Each milestone would be a theorem of a type the corpus does not yet contain: a forcing statement rather than a blindness statement. If several of them succeed, the field exists. If all of them fail, each failure is a sharp no-go that narrows where a forcing law could be.
