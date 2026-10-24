# RH obstacles: routine work, open mathematics, and the case for a new field

**Status at 2026-10-24.** 31 live routes, 17 standalone candidates, PM's PW-B branch. No route closes with known methods. Everything still missing is either an arithmetic estimate at the critical rate, a transfer that keeps orientation, or an arithmetic object built before the zeros. The preliminary steps toward each are largely proved, and each remaining target is a single precise statement.

Companions: [complete route report](hard-obstacles.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: the six named reports, corpus searches, and Lean statements read directly; nothing was compiled.

## 1. Categories

- **Just work.** The method and all inputs exist. Remaining effort is integration, formalization of an existing paper proof or published estimate, explicit regularity, a supplied finite certificate, or application of a proved dictionary.
- **Open, RH-strength (B-RH).** A target proved sufficient for RH. RH is an [unsolved Millennium Problem](https://www.claymath.org/millennium/riemann-hypothesis/); nobody has a solution.
- **Open, auxiliary (B-C).** A precisely formulated question with no known method. Some are classical open problems (quasi-RH, pair correlation beyond `α = 1`); others are corpus-specific and may be weaker or tractable. Worldwide novelty is not claimed for those.

A structural fact governs both open tiers: for every route whose graded receiver reads the zero width `Δ`, the first quantitative improvement over present technology, a bound at any fixed rate below `1/2`, is already a fixed zero-free strip `Θ < 1` (quasi-RH). The unconditional inputs that feed these receivers — the de la Vallée Poussin and Vinogradov–Korobov zero-free regions, zero-density and Guth–Maynard large-value estimates — improve constants or subexponential factors but never the exponent.

## 2.1 All "just work" tasks

None of these closes a route; each converts proved or published mathematics into usable, certified input.

| ID | Deliverable | Existing input | Outside this task |
|---|---|---|---|
| **J1 — Integrate working source** | Umbrella wiring, leaf checks and transitive axiom audits for the four unwired modules: `SuzukiCriticalL2FirstVariation` (with `SuzukiCriticalL2Arithmetic`, reachable only through it; R/Suzuki); `CHMDSharpWindowNodalConvergence` (R); `LambdaRingEffectivityAndHeckeLefschetzRigidity` (K); `ProducerCompletionAndPrimeClockKernelSynthesis` (B). Leaf checks and audits for the recently wired modules (compensated floor and vanishing-aperture transport (C), Suzuki `L²` pole/energy/cusp/normalization (R), Gaussian-tail bracketing and CHMD sharp cut (R), grid-tent transfer (A), complementary sector (C), recovery constants (B), Gaussian divisibility (R), centered damping spectrum (V)), none of which was compiled for this review. | Complete proofs; a text scan finds no `sorry`, `admit`, `axiom` or `native_decide`. | Any new estimate. |
| **J2 — Resolve the APT name clash** | Rename or privatize one of the two public `envelopePrimeMajorant_one_eq` (A:ExplicitCollarThresholdsAndKernelShape vs A:TheLinearWindowOfTheCriticalPrimeChannel), then integrate the explicit kernel-shape results (APT-7). | Both proofs exist; both modules are imported by the umbrella. | Positivity beyond the stated families. |
| **J3 — Formalize published analytic inputs** | The all-length Heath-Brown pair-sum bound (`HeathBrownPairSumBound` is still a Prop; restricted and middle-range pieces exist) and the sharp all-`k` S₂ family behind Guth–Maynard Prop. 12.1. | Statements used in the published [Guth–Maynard argument](https://arxiv.org/abs/2405.20552); large-value theorem already formalized unconditionally. | Any improvement on Guth–Maynard; these bounds still allow off-line zeros. |
| **J4 — Formalize paper-proved results** | (i) Centered-heat detector: a negative compact Weil witness for any off-line zero at aperture `≤ Cδ^{−2}(4+\|γ\|)^{38}`; (ii) CHMD sharp-cut generator-domain admission with bounded arithmetic commutator; (iii) SZ joint common-window Gamma-liminf with constant recovery; (iv) SZ literal high-dyadic-family deficit without smoothing. | Pipeline papers in stage 2 (named by the frontier map; not read here). | (i) is a detector of hypothetical zeros, not a sign; (ii)–(iv) give no global sign. |
| **J5 — Discharge explicit premises** | Fourier decay, integrability, collar support and derivative bounds for a specified compact source, with aperture-dependent constants. | Integration by parts; existing weighted-floor and compactification theorems. | Uniform constants over an unknown family. |
| **J6 — Evaluate constants and ranges** | Visibility lags, collar thresholds, window radii for a chosen probe, the `(1/2, 75)` allocation constant, centered-prime ranges. | Explicit formulas. | Moving an exponent; larger positivity windows are research. |
| **J7 — Apply proved dictionaries** | Translate a specified source through: the width functor; the aperture dictionary and aperture transport; the compensated-floor equivalence; Bohr-hull / repairing-ideal index formula; HF ceiling ⇒ AIP allocation; RW margin ⇒ heat-Hankel window; SZ first variation = Weil energy; ACS RR ⇔ AIP allocation; Lefschetz–adjunction identity. | All [L] except where marked [S]. | A converse not proved, a global sign, or a change of limit order. |
| **J8 — Verify supplied finite certificates** | Finite Frobenius/tower Gram indices, SAEI path packings and supersolutions, BVI radical-state tests at a fixed horizon, finite Hausdorff/Jensen/moment lists, finite heat-Hankel ranks, finite photonic stacks. | Exact finite objects and verification methods. | Finding a successful certificate; cofinal versions. |

**Qualification to J7:** applying the global HF ceiling dictionary requires
`windowCeiling L ≤ exp(L/2)+B(1+L)` eventually. This input itself implies RH
(`BiScaleUncertainty.PrimeWindowCeilingRHCriterion.riemannHypothesis_of_windowCeiling_le`);
choosing a compact source does not discharge it. The unconditional local odd-window
allocation and graded `(1/2,75)` allocation can be instantiated. The global ceiling
application belongs to A3 until its missing input is proved.

Certification: [routine-input certificate](../../drafts/pipeline/3-formalized/review-2410-just-work-certification.md)
records the completed leaf checks, axiom audits, concrete instances, and exact J7 scope.

Completed (not to be repeated): the real centered damping spectrum is in the tree; the odd `181/500` window has been transferred to the lag family (S:SharperOddWindowAndPhaseSelectiveSingleHeightLaw); the AIP odd-lattice calibration has its axis jets and self-energy asymptotic; the BiScale recovery constants are sharpened.

## 2.2 Open mathematics

### Tier A — RH-strength targets (B-RH); nobody has a solution

Each target collects every route that shares the same missing input. One complete solution of any target proves RH.

| Target | Precise open statement | Routes |
|---|---|---|
| **A1 — Critical cancellation of the actual prime/Möbius source** | One-sided lag, spline-packet, deficit-primitive or Mertens bound at every positive exponential slack; equivalently the interior anti-alignment gap `θ(ε,t) < 1` for `0 < ε < 1/2`, `t ≠ 0` (proved only on the VK and bounded-height small-`ε` collars); regularized prime series convergence for `σ > 1/2`; Robin's inequality on extremal integers; JAS power budget `y^{1/2}`. | WL, MC, PBM, RB, SRT, JAS, FU, RP, LI (in its own currency) |
| **A2 — Small-damping signed energy** | A horizon-uniform signed loss, corrected-loss or energy budget at arbitrarily small fixed `ε > 0`; equivalently vanishing Báez–Duarte/Haar error, compensated interior contraction, or first-column admission below half damping. | PM, CTF, BVI, ACCE, ACCC, SAEI |
| **A3 — Complete Weil positivity** | Nonnegativity of the full prime–Gamma–polar form at every aperture; equivalently payment of the finite low-frequency sector and its mixed terms uniformly in aperture, the shared incidence allocation, one-shift variation, the blind minima, the sign of SZ's first variation, the CHMD nodal inequality, or the arithmetic Hasse–Weil bound on the scaling surface. | RW, SZ, CHMD, OWU, EWU, ACT, AIP, HF, ACS, TT |
| **A4 — Uniformity of a proved finite positivity** | All degrees, ranks or heights at one heat time; order-uniform Hausdorff threshold; rank-uniform Schur decay; global disc margins; matrix-complete sub-unit trace. | LA, TH, HCF, GTA, PA, XN, TG |
| **A5 — Return and continuation through possible zeros** | Strong recurrence near every strip point (locally equivalent to nonvanishing); global dyadic root continuation; vanishing of the Ward cap; cofinal contrast balance. | BAG, DR, WD, FEL |
| **A6 — A faithful pre-divisor producer** | Any of the candidate constructions with its proved landing: centered Lee–Yang limit, lossless prime port, pre-divisor stabilization weld, compactness or confluence forced from source data. | All 17 candidates, PW-B |

### Tier B — auxiliary open problems (B-C)

| ID | Problem | Why it matters | Status of knowledge |
|---|---|---|---|
| **B1** | Any fixed exponent below `1/2` for any `Δ`-reading receiver. | First nontrivial step of A1–A3. | Equivalent to a fixed zero-free strip; classical open problem (quasi-RH). |
| **B2** | Exclude collapsed off-line multiplicity clusters at doubly exponential height. | The only obstruction to rate equality and to an unrestricted mass floor (R:OffLineClusterWeilUnbounded, D:MasterDCIPincerTheorem, C:CompensatedWidthFloorAndGroundEnergyRate). | Requires local multiplicity control beyond the known `O(log γ)`; no known method. |
| **B3** | Coalescent prime-pair surplus `≤ (1/18 + o(1))N` at bandwidth `4/3`. | Gives a `3/4` critical-line proportion (P:SmoothWeightedCertificateAtFourThirds). | Pair correlation beyond `α = 1`; open beyond the corpus. |
| **B4** | Balanced-scale row cancellation with cubic/quartic tails paid. | Feeds A1 and A2. | Leading coefficient is arbitrarily small [L]; tails open. |
| **B5** | A continuum arithmetic supersolution with packed shared paths for the odd Weil ledger; a lower bound for the ground energy from the frustration count. | Converts finite frustration payment into A3. | Finite models solved; frustration lives on prime-sum edges; the ground energy is bounded above by the frustration mass, not below. |
| **B6** | An arithmetic law distinguishing ζ from the golden Beurling datum (Witt-integral, FE, positive counts, impure). | Necessary for any effectivity route (A3/ACS). | Curve models: purity ⇔ bounded traces ⇔ Hasse–Weil; no ζ analogue. |
| **B7** | Horizon containment: exclude escape of deeper zeros to growing heights or tiny transform amplitudes. | Turns visibility into sign (SRT/RW). | Escape is compatible with every proved positivity window. |
| **B8** | Relative-to-absolute compensation: absolute transverse energy from super-logarithmic relative decay. | A2 at each fixed damping. | Normalized blow-up profile: admission or escape to horizon; exclusion open. |
| **B9** | Aperture-uniform constants for the CHMD quotient and graph norms. | Removes the last fixed-aperture qualification in U2 completions. | Fixed-aperture versions [L]. |
| **B10** | Nonempty Bohr-hull classification for actual μ at or below `Δ`, a repair leaving the Wiener unit class, and a non-perturbative index formula giving the paid class of the Möbius weight from arithmetic counts. | A2 in ideal-theoretic form. | Units cannot repair; hulls equal translated-zero hulls above `Δ`. |
| **B11** | Sharp observation horizon and conditioning for arbitrary-phase sieve rows; exact two-tower blind optima; exact full-grid tower deletion extrema; exact multi-tower joint capacity with the actual unequal weights; APT window-width law. | Calibrates the cost of information (Wall 3). | Bounds and enclosures [L]; sharp values open; likely tractable. |

### Solved or sharpened questions (not to be reopened)

| Former question | Present status |
|---|---|
| CHMD quotient lower bound and whole-quotient landing | Solved at fixed aperture: completion = supported maximal graph, with lower bound. |
| SZ passage `ω → 0` with all cusps | Solved for compact `C²` [L] and compact `L²` [S]: the limit is the Weil energy. |
| Mass-floor converse from width (SR-3, CE-6) | Exact dichotomy: compensated floor ≡ ground floor; mass-rate equality ⇔ no unbounded local depth mass. |
| Finite Hodge index of ζ | Finite at every aperture; positive on an explicit finite-codimension subspace. |
| Effectivity from Hecke/Adams structure | Negative: stability forces the defect floor, it does not produce it. |
| Growing-support negativity of the critical prime channel | Solved on linear-width windows. |
| Half-damping chain bounds | Bounded uniformly on `[1/2, 1)`; Hilbert–Schmidt exactly above `1/2`; residue modes Bessel, not Riesz. |
| Width readings as a theorem | Width functor: the six ζ receivers are isomorphic. |
| Which readings can certify depth | Trichotomy in model classes: cross Nyquist, read magnitude, or add mass/dilution/first-moment data. |

## 2.3 Would solving Tier A or B require a new field?

### What the corpus establishes

No theorem shows that existing mathematics is insufficient. The corpus does establish six facts that constrain any solution.

1. **Reformulation is exhausted.** All `Δ`-readings are isomorphic receivers, and every proved RH endpoint has been reached in many languages. Changing language changes no producer.
2. **Present inputs stop at rate `1/2`.** Every unconditional receiver estimate in the corpus sits at rate `1/2` with subexponential savings from the classical zero-free region. The reason is visible in the complete form: at lag `t` the prime measure and the polar measure both have density of order `e^{t/2}`, and their difference is the Chebyshev deficit, so paying the reflected-prime cost at a lower rate is the same as bounding the prime-number error below the square-root scale. All restricted positivity theorems (APT's factorial families, ACT/AIP windows) are paid instead by an archimedean gain such as `log M`, which is absent on the RH-complete cone. The first improvement in any `Δ`-reading route is quasi-RH, unsolved for over a century.
3. **Soft structure is shared by impure models.** Functional equation, Euler product, integrality of Witt data, positive prime counts, local zero counts, fixed-modulus cancellation, sign patterns of `μ` on primes and all translated periodic moments are each realized by a model that violates RH or the receiver: the golden `𝔽₅` Beurling datum, shifted pairs `ζ(s−a)ζ(s+a)`, parity and even-flip twins, cluster configurations, planted Euler factors, degree-`d` FE twins. A proof must use an arithmetic property that every one of these models lacks. THIM makes this exact for its own conservation and dissipation laws: they split into Beurling-universal laws, sign-blind parity-orbit laws, and a third class of `ℤ`-lattice laws driven by Bézout relations `gcd(n,n+1) = 1`, `pa − qb = 1` (T:CompleteSignedTransHorizonEnergyAndTransferSelectivity). The first class holds on every Beurling system and the second cannot tell a row from its parity twin; only the third uses the additive successor structure of `ℤ` that Beurling systems lack.
4. **Sub-Nyquist sign information is blind.** Bounded-aperture positivity is compatible with depth `1/2`; any depth-certifying reading must cross the Nyquist aperture, read magnitudes, or add mass-type data.
5. **Every route stops at the same threshold.** At height `T` the square-root aperture `½ log T` is where a test's prime horizon `e^{2a}` reaches `T` and its length `e^a` reaches `√T`; below it the Dirichlet mean value is exactly diagonal, above it `1`-separated height samples lose injectivity and admit hiding sections (O:TheNyquistBoundAtTheDiagonal). Below the threshold, Montgomery–Vaughan removes all off-diagonal prime pairs; the rank–trace method stops at `2/3`, sub-Nyquist sign readings are blind, and receiver estimates stop at rate `1/2`. Beyond it, the needed input is the signed correlation of prime pairs, which no unconditional method controls. Walls 1 and 3 are two faces of this square-root threshold.
6. **The obstruction is localized but not small.** At each aperture it is a finite low-frequency sector, of doubly exponential dimension; in the damping picture it is a Bohr-polydisk hull; in the incidence picture frustration sits only on prime-sum edges `log p + log q = log n`; in the zero picture it is collapsed clusters at doubly exponential height.

### The proposed field: arithmetic orientation geometry

The working hypothesis is that the missing input is an **orientation principle**: a mechanism that produces the sign of the prime–pole interaction at the critical scale from arithmetic alone, the way Castelnuovo–Severi positivity on `C × C` produces the Hasse–Weil bound for curves. The corpus has the exact identity this principle would feed — the scaling-surface Lefschetz–adjunction formula `L(x,a) − ((a+1)/2)(x·x) = ((√a−1)²/2)·defect(x,x) + (√a/2)·defect(ψ^a x − x)` — and the exact statement it would have to prove: the arithmetic Hasse–Weil bound `|L(x,a) − ((a+1)/2)x·x| ≤ √a·x·x` at every scale `a > 0` for every cycle of the positive cone (the cone of nef cycles obeying it equals the positive cone iff RH). For curves the bound follows from geometry of the Frobenius graph; for `Spec ℤ` there is no Frobenius graph, only the scaling flow. The field would be the geometry that supplies that inequality.

**Objects it must be built on.**

| Object | Corpus prototype | Required new property |
|---|---|---|
| Scaling surface with pole plane, test cycles and arithmetic sections | ACS `scalingSurface`; source-defined section cones; λ-ring and Hecke correspondences | `h⁰` defined from arithmetic, not from the sign of the form; a Riemann–Roch inequality proved independently. |
| Signed prime incidence complex | odd Weil ledger; frustration index; prime-sum edges; tower Cholesky squares | A continuum Laplacian with Gamma and pole terms, and an arithmetic supersolution (Allegretto–Piepenbrink for `Λ`). |
| Bézout-selective laws | THIM class III laws from `gcd(n,n+1) = 1` and `pa − qb = 1`; pronic successor structure | Laws strong enough to carry a signed estimate, not only to separate ζ from Beurling models. |
| Critical Wiener algebra on the Bohr polydisk | repairing ideals, obstruction hulls, unit orbits | A Nullstellensatz excluding hull points that would come from off-line zeros below `Δ`. |
| Receiver category with width functor | O:TheWidthFunctor | Producers as morphisms, not only receivers. |
| Multiscale compensated states | Bézout corrector; projection/transverse splitting | A conservation law turning relative alignment into absolute energy control. |
| Local zero geometry at extreme height | DCI pincer; cluster model; twin/triple visibility | An arithmetic anti-collapse principle bounding off-line multiplicity in unit windows. |

**Criteria it must meet.**

- *Selectivity:* fail, for a stated reason, on every model in fact 3; reduce to Weil's proof on curves and fail exactly for impure curve data.
- *Orientation:* use reflection-odd data; magnitude-only data provably cannot decide half-damped admission.
- *Cofinality:* hold uniformly in aperture, height, damping and rank; finite-radius readings admit non-positive mimics.
- *Supra-Nyquist:* read information above the Nyquist aperture or carry magnitude/mass data; in prime terms, control signed prime-pair correlations beyond `X ≍ T`.
- *Rate:* deliver an exponent strictly below `1/2`, at minimum a fixed zero-free strip.
- *Pre-divisor:* use no zero-indexed objects.
- *Exactness:* retain the Gamma factor, both polar terms and every prime power.

**Questions it must answer.**

1. What is an arithmetic section of a cycle on the scaling surface, and why does it satisfy Riemann–Roch without reference to the Weil sign?
2. Why do prime-sum frustrations cost less than the archimedean subsidy, uniformly in aperture?
3. Which arithmetic invariant prevents `log γ` off-line multiplicity from collapsing into a unit window at doubly exponential height?
4. What conserved quantity converts relative compensation into absolute energy at every fixed small damping?
5. When is the repairing ideal of the damped Möbius source the whole Wiener algebra, and can that be proved from Euler-product structure on the Bohr polydisk?
6. Is there an arithmetic correspondence on the scaling surface playing the role of the Frobenius graph, whose self-intersection gives the Hasse–Weil bound?
7. Which readings are orientation-faithful for the actual ζ source, not only in model classes, and what does each cost?

**Tools it aims to develop.**

- An Arakelov-type intersection theory on the scaling surface with arithmetic `h⁰`, ampleness and a Hodge index theorem.
- Signed spectral graph theory on prime-log incidence: frustration, Cheeger and supersolution theorems in the continuum.
- Gelfand theory for critical Wiener algebras with arithmetic obstruction hulls.
- Corrector theory for compensated energies across scales.
- Arithmetic anti-concentration for local zero configurations.
- Quantitative supra-Nyquist reading theory with explicit precision costs.

**Mechanisms to discover.** A positivity of correspondences (Frobenius-graph analogue); a contraction with an arithmetic supersolution (Markov / Beurling–Deny for the full form); or a conservation law whose signed flux has a forced sign. Each must be shown to exist for `Λ` and to fail for the impure models.

### Assessment

Tier A is RH-strength and its first step, B1, is quasi-RH; both are beyond current mathematics. Tier B contains problems of three kinds: classical open problems (B1, B3), problems needing an arithmetic principle not yet available (B2, B5, B6, B7, B8, B10), and tractable calibrations (B9, B11, B4's tails). A new field is not proved necessary. The corpus does show that every existing mechanism it has tested either reformulates the target, stops at rate `1/2`, or is shared by an impure model; a successful mechanism must therefore be selective in the sense above. Whether that comes from a new theory or from an unexpected use of existing ones is unknown.
