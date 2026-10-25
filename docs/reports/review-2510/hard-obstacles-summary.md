# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-25, corpus snapshot `0fa51c933`. This summary covers all 31 routes, 17 candidates, PW-B and the supporting programmes in the [complete report](hard-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md), and the supporting note [what forces blindness](what-forces-blindness.md). Evidence: Lean corpus search, statement reading and an umbrella-reachability check, recorded in `logs/review-2510-update/`. Nothing was compiled.

## 0. The frontier in six statements

1. **Single-channel positivity can only certify blindness.** For sharp-stable convolution ideals of the Meyer source and for scale-shift-invariant test spaces this is now a theorem. Every positive ideal lies inside the maximal blind ideal, i.e. the sources whose Mellin transform vanishes at every off-line zero (`isGreatest_meyerSharpPositiveIdeal`, `zeta_blindOffLine_of_scaleShift_subspace_weil_nonneg` [L]). Every other unconditional positivity theorem in the corpus is likewise positivity on a blind carrier: low-grid-blind tests, bounded orbits, positive degrees, large-height heated heads, frequency averages.
2. **Forcing exists, it is multiplicative, and it stops at the Vinogradov–Korobov region.** Four invariants force zero order zero on `Re s = 1` (`harmonic_quantized_zero_vanishing` [L]):
   - harmonic coefficient positivity from `Λ ≥ 0`;
   - a simple pole;
   - no poles at the harmonics;
   - integer zero orders.

   Sharpness models show that the pole conditions cannot be dropped. With growth inputs, the same positivity gives the de la Vallée Poussin, Littlewood and Vinogradov–Korobov regions [L]. Its next rung is a fixed zero-free strip.
3. **No route has a rung between Vinogradov–Korobov and quasi-RH.** Every graded cancellation receiver (WL, PBM, JAS, balanced and centred-prime bands, short windows, the Vaughan empty leg, RW/ACS floors) has a fixed strip as its first gain [L]. So does the multiplicative forcing law.
4. **Positivity is proved on average beyond the square-root threshold.** Averaged Weil positivity holds at aperture `κ₀ log Γ` on `[Γ, 2Γ]`, and subpower coercivity holds up to prime support `Γ^{4/3}` [L]. The remaining wall is **selection**: control at individual heights, in particular at zero ordinates.
5. **Faithfulness costs simplicity only through operator-norm carriers.** The maximal trace-bounded carrier keeps every critical jet, has Hodge index, RR, Bézout and ampleness, and equals the whole source iff RH [L]. The Hilbert–Schmidt, bounded-orbit and faithful-degree carriers need RH plus simple zeros.
6. **No countermodel has all of ζ's invariants.** Each model in the battery violates a named invariant (golden Beurling curves, planted Euler factors, shifted pairs, Wolff configurations, white-noise and augmentation kernels, magnitude and parity twins, Euler-blind sources, double-pole and periodic-pole systems, `Γ_R^d` abundance, over-regular Beurling systems). The functional equation forces the generalized-integer count to fluctuate, so over-regular systems cannot satisfy it [L]. Whether Riemann's functional equation and a nonnegative Beurling Euler product characterize ζ is open (Q2).

## 1. Just work

These obstacles can be removed with existing mathematics. Each stops before any unknown estimate. "Just work" does not mean small; W7 requires certified numerics.

| ID | Task | Concrete content | Completion criterion |
|---|---|---|---|
| **W1** | **Integration** | Wire the 20 committed modules that no umbrella reaches. ACS (14): `BoundedMeyerSourceSurface`, `BoundedMeyerFaithfulReserve`, `PositiveMeyerDegreesSeeReducedCriticalJets`, `MeyerAlgebraicCharacters`, `MeyerHermitianDegreePart`, `FiniteMeyerProjectorsSplitPositiveEnergy`, `MeyerFiniteJetAlgebra`, `MeyerFiniteProjectorAlgebra`, the four origin-mass modules, `SmoothFiniteReadingKernels`, `ArithmeticMajorantConeGeometry`. BVI (4): `TheTopologyOfSubcriticalVaughanGramLimits`, `UniformLogarithmicCancellationInMobiusFloorSums`, `UniformStretchedExponentialCancellationInTheVaughanConvolution`, `VaughanGramsAtTheirActualHarmonicAmplitude`. Others: `FiniteMobiusHarmonicSumsHaveExplicitLowerBounds`; APT `CriticalPrimeChannelBeyondLinearWindows`. | Each module is checked with `lake --old env lean` and imported; labels move from [S] to [L]. |
| **W2** | **Certificate replacement** | Replace `native_decide` in `RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean:749` (PA order-24 quadrature; three importers, none a receiver) and in `HTGeometry/MilnorKTwoSteinbergSurjective.lean:138` with kernel-checked arithmetic. | No forbidden tactic remains in the project packages. |
| **W3** | **Status-record synchronization** | The frontier map and killed-routes catalogue agree with the source at the snapshot. Corrected entries: the summation-scope "defects" (centred-prime band, upper Lefschetz/graph degree); integration labels for the half-damping, Dini, mean-value, scale-stable-family, maximal-ideal and harmonic modules; the functional-equation/count theorem; sparse annihilators. Labels must move again as W1 proceeds. | Every [S]/[L] label matches umbrella reachability. |
| **W4** | **Finite identities and certificates** | Gram matrices, Hausdorff and Hankel blocks, Jensen and heat-Hankel ranks, finite divisor heat transforms, finite schedules and histories, incidence ledgers, finite Robin and Li checks, finite JAS and Vaughan budgets. | Every finite term and error is certified. None of this gives a cofinal theorem. |
| **W5** | **Premise checks for specified sources** | Regularity, support, integrability, cutoff, real-lag decay and domain membership for a named test or family (SZ moving and noncompact limits, CHMD domains, candidate sources). | The exact hypotheses of an available transfer are discharged. No unknown uniform bound is hidden here. |
| **W6** | **Transport of proved inputs** | Push proved estimates through exact dictionaries: the width functor, RW↔SZ↔CHMD, HF→AIP, the Weil-margin→heat window, the graded Sobolev floors. Damping, aperture, rank, degree, height and horizon quantifiers are kept. | Each conclusion is stated at its true strength. |
| **W7** | **Certified finite extensions and explicit constants** | Push the pointwise windows beyond full `3/10`, odd `181/500` and primitive `(log 2+1/50)/2` toward the next prime thresholds, using the low-sector method with certified numerics. Make explicit `κ₀, c₀, C₀, Γ₀` (averaged positivity) and `R₀, T(λ)` (radius head). | Certified finite-aperture theorems, not uniform in aperture. |
| **W8** | **Corollary assembly from existing theorems** | (i) Merge the RW, SRT and ACS rate dictionaries through `groundRate = polarRate` [L]. (ii) Averaged RR and graded-cone statements on ACS from filtered positivity. (iii) The explicit residual region `{|t| ≤ T(λ), λ ≤ λ₀}` for LA/WD from the radius-head and KKL results. (iv) ACS effectivity as an exhaustion criterion: Bézout on the full cone ⇔ maximal blind ideal = ⊤ ⇔ RH. (v) An averaged bounded-energy statement for WL from the high-zero tail and the filtered deficit. (vi) In the harmonic module, replace the imported `c/(log t)^9` collar with the corpus's dlVP/VK regions. State "boundary forcing law + growth input ⇒ zero-free region" as one theorem; this is the classical argument. | Each statement is proved from existing theorems; none closes a route. |
| **W9** | **Dependency and axiom audit** after W1/W2 | `#print axioms` on route receivers and new capstones. This needs an authorized compile pass; reviews do not compile. | The audit is clean, or each finding is recorded. |

These tasks open no route. Their value is accuracy and calibration: W1–W3 make the labels true, and W7/W8 supply the explicit regions and the forcing-with-growth statement that any new mechanism must beat.

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

Each is equivalent to RH or stronger. Solving one closes every route that uses its receiver.

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit energy, a one-sided lag or Abel moment, the history floor, the regularized abscissa `1/2`, the JAS half-power budget, Mertens at square root, the late-lag sign. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Cofinal admission as `ε ↓ 0`; equivalently a Báez–Duarte residual → 0, signed interior Vaughan energy, or exclusion of cofactor escape. | PM, CTF, BVI, PW-B |
| **B1.3** | **Complete Weil positivity at every aperture.** Low and mixed sectors, Gamma and both polar terms, one shared budget. Equivalently: the nodal inequality, positive Suzuki first variation, odd capacity, the one-shift reflected collar, global allocation, the ceiling `O(L)`, Bézout on the exact source cone. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS |
| **B1.4** | **Selection.** From averaged or almost-all-height statements to control at every height, in particular at zero ordinates. | Shared by B1.1 and B1.3; faces in WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign.** Coefficient positivity on the bounded-height × small-heat residual region, i.e. the de Bruijn–Newman constant `Λ ≤ 0`. Also: all-rank Hankel positivity at one time, both literal heat grids at every degree, rank-uniform Schur decay, the Newton interior margin, order-uniform passivity. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization.** Exhaustion of the maximal blind ideal, by an input that is not single-channel sharp-stable positivity (the maximality theorem rules that out). Faces: the Ward cap vanishes; the integer trace residual is a nonnegative sub-unit; renewal boundary orientation; an effectivity source on the exact cone; a global stabilization weld; pre-divisor compactness; a descending potential; a centered Ising limit; a nonlocal lossless port; an arithmetic certificate stream. | TG, RN, WD, ACS and all 17 candidates with PW-B |
| **B1.7** | **Single-currency endpoints.** Cofinal contrast equality; the subexponential Li floor; the eventual Robin tail; recurrence near every possible zero; the global index `D < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **Stronger than RH: RH with all zeros simple.** A faithful positive Meyer degree; RR for the Hilbert–Schmidt reserve; exhaustion of the bounded-orbit carrier. RH alone is reached by the trace-bounded carrier (B1.6). | ACS/Meyer faithful branch |

### 2.2 Tier B2: classical open problems weaker than RH

Mathematics has no solution to these either. Each is a first rung or a partial target of the routes.

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | **Quasi-RH**: a fixed zero-free strip, `Θ < 1`. | First rung of WL, PBM, JAS, MC/BVI (balanced band, centred-prime band, short windows), the Vaughan empty leg, RW/ACS graded floors, DR, and the multiplicative forcing law beyond Vinogradov–Korobov. Formally equivalent in these receivers [L]. |
| **B2.2** | **Finite off-line index**: all sufficiently high zeros are critical. | HF/AOG index exit, WD collision masses, uniform heat counts. Stronger than B2.1, weaker than RH. |
| **B2.3** | **Simplicity of the zeros.** | Every operator-norm faithful realization (B1.8); Meyer numerical = principal. |
| **B2.4** | **Density hypothesis / large values beyond Guth–Maynard.** | Extending averaged positivity beyond `α = 2/3`; the zero census `HD(1)`; the filtered deficit exponents. |
| **B2.5** | **At least 3/4 of the zeros on the critical line.** | TTPC/ACS certificate: signed coalescent surplus `β ≤ 1/18`. |
| **B2.6** | **Power-saving sign correlations of μ and λ** (Chowla/Elliott with rates). | MC interior anti-alignment, SSA successor constants, BVI balanced rows. |
| **B2.7** | **Hardy–Littlewood prime-pair correlations, uniform near the square-root band.** | TTPC surplus, the selective square-root band, short-window selection (Q1). |
| **B2.8** | **Subconvexity and Lindelöf improvements; growth near `Re s = 1`.** | The KKL horizon constant `27/40` (size of the LA/WD residual region); the growth input of the multiplicative forcing law (B3.14). |
| **B2.9** | **Better upper bounds for the de Bruijn–Newman constant.** | Shrinks the B1.5 residual region; `Λ = 0` is RH. The corpus has `Λ < 1/8`. |

### 2.3 Tier B3: open problems isolated by this research

No solution is known, and none is proved RH-equivalent. Several are plausible research targets.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | **Rate equality** `polarGroundEnergyRate = Δ`. | `Δ ≤ polarRate = groundRate ≤ 1/2` [L]. Bounded local depth mass suffices; a failure needs collapsed clusters at doubly exponential height. |
| **B3.2** | **Escape-state classification** of cofactor limits, including the moving boundary. Equality of the paid ideal with the annihilator. | Proved for actual limits: inclusions, zero-cofactor dichotomy, rank-one classification, horizon-ratio law, faithful moving-origin mixtures [L]. Surviving abstract models: full white noise and augmentation; neither is tested against full paid-ideal annihilation. |
| **B3.3** | **Quantitative coercivity** of residual/trace reconstruction in the receiver norm. | Only algebraic injectivity is known; the dilation commutator is bounded. Cofactor-graph closedness ⇔ a uniform output-by-input estimate [L]. |
| **B3.4** | **A limit topology for the maximal blind ideal.** A source topology in which the ideal is closed, the trace is lower semicontinuous and tails are controlled, so that exhaustion can be proved by approximation. | The ideal is algebraic and complete as a carrier [L]. The origin-L² completion is excluded [S]. Finite projectors split positive energy with a nonnegative complement [S]. |
| **B3.5** | **Surface section law**: couple the base theta `h⁰` to test components so that it supplies effectivity. | Base `h⁰` RR and Mellin identities [L]. Boolean section counts and finite readings cannot pay; the Hecke graphs of `ℤ` satisfy no theorem of the square. |
| **B3.6** | **Signed shell flux** along the moving prime-threshold ladder. | Birth jumps vanish. The collar bound is `e^{−a}[ψ(e^{2c}) − ψ(e^{2a})]·mass`. Permanently frozen finite prime families fail. |
| **B3.7** | **Short-window averaged positivity.** The smallest `H(Γ)` for which averaged Weil positivity holds on `[Γ, Γ + H]`. | `H = Γ` is proved. `H ≍ 1/log Γ` would amount to selection. |
| **B3.8** | **A nonlocal shared-budget calculus** for frustrated arithmetic incidence; quantitative cofinal two-tower saving. | Frustration and descent laws are exact; fixed-box gaps are proved. |
| **B3.9** | **Arithmetic input on the residual heat region**; source-selective cofactor repair of the actual heated head. | The model geometry is complete. No universal positive multiplier exists. |
| **B3.10** | **Compatible oriented families** and quantitative bounds on the global index. | Common-endpoint classification; finite-target law; spline-orbit index ≤ 1 ⇔ RH. |
| **B3.11** | **Sub-half-damping signed control** of the size-cutoff forward interior. | The exterior is paid. The signed prime-divisor endpoint at `ε = 1/2` is bounded for every squarefree support [L]. Paid patterns below half damping have integer local exponents [L]. |
| **B3.12** | **Order-uniform PA thresholds**; decoupling rank from time for TH and HCF. | Fixed-order thresholds exist; Weil margins give coupled windows. |
| **B3.13** | **Sharp successor constants.** The optimal complex coefficient in `[−1/2, −1/3]`; the classification of zero-defect signs beyond conductor 3. | Odd shifts: exactly `1/3`, attained by `(−1)^{v₂(n)}`. Lag 2: exactly `1/4` (`lag_two_floor_sharp`) [L]. |
| **B3.14** | **Interior multiplicative forcing beyond growth input.** A multi-channel positivity structure (coupled dilated channels, or several frequencies on the prime torus) outside the maximality theorem's class, forcing zero-freeness in a region not given by growth bounds alone. Alternatively: a sharp theorem that every finite-degree coupling with growth input `G` is confined to the region `R(G)`. | Boundary line forced [L]. Interior regions dlVP, Littlewood and VK follow from growth inputs [L]. Fejér barrier `a₁ < 2a₀` [L]. The coupled off-line ceiling is unsigned. |
| **B3.15** | **Completeness of ζ's invariants.** Is ζ the only system with Riemann's degree-one functional equation, a Beurling Euler product with nonnegative prime measure, a simple pole at 1 and finite order? If not, does some such system have an off-line zero? | FE + decaying count error is impossible, so over-regular Beurling systems violate FE [L]. Hamburger holds for ordinary frequencies; its Laplace step holds for arbitrary frequencies [L]. `Γ_R^d` (d ≥ 3) is abundant without Euler positivity [L]. No full-invariant countermodel exists in the corpus. |

## 3. The three questions to answer next

Selection criteria:

1. Each question is weaker than RH, or independent of it, so it can actually be answered.
2. Either answer changes the frontier. A positive answer creates a selection, selectivity or exclusion mechanism. A negative answer is a sharp no-go that names the missing arithmetic input.
3. Together the three cover the three route families, each in its own currency.

**Questions that are settled.**

- Whether geometric carrier positivity can force: for single-channel sharp-stable carriers it cannot, by the maximality theorem.
- Whether positivity can force zero-freeness anywhere: it can on `Re s = 1`, and with growth input up to the Vinogradov–Korobov region.

Quasi-RH (B2.1) and the de Bruijn–Newman core (B1.5) are not on the list. Both are classical problems on which this corpus has no new leverage beyond restating them.

### Q1. Selection: how short can the averaging window be?

> *What is the shortest frequency window `[Γ, Γ + H(Γ)]` on which unconditional averaged positivity of the complete Weil form at logarithmic aperture holds? Can its exceptional set be shown to avoid zero ordinates in short windows?*

- **Why this question.** Averaged positivity is proved at `H = Γ` with prime support beyond the Nyquist aperture; pointwise positivity at every aperture is RH. Shrinking `H` is a graded path from the proved statement toward the open one. Every intermediate `H` gives a partial result of a new kind (positivity at almost all heights in short windows) that is not a zero-free strip.
- **Known tools.** Zero density in short intervals; Guth–Maynard large values; the all-length Heath–Brown estimate; the bad-frequency volume bound; the phase-selective single-height law; the high-zero tail law.
- **The obstruction to beat.** Syndetic phase recurrence: bad heights recur. The question is whether they can coincide with zero ordinates in short windows.
- **Possible outcomes.** A threshold theorem stating that no `H` below an explicit bound follows from density inputs alone would identify the missing input precisely: short-window prime-pair correlation (B2.7). A positive result supplies the selection step (B1.4) to RW, SZ, CHMD, EWU, OWU, ACT, AIP, HF, ACS, SRT and WL at once.

### Q2. Selectivity: do the functional equation and Euler positivity characterize ζ?

> *Is there a system other than ζ with Riemann's degree-one functional equation (`Γ_R(s)`), a Beurling Euler product with nonnegative prime measure, a simple pole at 1 and finite order? If so, can such a system have a zero off the critical line?*

- **Why this question.** Every mechanism killed in the catalogue was killed by a countermodel that keeps its axioms but drops one of ζ's invariants. The harmonic forcing law needs four invariants and has a sharpness model for each pole condition. The functional equation forces the integer count to fluctuate, and that excludes the over-regular Beurling countermodels [L]. No countermodel in the corpus satisfies all invariants at once. The question decides whether a forcing law built from these invariants can be selective at all.
- **What a positive answer (uniqueness) gives.** A Hamburger theorem for Beurling systems. Every countermodel must break a named invariant, so a mechanism that uses all of them cannot be refuted by any model. RH becomes a statement about the unique solution of an explicit rigidity problem, which opens a variational and rigidity approach.
- **What a negative answer gives.** An FE-respecting Beurling system distinct from ζ, and with an off-line zero the sharpest countermodel yet. It retires every mechanism built only from FE, Euler positivity and pole structure, and identifies the missing invariant as the integrality of the generalized integers (or something finer).
- **Known tools.** `false_of_functionalEquation_of_decaying_count` and the Gaussian-weighted Laplace–Plancherel bound [L]; Hamburger for ordinary frequencies (`coeff_eq_of_completed_functional_equation`) [L]; the general-frequency Laplace step and imaginary-axis residues (`freqSeries_eq_of_freqTheta_relation`) [L]; generalized Dirichlet-series injectivity; the over-regular, double-pole and periodic-pole Beurling constructions; `Γ_R^d` abundance.
- **Routes fed.** Every U3 candidate, ACS, HF and the selectivity criterion of every forcing proposal (§4.3).

### Q3. Escape: which abstract escape states survive all proved constraints?

> *Are full white noise `K_{jk} = δ_{jk}/j` and the augmentation kernel `K_{jk} = 1_{j=k=1}` compatible with full paid-ideal annihilation, the horizon-ratio law and the moving forcing boundary with its absolute word tail? More generally, classify the cyclic critical-Wiener modules that satisfy every proved constraint on actual cofactor limits.*

- **Why this question.** Cancellation routes have no rung below quasi-RH. Their only non-graded handle is the escape alternative: either admission, or escape carrying a rigid module structure. The constraint list is now long:
  - unit mass, critical radius, PSD packets and dilation contraction;
  - antipodality and the signed Gram collapse;
  - paid-ideal annihilation;
  - the horizon-ratio law;
  - the zero-cofactor dichotomy and the rank-one classification.

  Only two explicit models remain to test. This is a problem about an explicitly defined abstract class, so it is weaker than RH.
- **What a positive answer gives.** If no model passes every constraint, escape is impossible and the small-damping energy problem B1.2 is solved.
- **What a negative answer gives.** An explicit surviving model is a sharp no-go. Its structure states which arithmetic input the actual Möbius source must supply (ideal equality, coercivity, moving-boundary cost), and B3.2 and B3.3 become concrete.
- **Known tools.** Paid-ideal annihilation; the common-limit Wiener module; finite index as joint multiplicity; unit transport; quantile antipodality; the bounded dilation commutator; the power-subtracted forcing; the zero-cofactor and rank-one laws.
- **Routes fed.** PM, CTF, BVI, MC, FU, RP, JAS, PW-B.

The three questions are the forcing problem in each family's own currency: selection by height (Q1), selectivity of invariants (Q2) and escape exclusion (Q3).

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows that a new field is necessary. Two theorems now sharpen the pattern behind the [killed-routes catalogue](../rh-killed-routes.md).

- **Quadratic positivity is exhausted.** Weil, Hodge and trace positivity on a single channel, stable under the correspondence algebra, can only certify blindness (maximality theorem). The archimedean term pays above a horizon, heat above a height, averages above a density threshold. All of these are dominance or blindness results.
- **Coefficient positivity is exhausted below RH strength.** Positivity of `Λ` coupled across dilated channels forces the boundary line exactly, with every invariant necessary. Combined with growth bounds it reaches the Vinogradov–Korobov region, and its next rung is a fixed strip.
- **Every failed mechanism fails on a countermodel that drops one invariant.** No countermodel keeps all of them (statement 6 of §0).
- **The forcing mechanisms known elsewhere do not transfer.** Weil's proof for curves forces through the geometry of `C × C`: sections, ampleness, the Frobenius graph, and a ring of correspondences with a theorem of the square. Over `Spec ℤ` the corpus builds scaling and Meyer surfaces whose Hodge index is equivalent to RH. Their Hecke graphs satisfy no theorem of the square, and they have no independent source of ampleness.

The missing ingredient is **a forcing law of a third kind**: neither single-channel quadratic positivity nor finite-degree coefficient positivity, selective for ζ, quantitative across limits and independent of the conclusion. No existing toolkit over number fields contains one. If such a law exists, it will probably look like a new field: a theory in which the quadratic (Hodge) and multiplicative (Euler) positivities are two shadows of one structure.

### 4.2 Working name and subject

**Arithmetic forcing theory** (alternatively: *multiplicative positivity geometry*). Subject: how the multiplicative structure of an arithmetic source forces its spectral readings into blind carriers, with every loss priced across scale, limit and completion. The multiplicative structure here means the Euler product, the functional equation, integrality and the pole.

- **The phenomenon to explain.** Arithmetic sources sit exactly on the boundary between dominance (provable) and cancellation (unproved). The theory should explain why actual ζ, and not its countermodels, stays blind as the controlling parameter crosses that boundary. The parameter can be:
  - rate `σ → 0`;
  - aperture `A → ∞`;
  - heat `λ → 0`;
  - damping `ε → 0`;
  - window length `H → 0`;
  - the carrier growing toward the whole source.
- **Its character.** It would combine three things.
  - A **renormalization theory of positivity**: flows in aperture, damping and heat, with arithmetic beta functions (the prime-shell flux is the first one computed); fixed points (blind carriers); relevant directions (off-line zeros); and a forcing law that makes those directions irrelevant.
  - A **positivity geometry of the prime torus**. The boundary forcing law is positivity of a positive function (a nonnegative cosine polynomial) against a positive measure (`Λ(n)n^{−σ}`) along one frequency and its harmonics. The general object is positive-definite structure on the Bohr compactification, coupling several frequencies and primes. It must leave the single-channel class covered by the maximality theorem.
  - **Intersection theory with a ring of correspondences**: what replaces `ℤ[F]` and the theorem of the square over `Spec ℤ`.

### 4.3 Criteria it must meet

| Criterion | Test against the corpus |
|---|---|
| **Selectivity** | Distinguishes ζ from the whole countermodel battery, including the double-pole and periodic-pole systems, golden Beurling curves, over-regular Beurling systems and `Γ_R^d` solutions. It must use all four forcing invariants (and the functional equation where the battery requires it), not functional equation, positivity, integrality, Euler form, finite readings or local collars separately. It must survive every single-node perturbation `Λ + δ·δ_m`. |
| **Leaves the maximality class** | Its positivity is not single-channel sharp-stable positivity; otherwise the maximality theorem confines it to the blind ideal. |
| **Non-circularity** | No interface field, structure or premise contains the conclusion. The object is constructed before its sign, and the sign proof does not read zeros. |
| **Uniformity across limits** | Tails are paid in a topology that keeps the maximal blind ideal closed and every jet visible, not in the origin-L² completion. Aperture, height, rank, damping and window length are controlled together. |
| **Positivity–faithfulness separation** | RH follows from trace-bounded (non-faithful) data. Simplicity is a separate output, never a hidden input. |
| **Calibration** | Reproduces the boundary forcing law and the dlVP, Littlewood and VK regions as dominance-regime special cases. Reproduces Weil's proof for curves (genus-one Hasse = degree positivity of `ℤ[F]`), and explains why the golden datum fails it. |
| **New partial results** | Produces results that are not zero-free strips: positivity at almost all heights in short windows (Q1), invariant completeness (Q2), escape classification (Q3), or interior forcing beyond growth input (B3.14). This is evidence that the theory adds mechanism rather than criteria. |

### 4.4 Questions it must answer

1. **What separates ζ from systems that share its invariants, and do such systems exist?** Integrality (Witt), λ-ring and Rosati structure and positive counts are shown not to suffice. The functional equation excludes regular counts. Whether FE plus Euler positivity is complete is Q2.
2. **What replaces the Fejér barrier in the interior?** At `Re s = 1` the strict bound `a₁ < 2a₀` against a simple pole decides everything. In the strip, growth near the zero decides. What multi-channel structure supplies the missing margin?
3. **How does blindness propagate under the flows?** What is the sign of the arithmetic beta function (shell flux, collar correlation), and what keeps the ground energy above zero across the prime-threshold ladder?
4. **What is the right completion?** Which topology keeps the maximal blind ideal closed, makes the trace lower semicontinuous and controls actual tails? The origin-L² completion is excluded.
5. **How does an average become a point?** What selection principle passes from height averages to zero ordinates despite syndetic phase recurrence?
6. **What replaces the ample class and the ring of correspondences of `C × C`?** The Hecke graphs of `ℤ` satisfy no theorem of the square. What surface-level `h⁰` with independent RR would yield effectivity?
7. **How can quantization force vanishing in the interior?** On the boundary, integer zero order plus a sub-unit margin forces zero. The corpus has many other integer phenomena: even collision masses, two-scale deficits equal to four times a count, quotient index finite or continuum, winding numbers, a characteristic-zero Stepanov argument. Which arithmetic inequality pushes an interior integer charge below one?
8. **How are shared resources paid?** What nonlocal allocation calculus pays frustrated prime incidences from one budget?

### 4.5 Tools it would develop

- **Prime-torus positivity calculus.** Positive-definite trigonometric structure in several frequencies and primes, with forcing laws generalizing `harmonic_quantized_zero_vanishing` and sharpness models generalizing the double-pole and periodic-pole systems.
- **Growth-to-forcing renormalization.** One theorem turning a growth or large-values input into a forced region, with a sharp barrier. This identifies what any interior gain must supply.
- **An arithmetic beta-function calculus.** Signed flux formulas for the aperture, damping and heat flows, with sign criteria computable from source data.
- **Completions with tail control** for the maximal blind ideal and for cofactor modules: lower semicontinuity of trace energy and closedness of the blind ideal.
- **Short-window selection lemmas** turning density information into control at individual heights, with explicit exceptional sets.
- **Rigidity theory of functional equations for generalized integers.** Hamburger-type uniqueness, or explicit counterexamples, for Beurling systems.
- **Escape-state classification** for cyclic critical-Wiener modules under source constraints.
- **An arithmetic Stepanov method.** Auxiliary polynomials or sections over `ℤ` whose forced vanishing multiplicity bounds spectral counts. A characteristic-zero shifted-subgroup Stepanov lemma already exists in `HTGeometry`.
- **A nonlocal budget calculus** for frustrated signed incidence, with canonical-path packing and one shared reserve.

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | Arithmetic sources: prime and Möbius rows with Gamma and pole completion. Receivers. Carriers; the maximal blind ideal and its sub-carriers. Readings. Channels and couplings on the prime torus. Flows and their beta functions. Shells and collars. Cofactor modules with paid ideals, hulls and escape states. Meyer cohomology with its jets, sharp involution and positive degrees. Scaling surfaces with sections and `h⁰`. Orbits, families and indices. Generalized-integer systems with their invariants (FE, Euler positivity, pole structure, integrality). |
| **Language** | It must distinguish:<br>- equality, receiver equivalence and directional transfer;<br>- source and receiver;<br>- signed energy and absolute majorants;<br>- single-channel and coupled positivity;<br>- blind and faithful;<br>- finite, countable and uniform limits;<br>- distinct zeros, multiplicity and multiplicity squared;<br>- algebraic and bounded inverses;<br>- forced and imported regions;<br>- dominance regime and critical regime. |
| **Mechanisms to discover** | A **forcing law of the third kind**: arithmetic places the source in the closure of the maximal blind ideal. A **selection law**: averages become points. A **quantization law**: an interior integer charge with a sub-unit bound is zero. A **payment law**: one nonlocal budget pays every frustrated cost. A **rigidity law**: ζ's invariants determine ζ. |
| **First milestones** | (1) Averaged positivity on windows `H = Γ^θ` with `θ < 1` (Q1).<br>(2) Uniqueness or an explicit countermodel for FE + Beurling Euler positivity (Q2).<br>(3) A classification of escape states with the moving boundary included (Q3).<br>(4) A multi-channel carrier outside the maximality class with unconditional positivity on a nontrivial test class.<br>(5) dlVP and VK restated as instances of one forcing-with-growth theorem, with its sharp barrier (W8(vi), then B3.14).<br>(6) The sign of the shell flux on one ladder step beyond `3/10`, from a structural argument rather than a certified computation. |

Each milestone is a theorem of a type the corpus does not yet contain: a forcing, selection or rigidity statement rather than a blindness statement. If several succeed, the field exists. If all fail, each failure is a sharp no-go that narrows where a forcing law could be.
