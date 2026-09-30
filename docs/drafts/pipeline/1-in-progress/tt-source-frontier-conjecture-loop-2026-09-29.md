# TT source frontier conjecture loop

- **ID:** tt-source-frontier-2026-09-29
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** docs/reports/rh-current-frontier-map.md, route TT
- **Statement:** Find and prove an unconditional new source theorem advancing signed integrated covariance or directed natural-square-root-window means.

## Goal

Contribute significant new unconditional Lean knowledge toward RH; continue conjecture/proof/failure loops until a proof or falsification of RH is fully formalized without premises. A receiver reformulation does not discharge its source premise. Public-source searches can establish absence from inspected sources, not absence from all public literature or inaccessible training data.

## Plan

1. Audit TT frontier, relevant memories and exhaustive source search.
2. Freeze exact conjecture and write dependency-closed proof or failure mechanism.
3. Audit corpus overlap and public sources; iterate after failures or redundant results.
4. Formalize qualifying result, audit leaf with `lake env lean`, inspect axioms, wire umbrella, lint and clean scratch artifacts.

## Constraints

Unconditional capstone; no new axioms, analytic premises, numerical experiments, heartbeat increases, full builds or umbrella builds. One owned foreground Lean process at a time. Preserve unrelated working-tree edits. Use `--old` for necessary named incremental builds.

## Log

- 2026-09-29 — Initialized. TT has T1 signed centered nonlocal covariance and T2 directed natural-square-root-window source laws open. Existing positive stationary cone growth is unconditional but not centered-current control. Prior theta-tail signature work belongs to a different source-sign lane and supplies no TT producer.
- 2026-09-29 — Serena memory/manual read. `docs/architecture.md` and `docs/testing.md` absent. `update_plan` and `multi_tool_use.parallel` unavailable; plan persisted here and independent reads batched using `Promise.allSettled`.

## Conjectures

### C1 — stationary prime–vacuum cancellation

Candidate: centered complete stationary covariance is `o(X)` at moving cutoff `X`.
Rejected as a qualifying contribution: coarse PNT consequence with no critical-scale source control. No code promoted.

### C2 — exact half-density endpoint energy

Frozen before proof: `¬ WoldNatResidualSquareEnergy (1/2)`, equivalently the actual residual `R_N` is not square summable. Corpus has the strict result only for `t>1/2`.

Proof idea: square summability would make the natural Abel continuation holomorphic on the open translated critical half-plane. Cauchy–Schwarz bounds its radial value at `s0+x` by `O(x^(-1/2))`, so `x A(s0+x)→0`. Corpus forces a nonzero negative-integer residue at an unconditional Hardy zero, contradiction. Endpoint harmonic dual divergence therefore does not protect the energy producer.

Potential positive survivor: radial pole gives an explicit unavoidable critical energy charge; finite or summable polar repairs cannot erase all critical frequencies. Audit exact strength and overlap before promotion.

### C3 — logarithmically damped critical energy

Frozen stronger candidate: even `sum R_N^2 / (1+log N)` diverges. The dual kernel has squared norm `O(x^(-2))`; finite-head/tail splitting of a hypothetical summable energy then gives `x A(s0+x)→0`, contradicting the same quantized residue. This would identify the borderline logarithmic repair, rather than merely remove strict-power slack. Not yet paper-proved or formalized.

## Paper proof for C2

`[PROVED HERE]` Suppose `Q=sum |R_(N+1)|^2<infinity`. For `Re s>-1/2`, the complex-power unit-step estimate bounds the Abel atom by `|s||R_(N+1)|(N+1)^(-Re s-1)`. The squared dual series converges; on each interior ball its lower real abscissa supplies a common summable Cauchy–Schwarz majorant. Thus the Abel sum is holomorphic there. On `Re s>0`, the existing exact natural-cutoff partial-sum identity and telescope identify `A(s)+C` with the natural Abel germ.

For `s=s0+x`, `Re s0=-1/2`, `0<x<1/4`, Cauchy–Schwarz and the unit-step real-power tail bound give `|A(s)|^2 <= |s|^2 Q (1+1/(2x))`. Therefore `|x A(s)|^2 <= |s|^2 Q (x^2+x/2)→0`; the constant holonomy also has zero scaled radial limit. The forced critical-wall residue theorem supplies `x(A(s)+C)→-m`, `m>=1`, at one unconditional Hardy zero, contradiction. No RH premise or numerical calculation enters.

## Novelty and validation

Pending.

- 2026-09-29 — Lexical endpoint search returns existing strict `not_woldNatResidualSquareEnergy_of_half_lt`; exhaustive Wold source text has no endpoint or natural logarithmically damped counterpart. Deep Abel/L2 search is partial after deadline; its inspected candidates contain the forced wall residue and no endpoint result. Compiler freshness must still be supplied by named checks.
- 2026-09-29 — Generic Lean scratch checks Abel atom bound, shifted real-power square summability, Young majorant, finite-to-infinite Cauchy–Schwarz, and harmonic dual bound. Completing local holomorphy and radial residue annihilation; no tree proof promoted yet.
- 2026-09-29 — Public audit: Zhao, “On the mean values of the error terms in Mertens’ theorems” (2025), https://link.springer.com/article/10.1007/s40993-025-00640-y, studies classical E1/E2/E3. Lemma 9 gives E2 mean-square upper bounds; inspected results do not state the exact natural Wold endpoint. This is limited negative search evidence, not a global novelty certificate.

### C4 — quantized critical prefix-energy loading

Frozen positive-survivor candidate: an unconditional wall zero with multiplicity `m` and coordinate `s0=rho-1` forces nonzero logarithmic loading of the natural prefix square energy. More precisely, if a tail bound `E(N) <= c log N + O(1)` existed, the Abel residue would force `c >= m^2 / |s0|^2`. A real-source/reflected-frequency refinement may improve that constant; that stronger factor is a new conjecture, not asserted.

Paper mechanism to audit: split the radial exponent equally between source and dual in Cauchy–Schwarz, rather than use the unsplittable endpoint dual. Partial summation of the prefix-energy bound gives discounted source energy `O(c/x)`, while the dual is `O(1/x)`. The forced quantized residue then bounds `c` below. This extracts positive unavoidable source loading; a bare negation or generic Hilbert lemma will not close the no-go card.

- 2026-09-29 — C2 unconditional capstone accepted by `lake env lean GaloisForLFunctions/RHTower/XiHeatCassiniWoldNaturalSquareEnergyEndpoint.lean` (exit 0). Wired that leaf additively into RHTower. Named `lake build --old` and scratch axiom audit pending. This closes strict/equality gap, but novelty and positive-salvage bar remain open; goal not complete.

- 2026-09-29 — Named `lake build --old GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergyEndpoint` passed, leaf build 8.8s. No umbrella or full build run. Global `scripts/formal_tools.py lint` exit 1: 13 unrelated unreachable modules (CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, FermiNymanLogarithmicWitness, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellBoundaryLayer, ThetaMovingShellFourierJet, WeilPolarConeFirstVariation, ZetaZeroDensityPowerSaving). New endpoint leaf is wired and not named in errors. No unrelated modules edited to resolve others’ wiring.

- 2026-09-29 — Final exact endpoint leaf audit `lake env lean GaloisForLFunctions/RHTower/XiHeatCassiniWoldNaturalSquareEnergyEndpoint.lean` exit 0. Scratch `#print axioms` of unconditional capstone and radial annihilation lemma reports only `propext`, `Classical.choice`, `Quot.sound`. C3 remains active; positive salvage and external novelty unresolved.
- 2026-09-29 — Prefix-charge deep search inventoried 62,934 files, inventory complete; reranking partial after deadline. Inspected all returned 20 candidate lemmas, 20 source arguments, one proof idea and one ingredient proposal. Results contain power-spectrum receivers, strict square-energy estimates, safe natural Abel identity and residue-profile no-gos, but no logarithmic prefix-charge result. Most compiler metadata pending/stale, so source hits are not treated as validated Lean applicability.

## Paper proof for C3

`[PROVED HERE]` For `w_n=1+log(n+1)`, assume `sum r_n^2/w_n` finite. For each `q<-1/2`, the dual sequence `sqrt(w_n)(n+1)^q` is square summable: choose `e=-q-1/2>0` and use `w_n <= (1+1/e)(n+1)^e`. Young’s inequality gives absolute convergence of `sum |r_n|(n+1)^q`; interior balls therefore give the same local holomorphy and exact safe-germ identity as C2.

At the wall, put `d_x(n)=x sqrt(w_n)(n+1)^(-1/2-x)`. The bound with `e=x`, followed by the real-power tail estimate, gives `sum d_x(n)^2 <= (1+x)^2`. The scaled Abel atom is dominated by `(abs(r_n)/sqrt(w_n)) * (abs(s0+x) d_x(n))`. On `0<x<1` the second sequence has uniformly bounded square norm, whereas each scaled atom tends to zero. Split at a fixed natural index: the finite head vanishes, and Cauchy–Schwarz bounds the tail by a uniform constant times the square root of the remaining assumed energy. That tail tends to zero with the index. Hence `x A(s0+x) -> 0`. Adding the holonomy constant preserves zero scaled residue, contradicting the forced negative integer `-m`, `m>=1`.

The theorem remains a formalization candidate until the actual-source Lean capstone and axiom audit pass. Positive no-go closure is not claimed merely from this negative proof.

### C4b — finite-head/quantized loading survivor

Frozen weaker target for formalization: there exist an unconditional wall coordinate `s0` and integer multiplicity `m>=1`, and a positive constant explicitly proportional to `m^2/|s0|^2`, such that natural prefix residual square energy exceeds that constant times `log N` infinitely often. The exact proportionality factor is not asserted before the complete estimate. This strengthens nonsummability to unavoidable source loading and is not a restated negation.

Mechanism: an eventual logarithmic prefix-energy upper bound yields discounted source square energy `O(c/x)+O(1)` by finite Abel summation. Split the radial exponent equally between the source and dual; their product bounds the pole residue. Elementary `log n <= n^(x/2)/(x/2)` supplies a coarse but explicit constant without numerical computation. The sharp C4 constant remains a separate candidate requiring a sharper logarithmic real-power tail asymptotic and paper audit.

## Paper proof for C4b

`[PROVED HERE — FORMALIZATION PENDING]` Write `e_n=R_n^2`, `E_N=sum_(1<=n<=N) e_n`. Suppose `E_N <= c log N+C` for all `N>=1`, with `c,C>=0`. Finite Abel summation gives

`sum_(n<=N) e_n n^(-x) = E_N N^(-x) + sum_(n<N) E_n (n^(-x)-(n+1)^(-x))`.

For `x>0`, the mesh increment is nonnegative and at most `x n^(-1-x)`. The boundary term tends to zero. Using `log n <= (2/x)n^(x/2)` and the power-tail bound gives discounted energy

`D(x)=sum e_n n^(-x) <= 4c/x + 2c + C(1+x)`.

These finite-prefix bounds also prove convergence of `D(x)` for every `x>0`. For each interior Abel abscissa, split its exponent against a small discounted energy; Cauchy–Schwarz gives absolute convergence and a locally uniform majorant, so the exact natural safe germ has a holomorphic Abel continuation inside the sector.

At `s=s0+x`, split the exponent equally: source squared norm is `D(x)` and dual squared norm is at most `1+1/x`. Consequently

`|x A(s0+x)|^2 <= |s0+x|^2 [4c+(2c+C)x+Cx^2](1+x)`.

The unconditional residue `-m` therefore forces `m^2 <= 4c|s0|^2`. The holonomy constant has zero scaled limit. If `c=m^2/(8|s0|^2)`, this is impossible. An eventual prefix upper bound with that coefficient can be extended to all indices by adding a finite constant `C`; hence `E_N > [m^2/(8|s0|^2)] log N` infinitely often. Positivity follows from `m>=1` and `Re s0=-1/2`.

Exact survivor theorem to formalize: existence of an unconditional wall coordinate and multiplicity, together with infinitely many such explicit positive prefix-energy loads. This coarse factor `1/8` is now paper-closed. Sharp C4 coefficient still requires a better dual/logarithmic-tail estimate and remains a separate conjecture.

- 2026-09-29 — C3 actual-source scratch `lake env lean -j1 /tmp/hgt-tt-log-actual.lean` passed. Promoted to `XiHeatCassiniWoldNaturalLogCriticalEnergy.lean`, removed unnecessary tactic sequencing and wired into RHTower. Named `lake build --old GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalLogCriticalEnergy` passed (leaf 86s, no own warnings); scratch axiom audit and required final exact leaf audit pending. Main capstone: `RHTower.not_woldNatResidualLogCriticalEnergy`, no premises.
- 2026-09-29 — C4b simplification: bound finite Abel boundary uniformly by `c/x+C` instead of needing its limiting vanishing for summability. Then discounted energy bound is `5c/x+2c+C(x+2)`. This weaker intermediate bound still proves the exact positive survivor with coefficient `m^2/(8|s0|^2)` because `5/8<1`. Stronger paper estimate `4c` remains valid but need not enlarge the Lean dependency chain to prove the frozen survivor.

- 2026-09-29 — C3 scratch axiom audit passed: both `not_woldNatResidualLogCriticalEnergy` and `log_current_radial_zero` depend only on `propext`, `Classical.choice`, `Quot.sound`. Required final exact leaf audit running. C4b generic scratch prepared: finite real Abel identity, real-power increment bound, discounted boundary bound, and shifted power-series helpers. No C4b theorem claimed verified yet.

- 2026-09-29 — C3 required final audit `lake env lean GaloisForLFunctions/RHTower/XiHeatCassiniWoldNaturalLogCriticalEnergy.lean` exit 0, no output/warnings. C2 and C3 both built, wired, directly checked and axiom-audited. Neither goal novelty nor mandatory positive no-go closure is claimed complete. C4b generic prefix scratch first Lean check running; actual quantified prefix-loading capstone not yet created.

- 2026-09-29 — Positive-survivor strength audit: fixed coefficient `1/8` is safe but not strongest paper-closed consequence. The refined discounted bound `4c/x+2c+C(x+1)` forces `m²<=4c|s0|²`, so every coefficient strictly below `m²/(4|s0|²)` must occur infinitely often. Formalization target strengthened to that exact quantified statement; `1/8` becomes a useful corollary. Do not close the no-go at the weaker fixed-coefficient result.
- 2026-09-29 — Refined bound adds no new external premise: first establish discounted summability with coarse finite-prefix bound; then use vanishing `(c log N+C)N^(-x)` and finite Abel sums to recover the sharper `4c` estimate. Bound `log N N^(-x) <= (2/x)N^(-x/2)` supplies the boundary limit with the existing negative-power tail law, without numerical computation.

- 2026-09-29 — User extended goal: multiple significant contributions, with completion only at fully formalized unconditional proof or falsification of RH. C2/C3 are groundwork, not goal completion. Continue C4 source-loading survivor, then TT open source laws.

- 2026-09-29 — Generic C4 charge scratch `lake env lean -j1 /tmp/hgt-tt-prefix-energy-charge.lean` exit 0, no errors or warnings. Verified finite Abel identity; increment bound; coarse discounted summability; vanishing logarithmic boundary; refined discounted bound `4c/x+2c+C(x+1)`; local current holomorphy; and scaled norm-square bound. Actual source-loading bridge in `/tmp/hgt-tt-prefix-loading-actual.lean` under first Lean check. No RH claim and no goal-complete status.

- 2026-09-29 — Named incremental build of `XiHeatCassiniWoldNaturalCriticalPrefixLoading` passed, including its new generic bounds dependency. Scratch axiom audit of the unconditional capstone, scaled bound, and discounted bound reports only `propext`, `Classical.choice`, `Quot.sound`. Required final exact generic-file audit passed; actual-source file audit running. Global formal lint still fails on unrelated unreachable modules; neither new module appears among errors.

- 2026-09-29 — Required final actual-source audit `lake env lean GaloisForLFunctions/RHTower/XiHeatCassiniWoldNaturalCriticalPrefixLoading.lean` exit 0, no output or warnings. C4b fully built, wired, directly checked, and axiom-audited. Sharp C4c refinement underway; do not close the no-go card at the weaker coefficient.

### C4c — sharp single-pole loading

Frozen refinement of C4: replace the coarse logarithmic bound by harmonic-prefix comparison. If `E_N <= c log N+C`, then `E_N <= c H_N+C`. Nonnegative decreasing discount weights and finite Abel summation yield directly

`sum_(n<=N) e_n n^(-x) <= c sum_(n<=N) n^(-1-x)+C`.

Here the constant contribution telescopes exactly, and the harmonic comparison converts back to its reciprocal increments. Thus `D(x) <= c(1+1/x)+C`, instead of `4c/x+O(1)`. Equal exponent splitting now gives

`|x A(s0+x)|^2 <= |s0+x|^2 [c+(c+C)x](1+x)`.

The forced residue proves `m^2 <= c|s0|^2`, so every `0<c<m^2/|s0|^2` is exceeded infinitely often by `E_N/log N`. This is the original C4 coefficient, now paper-closed by finite harmonic comparison; no logarithmic-tail asymptotic is required. Formalize before retiring the failed critical-energy producer. Stronger real/reflected-frequency or joint multi-pole bounds remain separate conjectures.

### C9 — viable strict-subhalf energy criterion

Candidate, not yet paper-closed: `RH iff (forall 0<t<1/2, WoldNatResidualSquareEnergy t)`. Existing cofinal-three-quarter producer is dead. Direct weighted Abel holomorphy appears to remove the quarter-exponent loss in the corpus's square-energy-to-pointwise-spectrum transfer. This is a criterion, not an unconditional source estimate or RH proof. Corpus and public novelty audit required before promotion; develop after the sharp positive survivor's audit.

- 2026-09-29 — C4c generic scratch accepted finite harmonic majorization and sharp discounted bound except one rational-to-real harmonic cast normalization; corrected using `Rat.cast_add` and `Rat.cast_one`. Serena symbol lookup rejects the new untracked Lean files as ignored paths; normal text editing is the fallback, after source reads. Dependency audit: generic Hilbert lemmas currently import the actual-source forced-residue chain unnecessarily. Separating the existing generic body into a small leaf to reduce subsequent proof-check cost; no theorem statement or axiom changes in that extraction.
- 2026-09-29 — C4c and C9 deep corpus searches both have complete file inventories but partial semantic retrieval at deadline; all returned candidate/source statements inspected. No sharp harmonic prefix charge or cofinal-strict-subhalf energy criterion among hits. Compiler freshness mostly pending/stale, so applicability is checked independently. Public Mertens mean-square overlap remains unresolved; no novelty certificate claimed.

## Paper proof for C9

`[PROVED HERE — FORMALIZATION PENDING]` Assume every energy `E(t)` for `0<t<1/2` is finite. For any `q<-1/2`, choose `0<t<1/2` with `q<t-1`. Normalize the actual shifted row by `a_n=R_(n+1)(n+1)^(t-1/2)`. Its squared sum is exactly the shifted `E(t)`. The squared dual row with exponent `q-t+1/2` is summable because that exponent is below `-1/2`. Cauchy–Schwarz gives `sum |R_(n+1)|(n+1)^q<infinity`. Thus every interior ball of `Re s>-1/2` has a common absolutely summable majorant for the unit-step Abel atoms, and their sum is holomorphic there.

Add the holonomy constant to this sum to obtain `F`. The exact finite natural partial-sum identity and the mesh telescope identify `F` with the literal Abel germ on `Re s>0`. The corpus's cleared continuation identity therefore identifies `F` with the canonical singular carrier wherever zeta is nonzero in the positive-imaginary sector.

If RH fails, the corpus supplies a zero `rho` with `1/2<Re rho<1`. It is nonreal by the established real-strip nonvanishing theorem; conjugation chooses positive imaginary part. At the strict-interior point `s0=rho-1`, the canonical carrier has punctured residue `-m`, `m>=1`. Zeta's isolated-zero theorem and the cleared identity identify the canonical carrier with `F` along a sufficiently small positive real displacement. But `F` is holomorphic at that interior point, so its scaled radial limit is zero, contradiction.

Conversely, RH gives the corpus's natural pointwise power spectrum. For `0<t<1/2`, choose `t<c<1/2` and obtain an eventual `|R_N|<=B N^(-c)` bound. Then the energy terms are bounded by `B^2 N^(2t-1-2c)`, whose exponent is below `-1`; finite initial terms do not affect summability. Hence every strict-subhalf energy is finite.

No RH proof or unconditional energy producer has been obtained: the closed equivalence identifies the corrected source target. External novelty remains an independent unresolved gate.

- 2026-09-29 — Generic Hilbert extraction checked independently with only complex-power tail, real square root and Cauchy-dominated holomorphy imports: `lake env lean -j1 /tmp/hgt-tt-abel-hilbert.lean` exit 0. Promoted the small helper leaf, wired it into RHTower, and made the endpoint leaf import it. Named builds and final audits after this dependency change remain required.
- 2026-09-29 — Sharp prefix light scratch checks all inequalities except harmonic rational/real cast normalization. Corrected in two stages: cast rational harmonic sums to real first, then expand natural successor casts. No heartbeat adjustment. Once accepted, remove superseded coarse energy-majorant and boundary-limit helpers; exhaustive source references show they have no external callers.
- 2026-09-29 — Public novelty audit broadened to Bhattacharya–Martin–Simpson, "Correlations of error terms for weighted prime counting functions" (2025), https://arxiv.org/html/2507.13504v1. Their normalized reciprocal-prime errors use the same shifted zero denominator `rho-1`; persistent bounded differences characterize RH, while joint distributions require RH and LI. This is relevant overlap in mechanism and source coordinates, not evidence of global novelty for our unconditional prefix lower law or energy criterion. Numerical sections not used.

- 2026-09-29 — Sharp light scratch passed (exit 0): finite harmonic order comparison, discounted summability, sharp `c(1+1/x)+C` bound, local holomorphy and scaled `c` charge. Diagnostic tracing located a harmless ring-normalization hint in the increment telescope; replaced that tactic with `ring_nf` and removed traces before promotion. Generic bounds leaf now imports the small Hilbert leaf, deletes superseded coarse majorant/boundary machinery, and exposes the sharp bound. Actual capstone strengthened in place to every `0<c<m^2/|s0|^2`; explicit source-residue import added. Named incremental sharp build running. Previously checked versions are now stale until these revised files' builds and final audits pass.

- 2026-09-29 — Sharp named build passed: new Hilbert leaf 24s, sharp prefix bounds 77s, actual source-loading capstone 206s. No own warnings. Rebuilding the endpoint/log-energy target incrementally after the Hilbert extraction; scratch axiom audit and required final exact audits of revised modules remain pending.
- 2026-09-29 — New developer delegation mode permits proactive agents. Delegated disjoint C9 implementation, read-only public novelty audit, and read-only TT source-candidate investigation; each has explicit file scopes, one objective, constraints, and its own log/report. Root continues sharp-source audits; no shared write scope or duplicate owned build process.
