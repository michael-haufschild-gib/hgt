# Critical collar resonance and arithmetic dilation

- **ID:** APT-COLLAR-RESONANCE
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md`, topics 3–4.
- **Statement:** Determine the exact affine arithmetic skeleton and quantitative detuning of factorial shifted frequencies under prime dilation, then retain these couplings in the critical-envelope energy.

## Goal and scope

The active request is 100 significant, native APT contributions, each with an unconditional actual-source theorem, paper proof, novelty audit, and Lean certificate. Reading the attachment is initialization, not completion. Existing work is baseline, not credit toward this request. No result is counted merely because it adds a theorem or formalizes classical algebra. Current accepted count: **0/100**.

README is read-only. No numerical experiments, added axioms, full builds, or heartbeat increases. Use targeted `lake --old build` when dependencies need artifacts; final audit is `lake env lean` on each actual new leaf. Preserve existing shared changes, including the smoothing-channel module and envelope-module edit.

`update_plan` and `multi_tool_use.parallel` are unavailable in this session. This card tracks the plan; independent tool reads use `Promise.allSettled`. Serena symbol lookup on the Lean source reports the path ignored, so exact source reads are the available fallback.

## Plan

1. [x] Read all 92 lines of the field README, session instructions, relevant memories, WL/RW frontier, and exact collar/dilation sources.
2. [x] Search current corpus and primary literature; record overlap and coverage limits without treating missing hits as novelty evidence.
3. [x] Prove quantitative affine-clock defect and cross-scale resonance classification on paper.
4. [x] Test the stronger proposed uniform nonstationary gain on actual source harmonics; retain a positive classification if it fails.
5. [x] Formalize dependency-closed results, wire umbrella, pass actual-leaf/axiom audits, and run repository lint (concurrent ownership failures recorded below).
6. [x] Prove fixed-source critical prime admission using existing exact primitives; pass source, axiom, build and lint audits.
7. [x] Prove and audit the whole-span critical affine comparison; record the external global-lint failures separately.
8. [ ] Audit and prove the complete critical correlation/prime limit; count only contributions meeting the original significance standard.

### Critical admission: expanded reuse audit and paper proof

The next corpus pass found a more direct existing input than the generic periodic-primitive route:
`BiScaleUncertainty/FactorialMuntzTailPrimitive.lean` already proves a bounded primitive of the
literal factorial tail remainder, with bound 12 and derivative valid through every lattice join.
`ClampedLatticePrimitive.lean` supplies its Bernoulli primitive. These are baseline, not new results.
All 28 `bernoulli primitive` lexical hits and all five `clampedLatticePrimitive` hits were screened;
the exact names' source usages were checked exhaustively with `rg`. `ArithmeticClockFirstVariation`
already supplies the Bernoulli right derivative and global Lipschitz bound. The right-derivative
FTC in the installed mathlib therefore avoids inventing a smoothness assumption at the joins.

The deep query `factorial prime convergence critical` completed but returned mostly unrelated
factorial/prime results. The `dilation Lipschitz mean zero correlation` query was partial (interrupted
text/source retrieval). Neither is evidence of absence. The native-tail query was also partial
(malformed model output and runtime deadline); its available candidates and source arguments were
screened. It recovers the canonical tail primitive, readout, and prime/Gamma budget packages.
The completed autocorrelation query recovers `BlindCoreFarkasSeparation.autocorr_logPull`; its
source proves the general exponential change of variables. `FactorialMuntzTailPrimePolarBudget`
uses a `3/2` source envelope and a `5/4` correlation decay exponent, so it does not itself assert
critical reweighting admission. `DeningerCriticalFloquetVonMangoldtWall` assumes an exponential
autocorrelation bound on its own source space; no transfer to that space is asserted here.
Exact lexical derivative searches for the factorial profile and dyadic filter returned no hits;
an exhaustive source search agreed, but this is only a local API check, not a novelty certificate.

**Dependency-closed paper claim, now formalized at `β=1/2`.** Let
`F(v)=Σ_(n∈S) b_n Φ_(n+1)(v)` for real coefficients. Put
`A=2Σ|b_n|`, `L=14Σ(n+1)|b_n|`, `P=12Σ|b_n|/(n+1)`.
The existing bounded primitive, rescaled by `n+1`, gives a continuous `Q` with `Q'=F` on
the positive half-line and `|Q|≤P`. Existing collar bounds and Bernoulli slopes give
`|F|≤A` and a right derivative `F'_+` with `|F'_+|≤L`.
For `r≥1`, differentiate `H(v)=v⁻² F(v)Q(rv)/r` from the right. Its derivative is
`v⁻²F(v)F(rv)+E(v)`, where `|E(v)|≤P(2A+L)v⁻²/r` for `v≥1`.
The right-derivative FTC comparison on `[1,T]` and `|H(1)|,|H(T)|≤AP/r` imply
`|∫_1^T v⁻²F(v)F(rv)dv|≤P(4A+L)/r`.
The integrand is dominated by `A²v⁻²`; hence passage to the genuine Lebesgue integral gives
the same bound on `[1,∞)`. Consequently
`Σ_(r≥2) (Λ(r)/r) |∫_1^∞ v⁻²F(v)F(rv)dv| ≤ P(4A+L) Σ_(r≥2) Λ(r)/r² < ∞`.
For the actual critically reweighted source
`g(x)=1_(x≤0)e^(x/2)F(e^(-x))`, change of variables gives
`∫ g(x)g(x-log r)dx=r^(-1/2)∫_1^∞v⁻²F(v)F(rv)dv`.
Thus this is a fixed-source absolute prime-channel admission theorem. Its constant retains
coefficient and scale moments; it does not establish a uniform ℓ² bound, complete polar admission,
or positivity. The primitive and integration-by-parts mechanism are classical and already present
in the corpus; a new formal endpoint alone does not meet the requested significance standard.

The external Deninger candidate was checked further: all 36 exact source-space lexical hits were
screened, and the actual target requires smoothness plus decay of every derivative faster than
every exponential at both ends. The critical factorial source has neither that smoothness nor
that decay. Its correlation estimate therefore cannot be advertised as discharging Deninger's
premise. Any transfer through smooth compact approximants would need its own exact theorem.

Lean scratch implementation passed in `/tmp/apt_critical_admission.lean`. It includes the full
profile (not a harmonic truncation), the exact identity with critically reweighted corrected tails,
integrability of each correlation, and absolute summability of the resulting prime atoms. The
complete file exited 0. All four public theorem axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Installed the unchanged declarations as
`FactorialCriticalPrimeAdmission.lean` and added its APT umbrella import. Targeted leaf build
passed (new leaf plus four required dependency refreshes; cached remainder). The required
actual-file audit passed with an empty diagnostic log. `scripts/formal_tools.py lint --check-generated` passed; the earlier
unrelated ownership failures were repaired concurrently. This is useful admission infrastructure, not a
counted novel significant contribution; accepted count remains 0/100.

Next candidate: retain the same bounded primitive in the critical polar readout. For
`R(s)=∫_1^∞ F(v)v^(-s-1)dv` on `Re s>0`, integration by parts gives
`R(s)=-Q(1)+(s+1)∫_1^∞Q(v)v^(-s-2)dv`. The latter is a candidate continuation to `Re s>-1`,
with `|R(s)|≤P(1+|s+1|/(Re s+1))`, including both polar points 0 and 1. This does not replace
the raw non-absolutely-integrable boundary readout by a Lebesgue integral. Existing
`FactorialTailReadout` and `FactorialMuntzAnalyticRepair` give the original tail's open domain
`Re s>-1`; shifting to the critical source brings its endpoint to `Re s=0`. The deep primitive
Mellin query was partial (Qdrant timeout and malformed model response); available hits include
prior centered Bernoulli tail bounds and Sonin continuations with additional space hypotheses.
No new continuation code or novelty claim has been made.

### Next structural conjecture: the affine model on whole critical spans

Define a proposed comparison profile `Ψ_N(v)=P₀((N+1/12)v)-P₀(Nv)`. The verified defect
`e_N=N+1/12-λ_N≤1/(140N)` suggests the stronger whole-span statement
`∫_1^∞v⁻²|Σ_(N≥M)b_N(Φ_N(v)-Ψ_N(v))|²dv ≤ (C/M)Σ|b_N|²`, with universal `C`.
This would retain the near-resonant affine graph instead of excluding it, and improve the
fixed-vector admission result to an operator estimate independent of support cardinality.

Proposed proof mechanism: interpolate shifted frequencies through
`N+1/12-θe_N`, `0≤θ≤1`. They remain uniformly separated. Duhamel's identity plus the existing
Montgomery–Vaughan bound should give harmonic-layer window errors bounded by
`C min(1,(k(j+1)/M)²) Σ|b_N|²` on `[j,j+1]`. Summing against `j⁻²` gives `Ck/M`.
Minkowski then uses the actual filter coefficients `|χ(k)|/k²` and the convergent sum
`Σ k^(-3/2)`. These steps need a dependency-closed proof and exact corpus applicability audit.

Potential sharpness law: `N∫_1^∞v⁻²|Φ_N(v)-Ψ_N(v)|²dv → 7ζ(3)/(256π²)`.
The candidate constant follows from `Ne_N→1/144`, the single-mode integral
`∫_0^∞(1-cos(av))/v² dv=π|a|/2`, and
`Σχ(k)²/k³=(1-4⁻³)ζ(3)`. Cross-mode limits and a uniform harmonic-tail interchange remain
to be proved. This is a conjectured exact native error law, not a theorem or a counted result.

Search audit begun: all 177 `affine profile` lexical hits were paginated and screened; they are
mostly unrelated affine source and Gamma-profile work. Deep `frequency perturbation Riesz`
completed but returned mostly unrelated Riesz representation/function results. The rephrased
`separated exponential sums frequency interpolation` query completed; it found argument-increment
bounds and existing exponential-sum machinery, not a direct coefficient-uniform perturbation
endpoint. A module-filtered corpus query located all three interval-integral declarations in
`HTGeometry/MontgomeryVaughanIntervalMeanSquare`; inspected the exact upper-bound source at line
243. It allows arbitrary separated frequencies and gives `(ℓ+26/(πD))Σ‖c‖²`, suitable for the
interpolated families after their source separation is proved. Missing matches do not establish novelty.

### Stronger proof mechanism: exact frequency intervals

The window/Duhamel argument is unnecessary. Put
`D_(a,b)(v)=(cos(2πav)-cos(2πbv))/v`, with `0<a≤b`. The Fourier transform of
`1_(a,b)-1_(-b,-a)`, multiplied by `πi`, is this function, up to the harmless
transform sign. Plancherel gives
`∫_ℝ D_(a,b) D_(c,d) = 2π² |(a,b)∩(c,d)|` for positive ordered endpoints.
Equivalently, expand the cosine product and use the already-proved corpus identity
`∫_ℝ(1-cos(tv))/v²=π|t|`. This yields the same interval-overlap formula without
new Fourier infrastructure. The scalar kernel, Plancherel, and generic divided-difference
mechanism are prior mathematics, not contribution credit.

For each fixed positive harmonic `k`, the exact native intervals
`[kλ_N,k(N+1/12)]` are disjoint as `N` varies: `λ_N≥N+1/15`, while
`N+1/12<N+1+1/15`. Their lengths are `k e_N`. Therefore, for arbitrary finite
complex coefficient families, the whole-line identity is exactly
`∫_ℝ |Σ b_N D_(kλ_N,k(N+1/12))|² = 2π² k Σ e_N |b_N|²`.
Evenness halves this on `(0,∞)`; restriction to `(1,∞)` only decreases it.

Let `Z=Σ_(k≥1)|χ(k)|/k^(3/2)`, finite by the p-series test. The exact Fourier
coefficients of `P₀` are `-2χ(k)/(π²k²)`. Minkowski over finite harmonic sums,
then Fatou (pointwise absolute convergence follows from `Σk⁻²<∞`), proves
`∫_1^∞v⁻²|Σ b_N(Φ_N-Ψ_N)|² ≤ (4Z²/π²) Σ e_N |b_N|²`.
The verified bound `e_N≤1/(140N)` gives the stronger weighted endpoint
`≤ (Z²/(35π²)) Σ |b_N|²/N`, hence the previously proposed `C/M` estimate.
This paper proof has no support-cardinality loss and no uniform cross-harmonic spacing
assumption. The complete all-harmonic scratch proof has now passed Lean; actual-leaf
build and audit status is tracked below.

This also changes the sharpness proof: finite collections of distinct harmonics of one source
have disjoint frequency intervals once `N` is large. Their Gram matrix is then exactly diagonal.
Uniform harmonic-tail control above permits passage to all harmonics. The omitted physical
segment `(0,1)` is `O(e_N²)` for each fixed finite collection, by the cosine Lipschitz bound.
Combining this with `Ne_N→1/144` gives the previously conjectured constant
`7ζ(3)/(256π²)`; the limiting and tail passages still require a formal proof.

Fresh search audit: screened all 55 `perturb frequency` lexical hits and all three
`Duhamel mean square` hits. `Sieve/DuhamelMeanSquare` is a triangular integration lemma,
not directly the fixed-parameter comparison. `Bernoulli dilation difference integral`
completed with complete source inventory but unavailable semantic-coverage metadata;
its applicable primitives were already known. The L² perturbation and interval-Fourier deep
queries stopped at their reranking deadlines, so their results are partial. Direct corpus
search found all 16 `OneSubCosKernel` declarations; its exact integral and integrability
provide the needed scalar kernel. The inspected `FourierPlancherelIntegral` also gives an
alternative direct proof. No failed search is evidence of novelty.

External context checked: Avdonin–Ivanov, *Exponential Riesz bases of subspaces and divided
differences*, https://arxiv.org/abs/math/0103160, studies exponential families with coalescing
frequencies. Its abstract establishes relevant prior context, not the exact native factorial
endpoint or its absence. Accepted contribution count remains 0/100.

### Whole-span comparison: leaf validation complete, 2026-10-19

The complete scratch file `/tmp/apt_affine_shell.lean` exited 0. All six endpoint
axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
The proof reuses `OneSubCosKernelIntegral`, `ComplexIntegralGram`, and
`integral_norm_tsum_weighted_sq_le`. It uses the finite measure `1_(v>1)v⁻²dv`
and normalized harmonic layers divided by `sqrt(k)`, so the original coefficient
series has summable weights `|χ(k)|/k^(3/2)`. This certifies all harmonics and
arbitrary finite complex coefficient families.

Installed the declarations in `FactorialAffineFrequencyIntervals.lean` and
`FactorialCriticalAffineComparison.lean`, and wired both APT umbrella imports.
The latter also includes the explicit high-scale corollary using `S.filter (m≤·)`;
the targeted build checked both leaves, including that corollary. The universal constant
is `C=4Z²/π²`. The final bound is `C/140 * Σ‖b_n‖²/(n+1)`, with actual
integrability proved separately. No new premise, unproved public hypothesis,
axiom, heartbeat increase, or numerical experiment was introduced.

Targeted build: `lake --old build '+GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalAffineComparison'`;
exit 0, log `/tmp/apt_affine_comparison_build.log`. Both required actual-file audits exited 0
with empty diagnostic logs: `/tmp/apt_affine_intervals_actual.log` and
`/tmp/apt_affine_comparison_actual.log`. The interval audit was repeated once because its first
tool exit status was lost across compaction; the repeat has an explicit status file.
An axiom audit importing the installed leaf also exited 0; all seven public theorems,
including the high-scale corollary, use only `propext`, `Classical.choice`, and `Quot.sound`
(`/tmp/apt_affine_comparison_axioms.log`). Index refresh completed,
and all ten public declarations are present. The final refresh also exited 0
(`/tmp/apt_affine_comparison_index_final.log`). Global lint remains red as concurrent work
changes the corpus: the latest run reports three BiScaleUncertainty and three
TransHorizonIncidenceMechanics modules not yet umbrella-reachable, plus generated API/overview
drift. `/tmp/apt_affine_comparison_lint_final.log` is authoritative for these external failures.
Completed-proof scratch files and fragments were removed; search JSON and validation logs remain.
Accepted count remains 0/100: this supplies a native comparison tool,
but the original novelty/significance gate is stricter than a new correct endpoint.

### Structural consequences to audit after the comparison

The affine model is exactly 12-periodic. Its shifted Fourier frequencies are
`k(12N+1)` in period-12 coordinates, while its integer-branch frequencies are
`12kN`. Whenever `χ(k)≠0`, one has `4∤k`, and `12N+1` is odd. Thus every surviving
shifted frequency avoids multiples of four; every integer-branch frequency is
a multiple of twelve. These two complete harmonic branches have disjoint Fourier
supports on a full period, without an admitted-band restriction. This is a proposed
native arithmetic decomposition, not yet a checked Lean endpoint.

Their coefficient maps are explicit divisor convolutions: shifted output at `m`
is `Σ_(12N+1 | m) χ(m/(12N+1)) b_N/(m/(12N+1))²`; integer output at `12m` is
`Σ_(N | m) χ(m/N) b_N/(m/N)²`. Corpus/novelty audits and exact norm identities are
still required. The critical physical weight periodizes to a nonconstant positive
weight, so period orthogonality must not be substituted for weighted orthogonality.
Likewise, an L²-small comparison error alone does not transfer an unbounded prime
quadratic form. Neither observation proves Weil positivity or earns contribution credit.

### Further reuse checks and a coherent-scale candidate

The corpus already contains `factorialPhaseCombination_window_lower` and
`factorialPhaseCombination_dilated_window_upper`, as well as physical Riesz bounds for the
literal correction tails. Their source statements were checked. A new critical-weight Riesz
wrapper would not be a significant contribution. The complete prime/divisor reindexing in
`RHTower/WeilPhiDoobDivisorEnergy.lean` was also checked: it concerns the theta-ground-state
Doob form with a bounded continuous quotient, not an automatic admission theorem for the
untruncated critical factorial source. Its signed theta fibers are not pointwise nonnegative.
The deep logarithmic-diagonal/square query was partial (unfinished follow-ups and reranking),
with old-generation coverage and unavailable semantic metadata. Its available candidates do
not justify claiming that the desired affine prime graph is absent.

**Candidate, not yet a certified endpoint.** Fix a finite family of positive integers
`q_i ≡ 1 (mod 12)` and let `L→∞` through `L≡1 (mod 12)`, with
`N_i(L)=(q_i L-1)/12`. The verified comparison replaces each actual phase by
`P₀(q_i Lv/12)-P₀(q_i Lv/12-v/12)` with an error tending to zero in the critical
physical norm. Thus the candidate limiting Gram form is

`∫_1^∞ v⁻² ∫_0^1 |Σ_i b_i [P₀(q_i x)-P₀(q_i x-v/12)]|² dx dv`.

This retains a slow phase as well as a fast arithmetic carrier. Averaging only over a full
period of the affine model would lose the slow phase and gives the wrong physical limit.
For a fixed dilation `r`, the corresponding correlation candidate replaces the second
bracket by `P₀(r q_j x)-P₀(r q_j x-rv/12)`; the surviving Fourier relations are exactly
`k q_i = r l q_j`. Absolute harmonic convergence permits a finite-harmonic proof followed
by a uniform tail limit; the finite-harmonic step uses oscillatory-integral decay.

The existing fixed-source prime bound has `P=O(L⁻¹)` and derivative bound `O(L)`
on this fixed finite pattern. Consequently its product is bounded uniformly in `L`, giving
a summable majorant `C Λ(r)/r²` for the integrated prime atoms. This suggests passage to the
**complete** prime series after the fixed-dilation limit, not just a finite prime truncation.
The precise constants, exact index parametrization, all limiting passages, source-space
conditions, and novelty/significance audits remain open. No new contribution is credited.

The singleton case and the full prime-series interchange are now formalized and tracked in
`apt-critical-single-source-prime-limit-2026-10-19.md`. The actual full-profile correlation
and complete logarithmic prime-series limits, strict dyadic sign law, targeted builds,
three actual-file audits, and eleven endpoint axiom audits passed. The global lint gate
still has two unrelated TransHorizon umbrella-reachability errors. No significant-result
credit is assigned before a native consequence and priority audit justify it.
All 41 `factorial Riesz` hits,
31 module-filtered `factorial limit` hits, 47 `periodic averaging` hits, and 86
`Riemann Lebesgue` hits were paginated and screened. The exact reusable cosine decay theorem
is `RHTower.tendsto_integral_mul_cos_atTop` in `HTGeometry/SoninCosineRiemannLebesgue.lean`;
its actual hypothesis is `Integrable g`, despite its narrower prose description.

### Critical admission validation, 2026-10-18

- Full scratch proof and four axiom audits: exit 0; `/tmp/apt_critical_admission.log`.
- Targeted `lake --old build '+GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeAdmission'`:
  exit 0; `/tmp/apt_critical_leaf_build.log`. Four needed dependency leaves refreshed, then the
  new leaf built; remaining jobs replayed cached artifacts. No umbrella/full build.
- Required `lake env lean GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeAdmission.lean`:
  exit 0, no diagnostics; `/tmp/apt_critical_actual_audit.log`.
- `scripts/formal_tools.py index`: exit 0; all six public declarations appear in `formal/LEAN_API.md`.
- `scripts/formal_tools.py lint --check-generated`: exit 0, existing large-file warnings only;
  `/tmp/apt_critical_lint.log`. Earlier unrelated global lint failures are superseded by this run.
- Whitespace checks passed. No commits/push, README edits, added axioms/premises, numerical
  experiments, heartbeat increases, or changes to foreign source files.
- Owned scratch Lean files/fragments removed after validation; search JSON and validation logs retained.
  No own build, search, index, or lint process remains live. Accepted contribution count stays 0/100.

## Current exact input

`FactorialCollarIrrationalityAndSpacing.lean` proves

\[
4\lambda_N^3=N^2(4N+1),\qquad
1/15\le\delta_N:=\lambda_N-N\le1/12.
\]

It proves irrationality, a cubic equality criterion, and separation of `r λ_N` from `λ_(rN)`. It does not supply separation from every different scale. The envelope module's integration-by-parts theorem concerns a single base frequency and its dilation; applying it uniformly to all mixed scale pairs would need a new gap theorem.

## Conjecture loop

### C1: uniform cross-scale oscillatory gain

**Candidate to test:** high factorial scales force all shifted prime-dilation frequency gaps away from zero. This would allow a uniform integration-by-parts gain in the critical prime budget.

**Potential counterfamily:** `r=13`, `N=13M+1`. The affine clocks satisfy `N+1/12=13(M+1/12)` exactly. The exact cubic clocks remain distinct but may approach one another.

### C2: positive survivor — affine residue classification

Set `e_N=N+1/12−λ_N`. Cubic expansion gives the exact identity

\[
N e_N=\delta_N^2+\frac{\delta_N^3}{3N}.
\]

The existing collar bounds should imply `1/(225N) ≤ e_N ≤ 1/(140N)`. Consequently

\[
\lambda_N-r\lambda_M
=\frac{12N+1-r(12M+1)}{12}+r e_M-e_N.
\]

For `M≥r≥2`, a nonzero integer numerator gives a uniform gap; a zero numerator requires `r≡1 mod12` and forces a positive gap of order `r/M`. Prove both regimes with explicit constants, not numerical scans. This would identify exactly where the single-frequency oscillatory gain cannot transfer to mixed scales.

### C3: complete source consequence (open)

Use the arithmetic skeleton `12N+1` to isolate resonant shifted couplings and bound their aggregate cost together with the integer-frequency divisor couplings. A frequency classification alone does not establish a complete prime/Gamma/polar sign, nor does it yet pass the requested significance gate.

## Evidence and novelty status

Initial hybrid and divisor-energy deep searches completed with `partial=false`, no reported errors; compiler coverage is mixed and most indexed sources are not freshly compiled. Candidate/source-argument hits were inspected; no theorem was accepted from a search snippet. Extended collar, harmonic and mixed-frequency searches and source audits are recorded below, including partial results. No external-priority claim and no accepted contribution yet.

### Expanded corpus audit

After the user's explicit reminder, ran additional exact-name and deep searches for `factorialShiftedFreq`, `collar affine`, finite-window near-resonance correlations, and prime-dilation affine frequencies. Exact lexical search with the module cap removed returned all nine named clock declarations. Their source establishes the cubic relation, irrationality, fixed-layer spacing, and the special comparison `r λ_N−λ_(rN)≥1/20`. It does not state the comparison with `λ_(rN+(r−1)/12)`.

Existing general results must be reused:

- `DyadicBernoulliFilterAndBohrCoercivity.tendsto_bohr_mean_cexp_zero_of_ne_zero`: every fixed nonzero frequency has zero Bohr mean. Not a uniform statement when frequencies approach zero.
- `HTGeometry/FiniteWindowOneKnobUniformity.lean`: compact sets avoiding finitely many relation roots admit a uniform detuning gap. The current sequence approaches an asymptotic collision, so its avoidance premise does not provide a uniform gap.
- `HTGeometry/CountableRecurrenceWallRayLaw.lean`: affine character detuning and recurrence-wall infrastructure. Generic affine-frequency algebra is existing work.
- `RHTower/ZetaNotchResonanceCount.lean`: quantitative weighted near-resonance counts for logarithms of integer ratios, including `tsum_nearRes_le`. These are potential aggregate-budget inputs, but their logarithmic ratio and pair weight differ from the literal cubic collar frequency.
- `RHTower/MobiusAdditiveDilationDiagonalization.lean`: existing exact divisor–Möbius Fourier coefficient transform and Parseval diagonalization. Reproving this mechanism is not new.
- `RHTower/PMRamanujanNearbyPrimeResonance.lean`: literal primitive Gram covariances for nearby prime dilates, including unbounded centered covariance. Thus the generic discovery that arithmetic cross-scale correlations need not decay is already present.
- `RHTower/WeilPhiDoobDivisorEnergy.lean`: a von Mangoldt-weighted divisor graph energy is already an explicit corpus object. A generic graph-square rewrite is not a new APT field contribution.

Paginated and inspected all 69 metadata hits for lexical `near resonance` and all 52 hits for `frequency dilation`; read the relevant mechanisms listed above. The three additional broad deep searches returned partial results with runtime deadlines. Their available hits were used, then exact lexical searches supplied deterministic coverage for those queries. This is scoped search evidence, not exhaustive mathematical non-equivalence or a proof of novelty.

Primary literature inspected: [Aistleitner–Berkes–Seip, GCD sums and dilated functions](https://arxiv.org/abs/1210.0741), [Aistleitner–Berkes–Seip–Weber, spectral norms of GCD matrices](https://arxiv.org/abs/1407.5403). These already connect arithmetic dilation and correlation. An ordinary GCD-sum reformulation cannot count as a new contribution. No exhaustive priority claim follows from the present search.

## Paper proof of the candidate frequency classification

**Status: [PROVED HERE] algebraic frequency result; targeted leaf build, actual-file Lean audit and axiom audit passed. Significance gate remains pending; repository ownership lint is affected by concurrent work.**

All indices in this paragraph are positive integers. Expand the proved cubic law with `λ_N=N+δ_N`:

\[
3N^2\delta_N+3N\delta_N^2+\delta_N^3=N^2/4.
\]

Hence `N e_N=δ_N²+δ_N³/(3N)`. Since `1/15≤δ_N≤1/12` and `N≥1`,

\[
1/225\le N e_N\le 1/144+1/5184=37/5184<1/140.
\]

Let `r≥2`, `M≥r`, `N≥1`, and set `A=12N+1−r(12M+1)`, an integer. The exact gap is

\[
g=\lambda_N-r\lambda_M=A/12+r e_M-e_N.
\]

Both `r e_M` and `e_N` lie in `[0,1/140]`. If `A≠0`, therefore

\[
|g|\ge1/12-1/140=8/105>1/15.
\]

If `A=0`, then `N≥rM≥2M`. The defect bounds imply `M e_N≤1/280`, and thus

\[
M g=r M e_M-M e_N\ge r/225-1/280\ge r/400,
\qquad M g\le r/140.
\]

Consequently the full dichotomy in this range is

\[
|\lambda_N-r\lambda_M|<1/15
\iff 12N+1=r(12M+1),
\]

and in its small-gap branch `r/(400M)≤g≤r/(140M)`. The equality forces `r≡1 mod12`. Conversely for `r=12q+13`, `N=rM+q+1` realizes the equality for every `M≥1`; the two-sided bounds themselves do not require `M≥r`.

For `r=13`, `N=13M+1`, the gap is strictly positive for every `M` and tends to zero. This disproves C1 for the actual shifted first-harmonic frequencies. It neither disputes fixed-layer spacing nor assumes cancellation between different harmonics.

### Physical comparison and stronger quantitative target

Put `g_M=λ_(13M+1)−13λ_M` and

\[
K_M=\int_1^\infty v^{-2}e^{2\pi i g_Mv}\,dv.
\]

The exact critical physical weight is `v⁻²`. The integrand has norm `v⁻²`, whose integral is one. Since `g_M→0`, dominated convergence gives `K_M→1`. Meanwhile the existing Bohr theorem gives zero long-window mean at every fixed `M`, because `g_M>0`. Thus infinite-window orthogonality cannot provide a scale-uniform estimate of these physical shifted-harmonic couplings.

The sharp further target is `M g_M→7/78`: first `δ_M→1/12`, then `M e_M→1/144`, and use `(13M+1)e_(13M+1)→1/144` with `M/(13M+1)→1/13`. This identifies the resolving window scale as `M`, but the corresponding full-profile signed prime budget is still open.

## Next conjecture: residue-restricted divisor budget

### Next admission question: fixed-vector prime convergence below the absolute-envelope threshold

For a finite actual profile combination `B(v)=Σ b_N Φ_N(v)`, consider
`g_β(x)=1_{x≤0} exp(βx) B(exp(-x))`, `β>0`. Candidate: its prime autocorrelation
series is absolutely convergent even at and below `β=1/2`, with a bound depending
on the coefficient frequency moments. Each centered periodic Bernoulli component
has a bounded primitive; dilation should give a correlation gain `O_B(1/r)`.
Then the prime tail is bounded by a constant times `Σ Λ(r)/r^(β+3/2)`.
A Fourier proof could split at harmonic order proportional to `r`; the high harmonic
tail has size `O_B(1/r)` and the remaining phases have gaps proportional to `r`.
This is not a coefficient-uniform estimate, and the near-resonant source-scale pairs
above explain why its constant must retain scale information.

The full functional is a separate issue: for `β≤1/2`, absolute polar readout
integrability can fail. Do not replace Lebesgue integrals by conditionally convergent
improper integrals without an actual-source continuation theorem. Initial corpus
searches are `periodic primitive dilation`, `mean zero primitive`, and `Bernoulli
Lipschitz`; no implementation started. `HTGeometry/PaperDirichletPeriodicPrimitive`
already gives a bounded primitive for the mean-zero Dirichlet kernel; that generic
mechanism is prior work, not a new contribution.

### Refined prime-channel question

The mixed-branch exclusion has a sharp prime-family exception. Odd `r` preserves
`χ(rk)=χ(k)`, since the dyadic multiplier depends only on whether `v₂(k)` is zero,
one, or at least two. Hence surviving odd-prime-power mixed branches stay separated
once the source scale admits `rk`. For the prime two, the surviving harmonic `k=6`
has `χ(6)=-1`, but dilation by `r=2` produces effective harmonic `12`. Taking the
integer branch at scale `N=12M+1` gives
`12 λ_M-(12M+1)=-12 e_M`, which is nonzero and tends to zero. For `r=4`, harmonic
`k=3` gives the same pair. Thus excluding mixed aliases for every prime power is
false; the corrected split is odd prime powers versus powers of two. The latter
have a geometric critical weight `Λ(2)/2^e` and may admit a separate absolute
budget. This is an exact source mechanism, not a numerical experiment. Formal
implementation and the full weighted error estimate remain open.

The surviving skeleton is the integer coordinate `Q_N=12N+1`. At its fundamental shifted branch, resonant dilation preserves this coordinate exactly: `Q_N=r Q_M`. For `r≡1 mod12`, a critical coupling carries weight `Λ(r)/r`. Before inventing a new energy, audit the existing divisor-graph corpus for the exact weighted square decomposition with ground ratio `1/r`, diagonal `Σ_(r|Q_N,r≡1 mod12) Λ(r)`, and the complementary residue budget. The full identity `Σ_(d|Q_N)Λ(d)=log Q_N` is classical and existing.

The potential new problem is simultaneous control of the integer skeleton `N` and affine skeleton `12N+1` with the same source coefficients and all nonresonant harmonic errors. Their coprimality alone does not establish a quantitative signed estimate. No positivity claim, new hypothesis, or contribution credit is attached to this conjecture.

## No-go closure

### Next rigidity conjecture: no exact collision inside the admitted harmonic band

The general small-gap classification exposes a stronger paper theorem. For positive
`a,b,N,M` with `a≤N` and `b≤M`, equality `a λ_N=b λ_M` implies both `a=b` and `N=M`.
Indeed, the small-gap theorem gives `aQ_N=bQ_M`. Cancelling `a` in the two relations
gives `λ_N Q_M=λ_M Q_N`. Cubing and applying the exact source cubics yields
`N²(4N+1)Q_M³=M²(4M+1)Q_N³`. Their difference factors exactly as

`(N-M) [144NM(N+M)+4N²+40NM+4M²+N+M]`.

The bracket is strictly positive for positive source scales. Hence `N=M`, then `a=b`.
This proves exact cross-layer rigidity in the admitted band, while the prime-thirteen
family still shows that positive separation is not uniform in physical space.
Outside this band no rational-independence claim is made. The existing cubic resonance
classification is reused rather than treated as absent. Corpus search
`shifted harmonic injective resonance` completed without a relevant exact-source hit;
this is limited retrieval evidence, not a general priority certificate. Formal status:
paper proof complete; implementation, targeted build, actual-file audit and axiom audit passed.

### Dependency-closed paper refinement: all harmonics and mixed branches

Let `a,b ≥ 1`, `N ≥ a`, and `M ≥ b`. Set `Q_N=12N+1` and `A=a Q_N-b Q_M`.
The exact identity is
`a λ_N-b λ_M=A/12+b e_M-a e_N`.
Both defect terms lie in `[0,1/140]`. If `A=0`, the gap has absolute value at most `1/140`.
If `A≠0`, integer separation gives absolute gap at least
`1/12-1/140=8/105>1/15`. Thus the same small-gap iff criterion holds between
arbitrary harmonic layers, with the explicit admission conditions above. This includes
exactly resonant pairs; no assertion of irrational independence is used.

For the mixed branch let `k≥1`, `N≥1`, and `J∈ℤ`. Its integer residue is
`B=k Q_N-12J`. If the source multiplier `χ(k)` is nonzero, then `4∤k`.
Since `Q_N≡1 (mod 4)`, `B=0` would imply `4∣k`, a contradiction. Hence
`|k λ_N-J| ≥ 1/12-k e_N ≥ 1/12-k/(140N)`.
If `χ(k)=0`, the weighted version remains trivially true. Therefore, without any
spectral premise,
`|χ(k)|/12 ≤ |k λ_N-J|+k/(140N)`.
In particular, if `N≥k` and `χ(k)≠0`, the mixed gap is at least `8/105`.
An odd dilation preserves `χ(rk)=χ(k)`, so this also controls the reversed mixed branch
when `M≥rk`. The dyadic prime-power channel needs separate treatment.

These statements isolate two surviving arithmetic relations in the full dyadic Fourier
expansion: `aN=bM` in the integer branch and `aQ_N=bQ_M` in the shifted branch.
They do not yet estimate the full signed prime sum, pass all harmonic tails, or prove
positivity. Formal status: general harmonic classification and mixed separation passed the scratch Lean audit; the odd-dilation reformulation remains to wire. Significance remains under review.

- Source audit of `FactorialSourceWeilContrastAndDivisorResponseProducer` confirms its
  small normalized quantity is a difference of two genuine source autocorrelations.
  Its complete functional identity is exact, but neither theorem supplies the sign of
  an arbitrary high-scale signed factorial span. No missing positivity premise is
  discharged by merely renaming that existing contrast estimate.

C1 is false. Its positive survivor is C2 and the admitted-band rigidity theorem, together with a literal critical physical-correlation consequence. Their paper proofs, targeted build, actual-file Lean and axiom audits passed. The failed route and positive survivor are recorded in `../../../5-failed/apt-uniform-critical-cross-scale-gap-2026-10-18.md`; the critical prime-energy programme remains open.

## Log

- Final index regeneration passed, exit 0 (`/tmp/apt_collar_index.log`). `FiniteGridNullCorrector` now has its umbrella import, but `ClosedCycleAmbiguityDecay` still has no import in `BiScaleUncertainty.lean` at the final inspection. Do not rerun the full lint merely to rediscover that known concurrent failure. Last repository lint result remains exit 1; the actual new leaf, its artifact build and all printed axioms are verified. No own build, search or index job remains running.

- Final actual-file audit passed, exit 0, with empty diagnostic log: `lake env lean GaloisForLFunctions/arithmetic-positivity-theory/FactorialAffineClockResonance.lean`. Evidence `/tmp/apt_collar_actual_audit.log`. No own Lean/build remains running. Removed six owned scratch source/diagnostic files; kept search and validation evidence. A second index regeneration (session 83807) addresses concurrent API staleness; its result is pending.

- Lint recheck exited 1. The previous Bezout/TransHorizon errors disappeared; concurrent BiScaleUncertainty leaves `ClosedCycleAmbiguityDecay` and `FiniteGridNullCorrector` are now unreachable from their umbrella, and `formal/LEAN_API.md` became stale during concurrent edits. Final index regeneration remains necessary. New APT leaf still has no reported lint violation.

- Targeted leaf build passed, exit 0: `Built ...FactorialAffineClockResonance (257s)`. Cached dependency warnings were replayed; only the new leaf was built. Evidence: `/tmp/apt_collar_leaf_build.log`. Final actual source audit now runs as session 62828: `lake env lean GaloisForLFunctions/arithmetic-positivity-theory/FactorialAffineClockResonance.lean`, log `/tmp/apt_collar_actual_audit.log`. Do not start another own Lean/build before this handle exits.
- The previously unreachable Bezout module now has its umbrella import at line 106; this external change justifies one lint recheck. Session 44008 runs `scripts/formal_tools.py lint --check-generated`, log `/tmp/apt_collar_lint.log`. The prior lint failure remains the known result until this check exits.

- Next-candidate searches completed: all 80 `mean zero primitive` lexical hits and all 9 `Bernoulli Lipschitz` hits screened. The exact source bound `RHTower.DeletionMixedRefinement.bernoulliPeriodic_lipschitz_bound` in `ArithmeticClockFirstVariation.lean` gives `|B₂(x)-B₂(y)|≤|x-y|/2`, including joins. `CCMSawtoothDilationMean` supplies prior periodic product primitives and integration-by-parts machinery. Deep `periodic primitive dilation` retrieval was partial (malformed model response/deadline); use available source hits, not an absence inference.

- Complete scratch audit passed with exit 0. All seven printed endpoints, including `factorial_admitted_harmonic_resonance_iff`, use only `[propext, Classical.choice, Quot.sound]`. Evidence: `/tmp/apt_collar_final_axioms.log`. Targeted `lake --old build '+GaloisForLFunctions.«arithmetic-positivity-theory».FactorialAffineClockResonance'` is now running; final actual-file audit follows after that single foreground build exits. No full or umbrella build requested.

- `scripts/formal_tools.py index` completed: regenerated `formal/LEAN_API.md`, `formal/LEAN_GAPS.md`, `formal/LEAN_OVERVIEW.md`; new leaf and its public endpoints are present in the generated API index.
- `scripts/formal_tools.py lint --check-generated` exited 1. No new-leaf diagnostic; two unrelated ownership errors remain: `owned module unreachable from theorem-area umbrella GaloisForLFunctions.BezoutValuationIncidence: GaloisForLFunctions.BezoutValuationIncidence.RamanujanGapChainExactPrefixGram`; `research leaf module at package root: TransHorizonIncidenceMechanics.lean; move it into an owned theorem area`. Numerous pre-existing large-file warnings were also emitted. Preserve those concurrent files; do not report the global lint gate green.

- Installed `FactorialAffineClockResonance.lean` and added its APT umbrella import, preserving the concurrent `FactorialSpanTestPolarPrimeGammaBudgets` import. Current scratch audit rechecks the complete implementation and axiom closure after replacing a reserved local identifier; final actual-file audit remains required. Index regeneration is running separately and does not launch a Lean build.

- Second extension audit: `factorial_small_harmonic_gap_iff_affine` passed with only standard Lean axioms, as did the fixed-scale prime-thirteen Bohr limit. The physical cosine limit needed explicit unfolding of its function in the goal, and the mixed-gap triangle inequality used an obsolete name (`abs_add`; corrected to `abs_add_le`). Those corrections and the admitted-band exact-resonance rigidity proof are now in one foreground scratch audit. Failed elaborations are not counted as proofs; their diagnostic `sorryAx` is not an accepted endpoint.

- Concurrent-source refresh: `FactorialSpanTestPolarPrimeGammaBudgets.lean` appeared in the shared tree. Inspected its Gamma lower bounds, exact pole readouts, `factorialSpanTest_polar_budget`, and `abs_atomPairing_factorialTailCombination_le`. It supplies the canonical `β=3/2` absolute prime budget via `∑Λ(r)/r²`, plus polar budgets. This task's inverse-square phase correlation is the critical `β=1/2` measure, not the canonical tail's `v⁻⁴` measure. Do not duplicate those concurrent budgets or infer full signed-span positivity before its remaining assembly is checked. Their build status has not been independently audited here.
- Filter audit: all 10 `dyadicHarmonicChi` lexical hits and all 87 `mixed frequency` lexical hits were screened. The exact dyadic object occurs only in the existing filter and harmonic-layer modules; existing generic mixed-frequency/Bohr/Abel results do not assert the proposed factorial affine alias exclusion. Deep `dyadic mixed resonance collar harmonic` retrieval was partial; irrelevant hits are not absence evidence.

- Lean scratch audit `/tmp/apt_collar_affine.lean` completed with exit 0 for the exact affine defect identity, inverse-scale defect bounds, all `r ≡ 1 mod 12` resonant families, prime-thirteen positive gap, and small-gap iff classification. Physical inverse-square cosine correlation and fixed-scale Bohr comparison added; their audit is running. No contribution counted yet.
- Extra corpus searches: `affine collar` lexical (all 8 hits inspected); `vonMangoldt square logarithm` deep (complete retrieval, source/compiler snapshot coverage remains largely pending); `factorial prime divisor cancellation` deep (complete); `factorial profile dilation correlation limit` deep (partial, runtime deadline). The divisor search exposes `FactorialSourceWeilContrastAndDivisorResponseProducer.factorialSource_contrast_and_divisorResponse_master`; complete source cancellation must reuse/check that result. The broad profile query mostly found unrelated factorial growth and is not absence evidence.
- New conjecture to audit: the canonical dyadic multiplier kills `4 ∣ k`. For `N ≥ k ≥ 1`, a mixed gap `k λ_N − J` with integer `J` has residue `k(12N+1) − 12J`; its vanishing forces `4 ∣ k`, hence zero source multiplier. Together with `k e_N ≤ 1/140`, surviving mixed harmonics should have a uniform `1/15` gap. For the reverse mixed branch after an odd dilation, the same argument uses `4 ∣ r k ↔ 4 ∣ k`. This is a proposed source-specific refinement, not yet a formal theorem or novelty claim.

- 2026-10-18 — Opened from the user attachment ending `4185f2f3-69a7-4408-a6e5-51260ec1f59e/pasted-text-1.txt`; persistent 100-contribution goal remains active.
