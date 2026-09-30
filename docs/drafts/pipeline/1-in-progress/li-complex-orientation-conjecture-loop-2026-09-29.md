# LI complex orientation conjecture loop

- **ID:** LI-CO-2026-09-29
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP
- **Source:** `docs/reports/rh-current-frontier-map.md`, route LI; corpus searches and exact source inspection.
- **Statement:** Seek a source-specific complex-support or indefinite-matrix orientation law for the literal Cassini Euler defect, retaining the completed-Abel coefficients exactly.

## Goal and completion contract

Goal remains active until an unconditional Lean proof or falsification of RH is complete. Auxiliary identities, receivers and failed conjectures do not meet that goal. No numerical exploration, additional axioms, assumed analytic inputs or zero-location premises may certify a contribution. Universal absence from public literature or model training data cannot be certified: novel status requires bounded corpus and primary-source audits, with their limitations stated.

## Current verified frontier

- `LiEvenCrossTwoScaleRadialGeneratingLaw.lean:924`: full actual-divisor/all-mode generating law is a reciprocal-scale divided difference of `D(y)=y(Re M₀(y)−y Re M₁(y))`.
- `LiEvenCrossCassiniRadialEulerBridge.lean:39`: `D(y)=2y[y(logDeriv C)'(1−y)−logDeriv C(1−y)]`, with `C` the fixed Cassini source; no new continuation/orientation law asserted.
- `LiEvenCrossRadialPositivity.lean:67`: `D(y)>0` for every positive real mass, unconditionally. Scalar first-response positivity is already exhausted.
- `LiEvenCrossGlobalRealAxisSignNoGo.lean:121`: global real-axis quotient positivity plus all-order positive-ray complete monotonicity coexists with a negative completed-Abel mode in a conjugation-symmetric packet.
- `LiEvenCrossCompletedAbelInteriorFirstZero.lean`: each fixed mode starts strictly positive at mass zero; all-mode zero exclusion on `(0,1/4]` remains a sufficient RH-strength burden, not an established producer.
- Prior finite-critical-prefix, sublinear repair, coefficient-recovering regularization and uniform infinite-tail no-gos forbid prefix arguments that discard leading tail cancellation.

## Working plan

1. Audit actual LI complex continuation, fixed Cassini jets, and existing matrix/indefinite classifications.
2. Conjecture from exact inspected source formulas; attempt dependency-closed paper proofs or explicit symbolic obstructions.
3. Audit novelty before claiming new knowledge. Formalize only a significant survivor absent from the audited corpus and primary literature; wire leaf imports without full umbrella builds.
4. Run targeted foreground checks, final `lake env lean <leaf>` audit, scratch-only axiom audit and formal lint. Continue to next conjecture regardless of outcome.

No `update_plan` tool is exposed in this session; this card tracks the multi-step work.

## Conjecture ledger

### LI-CO1 — real radial response sign

**Disposition:** rejected as already proved and nonselective. Actual `D(y)>0` for all `y>0`; generic packet masks retain that sign with wrong LI coefficients. No new Lean code.

### LI-CO2 — unavoidable complex double-pole support

**Candidate:** the continuation of the literal Euler defect has double poles at squared Xi nodes, with linked principal coefficients that recover location and intrinsic multiplicity.

**Critique:** generic Euler pole amplification already appears in `SuzukiCarlemanJumpEulerDefectWeld.lean` and `SuzukiCarlemanJumpPhaseObstruction.lean`. Exact principal coefficients are local logarithmic-derivative calculus; novelty and significance are not established. Do not count a specialization or a renamed classical fact as new knowledge.

**Status:** read-only audit; test stronger matrix-signature survivor before any implementation.

### LI-CO3 — corrected indefinite-matrix signature

**Candidate under formulation:** ordinary Pick/Loewner positivity of the normalized double-pole response may contain a mandatory indefinite baseline from genuine critical poles. Determine whether subtracting/classifying that baseline exposes a coefficient-faithful excess signature for nonreal support, and whether that signature has a source producer.

**Status:** exact statement unresolved; corpus and primary-literature audits running. No positivity assumption accepted.

**Audit outcome:** rejected as new knowledge in its generic finite-packet form. A real double pole contributes one positive and one negative square; a nonreal conjugate double-pole pair contributes two of each. The index counts distinct double poles, not original Xi multiplicity. Exact rational negative-index classification is public (Song–Hao–Hu–Chen 2014, DOI `10.1155/2014/605492`, Theorems 20–21). Integrating once gives the corpus's existing `xiEulerAudenaertIncreasing`; corrected factorial Hankel jets are already the increasing parity tower in `XiSquaredEulerAntiLownerHankelEndpoint.lean`. No duplicate Lean module will be added.

### LI-CO4 — Euler differential current ladder

**Derived identity:** write `E=v∂v`, `C_n(v)=current(v,n)` and `C_{−1}=0`. Then

`(n+1)(2n+3) C_{n+1} − 4(n+1)² C_n + (n+1)(2n+1) C_{n−1} = 8(E+1)² C_n`.

The transfer polynomials `p_n` satisfy `C_n=p_n((E+1)²)C_0`, `C_0=2D′`. Their increments admit a positive recurrence:

`Δ_{n+1} = 8/((n+1)(2n+3)) · T p_n + (2n+1)/(2n+3) · Δ_n`,

so every coefficient of `p_n` and `Δ_n` is nonnegative.

**Novelty outcome:** generic recurrence is classical Mittag–Leffler/Meixner–Pollaczek theory. Stanković–Marinković–Rajković, *Deformed Mittag-Leffler Polynomials*, arXiv:1007.3612, Theorem 2.1 (parameter 1) gives the exact recurrence after eliminating even indices; Paris, *The Asymptotics of Mittag-Leffler Polynomials* (2012), equation (1.3), identifies the normalized family. Actual LI realization was not found publicly, but recurrence alone reformulates the existing two-scale encoding without source sign control. Do not count it as significant new knowledge.

**Next hostile test:** all even shifted Euler derivatives of `C_0` would suffice by transfer coefficient positivity. Test whether the actual source's nonreal logarithmic-mass poles force that stronger cone to fail even when critical zeros are present unconditionally.

### LI-CO5 — actual complete-source balanced Pick index

**Candidate closed statement:** for every natural `k`, the literal normalized Cassini Euler quotient has one regular upper-half-plane `k`-node Pick matrix strictly negative definite and another strictly positive definite. No RH or source-positivity premise.

**Proof mechanism:** Hardy's corpus theorem supplies arbitrarily many distinct positive real Xi zeros. Their negative squared masses are distinct real double poles of the actual quotient. At each such pole `p`, quotient principal term is `−2mp/(z−p)²`, with `m>0` and `p<0`. Approaching distinct poles along opposite upper-half-plane diagonal rays gives, after common `ε³` scaling, strictly negative/positive diagonal matrix limits; off-diagonal entries tend to zero. Finite-dimensional coercivity supplies the two definite matrices. This is an actual infinite-source obstruction, not an RH countermodel or a fixed finite packet.

**Potential stronger extension:** every nonzero finite linear differential operator with real-polynomial coefficients preserves higher-order real poles at infinitely many critical masses, hence also has unbounded balanced Pick index. Highest nonzero coefficient has finitely many roots; at every retained pole the transformed order is `degree+2`. Nonlinear cancellations and nonlocal integration are outside this statement.

**Status:** dependency and exact-source novelty audits underway. Generic pole-index mechanism is public and is not claimed new. Canonical primitive duplicates AudenaertIncreasing; strongest potentially new positive survivor is the actual source's unbounded bidirectional signature itself.

**Disposition:** retained as useful classical consequence, not banked as significant original knowledge. Public general Krein–Langer pole count plus Hardy already forces unbounded indices after every nonzero finite polynomial differential readout. No repository module created for this branch.

### LI-CO6 — cofinal sign oscillation of actual even Euler jets

**Paper result:** for every `v∈(0,1/4]`, even shifted Euler derivatives of `C₀(v)` take both signs cofinally. Even logarithmic-mass germ `R_v(t)=Γ(v exp t)+Γ(v exp(−t))`, `Γ=2zD′`, retains disjoint actual cubic-pole lattices with coefficients `±8m`. Finite positive Taylor radius plus real-axis analytic continuation excludes eventually either coefficient sign by Vivanti–Pringsheim.

**Positive survivor:** evenization does not erase actual source multiplicity; it retains two disjoint periodic pole families. Nonnegative coefficients of the universal transfer polynomials therefore still require structured cancellation among source jets of both signs.

**Status:** Lean-closed in `docs/drafts/pipeline/3-formalized/li-even-euler-jet-oscillation.md`, strengthened to every positive mass and literal real derivatives. All five leaf audits passed; axioms are foundation-only. Bounded primary/corpus audit found no exact collision; worldwide novelty remains unverified. No RH conclusion or individual-current negativity follows.

### LI-CO7 — all-positive-mass strengthening

**Next conjecture:** cofinal both-sign even Euler jets hold for every `v>0`, not only `v≤1/4`. Choose a sufficiently large genuine Hardy squared node so reflected inverse mass avoids the entire pole support. Paper and novelty audit needed before widening the Lean capstone.

**Paper audit passed:** Hardy gives actual real Xi nodes of arbitrarily large modulus. For each fixed `v>0`, choose `b` with `|b|>v²`. At `t₀=log(−b/v)` the direct current has order `−3`; the reflected mass has norm `v²/|b|<1`, inside the existing source zero-free disk. Thus one pole survives at every positive mass, regardless of possible cancellation at other nodes. Real-axis analyticity is already unconditional for every positive mass. The same canonical-radius and finite-tail Pringsheim proof applies unchanged. New leaf `LiEvenCrossCassiniAllMassPole.lean` and stronger coefficient/current domains are being audited; compilation not yet claimed.

**Final status:** Lean-closed. `exists_liEvenCrossCassiniEvenLogMassGerm_cubic_pole_positive` supplies the source pole. Canonical coefficient/current theorems now quantify over `LiEvenCrossPositiveMass`; `liEvenCrossRealLogMassFirstCurrent_even_deriv_cofinal_both_signs` certifies the paper's literal real derivatives. Targeted builds, every exact final leaf check and capstone axiom audits passed. Whole-tree lint remains red outside these leaves.

### LI-CO8 — quantitative sign density

**Candidate:** at each fixed interior mass, both sign sets of even Taylor coefficients have positive lower density, with nonzero excursions after normalization by nearest-pole radius and cubic polynomial scale.

**Audit:** nearest cubic-pole shell gives a finite trigonometric sum plus a vanishing remainder. After grouping opposite poles, characters are distinct and nontrivial, so compact orbit closure supplies positive-frequency positive and negative excursions. Full natural density is not automatic if the leading sum vanishes on whole orbit-closure components.

**Disposition:** generic mechanism overlaps Wilson (1950, DOI `10.1017/S0013091500008701`) and Bell–Gerhold, arXiv:math/0506398, Theorem 2. Exact actual-source specialization not located, but strengthening excludes no additional source-sign producer beyond LI-CO6 and supplies no RH orientation inequality. Do not bank generic density as separate significant discovery.

### LI-CO9 — reciprocal-divisor cancellation boundary

**Candidate:** outside the interior window, logarithmic reflection retains cubic coefficient `8[m(b)−m(v²/b)]`. Balanced reciprocal multiplicities erase the principal part; unbalanced multiplicities retain cubic order. Quotient source `F_v(t)=C(1−v exp t)/C(1−v exp(−t))` yields `R_v=4·deriv²(logDeriv F_v)` on punctured regular germs.

**Correction exposed by hostile audit:** removable meromorphic germ does not imply literal `AnalyticAt` of totalized Lean expression at canceled source zeros. Assigned point value must be audited or canonical extension defined. Full candidate and proof audit live in `1-in-progress/li-logmass-reciprocal-divisor-balance.md`. Interior proof avoids this pitfall through strict node separation.

### LI-CO10 — sharp small-mass first-sign boundary

**Paper result:** actual first-current even jets have uniform two-term profile `J_k(v)/(2v)=M_0−4^(k+1)M_1 v+O_C(v^(2−log₂3))` for every natural `k≤log(1/v)/(2log2)+C`. Positive actual `M_0,M_1` and uniformly bounded higher moments give first negative order `log(1/v)/(2log2)+O(1)`. Exact threshold uses existing source tangent `τ=M_1/M_0`; no signs of higher moments assumed.

**Status:** Lean-closed in `3-formalized/li-even-euler-jet-small-mass-crossover.md`. Exact source series, complete uniform remainder, literal jet profile, arbitrary-filter binary-scale limit, least negative natural index, bounded-offset law and ratio limit passed targeted builds, final exact checks and foundation-only axiom audits. Generic binary scale and weighted coefficient-ratio boundary overlap Durán, arXiv:2404.03249, Theorems 2–3, under multiplier hypotheses; actual source need not satisfy those hypotheses. No significant worldwide novelty or RH conclusion claimed.

**Continuation:** cofinal/pole/current integration is now Lean-closed. Paper normalization audit confirms that `Γ(0)=0`; coefficient `2(−1)^n(n+1)²M_n` occurs at mass power `n+1`, not `n`. The interleaved central moment germ cannot be substituted as an ordinary mass generating function. Disjoint exact mass-series and exponential-jet leaves are being implemented; root owns sharp geometric source-moment bounds and uniform remainder. No growing-order interchange accepted before a fixed-order source-jet identity passes Lean.

**Source-series checkpoint:** `LiEvenCrossEulerMassSeries.lean` and `LiEvenCrossEulerMassJetSeries.lean` passed named builds, exact final leaf audits and foundation-only axiom audits. Actual `Γ` has the canonical mass Taylor series at zero with radius at least `1/2`; every fixed real logarithmic-mass derivative has the exact source series. `LiEvenCrossEulerSmallMassRemainder.lean` passed a named build and proves complete tail bound `18A(3^k v/150)²`, a positive decay exponent, and uniform convergence over all earlier indices in each logarithmic window. Root actual two-term profile and delegated least-negative-index capstone are still being checked.

**New audited survivor:** isolating positive `M_2` gives a source-dependent vanishing displacement of the first-sign boundary. The tail beyond the third term is `O(v)` at bounded crossover offsets. Both source correction coefficients, quantified floor sandwich and arbitrary-filter variable-drift limit are Lean-closed in `3-formalized/li-even-euler-jet-source-boundary-layer.md`. All six boundary leaves passed named builds, final exact source checks and foundation-only axiom audits. No numerical experiments or RH conclusion.

**Final crossover checkpoint:** all six parent and all six boundary leaves are final-audited and wired. Exact mass transport is diagonal rescaling of every source moment and supplies no new arithmetic recurrence. Existing theta cumulant recurrence and full/cofinal Hankel endpoints already encode the remaining RH-strength cancellation; signed third-product and score-defect kernels remain concrete source material, not proofs of all-mode orientation.

### LI-CURRENT — transfer-combined source currents

Constituent-jet failure does not settle actual current signs. Lean proves a uniform positive prefix `C_n(v)/(2(n+1)²)≥(787/6552)A` whenever `v>0` and `(n+1)²v≤25`. Its final card is `3-formalized/li-actual-current-uniform-positive-window.md`. Complete-source arbitrary-filter limit in `3-formalized/li-actual-current-entire-clock-limit.md` is final: `v→0+`, `(n+1)²v→w` imply normalized literal current tends to `S(w)`, with margin `S(w)≥(1051/2184)A` on `[0,25]`.

Beyond compact clocks, `3-formalized/li-actual-clock-volterra-positive-mass.md` now closes actual raw-source `F⋆B=tB'`, divergent weighted degree and positive clock mass, cofinal positive `S` values, and positive actual-current corridors beyond every clock threshold. Seven additional leaves passed final named/direct/axiom checks and are wired. These are eventual signs along prescribed shrinking masses; all-mode signs at each fixed mass remain open. Stronger [unbounded response height](../3-formalized/li-clock-unbounded-support-response-growth.md) is now formal: every tail contains F above every fixed bound, using source growth beyond every square-root exponential. Three leaves and all 12 public axiom audits passed. Literal reciprocal sine identity, RH-conditional S decay and non-RH top-rate isolation are also formalized; signed packet asymptotics and RVM mean remain paper-only.

[Central prime–Gamma contour transport](../3-formalized/li-clock-central-prime-gamma-contour.md) now proves exact coefficient recovery and both phase-preserving source contour formulas for every real clock, with one central radius. Honest finite prime series converge only for `Re(s)>3/2`; central continuation already contains zeta log derivative. No independent signed arithmetic producer follows.

Paper obstruction in `2-fully-proven/li-mass-calibrated-score-floor-obstruction.md` retains literal `R_0` and every prescribed polynomial score floor with strict surplus while a cumulant determinant is negative. Its strongest actual first-atom envelope is formalized in two leaves with factor `110843/111104`; all 13 public declarations passed foundational axiom audits and final exact checks. Full analytic countermodel, theta source membership and actual moment sequence remain unmatched; no RH or literal-source falsification.

### Source score-gap matrix survivor

The actual raw theta score defects `D_j=(32j+17)R_j−303R_(j+1)` have a Lean-closed positive definite Hankel extension, retaining the fixed first-atom polynomial-square lower floor. `3-formalized/prime-arch-theta-polynomial-score-gap.md` records exact raw normalization, signed-square proof and generic Hermite obstruction. Named build, final exact source check and all nine capstone foundation-only axiom audits passed; root spot-check and umbrella wiring complete. Literal first-atom floors themselves are now matched by [formal dark-divisor packets](../3-formalized/theta-derivative-packet-full-score-floor.md), simultaneously for every signed polynomial square. Exact original packet properties survive at one ε. These deformations do not retain actual critical strip, half-charge or full theta/Euler membership; that membership burden remains decisive.

## No-go closure

### Cross-route hostile audit — LI / TT signed work

The literal TT/theta-Green Ward reflection already has its source-forced opposite grade. `XiHeatCassiniThetaExteriorReflectionGradeLock.lean` keeps that sign; replacing it with Wold's even sign creates the known RH-equivalent endpoint rather than a second source equation. The actual LI jet signs do not repair this grade mismatch.

A proposed new weighted-work producer was rejected as a renamed energy endpoint. Write `a_n=n^(2c)`, `d_n=R_n−R_(n−1)`, `D_c(N)=Σ(a_n−a_(n−1))R_(n−1)²`, `W_c(N)=Σa_nR_(n−1)d_n`, and `I_c(N)=Σa_nd_n²`. Exact telescoping gives

`a_NR_N²−R_1²=D_c(N)+2W_c(N)+I_c(N)`.

For strict subhalf `c`, fresh-square noise has finite total. A cofinal bound `W_c≤−(1/2+ε)D_c+C` forces finite `D_c`, but conversely finite `D_c` provides a cofinal sequence with `a_NR_N²→0`, hence the same bound. No arithmetic mechanism enters that equivalence. Positive survivor is the complete endpoint/drift/old-current/noise decomposition, retaining the endpoint. The missing source estimate remains literal signed prime-work cancellation; no receiver-only Lean module added.

No new route is retired yet. Each failed mechanism must receive a serious positive-survivor pass. Dependency-closed survivors must be formalized before a no-go is closed; otherwise record the exact remaining dependency or `NO POSITIVE SALVAGE FOUND`.

## Audit evidence and limitations

- Initial hybrid search `research 'route LI Li coefficient frontier' --no-refresh --budget-seconds 60`: no lexical matches; useful candidate declarations recovered; semantic coverage unmeasured; many source-only/stale compiler records. Source reads, not index rank, determine applicability.
- Deep search `research 'Cassini Euler defect complex support orientation' --mode deep --no-refresh --budget-seconds 60 --json`: partial; exact existing bridge/jet/resolvent candidates recovered; no proof ideas or ingredient sets returned.
- Narrow search `research 'Li radial complex pole singularity' --any --module LiEvenCross --no-refresh --budget-seconds 45 --json`: partial; existing real and complex radial definitions and no-go family recovered.
- Public searches begun for LI Cassini Euler response and generalized Nevanlinna double-pole negative squares. No novelty conclusion yet.
- Literature freshness check: [Polson, arXiv:1804.10043v9, Remark 23](https://arxiv.org/html/1804.10043v9) explicitly withdraws the earlier critical-center GGC assertion and its claimed RH consequence. The revision distinguishes its claimed unconditional self-decomposability from the RH-equivalent complete monotonicity step. This is corroborating route-boundary evidence, not a verification of every theorem in that paper or a new arithmetic producer. Existing corpus Thorin quarter-tilt obstruction remains the exact audited local failure.

## Log

- 2026-09-29 — Continuation classified as concrete progress: current bridge source found complete, named three-leaf build passed, direct pole audit passed, three original leaves wired. Strengthened LI-CO7 on paper to every positive mass; disjoint large-node and real-derivative leaves delegated. Canonical coefficient/current domains broadened; their stronger final audits remain pending. No RH proof or falsification claimed.

- 2026-09-29 — Session initialized; formal README/overview, route LI ledger and relevant memories read. Existing unrelated workspace changes retained.
- 2026-09-29 — Independent read-only corpus and public novelty audits delegated with disjoint/no-write scopes. Main thread continues source investigation independently.
- 2026-09-29 — Rejected scalar positivity and generic pole-order specialization as contribution targets. Candidate focus: coefficient-faithful complex or indefinite signature of the actual source.
- 2026-09-29 — Rejected generic finite-packet inertia and differential clock ladder after public-primary-source collisions. Retained actual complete-source balanced-index candidate and started hostile audit of the stronger all-even-Euler-jet cone.
- 2026-09-29 — Bounded audit classified full polynomial-differential balanced-index exclusion as a classical consequence; kept it out of the corpus. New LI-CO6 actual even-Euler-jet fluctuation has complete paper proof and no exact collision found. Formalization in progress; LI-CO7 queued as next conjecture.
- 2026-09-29 — LI-CO8 density strengthening has classical generic overlap and no additional cone exclusion. LI-CO9 replaced false all-mass pole retention with exact reciprocal-multiplicity cancellation; punctured-germ statement corrected for totalized source values. Root verifies first-current polynomial/moment identification in scratch while leaf implementations proceed independently.
- 2026-09-29 — Pole and coefficient leaves passed initial direct audits; source leaf strengthened to full periodic multiplicity-faithful lattices. Root first-current identification and evenization scratch passed after explicit analytic composition repair. Final bridge audit, umbrella wiring, axiom check and lint still pending. LI-CO10 sharp source-dependent first-sign boundary paper proved; no Lean or worldwide novelty completion claimed.


[Paired eta central arithmetic](../3-formalized/li-clock-paired-eta-central-source.md) now formally supplies the full-disk denominator floor, complete finite quotient error and exact complex-clock approximation. Literal finite responses converge on logarithmically growing windows and preserve arbitrary fixed positive fractions of actual qAt margin on0<t≤20, including normalized convergence down to zero. Eleven leaves/63 public declarations passed named/final and foundational axiom checks; global lint remains red on15 unrelated reachability errors. Growing-window sign is open. Two source survivors are now final: [off-line negative response and window-sign receiver](../3-formalized/li-clock-off-line-negative-response.md) (four leaves/17 public declarations) and [finite eta deflation/cancellation](../3-formalized/li-clock-finite-eta-deflation.md) (one leaf/12). Under not-RH, actual response tends to minus infinity along cofinal clocks; eventual actual nonnegativity, and the explicit growing finite-prefix sign premise, each imply RH. Exact deflation retains calibrated positive compensation on clocks up to20. Named, final exact and all-public foundational axiom audits passed; latest index gate passed; whole-tree lint remains red on19 unrelated unreachable modules, with no proof-debt errors. Growing arithmetic window sign remains open; no converse or RH proof.

[Full-copy damped signed areas and finite eta cancellation](../3-formalized/li-clock-damped-endpoint-sum-rule.md) are final (four leaves/35 public declarations): literal transform p>1/300, positive absolutely summable resolvent p>0, source-defined growing finite-window area limit and eventual positive area, explicit approximation-plus-tail bound, all-p finite pole renormalization and exact p=2 centered arithmetic intercept. Every named/final source check and foundational axiom audit passed; independent reviews checked every public declaration and proof. These signed aggregates do not close growing-window pointwise cancellation. Main source candidate remains open; no RH proof or route retirement.

2026-09-30 02:29 UTC: damped signed-area closure index PASS; global lint has23 unrelated reachability errors and no proof debt. New four leaves reachable; pointwise source sign remains OPEN.


[Short-prefix pole asymptotics and positive deflated survivor](../3-formalized/li-clock-short-prefix-pole-asymptotic.md) are final: three leaves/37 public declarations. Every actual fixed N>0 with log(2N)<2pi and every0<r<1/2 has complex exp(-2t)F_N->-1 and real F_N->minus infinity. The first literal deflated clock has exact positive second-pole term(2/5)sinh(2t/5), complete complex radius-three remainder bound, complex exp(-(2/5)t)Fdef_1->1/5, and real escape to plus infinity; its positive tail remains below the removed2sinh(2t) pole. Named/final/all-public foundational axiom and independent proof audits PASS. This excludes generic all-clock positivity from finite Laplace positivity plus completion; it does not falsify the eventual-N growing-window candidate. The stronger [exact first-prefix Gamma clock/global signs](../3-formalized/li-clock-first-prefix-gamma-exact-sign.md) is final in two leaves/55 public declarations, with complete paper/source and named/direct/all-public foundational axiom audits PASS. No route retired; RH remains open.

2026-09-30 03:33 UTC: short-prefix closure index PASS (1 changed,0 removed). Scoped diff check PASS; all three new leaves reachable. Global formal lint currently has17 unrelated umbrella-reachability errors and no proof-debt errors; concurrent external lanes changed the earlier23-error inventory. Logs `/tmp/hgt-li-short-prefix-index.log`, `/tmp/hgt-li-short-prefix-lint.log`. No unrelated files repaired.


[Positive full Gamma/dyadic completion clock](../3-formalized/li-clock-positive-gamma-dyadic-completion.md) is final: two leaves/62 public declarations. For every regular0<r<1/2, its literal all-complex contour equals the complete Gamma/nonzero-dyadic hyperbolic kernel, both families absolutely and locally uniformly convergent. All odd moment coefficients are real and quantitatively positive; for realt>0 the actual completion clock is at least(2/5)sinh(2t/5)-(3/8)sinh(t/8), hence at least181/640*sinh(2t/5)>0, and is real. Exact finite decomposition retains the removed2sinh(2t) pole and the signed partition clock under circle-only eta nonvanishing. Named/final/all62 public foundational axiom and complete independent source audits PASS. Growing arithmetic pointwise compensation remains OPEN; no RH proof/falsification or route retirement.

2026-09-30 04:20 UTC — Positive completion closure index PASS (15 changed,0 removed); scoped diff PASS. Global lint reports11 unrelated unreachable modules and one unrelated `sorry` at `DeBruijnStrictLaguerre.lean:152` (`sq_norm_riemannHeat_vertical_ge`); both completion leaves reachable, own closure free of proof debt. Logs `/tmp/hgt-li-positive-completion-index.log`, `/tmp/hgt-li-positive-completion-lint.log`. No unrelated repairs.

[Exact first-prefix Gamma clock and global signs](../3-formalized/li-clock-first-prefix-gamma-exact-sign.md) are final: two leaves/55 public declarations. Every0<r<1/2 and every complex clock have literal Fdef_1=sum_n sinh(t/(2n+5/2))/(2n+5/2) and F_1=-2sinh(2t)+Fdef_1. Actual ratio trace is even and its entire clock vanishes, with all source constants retained. Exact square mass0<S<9/25 gives sharp full-complex(5S/2)sinh(2|t|/5) envelope; every realt>0 has strict first-atom/positive deflation, both sharp mass fences, and F_1<-(91/50)sinh(2t)<0. Genuine zero derivative S and right-punctured slope force both optimal coefficients. Named/final/all55 public foundational axiom and complete independent proof audits PASS. This classifies first prefix only; eventual-N growing arithmetic sign and RH remain OPEN, no route retired.

2026-09-30 04:41 UTC — New [completion/arithmetic cancellation boundary](../3-formalized/li-clock-completion-arithmetic-cancellation-boundary.md) is in paper audit. Actual finite source is a union of odd-even log intervals; replacing it by a contiguous interval discards signed gaps. Existing full-clock rate≤t*exp(t/300) versus completion rateexp(2t/5) exposes necessary nearly exact negative arithmetic cancellation; fixed-fraction completion floors are being audited as a no-go, with the strongest normalized source decomposition required before retirement. Main eventual-N pointwise sign is unchanged and OPEN.

2026-09-30 04:45 UTC — Final first-prefix closure index PASS (0 changed,0 removed after managed research refresh), `/tmp/hgt-li-first-prefix-gamma-final-index.log`; tracked scoped diff and both untracked new-file no-index checks have empty diagnostics. Global lint currently reports11 unrelated umbrella-reachability errors and NO proof-debt error; external `DeBruijnStrictLaguerre` debt from prior snapshot is no longer reported, while `WeilShiftPairLandau` is now unreachable. Both new first-prefix leaves are reachable; own closure is proof-debt free. Full current errors: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, WeilShiftPairLandau, ZetaZeroDensityPowerSaving. Log `/tmp/hgt-li-first-prefix-gamma-final-lint.log`; no unrelated file repaired.

2026-09-30 06:16 UTC — [Literal completion/arithmetic cancellation boundary](../3-formalized/li-clock-completion-arithmetic-cancellation-boundary.md) FINAL: three leaves52publics, every proof component independently audited, named/exact-direct/all-public foundational checks passed. Exact finite source F_N=C-K_N+H_N, actual eta scaledlimit-1/5 and ratio-1, and ANYc>0/theta<1 finite eta/gap fractional-floor obstruction are formalized. Closureindex passed; global lint10unrelatedunreachable modules, no proof-debt errors. Actual required ReH_N>=K_N-C and growing finite pointwise sign remain OPEN. Joint moving-clock cancellation requires0<c<r/4 and is tracked separately.

2026-09-30 06:35 UTC — [Actual finite-partition Volterra survivor](../3-formalized/li-clock-finite-partition-volterra-positive-area.md) FINAL: full double half-tilt and all even moments, exact factor-two convolution, unbounded positive-part area, cofinal positive clocks, and unconditional regular-radius existence. All40 public declarations pass exact named/direct/foundational axiom checks; every proof independently audited. Moving model helper also FINAL (one public theorem). Index PASS; global lint12 unrelated unreachable modules, no proof-debt errors. No actual pointwise completion compensation or RH sign follows.

2026-09-30 06:48 UTC — [Joint moving-window arithmetic cancellation](../3-formalized/li-clock-joint-arithmetic-cancellation-window.md) FINAL: one common radius, two new leaves/two public declarations, eight actual finite-source limits; named/direct/all-public foundational checks and full independent proof audits PASS. Both finite eta/gap scaled limits are-1/5, completion ratios-1, real parts tend minus infinity; completed finite clocks have normalized limit0. Exact window0<c<r/4 preserved. Index PASS; global lint13 unrelated unreachable modules, no proof-debt errors. New [density-ratio/endpoint boundary](../3-formalized/li-clock-partition-density-ratio-endpoint-boundary.md) enters paper audit; no actual residual sign or RH conclusion.

2026-09-30 07:16 UTC — [Complete contiguous comparison survivor](../3-formalized/li-clock-contiguous-comparison-window.md) FINAL: Source20+Comparison44 public declarations, every original paper target formalized, full root/producer proof audits and named/direct/all-public foundational checks PASS. Entire filled U, full k0 lattice and exponential packets, all absolute/local-uniform exchanges, exact radial O bound, strict real K positivity and eventual completed MODEL positivity for0<c<1/16 are closed. Index PASS; global lint10 unrelated unreachable modules, no proof-debt errors. [Actual density-ratio/endpoint boundary](../3-formalized/li-clock-partition-density-ratio-endpoint-boundary.md) now paper-PASS/Stage2 with sharp moment/Borel survivor and both radial a.e monotonicity obstructions; disjoint Lean scopes released. Actual residual sign and RH remain OPEN.

2026-09-30 08:21 UTC — [Generic complete Borel-ratio transfer](../3-formalized/li-clock-positive-borel-ratio-transfer.md) FINAL/Stage3:283 lines,11 public declarations, full independent proof audit and named/direct/all-public foundational certificates PASS. [Actual endpoint boundary](../3-formalized/li-clock-partition-density-ratio-endpoint-boundary.md) now has FINAL reference measure600/54, preserving the whole actual interval union and both tilt normalizers; sharp endpoint/density consumers remain in formal work. Both new leaves wired; index PASS, global lint11 unrelated unreachable modules/no proof-debt errors. [Infinite-source density-tail boundary](../3-formalized/li-clock-infinite-partition-density-tail-boundary.md) begins prior-research/paper audit to test limit-order effects; no new Lean or sign conclusion authorized. Actual residual Re(C-K+H)>=0 and RH remain OPEN.

2026-09-30 09:12 UTC — [Infinite-source density-tail and limit-order boundary](../3-formalized/li-clock-infinite-partition-density-tail-boundary.md) paper-PASS/Stage2: ALL508+84 proof lines/source and prior-overlap audited. Sharp periodic correction, lambda<1, every normalized moment/full Borel term, growing complex disks c<1/16, exact spatial bulk and both noncommuting limits closed on paper. Fixed-N ratios approach kappa>1; source-first and growing-window ratios approach lambda<1. Formalization pending; no inverse forcing/clock sign or RH conclusion. Exact compensation residual remains OPEN.

2026-09-30 09:23 UTC — [Actual density/source/classification and sharp fixed-prefix endpoint comparison](../3-formalized/li-clock-partition-density-ratio-endpoint-boundary.md) FINAL/Stage3: Density1463/83public and Endpoint1217/33public, ALL proofs independently/root audited; exact named/direct/116public foundational certificates PASS. Canonical full/radial sources, both a.e. radial order obstructions, N1 exception, signed four-coordinate forcing, sharp all-order/full Borel limits and both divergent gaps retained. Both unique imports wired; index PASS, global lint14 unrelated unreachable modules/no owned/proof-debt error. Relative central-clock expansion remains separate Stage2; infinite592-target paper-PASS formalization pending. No uniformN inverse-sign or RH claim; actual compensation residual remains OPEN.
