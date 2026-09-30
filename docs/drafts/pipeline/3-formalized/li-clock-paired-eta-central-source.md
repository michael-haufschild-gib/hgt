# Paired integer arithmetic realizes the complete central clock

- **ID:** LI-CLOCK-PAIRED-ETA-CENTRAL-SOURCE
- **Stage:** 3-formalized; exact central source and quantitative finite-clock transport checked
- **Type:** THEOREM (Lean 4); exact source, sharp finite approximation and normalized positive-window survivor
- **Parent:** [central prime–Gamma contour](../3-formalized/li-clock-central-prime-gamma-contour.md)

## Exact central arithmetic source

Let `E(s)=Σ_n[(2n+1)^(−s)−(2n+2)^(−s)]` and `d(s)=1−2·2^(−s)`. For `s=1/2+iz`, put

`T_eta(z)=i[E'(s)/E(s)−2log2·2^(−s)/d(s)+1/s+1/(s−1)+γ_R(s)]`.

The formal source identity is `T_eta=T` on one full central complex disk, where T is the literal inverse-tilted prime–Gamma trace. This uses convergent paired integer sums at center, rather than treating continued zeta logarithmic derivative as an uncontrolled input. Local eta–zeta factorization identifies the source; no RH premise or global divisor holomorphy is needed.

Existing corpus gives pair, derivative and finite quotient convergence throughout the positive half-plane away from E zeros. Exact completed contour therefore preserves every clock coefficient and all analytic multiplicities. This is integer arithmetic, not an ordinary convergent prime series.

## Literal tail bounds

Each pair has exact integral `E_n(s)=s∫_[2n+1,2n+2] x^(−s−1)dx`. For `Re(s)≥σ>0`, `|s|≤R`, a=2N+1 and finite sum E_N, disjoint intervals give

`|E−E_N|≤(R/σ)a^(−σ)`,

`|E'−E_N'|≤a^(−σ)[1/σ+R(log(a)/σ+1/σ²)]`.

Paper analytic envelope: every fixed derivative order k≥1 has tail bounded by

`∫_a^∞ [R(logx)^k+k(logx)^(k−1)]x^(−σ−1)dx`.

The new formal tail leaf certifies the exact value and first-derivative inequalities above. Higher-order integral envelope here is explanatory paper context; existing fixed-order differentiated convergence is reused. Full-half-plane factorization E=d·ζ and d≠0 for Re(s)<1 give the logarithmic quotient identity wherever E≠0. Existing derivative wrapper assumes Re(s)>1/2; new source leaf proves the exact `0<Re(s)<1` wrapper required on a central circle.

## Formal central denominator floor

`|s−1/2|≤1/128 ⇒ Re E(s)>1/8`.

At the real center all pairs are positive, so `E(1/2)≥1−2^(−1/2)>1/4`. On the larger box `Re(s)≥1/4`, `|s|≤3/4`, pair integrals give

`|E'(s)|≤∫_1^∞(1+(3/4)logx)x^(−5/4)dx=16`.

A complex segment inside that box loses at most 16/128=1/8. This proves source nonvanishing on the full small disk without importing an RH-equivalent half-plane criterion.

## Formal finite arithmetic clock approximation

Set `δ0=3a^(−1/4)`, `δ1=(16+3log a)a^(−1/4)`. Once δ0≤1/16, finite denominators satisfy `Re E_N>1/16` and

`|E_N'/E_N−E'/E|≤16δ1+2048δ0`.

Replace only eta quotient in T_eta by its finite quotient, yielding T_N. Define the complete complex response `F_C(t)=Σ_j(−1)^j(M_j:ℂ)t^(2j+1)/(2j+1)!`, whose restriction to real clocks is the complexification of literal F. For a fixed positive circle r≤1/128 inside the actual contour radius, use exact trace contour to define complex F_N. For every complex clock bound L≥0,

`sup_(|t|≤L)|F_N(t)−F_C(t)|≤(16δ1+2048δ0)sinh(L/r)≤(16δ1+2048δ0)exp(L/r)`.

Finite T_N generally has nonzero center value and need not satisfy functional-equation symmetry. Use filled divided difference for germ transport; do not assume T_N(0)=0. Additional audited reflection `T_N(−conj z)=−conj(T_N(z))` proves odd Taylor coefficients real and therefore F_N real at real clocks. This reflection is weaker than oddness and supplies no sign law. The extra constant contributes zero to the trace contour since sin(t/z)/z has no z^(−1) term.

## Prior source and novelty audit

Root checked `ZetaRealStrip.lean:38,42,267`, exact eta–zeta factorization on Re(s)>0 away from1; `RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation.lean:149,183`, locally uniform derivatives and finite quotients; and `...EtaDerivative.lean:193,223`, restricted wrapper and its proof. Producer also inspected actual positive logarithmic-interval Laplace measure and fixed all-order log moments. Convergence mechanisms preexist. Corpus audit must compare finite Rouche, leading-coefficient enclosures and local eta contour modules before any local novelty claim.

Documented deep research query `alternating Dirichlet eta paired integer series locally uniform derivatives real part positive riemann zeta` completed at generation/current1145443, complete63096-file inventory, source-only candidates, unmeasured semantic coverage and mostly pending/stale compiler evidence. Tool transcript session4845, finalchunk94929f; no saved output file. No world-novelty claim.

## Plan and limits

1. Independent hostile paper audit PASS: source signs/domain, complete derivative tails, disk floor, finite denominator/quotient estimate and sharp contour error.
2. Check overlap with all relevant inspected corpus survivors; use existing exact APIs where applicable.
3. Formalize only dependency-closed new exact clauses in disjoint leaves after audit; no numerical experiments.
4. Investigate independent signed cancellation in the completed oscillatory clock. Local real-pair positivity does not prove all-clock sign or RH.

No route retired. This closes a local arithmetic representation burden, not a source-tested all-clock orientation estimate or RH proof.

## Log

- 2026-09-30 — Candidate recorded before Lean work. Existing paired eta and finite quotients cross center unconditionally. Proposed source-only full-disk floor and quantitative contour approximation are paper-closed by producer; independent audit pending. Root verified source APIs and identified restricted-half-strip wrapper requiring exact weakening.

- 2026-09-30 — Independent audit confirms signs, full-center domain and numerical constants; sharper complex-clock error uses sinh(L/r), with no extra factor two. Existing `DQPTEtaDeriv.lean:390` already proves the derivative box bound via `dqpt_norm_etaPairDeriv_le`; `DQPTEtaBound.lean:146` already bounds eta value. Reuse these existing survivors. Complete independent proof/overlap audit still pending; no new Lean source yet.

- 2026-09-30 — Full independent paper audit PASS, including stronger real-clock finite-source reflection and sharp sinh contour bound. Root checked quotient algebra, a=2N+1, δ0/δ1 constants and exact contour cancellation. Promoted to stage two. Existing derivative envelope and local uniform quotient machinery will be reused; source sign remains open.

## Independently audited growing-window survivor

Exact tail bound simplifies to `B_N=(6400+48log a)a^(−1/4)`. For fixed r>0 and `0<c<r/4`, the quantitative bound suggests

`sup_(|t|≤c log a)|F_N(t)−F_C(t)|→0` as N→∞.

Indeed exponential factor is `a^(c/r)`, leaving a logarithm times negative power. Independent paper audit PASS: with epsilon=1/4-c/r>0, the error is at most `(6400+48log a)a^(−epsilon)→0`, and the finite denominator condition holds eventually. Exact literal growing-window convergence is formal in `exists_liClockPairedEtaFiniteClockResponse_uniform_windows`. Cofinal oscillation at uncontrolled clocks cannot be passed through compact approximation.

## Disjoint formal plan

1. `LiClockPairedEtaCentralDisk.lean`: exact source-only ReE>1/8 on closed disk1/128, reusing existing derivative bound.
2. `LiEvenCrossActualClockPairedEtaSource.lean`: domain-weakened eta logarithmic quotient and exact literal central source reconstruction; use `0<Re(s)<1`, E≠0 rather than a right-half-strip assumption.
3. Root-owned `LiClockCentralSineContourStability.lean` supplies generic exact trace-contour error; exact tails, finite quotient error, complex clock extension and actual `LiEvenCrossActualClockPairedEtaContour.lean` follow stable source APIs. Preserve every term and all phases.
4. Named builds, final exact checks, public axiom audits and authoritative gate; promote only exact completed clauses.

- 2026-09-30 — Six-module corpus audit confirms existing qualitative finite nonvanishing, fixed-order log-moment enclosures and moving-height residual bounds. None of those inspected capstones states this exact literal central floor/clock transfer; no broader novelty claim. Independent source audit confirms growing-window error tends to zero for c<r/4. Existing finite energy/flux reads the completed source at zero-based coordinates and high-order moments; a signed inequality for its central logarithmic derivative remains absent.

## Formal normalized finite-prefix positive survivor

The literal actual source already proves `S(w)≥qA` on `0≤w≤25`, with `q=1051/2184` and `A=xiShiftAbsoluteMass 0>0`. Hence `F(t)≥qAt` on `0≤t≤20`. For a fixed `0<r≤1/128`, sharp transport gives

`|F_N(t)−F(t)|≤B_N sinh(t/r)≤[B_N cosh(20/r)/r]t`.

Since `B_N→0`, eventually every N satisfies `Re F_N(t)≥qAt/2>0` uniformly for `0<t≤20`. Reflection also makes F_N real. Independent hostile proof/overlap audit PASS. Radius must also lie inside the exact actual-contour radius unless full eta-source disk analyticity is separately proved. This gives no growing-window positivity. Existing energy/flux signs do not control the central logarithmic derivative.

- 2026-09-30 — Final formal clauses: five public central-disk APIs in `LiClockPairedEtaCentralDisk.lean`, five public full-strip source APIs in `LiEvenCrossActualClockPairedEtaSource.lean`. Named builds and exact final checks exit0; all public declarations use only `[propext, Classical.choice, Quot.sound]`. Root checked disk statement/proof and source quotient signs and domain. Generic sharp contour stability passed complete scratch Lean; literal tails and quotient stability have disjoint implementation owners. Whole quantitative card remains stage two.
- 2026-09-30 — Producer audited completed finite-source overlap with four energy/flux modules plus finite arithmetic flux. No direct signed central-clock estimate follows: flux evaluates zero-based completed finite values/moments, retains cosine and distinct-zero cancellation, and its sign receiver is explicitly RH-equivalent. Deep search completed68.21s with complete63102-file inventory, generation1145742/current1145743, source-only candidates and unmeasured semantic coverage; lexical follow-up found17 declarations in5 modules. Transcript session4294/finalchunk46487b; no broader absence or novelty claim.

- 2026-09-30 — Generic `LiClockCentralSineContourStability.lean` final: two public APIs, named build2714jobs exit0, exact direct check exit0 with empty diagnostics, both public axiom audits foundational. Root wired this and the two final eta-source leaves. Independent finite-window audit exposes stronger normalized convergence: `sup_(0<t≤20)|F_N(t)/t−S(t²/16)|≤B_N cosh(20/r)/r→0`, hence any fixed fraction theta∈(0,1) of qAt holds eventually. Correct finite raw-derivative expansion has squared odd factorial denominator; constant/even trace coefficients vanish without finite oddness or finite functional equation. Source reflection/continuity, exact arithmetic tails and quotient stability have disjoint owners; root owns literal complex clock and eta contour transfer. Quantitative clauses remain unformalized until their exact Lean checks pass.

- 2026-09-30 — Root prepares generic weighted clock-error/fraction-margin transfer in separate scratch before finite arithmetic integration. Independent audit already covers exact statement: sinh(t/r)≤cosh(20/r)t/r and any fixed positive fraction of actual qAt margin. Public source-tail leaf will expose derivative16 and exact δ0/δ1 specializations; generic quotient leaf three public APIs is final and root checked algebra and all proof logs. Growing-window envelope limits have disjoint implementation owner.

- 2026-09-30 — Root literal complex response and paired eta contour: complete scratch exit0, named leaf12947jobs own45s exit0, final exact source exit0 with empty diagnostics. Seven public APIs including complex coefficient/response definitions, absolute summability, exact real restriction, pointwise closed-disk source reconstruction, and one central arithmetic contour radius. Radius is explicitly≤1/128 and inside actual analytic germ. Public axiom audit pending. Root read all182lines of ArithmeticTail leaf and checked exact shift n+N and all central constants; named build passes, final audits pending.

- 2026-09-30 — Seven complex-clock/actual eta-contour public axiom audits exit0, all foundational; final leaf is wired. Logs `/tmp/hgt-li-clock-paired-eta-contour-{build,direct,axioms}.log`. Exact arithmetic source contour is now formal, while finite quantitative transport/growing-window/normalized positivity clauses remain in progress.

- 2026-09-30 — Exact ArithmeticTail five public APIs are final/wired: named build12919jobs own9.6s exit0, final exact empty diagnostics, all5publicaxes foundational; root checked full182line proof. Root prepares generic weighted positive-margin transfer in `/tmp`; independent audit covers statement. Generic trace sine-series/reflection leaf has disjoint owner: arbitrary nonzero center allowed, odd raw derivatives divided by squared odd factorials, anti-Schwarz gives real response. This completes a missing finite-source interface without imposing finite functional equation.

- 2026-09-30 — GrowingWindow seven public declarations final/wired: exact B_N definition/nonnegativity, B_N→0, eventual denominator threshold, exact growing exponential-to-negative-power identity and exponential/sinh envelope decay. Named build2205jobs own2.1s exit0; final exact empty; all public axioms foundational. Root read full leaf and checked exponent epsilon=1/4−c/r>0. Generic fraction-margin transfer scratch passed analytic envelope/MVT clauses; one association rewrite is under correction. Literal source-error integration is drafted, retaining full finite completion and explicit denominator condition.

- 2026-09-30 — Root reserves `LiEvenCrossActualClockPairedEtaApproximation.lean` for literal finite clock definition, finite real-part denominator floor, exact completed source difference≤B_N, and all-complex-clock sinh error on one actual radius. Root reserves `LiClockWeightedResponseStability.lean` for generic linear envelope/fraction-margin transfer. Growing limits are already formal in separate stable leaf; window convergence and normalized positive finite response will integrate those exact APIs. No source parity or finite functional equation is assumed.

- 2026-09-30 — Final/wired FiniteSource13 public declarations (including analyticAt full-strip/norm wrappers and DiffContOnCl on finite-zero-free disk), TraceSineReflection6 declarations (squared odd factorial series and real-clock output), WeightedResponseStability4 declarations (linear sinh envelope, actual qAt margin, generic fraction and strict positivity). Named builds, final exact sources and every public axiom audit exit0; sources have empty exact diagnostics, only foundational axioms. Root checked finite analytic proof/source completion, generic odd derivative conjugation and weighted proof. Exact literal instantiation is in first scratch validation: growing complex-window convergence, finite response reality, uniform normalized convergence down to zero, and eventual arbitrary positive fraction on0<t≤20. Whole card remains stage two until that check/build/final audit passes.

- 2026-09-30 — Complete literal Approximation scratch exit0/empty diagnostics, independent hostile mathematical/interface review PASS for all six public clauses. Includes actual finite response definition, strict finite real-part denominator floor, real output at real clocks, exact completed source error≤B_N, one all-complex-clock error radius, and full joint growing-window/arbitrary-positive-fraction/uniform-normalized convergence theorem. Source leaves and all phases retained; normalized quotient excludes t=0. Named build, final source and all public axiom audits now pending before promotion.

- 2026-09-30 — Literal Approximation six public declarations final/wired: named build12965jobs own15s exit0; exact direct exit0/empty; all6public axiom audits foundational. Root independent interface review PASS and fullscratchpassed. Logs `/tmp/hgt-li-clock-paired-eta-approx-{work,build,direct,axioms}.log`. Across eleven new eta/contour/transfer leaves,63 public declarations are individually checked; authoritative global index/lint gate remains pending. No growing-window positivity or all-clock source sign claim.

## Exact formal coverage

Eleven final leaves expose63 checked public declarations: central arithmetic disk5; full-strip complete source5; generic contour stability2; literal complex response/eta contour7; sharp arithmetic tails5; generic quotient stability3; growing envelopes7; full finite completed source13; raw trace series/reflection6; weighted positive-margin stability4; exact literal finite approximation6. Every leaf passed named build, final exact source and all public axiom audits with only `[propext, Classical.choice, Quot.sound]`.

The joint actual theorem proves uniform complex-clock convergence for `|t|≤c log(2N+1)` with `0<c<r/4`, uniform normalized convergence on `0<t≤20`, and eventual preservation of any fixed positive fraction theta∈(0,1) of actual qAt margin. It does not prove growing-window positivity. Higher-order explanatory tail integral and a separate formal entire-function theorem are not added by these leaves.

- 2026-09-30 — Authoritative index exit0; API/GAPS/OVERVIEW refreshed. Lint exit1 with15 unreachable-module errors, all outside these eleven eta/contour leaves, and no proof-debt errors. Global gate remains red; independent local leaf checks and all63 public axiom audits passed. Logs `/tmp/hgt-li-central-eta-{index,lint}.log`. Promoted exact completed clauses to stage three; growing-window source sign stays open in separate stage-one card.
