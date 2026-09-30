# Signed finite-eta orientation on a growing clock window

- **ID:** LI-CLOCK-FINITE-ETA-ORIENTATION-WINDOW
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; conditional-strength and artificial-pole audit
- **Source:** [paired eta central source](../3-formalized/li-clock-paired-eta-central-source.md)
- **Statement:** For one fixed admissible central contour radius r, seek a fixed 0<c<r/4 such that every sufficiently long finite eta prefix has Re F_N(t)>=0 for every 0<t<=c log(2N+1).

## Goal and exact observable

Let a_N=2N+1, E_N(s)=sum_(n<N)[(2n+1)^(-s)-(2n+2)^(-s)], d(s)=1-2*2^(-s), C(s)=s(1-s)Gamma_R(s)/d(s), and H_N=C*E_N. In the central coordinate s=1/2+iz, retain the full trace

T_N(z)=i[E_N'(s)/E_N(s)-d'(s)/d(s)+1/s+1/(s-1)+gamma_R(s)].

Define F_N(t) by the installed negative trace sine contour on |z|=r. Choose 0<r<r0, where r0 is supplied by `exists_liClockPairedEtaFiniteClockResponse_error_radius`; in particular r<=1/128. The finite denominator condition holds eventually. Anti-Schwarz reflection retains the finite real-clock phase without assuming a finite functional equation.

The candidate is a new signed source burden. Existing energy/flux inequalities evaluate completed finite values or cutoff-centered moments at zeta zeros and do not establish this central quotient sign.

## Gates

- [x] 0 -> 1: literal observable, admissible domain, existing exact approximation, bounded corpus audit initiated.
- [ ] 1 -> 2: independent arithmetic proof or falsification of the growing-window sign.
- [ ] 2 -> 3: only paper-closed source clauses may be formalized.

## Existing positive survivor and strength questions

`LiClockPairedEtaGrowingWindow.lean` defines B_N=(6400+48 log a_N)*a_N^(-1/4), proves B_N>=0 and B_N->0, and proves B_N*exp(c log a_N/r)->0 and its sharper sinh analogue for 0<c<r/4. The exact central approximation therefore converges uniformly on these growing windows.

Consequently the proposed eventual sign implies actual F(t)>=0 for every fixed t>0: eventually t lies in the window and F_N(t)->F(t). No equivalence with RH is asserted. Inspect the exact actual-clock receivers before drawing further consequences.

Existing actual-clock source margin gives F(t)>=(1051/2184)*A*t for 0<=t<=20, A=xiShiftAbsoluteMass(0)>0. Together with the sharp sinh error this yields an eventual finite-prefix margin on that fixed interval. This does not establish sign on a growing interval.

## Conditional strength: audited formal receiver

Put W_N=c log a_N and epsilon_N=B_N sinh(W_N/r). The installed growing-envelope theorem gives epsilon_N->0. For each fixed t>0, eventually t<=W_N; therefore the candidate implies F(t)>=0. The converse is not furnished by approximation: F>=0 gives only Re F_N>=-epsilon_N on the window. Exact finite signs require a positive margin or an independent signed source inequality.

The independently audited formal consequence is eventual actual F>=0 => RH. `LiEvenCrossActualClockNegativeResponse.lean` proves the stronger not-RH cofinal response to minus infinity. `LiEvenCrossActualClockPairedEtaWindowReceiver.lean` passes the explicit eventual finite-prefix sign to all actual clocks t>=0 and RH, with one exact approximation radius and any c>0. All final checks and public foundational axiom audits passed. This is a one-way receiver; no equivalence is asserted. Under not-RH, `exists_liEvenCrossActualClockTopPacket_of_not_rh` (`LiEvenCrossActualClockTopFrequency.lean:142`) supplies b>0, a nonempty finite maximal packet Q of the complete multiplicity-copy frequencies w_q=(xiSpectralPoint q)^(-1), and a strict complementary rate b_2<b. For w_q=a_q+/-ib in Q,

`exp(-bt) Re(w_q sin(tw_q)) - (a_q sin(a_q t)-b cos(a_q t))/2 -> 0`.

There exist cofinal positive t_l with exp(i a_q t_l)->1 simultaneously for all q in Q. To see this without rational-independence assumptions, take a convergent subsequence of the integer orbit in the finite compact torus, thin it to increasingly large consecutive integer gaps, then take those gaps. The normalized top sum consequently tends to -b*|Q|/2<0. For the complementary copies, the integral formula for sine gives

`sum_(q notin Q) |w_q sin(tw_q)| <= t exp(b_2 t) sum_q |w_q|^2`.

The last sum is finite by the existing complete `xiSpectralPoint_inv_sq_summable`; after division by exp(bt), the remainder tends to zero. `LiEvenCrossActualClockSineSource.lean:125,141` identifies the entire literal F with this full sine trace. Thus not-RH gives negative F cofinally. This proves the stated implication on paper while preserving every analytic multiplicity copy. All required components are now formal: installed finite-torus recurrence, `LiClockFiniteTopSinePacket.lean`, `LiClockSineImaginaryEnvelope.lean` and literal `LiEvenCrossActualClockNegativeResponse.lean`. `LiEvenCrossActualClockSineDecay.lean:61,80` proves only RH-conditional decay, not RH=>F>=0. The proposed growing-window sign is therefore at least RH-strength; its reverse implication is unaudited and is not used.

## Exact finite deflation and calibrated cancellation: Lean-closed

Independent paper audit PASS; `LiClockPairedEtaFiniteDeflation.lean` now formally proves the regular-strip source identity, exact all-complex contour split and calibrated compensation. Its 12 public declarations passed named, final exact and foundational axiom checks. The following filled endpoint interpretation at s=0 remains paper-only. The existing exact identity `pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition` (`RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaFiniteLaplacePartition.lean:98`) is

`E_N(s)=s L_N(s)`,

where L_N(s) is the sum of integrals exp(-su) over the positive logarithmic intervals [log(2n+1),log(2n+2)]. For N>=1, L_N(0)=sum log((2n+2)/(2n+1))>0, so E_N has a simple zero at zero.

The independent paper pole audit passes the following precise point-value correction. Set

`Ctilde(s)=2 pi (1-s) Gamma_R(s+2)/d(s)`.

Installed `GaloisForLFunctions.gammaReal_shift_two` (`ArchimedeanGamma.lean:29`) states `Gamma_R(s+2)=[s/(2 pi)] Gamma_R(s)` for s!=0. Thus C=Ctilde on a punctured neighborhood of zero. Since Gamma_R(2)=1/pi and d(0)=-1, Ctilde(0)=-2; Ctilde is analytic and nonzero near zero. The literal totalized factor instead has C(0)=0. Nevertheless the literal product H_N=C*E_N agrees near zero with `s*Ctilde(s)*L_N(s)`, including at zero because both products vanish there. Therefore H_N itself is analytic at zero and has the simple-zero derivative `H_N'(0)=-2 L_N(0)!=0` for N>=1. This is stronger than an assertion only about an unnamed meromorphic extension. `Complex.Gammaℝ_residue_zero` (`Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean:95`) independently confirms residue 2. This endpoint interpretation is paper-audited; the formal deflation leaf uses literal C*L_N only in the regular strip and does not formalize this endpoint extension.

Define the regular deflation near zero by `Hhat_N=Ctilde*L_N`. On every regular admissible central circle it equals C*L_N=H_N/s, and set Tdef_N(z)=i Hhat_N'(s)/Hhat_N(s). At zero the regular deflation has Hhat_N(0)=-2 L_N(0), whereas the totalized pointwise quotient H_N(0)/0 is zero; those point values are not identified. The installed finite completion/logarithmic-derivative identity (`LiClockPairedEtaFiniteSource.lean:103`) and the finite Laplace identity give

`T_N(z)=i/s+Tdef_N(z)=1/(z-i/2)+Tdef_N(z)`.

Let Fdef_N be the same negative trace sine contour of Tdef_N. For r<1/2, the geometric series of 1/(z-i/2) converges uniformly on the contour. Extracting its odd coefficients gives exactly

`-(1/(2 pi i)) integral_(|z|=r) [1/(z-i/2)] sin(t/z) dz/z = -2 sinh(2t)`.

Consequently, for all complex clocks and every regular finite contour,

`F_N(t)=-2 sinh(2t)+Fdef_N(t)`.

This proof uses local finite algebra and one uniformly convergent geometric series; it needs no global divisor representation, RH, finite functional equation or sign premise. On quantitatively valid central circles, finite real-clock reality follows anti-Schwarz reflection (`LiClockPairedEtaFiniteSource.lean:89`); deflated reality follows the exact split. Oddness is not assumed.

The paper-closed fixed-window fraction margin therefore forces, for any fixed theta in (0,1), eventually uniformly on 0<t<=20,

`Fdef_N(t)>=2 sinh(2t)+theta*(1051/2184)*A*t`,

where A=xiShiftAbsoluteMass(0)>0. This is a nontrivial exact source cancellation statement. More generally, if actual F>=0, approximation forces `Fdef_N(t)>=2 sinh(2t)-epsilon_N` uniformly on the growing window. Deflation changes the observable; its positivity alone is not the desired inequality. The missing independent arithmetic estimate is precisely Fdef_N(t)>=2 sinh(2t) throughout the growing window, with an appropriate positive margin wherever one is claimed.

Formal-wrapper context: all eleven central-eta leaves/63 public declarations passed final named, exact-source and foundational axiom checks. Exact complete finite error, growing complex windows, fixed positive fraction margins and normalized convergence down to zero are final. The four negative-response/window-receiver leaves add17 final public declarations; the finite deflation leaf adds12. Their formalized cards are [negative response/receiver](../3-formalized/li-clock-off-line-negative-response.md) and [deflation/compensation](../3-formalized/li-clock-finite-eta-deflation.md). Growing arithmetic sign remains open.

## Completion poles: local author audit PASS; pole-only no-go argument FAILS

For each nonzero integer k, put s_k=1+2 pi i k/log 2. At this zero of d, the exact finite sum satisfies

`E_N(s_k)=sum_(m=N+1)^(2N) m^(-s_k)`.

The integral from N to 2N of x^(-s_k) is zero. The complex trapezoidal rule with second derivative bound yields

`|E_N(s_k)+(1/4)N^(-s_k)| <= |s_k(s_k+1)|/(12N^2)`.

Indeed, there are N unit intervals and |f''(x)|<=|s_k(s_k+1)|N^(-3). Hence each fixed k has E_N(s_k)!=0 for all N>|s_k(s_k+1)|/3. The corresponding finite H_N has a genuine simple pole with logarithmic residue -1. In central coordinates p_k=2 pi k/log2-i/2. The conjugate pair's isolated clock component is `-2 Re(p_k^(-1) sin(t/p_k))`; if p_k^(-1)=a+ib, b>0, its leading term is exp(bt)[b cos(at)-a sin(at)]. This isolated component oscillates. It does not establish the sign of the full response.

At s=-2m, m>=1, every finite odd-even summand is negative, so E_N(-2m)<0 for N>=1. The Gamma_R simple poles therefore remain uncancelled; their isolated positive clock terms are `(2m+1/2)^(-1) sinh(t/(2m+1/2))`, with maximal rate 2/5. The known zero at s=0 contributes rate 2 with the exact negative sign computed above. Neither list exhausts the zeros of the finite exponential polynomial E_N. No complete meromorphic canonical-divisor expansion, remaining-frequency bound or uniform first-negative-clock estimate has been established in this audit. In particular, full F_N negative cofinally for fixed N is not claimed.

The finite completed source can be meromorphic while its local sine-contour response is entire in t: the fixed contour gives a factorial majorant. Artificial poles therefore do not make the growing-window candidate ill-posed. Their visible components do not prove an obstruction inside c log a_N. Under actual all-clock nonnegativity, any negative excursion inside that window has depth at most epsilon_N->0. This excludes a nonvanishing negative margin there, but does not exclude arbitrarily small negative values. No exact obstruction scale was proved. The fixed-prefix and growing-prefix limits cannot be interchanged without new uniform divisor/cancellation estimates.

## Research evidence and limits

Documented query executed directly:

`python3 scripts/formal_tools.py research 'finite eta completed clock orientation growing logarithmic window artificial elementary poles sine positivity' --mode deep --budget-seconds 300 --explore 0`.

Completed56.21s, lexical AND0 declarations; deep hits largely mismatched simple-sine or generic growth observables. Complete63121-file inventory, generation1146128/current1146129, older coverage snapshot, unmeasured semantic coverage and source-only candidates. Transcript session65204/finalchunk0c062f; no saved search file. Direct source inspection covers the finite completed trace, exact actual contour, maximal reciprocal packet and RH-conditional decay. No compiler or numerical experiment in this audit. No corpus-wide or public novelty claim.

Additional direct query: `python3 scripts/formal_tools.py research 'finite trigonometric simultaneous phase recurrence cofinal real frequencies sine cosine' --mode deep --budget-seconds 300 --explore 0`. Completed66.06s, lexical AND0 declarations; surfaced polynomial sine recurrences and unrelated periodicity rather than the required cofinal simultaneous phase statement. Complete63123-file inventory, generation1146157/current1146158; older coverage snapshot and unmeasured semantic coverage, all shown candidates source-only. Transcript session92715/finalchunk7e5d73; no saved output file. Direct rg inspection of in-scope actual-clock leaves finds the exact top/gap and source-sum interfaces used above; this is not an exhaustive corpus absence claim.

## Log

- 2026-09-30 — Recorded candidate before the detailed pole/scale analysis. Scope is signed-window strength and artificial completion artifacts; source sign remains open.
- 2026-09-30 — Author conditional-strength and exact-deflation paper audits PASS; both independent audits pending before formal work. Growing-window source sign remains open; artificial-pole-only sign/scale obstruction rejected. Strongest proposed closed survivor is the exact -2 sinh(2t) deflation and forced compensating positive fixed-window margin. No Lean builds or numerical experiments; no route retired.
- 2026-09-30 — Independent pole audit preliminary PASS corrects the literal point values: C(0)=0, Ctilde(0)=-2, while literal H_N itself is analytic with derivative -2 L_N(0). Final independent pole audit pending; stage unchanged. Root finite approximation wrapper mathematical/interface review PASS and scratch95701 exit0/empty; promoted reserved leaf named build66559 pending. This agent made only the assigned card edit, with no compiler jobs or other source/docs writes.

- 2026-09-30 01:32 UTC — Formal receivers and calibrated deflation are final (17+12 public declarations). Parent candidate remains stage1: independent source sign on growing logarithmic window is unproved. Two read-only arithmetic audits now target positive finite-Laplace/endpoint moments and direct completed quotient/Taylor cancellation; no numerical experiments or premature Lean.

## Final damped signed-area survivor

[Exact damped clock sum rules](../3-formalized/li-clock-damped-endpoint-sum-rule.md) are final: four leaves/35 public declarations. Literal full-copy area at p=2 equals `(2+EulerGamma-log(4pi))/4>0`; every p>1/300 has a positive source resolvent limit. For one admissible r and every0<c<r/4, actual finite logarithmic-window areas converge to that invariant and are eventually positive, with explicit finite-error plus complete-tail control. The source-defined deflated area minus its literal finite pole area has the same limit for all permitted p; at p=2 subtracting W_N gives `(xiEndpointCompletedCurvature-1)/4`. Named, final exact, all-public foundational axiom and independent source audits PASS. Growing pointwise source sign remains OPEN; these aggregate laws remain compatible with not-RH cofinal negative clocks.

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

2026-09-30 06:48 UTC — [Joint moving-window arithmetic cancellation](../3-formalized/li-clock-joint-arithmetic-cancellation-window.md) FINAL: one common radius, two new leaves/two public declarations, eight actual finite-source limits; named/direct/all-public foundational checks and full independent proof audits PASS. Both finite eta/gap scaled limits are-1/5, completion ratios-1, real parts tend minus infinity; completed finite clocks have normalized limit0. Exact window0<c<r/4 preserved. Index PASS; global lint13 unrelated unreachable modules, no proof-debt errors. New [density-ratio/endpoint boundary](../2-fully-proven/li-clock-partition-density-ratio-endpoint-boundary.md) enters paper audit; no actual residual sign or RH conclusion.

2026-09-30 07:16 UTC — [Complete contiguous comparison survivor](../3-formalized/li-clock-contiguous-comparison-window.md) FINAL: Source20+Comparison44 public declarations, every original paper target formalized, full root/producer proof audits and named/direct/all-public foundational checks PASS. Entire filled U, full k0 lattice and exponential packets, all absolute/local-uniform exchanges, exact radial O bound, strict real K positivity and eventual completed MODEL positivity for0<c<1/16 are closed. Index PASS; global lint10 unrelated unreachable modules, no proof-debt errors. [Actual density-ratio/endpoint boundary](../2-fully-proven/li-clock-partition-density-ratio-endpoint-boundary.md) now paper-PASS/Stage2 with sharp moment/Borel survivor and both radial a.e monotonicity obstructions; disjoint Lean scopes released. Actual residual sign and RH remain OPEN.
