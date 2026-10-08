# WP06 result register

**Overall verdict: OPEN.** The required zero lower deficit density has not been proved. No application yielding `λ = Λ` or RH has been added.

**Quantitative milestone proved in Lean:** for every `hW : WeilPositiveFull λ`, every n≥2 and ε>0, eventually

`|λ(n)−Λ(n)|/(4π√n) ≤ D(T)/T + ε`.

This sharpens the previous `4πn` coefficient scale to `4π√n`, with no assumed upper deficit bound. The exact character discrepancy and sharp-window mass balance are also proved. Twenty-two modules, 93 public theorem axiom audits, only standard Lean foundations. This is a quantitative corpus advance; external scientific novelty is not established.

## Audited Lean results

`WeilWorkDeficitRecovery.lean` proves exact regularized-deficit decomposition and uniform atom recovery over every prefix of a fixed bounded height window. All eight theorem axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Targeted build and final `lake --old env lean` both passed. Umbrella import wired.

Classification: **BRIDGE**. No effective recovery rate as height grows, no upper bound on the actual deficit, no scientific novelty claim.

`WeilWorkDeficitSharedMass.lean` constructs the actual common critical submeasure `χ≤μ,ν` and proves:

- `χ((0,T])=N(T)−D(T)`, with every multiplicity copy retained;
- `‖∫_(0,T] e^(ikr)dμ−∫_(0,T] e^(ikr)dν‖≤M(T)−N(T)+2D(T)` for every real `k,T`.

Here `ν` is the projected actual Xi divisor and `M(T)=μ((0,T])`. Diffuse spectral mass and off-line copies are included. All twelve public theorem axiom audits report only standard Lean foundations. Targeted build and final direct `lake --old env lean` passed without target diagnostics. Umbrella wired. Full audit output is in `lean-audit.log`.

Classification: **EXACT COMPARISON / BRIDGE**. This supplies the shared-submeasure step used in the sharper bound below; it does not produce small deficit.

## Active quantitative research

The dependency-closed argument in `PROOF.md` is now formalized through `WeilWorkDeficitCoefficient.lean`, using actual shared critical mass, Poisson endpoint control, and the corpus's exact Dirichlet cosine means. Ford–Zaharescu supplies external ancestry, not an imported formal premise.

Shared-mass comparison, leakage and complex Fourier transport for both actual measures, the full-prefix square-moment limit, zero multiplier projection, and arithmetic assembly are all formalized. The full-line transform `HTGeometry.integral_cexp_mul_inv_sq_add_sq` was reused. The next research obligation is an upper bound on actual missing overlap, retaining the unit cost of every off-line copy.

## Validation limits

Latest completed repository-wide formal lint status is recorded in `EVIDENCE.md`: seven unrelated reachability errors, none in WP06. All twenty-two finished WP06 modules are umbrella-wired. No full or umbrella build was run. No numerical experiments, heartbeat increases, commits, or added mathematical axioms.

## Verified linear-scale Poisson leakage

Three additional modules extend the logarithmic unit-window mass estimate to arbitrary bounded intervals and prove the full canonical leakage limit:

`(1/T) ∫ |countKernel T r − π 1_(0,T](r)| dμλ(r) → 0`.

The proof retains endpoint atoms and diffuse mass. Endpoint intervals of width `√T` and the remaining bounded interval contribute `O(log T/√T)` after normalization. The distant contribution is bounded by `12∫_(|r|>2T)(1+r²)⁻¹dμλ(r)`, which tends to zero by the corpus's Cauchy-weight integrability. No new scientific hypothesis is used.

Sources: `WeilWorkDeficitMassBounds.lean`, `WeilWorkDeficitPoissonLeakage.lean`, `WeilWorkDeficitLeakageIntegral.lean`. Their original eleven public theorem axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`; targeted builds and direct audits passed. The later actual-ordinate extension and its fresh audits are recorded below. Umbrella imports are wired.

Classification: **BRIDGE**, not a small-deficit theorem or a claim of scientific novelty. It is an audited dependency of Candidate A.

Frontier correction: `WeilFibreBochnerLaw` already excludes both signs of the nonzero Cramér-restored profile. The prime-deficit profile escapes the rough-sign test alone, but does not survive the full corpus's fibre constraints.

## Verified canonical Fourier transport

`WeilWorkDeficitFourierTransport.lean` proves, for every full-positive λ and `T≥1`,

`‖∫_0^T e^(ikt) Re Φλ(2+it)dt − π e^(−3|k|/2) ∫_(0,T]e^(ikr)dμλ‖ ≤ ∫ deficitPoissonLeakage T dμλ`.

Consequently its error divided by T tends to zero, even for an arbitrary frequency function `k(T)`. Product integrability and the Fubini exchange are proved for the actual canonical measure. All four public theorem axiom audits report only standard Lean foundations. Targeted build and final direct `lake --old env lean` passed; umbrella wired.

Classification: **BRIDGE**. Forward uniformity in frequency does not justify uniform inversion of the exponentially decaying multiplier and does not recover small atom deficit.

The internal subtraction route takes means of `Φλ−ξ'/ξ` directly, avoiding separate archimedean asymptotics. Exact arithmetic extraction and current zero-side proof status are recorded below. The main target stays active throughout.

## Verified arithmetic difference means

`WeilWorkDeficitArithmeticMean.lean` proves, for every σ>1 and n≥2,

`T⁻¹∫_0^T (Re Φλ(σ+it)−Re ξ'/ξ(σ+it)) cos(t log n)dt → (Λ(n)−λ(n))n^(−σ)/2`,

and the zero-frequency difference mean tends to zero. It reuses the exact Dirichlet cosine-series identity and Bohr means, then removes the fixed initial interval. No separate asymptotic assertion about the archimedean term is assumed. Both public theorem axiom audits contain only standard Lean foundations. Targeted build and final direct source audit passed with no target diagnostics; umbrella wired.

Classification: **BRIDGE / CORPUS CONSEQUENCE**. These two means supply Candidate A's arithmetic input; they do not by themselves bound missing overlap.

## Verified horizontal square moment

`WeilWorkDeficitSquareWindow.lean` transports the corpus's weighted right-tail estimate to every finite set of actual Xi copies in the admissible window, with no assumed symmetry of that finite set. `WeilWorkDeficitSquareMoment.lean` then proves unconditionally

`Q(T)/T → 0`, where `Q(T)=Σ_(0<γ_q≤T)(β_q−1/2)²`.

The proof pays the Xi/zeta multiplicity conversion, left-tail conjugation, omitted endpoint strips, and geometric prefix assembly. It uses the weaker uniform first-displacement tail bound, without the exponential refinement. Both direct source audits and targeted builds passed; both public theorem axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`. Both imports are wired. The SquareMoment audit emitted one informational `ring_nf` suggestion and no errors.

Classification: **BRIDGE / CORPUS CONSEQUENCE**. Small squared displacement does not imply few off-line copies: the target deficit charges each such copy one full unit. The main target remains open.

## Verified zero projection and actual-ordinate leakage

`WeilWorkDeficitProjection.lean` proves, for every real k,T,

`‖Σ_(0<γ_q≤T) exp(−(2−β_q)|k|)e^(ikγ_q) − exp(−3|k|/2)Σ_(0<γ_q≤T)e^(ikγ_q)‖`
`≤ exp(−3|k|/2)(k²/2)cosh(|k|/2)Q(T)`.

Consequently the normalized error tends to zero for each fixed frequency. The proof pairs the actual full prefix by line conjugation; it does not assume critical support or discard multiplicity copies.

MassBounds now also proves logarithmic interval mass and Cauchy-weight integrability for the actual ordinate measure ν. LeakageIntegral shares its measure-independent argument privately, preserves every canonical public statement, and proves unconditionally

`T⁻¹∫ deficitPoissonLeakage T r dν(r) → 0`.

All source audits and targeted builds passed. Axiom inspection of the three projection theorems, all five mass theorems, all six leakage theorems, and the four canonical transport theorems reports only standard Lean foundations. At that checkpoint ten modules contained 47 audited public theorems; the current total is 57 after the capstone below.

Classification: **BRIDGE / CORPUS CONSEQUENCE**. Neither matching smoothed mass nor quadratic horizontal projection supplies the exact atom overlap required by the main deficit target.

## Verified actual-zero transport and coefficient capstone

`WeilWorkDeficitZeroKernel.lean` and `WeilWorkDeficitZeroTransport.lean` integrate the complex actual-copy Poisson series, identify the sharp finite character sum with the ν-window integral, and prove

`T⁻¹[∫_0^T e^(ikt) Re ξ′/ξ(2+it)dt − πe^(−3|k|/2)∫_(0,T]e^(ikr)dν] → 0`

for every fixed real k. The raw transport error before horizontal projection is bounded by `(3/2)∫L(T,r)dν(r)` uniformly in k. All multiplicity copies and endpoint atoms are retained.

`WeilWorkDeficitCoefficient.lean` defines the actual character gap `G_k(T)=∫e^(ikr)dμ−∫e^(ikr)dν` over `(0,T]` and proves

- `Re G_(log n)(T)/T → (Λ(n)−λ(n))/(2π√n)`, n≥2;
- `(M(T)−N(T))/T → 0`;
- the eventual square-root deficit lower bound stated at the top of this register.

Each of the three new modules passed its final direct `lake --old env lean` audit with empty diagnostics and its targeted build. The combined ten-theorem axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`. All imports are wired. No unfinished owned Lean source or active owned build remains.

Anti-theatre: the quantitative corpus frontier moved; external novelty remains unestablished. The analytic ingredients are classical or existing corpus consequences. This completes the requested stronger intermediate comparison, not the required small-deficit producer. Anti-laziness: the entire comparison was paid through actual objects and final audits; the next cycle must attack growing-height atom overlap using the exact Weil datum, since the fixed-frequency bridge now has its finished application.


## Verified restricted obstruction; coherent cancellation remains open

`WeilWorkDeficitRadicalTranslateObstruction.lean` proves a uniform δ>0 such that every finite positive mixture of independently translated truncated Riemann kernels with cutoffs at least `log 2+1` satisfies

`δ Σ_i w_i |paperFT f_i(r)|² ≤ Σ_i w_i logValue f_i 2`

at every real frequency r. Thus spectral normalization in this family forces a positive lower arithmetic repair cost. Different cutoffs and arbitrary translations do not remove the obstruction. Coherent combinations inside a test remain outside its scope.

Classification: **PROVED RESTRICTED NO-GO / ELEMENTARY CORPUS CONSEQUENCE**. No claim of scientific novelty. Direct `lake --old env lean`, targeted build and the public axiom audit passed; only standard Lean foundations. Umbrella wired. The C0 checkpoint had 58 audited theorems across fourteen modules; the current total includes C1g below.

Frontier correction: the existing critical-carrier theorem already handles arbitrary atom masses once support on actual critical zeros is proved. Its explicit Lean type was freshly checked. The next construction must remove mass outside that set, not reprove mass uniqueness. Conjecture C asks for spectral majorization with small actual zeta energy and full weighted arithmetic repair cost. The sharper C1 asks for all-integer cancellation by coherent logarithmic translates with polynomial coefficient cost. Both remain OPEN, with exact statements and attacks in PROOF.

Anti-theatre: this cycle produced no significant new scientific knowledge; it paid a restricted no-go and avoided several rediscoveries. Anti-laziness: no difficulty or effort estimate was used to abandon work. The unresolved core is now a concrete positive covariance construction with a quantitative normalization bound. Goal remains ACTIVE and unsolved.
## Verified coherent geometric-grid rigidity and exact positive invariant

`WeilWorkDeficitGeometricRadicalObstruction.lean` proves two actual-kernel results:

- `geometric_radical_outer_autocorrelation`: for any real spacing c>0, L≥c+1 and nonzero finite complex coefficient family, the last nonzero sampled correlation occurs at R+D with exact value C(D)κ(R); every later sample vanishes. R and D are the last nonzero kernel and covariance indices, with R≥1 and D≥0.
- `logValue_geometric_radical_eq_zero_iff`: at spacing log b for any integer b≥2, vanishing of every positive-power logarithmic value is equivalent to every coefficient being zero.

Both pass final direct `lake --old env lean`, target-only build, and axiom audit with standard foundations only. Umbrella wired. The positive invariant and C0's uniform coercivity law are recorded on the closed restricted-route card `docs/drafts/pipeline/5-failed/weil-work-06-restricted-radical-cancellation.md`.

Classification: **PROVED RESTRICTED NO-GO WITH EXACT POSITIVE INVARIANT / REDISCOVERED PARENT ALGEBRA**. No external scientific novelty claimed. This does not rule out mixtures on the logarithms of general integers, does not give a degree-uniform lower cost, and does not bound the actual deficit from above.

Next conjecture C2 uses centered shifts log(j/N), j∈[ceil(N/2),N]. Complete paper support and energy reductions leave O(log N) active arithmetic constraints and zero energy O(N^(A+1−C)). The positive covariance construction with coefficient norm ≤N^A, exact integer cancellation, and off-zero spectral normalization remains OPEN. No C2 theorem or small-deficit producer is claimed.

## Verified restricted xi density; finite feasibility and cost reduction on paper

`WeilWorkDeficitRestrictedXiDensity.lean` proves that the actual functions `XiC(r) exp(−itr)`, with t in any nonempty open real interval, have dense complex span in L²(ℝ). Its two public theorems are the exact zero-annihilator equivalence and dense-span conclusion. Direct source audit, targeted build, specialized API check and standard-only axiom audits passed; umbrella wired. Classification: **BRIDGE / CLASSICAL ANALYTIC DENSITY**, no scientific novelty claim or coefficient bound.

PROOF contains the complete paper theorem C2f: every fixed finite arithmetic horizon admits positive real coherent mixtures on all sufficiently fine centered logarithmic grids, with a finite coefficient budget uniform over sufficiently large physical cutoffs. Only its complex-density component is formalized; the real-mixture, cone and grid steps remain paper-only. It supplies no joint asymptotic rate.

Next candidate C3 requires cancelling through M with the baseline Φ retained and squared absolute-coefficient-sum cost ≤C exp(θM), θ<π/2. The complete paper reduction C3→C now includes the actual repair-cost bound `atomCost(n)≤C(n+1)√n` and dominated convergence of the entire weighted arithmetic budget. The repair-cost step and full weighted packet truncation convergence are now formalized as recorded below. The full finite-mixture spectral-majorant assembly remains paper-only. C3t+ improves the sufficient rate to θ<π, and C7 below permits an unbounded subsequence at any one fixed aperture. The finite-mixture rate in C3 is OPEN, as are C2 and the assigned small-deficit target.


## Verified polynomial cost of actual isolated-atom repair

`WeilWorkDeficitRepairCost.lean` proves unconditionally that there is C>0 with

`atomCost(j) ≤ C (j+1)√j` for every actual `LogIndex` j.

Its other three public theorems give exact physical bump scaling, complex Fourier scaling, and squared-mass scaling. The proof bounds the gamma integral uniformly and retains both pole contributions. The existing PBAP definitions are unchanged. Final direct source audit, target-only build, and all four axiom/API audits passed with empty source diagnostics and only standard foundations. Umbrella wired. Seventeen finished modules / 66 public theorem audits.

Classification: **BRIDGE / CLASSICAL SCALING**. This pays C3r; it does not construct a low-cost cancelling mixture or prove small deficit. C4b now has a complete paper-only quartic lower-cost argument `A_M≥c M⁴/(log M)³⁴`; no Lean claim. Next hard conjecture C5p asks for a polynomial upper bound for the particular baseline defect, with K≥4 forced by that paper boundary. C3, C5p and the assigned target remain OPEN.

## Verified full weighted radical budget and arithmetic tails

`WeilWorkDeficitRadicalBudget.lean` proves nine unconditional packet theorems for the actual compact `shiftComb`, `logValue` and PBAP `atomCost`. For every 0<r<π, one constant C_r controls every real finite packet P with shifts in [−log 2,0], every physical cutoff L, and every integer tail:

`Σ_(n≥M) (Λ(n)+atomCost(n)) |b_(P,L)(n)| ≤ C_r cost(P) exp(−rM)`.

The untruncated coefficients obey the same bound. The complete weighted ℓ¹ difference between truncated and untruncated coefficients tends to zero as L→∞; consequently the entire absolute repair budget converges, including every new integer coordinate activated by truncation. These limits fix P first; no uniform limit over growing families is asserted. The exact natural indexing starts at n=2.

Target-only build, final direct `lake --old env lean`, all nine public axiom audits and the specialized API checks passed. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired. Classification: **BRIDGE / reuse of the corpus's sharp theta envelope**; no significant external scientific novelty claim.

This pays the weighted-tail/truncation component of C3t+. The selected next conjecture C7 asks for affordable exact finite cancellation along an unbounded sequence, at some fixed shift aperture a>0, with cost exponent θ<2π exp(−a). Its full implication is paper-proved; the actual positive family construction remains OPEN. The stronger near-quartic C6Q and critical exponential obstruction C6E are unproved diagnostic alternatives, not an exhaustive dichotomy. C4b's lower boundary remains paper-only. The assigned spectral-deficit target is still UNSOLVED.

## Verified cost of strong Xi-profile approximation

`WeilWorkDeficitXiApproximationCost.lean` proves four unconditional theorems. For any actual real Xi zero γ, any finite complex packet `F=Σ c_j Φ(·−x_j)` with |x_j|≤a, variation `V=Σ|c_j|`, physical error `E=‖F−exp(−iγ·)Φ‖₂`, and `h=|XiC(0)|>0`, universal constants B>0 and K>1 give:

- Exact Fourier mismatch at γ: `paperFT(F−exp(−iγ·)Φ)(γ)=−XiC(0)`.
- For every L>0: `h≤sqrt(2L)E+2B(V+1)exp(−exp(2(L−a)))`.
- If N≥0 and V≤exp N: `h²≤8(a+log(N+K))E²`.
- Always E>0 and `exp(exp(h²/(8E²)−a)−K)≤V+1`.

No zero simplicity or approximation premise is assumed. Target-only build, final unchanged direct `lake --old env lean`, and all four public axiom/API audits passed. Only standard Lean foundations; umbrella wired. The spectral Plancherel restatement remains paper-only.

Classification: **BRIDGE / quantitative obstruction**, with no sharpness or external scientific novelty claim. This rules out a uniform cheap strong-L² transfer theorem covering all spectral shifts. It does not refute transfer for the particular M-dependent Bernoulli witnesses, finite quadratic moment transfer, or C7. The precise failed shortcut and its positive survivor are recorded in `weil-work-06-cheap-strong-transfer.md`.

The next competing constructions are C9's target-relative quadratic witness rate and C10's real derivative packets of order at most M, retaining Φ and cancelling through M while their complete actual PBAP-weighted tail decays exponentially. Existing derivative radical identities pay zero preservation; the bounded-degree positive cone and cost of its cancelling family remain OPEN. The uniform growing-order analytic budget is now formalized below. Neither conjecture is introduced as a Lean premise. The main goal remains ACTIVE and UNSOLVED.


## Uniform factorial derivative budget (C10u)

`WeilWorkDeficitUniformDerivativeBudget.lean` proves five unconditional analytic theorems. For every `0<a<π`, one B>0 controls every derivative order:

`‖Φ^(k)(u)‖ ≤ B [3+4π/(π−a)]^k (k+2)! exp(−a exp(2|u|)) exp(−|u|)`.

The same constants control arbitrary finite complex derivative packets and their complete correlations, including integrability. For `0<r<2π`, set `C_r=3+16π/(2π−r)` and `V=Σ_j |c_j| C_r^(k_j)(k_j+2)!`. The full actual PBAP-weighted arithmetic tail is summable and bounded by

`Σ_(n≥N+2) (Λ(n)+atomCost(n)) |correlation(f,log n)| ≤ B_r V² exp(−r(N+2))`.

Constants precede every order, row count and coefficient. No integer or actual repair term is omitted. No sharpness is claimed for the explicit base. At r=π it is exactly19, verified in the specialized real-packet API audit.

Final validation on2026-10-08: target-only build exit0 (114s target); unchanged `lake --old env lean` exit0 with empty output; all five public axiom audits and specialized API examples exit0, only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired. Formal lint exit1 has eight reachability findings outside WP06.

**Verdict: BRIDGE.** This pays growing-order analytic costs, not positive prefix cancellation or the required upper deficit. C11 asks for nonnegative diagonal derivative coefficients through order M cancelling n=2..M. C11q additionally asks, along unbounded horizons, for `Σ_k d_k 19^(2k)((k+2)!)² ≤ exp(θM)` with fixed `0<θ<π`. Its competing finite dual obstruction and precise limitations are in PROOF. Both remain open; no new Lean premise encodes them.

## Verified full divisor–Bessel correlation matrix (C11b)

`WeilWorkDeficitBesselCorrelation.lean` proves the exact convolution identity for arbitrary real polynomial theta series, absolute convergence of each full divisor–Bessel monomial series, and integrability of all polynomial and actual mixed-derivative correlations. Every positive factor pair is retained. The actual matrix `A(n,k)` is now identified in Lean through the same formula at derivative orders `(k,k)` and shift `log n`.

The explicit actual-kernel specialization is

`κ(y) = exp(y/2) Σ_(N≥1) d(N) [(x⁴+9x²)K₀(x) − 6x³K₁(x)]`, `x=2πN exp(y)`.

All seven public theorem audits use only standard foundations; target build and final unchanged direct audit passed. Umbrella wired. Checkpoint:21 modules/91 public theorem audits.

Classification: **CLASSICAL-PARENT BRIDGE**. This verifies the infinite arithmetic correlation matrix without deciding its signs, producing a positive cancellation family, or proving any upper deficit bound. C11/C11q and C12 remain open. The next hard step is the growing-order arithmetic asymptotic or the quantitative cancellation construction, not another unneeded representation theorem.


## Verified full twisted-gap budget; C12 paper checkpoint

`WeilWorkDeficitTwistedGapBudget.lean` proves summability and an explicit
conductor-linear bound for the complete integer-twist reciprocal-square
frequency sum, with all positive factor pairs retained. For T≥1 and n≥1,

`Σ_(r,m≥1) (rm)^(-1/2) min(1,T/(rm))² / (log(m/r)-log n)² ≤ (48 n² Z + 16 pairZeta) T`,

where Z is the finite reciprocal-square integer-lattice mass and the diagonal
summand is zero. Target-only build, final unchanged direct audit and both
public axiom audits passed; standard foundations only. Umbrella wired.
Classification: **BRIDGE**; no external scientific novelty claimed.

PROOF now contains a complete paper argument for C12g's square-root Gaussian
twisted moment and C12's literal normalized derivative-correlation limit
`A(n,k)/A(1,k)→1/sqrt(n)` for each fixed integer n≥2. The analytical assembly
and Xi transfer remain **unformalized**. The new Lean module proves only the
full arithmetic gap estimate used by that argument. Eventual positivity on
fixed finite rows is a paper consequence, not a completed Lean no-go.

C11q's positive construction/cost and the main upper-deficit producer remain
open. New C13 asks for a truncated-prime lower bound on a coupled derivative
order band, preserving finitely many low-order exceptions; it is conjectural.
