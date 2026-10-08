# WP06 result register

**Overall verdict: OPEN.** The required zero lower deficit density has not been proved. No application yielding `λ = Λ` or RH has been added.

**Quantitative milestone proved in Lean:** for every `hW : WeilPositiveFull λ`, every n≥2 and ε>0, eventually

`|λ(n)−Λ(n)|/(4π√n) ≤ D(T)/T + ε`.

This sharpens the previous `4πn` coefficient scale to `4π√n`, with no assumed upper deficit bound. The exact character discrepancy and sharp-window mass balance are also proved. Thirty-seven modules, 156 public theorem axiom audits, only standard Lean foundations. This is a quantitative corpus advance; external scientific novelty is not established.

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

Latest completed repository-wide formal lint status is recorded in `EVIDENCE.md`: seven unrelated reachability errors, none in WP06. All thirty-seven finished WP06 modules are umbrella-wired. No full or umbrella build was run. No numerical experiments, heartbeat increases, commits, or added mathematical axioms.

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

## Verified actual cutoff two-jet bounds; coupled cost research

`WeilWorkDeficitSmoothCutoffJets.lean` proves the literal first and second
height derivatives of smoothAFECutoff(P/t) and one bound, uniform for all
positive P,t, for orders j=0,1,2:
`|V_j(P,t)| <= C/t^j * min(1,(t/P)^2)`.
Three public theorems, target build, unchanged direct Lean audit and
standard-only axiom audit passed; umbrella wired. This closes G2, the
moving-cutoff dependency of C12g. G3 below now supplies twice integration
by parts and full off-diagonal summation. The endpoint moment and Xi
transfer still require formalization.

On paper, C13 now holds for all sufficiently large k and every M>=beta k
whenever beta>(2/pi)log(19pi/4); beta=2 suffices. Its exact full prime
identity retains the signed pole term (-1)^k/4^(k+1). Combining this with
C11q's budget proves tightness of normalized derivative-energy weights:
any C11q family would produce a probability on derivative orders with
finite logarithmic moment and all integer correlations zero. No retained
zeroth mass is asserted after normalization. These are paper consequences
of C12/C13, currently unformalized, and do not settle the target.

C14 (every positive proportional prime cutoff) and C15 (nonexistence of
the limiting positive derivative mixture) are open competing-conjecture
attacks. Published polynomial-approximation work already contains the
Xi-square derivative Gram framework; no novelty claim for that framework
or the new analytic bridges. General compact atom-cancelling mixtures in
the corpus do not answer C15, whose support is the actual derivative family.


## Verified actual oscillatory windows and full off-diagonal (G3)

`WeilWorkDeficitOscillatoryWindow.lean` proves two unconditional results:

- One constant bounds the literal fixed bump times smoothAFECutoff(P/t)
  by K H min(1,(T/P)^2), and its oscillatory integral by
  K/(H lambda^2) min(1,(T/P)^2), for P,H>0, T>=2H and nonzero lambda.
- Every positive factor pair off the exact integer-twist diagonal is
  absolutely summable, and the full complex sum is bounded by
  K(48 n^2 integerGapBudget + 16 pairZeta) T/H, for n>=1,T>=1.

Thus the complete off-diagonal costs O_n(sqrt T) at square-root width.
Both public theorem types and standard-only axiom audits passed; targeted
build and unchanged direct source audit passed; umbrella import wired.
Classification: classical-parent BRIDGE, no external novelty claim.
The fixed compact window is actual, but Gaussian extension, diagonal
asymptotics, AFE integral interchange and Xi transfer remain unformalized.
C15 remains open. New C16 tests the exact full absolute prime pairing
against log(k+2) E_k; neither that bound nor its negation is established.

## Verified full prime product-kernel budget (G4)

`WeilWorkDeficitPrimeKernelBudget.lean` proves three unconditional results:
absolute convergence of the full d(m)log(m)-weighted kernel sum, the exact
actual correlation formula at every real shift, and

`sum_n Lambda(n)|A(n,k)|/sqrt(n) <= sum_m d(m)log(m)|K_k(m)|/2`

for every derivative order k. Every positive factor pair and prime power
is included. The proof uses the corpus's existing Lambda*d=d log/2;
that identity is not claimed as new knowledge. Targeted build, unchanged
final direct audit and all three exact-type/axiom audits passed. Only
standard foundations; umbrella wired. Classification: classical-parent
BRIDGE. No uniform-in-order estimate is proved by this Lean module.

The new C17 paper argument identifies this exact kernel by Mellin
inversion, proves its local signed Gaussian profile and a uniform global
fourth-power envelope, and prices compact heights separately. It yields
C16's logarithmic full absolute-prime budget and C14's limit for every
positive proportional prime cutoff. These analytical results remain
UNFORMALIZED. Their complete argument and dependencies are in PROOF;
no scientific novelty or solved-deficit claim is made.

C15's actual positive derivative mixture remains open: paid absolute
prime interchange alone does not contradict its finitely many signed
low-order contributions. C18 now tests the sublinear cutoff transition
beta-beta^2/2 against its competing failure conjecture. Main goal remains
ACTIVE and UNSOLVED.

### G5 completed: actual product-kernel Mellin transform (2026-10-08)

`WeilWorkDeficitProductKernelMellin.lean` proves absolute Mellin
integrability for Re(s)>0 and the exact formula

`integral_0^infinity x^(s-1)K_k(x) dx = (-1)^k (s-1/2)^(2k) s^2(s-1)^2 pi^(-s) Gamma(s/2)^2/4`.

The proof uses the actual finite `riemannKernelPoly` coefficients,
absolute Fubini, and its exact derivative recurrence. Both public
statements passed exact-type/axiom audits with standard foundations
only; target-only build and final unchanged direct source audit passed.
Umbrella wired. Twenty-six completed modules /103 public audits.
Classification BRIDGE: this is no scientific novelty claim and does
not prove C17's growing-order estimate or the deficit upper bound.

C19 supplies another paper representation of C15: within the exact
positive probability/finite-log-moment class, all integer correlation
cancellations are equivalent to the mixture kernel equaling1 at m=1
and0 at every integer m>=2. Finite Euler deletion, followed by dominated
convergence, avoids an unjustified infinite Möbius rearrangement.
This depends on paper C17 for the absolute budget and is not yet
formalized. It constructs no mixture and proves no obstruction.

Next analytic assembly must reuse the existing sharp all-order
polygamma bound in `PolygammaVerticalSharpDecay.lean` and the full
Stirling ladder. C15, C18, and the assigned deficit target remain OPEN.

### G6 completed: common Mellin bulk envelope (2026-10-08)

`WeilWorkDeficitMellinAmplitude.lean` proves the literal Mellin norm on
Re(s)=4 and one Gaussian bulk bound uniform in every derivative order k.
For T=(2k+7)/(pi/2), B=T^(2k+7)exp(-pi*T/2), there is one C>0 with

  |M_k(4+it)| <= C B exp(-pi*(t-T)^2/(18T)), T/2<=t<=2T.

Both exact public types and axiom audits passed with standard foundations
only. Target-only build112s; final unchanged direct audit exit0/empty;
umbrella wired once. Twenty-seven completed modules /105 public audits.
G6 is a classical-parent BRIDGE. It does not prove global tails,
differentiated amplitude bounds, or the assigned deficit upper bound.

C20c now has a dependency-closed paper proof, using paper C17 and the
published maximal divisor mean-square bound: the dyadic average of
B_k/log(k+2) tends to (3+R_a)/8, where R_a=integral|J_a|/integral J_a>1.
The low prime rows retain signed mass3/8, while separated high rows
retain absolute profile massR_a/8. All transition rows, tails and the
discrete averaging step are included. This remains UNFORMALIZED;
scientific novelty of the sharp coefficient is not certified.
C20's pointwise law and C15's positive mixture remain OPEN. Goal ACTIVE.

### G7 completed; C21 comparison disproved on paper (2026-10-08)

`WeilWorkDeficitMellinSlope.lean` proves exact differentiation of the
actual demodulated Mellin integral and a common bulk bound for its
scaled first derivative. With G6's T,B and
F_k(t)=M_k(4+it)exp(-it log(T/(2pi))), one C>0 satisfies

  sqrt(T)|F_k'(t)| <= C B (1+|t-T|/sqrt(T)) exp(-pi*(t-T)^2/(18T))

for all k and T/2<=t<=2T. Target build, final unchanged direct source
audit, and both exact-type/standard-only axiom audits passed. Umbrella
wired. Twenty-eight completed modules /107 public audits. This remains
a classical-parent BRIDGE, not the full C17 derivative/tail assembly.

C21a is FALSE on paper. The exact low-order product kernels satisfy
K_0(x)>0>K_1(x) for every real x>=2. Absolute divisor expansion gives
opposite strict signs for their entire nontrivial integer correlation
columns, and K_0(1)<E_0 while E_1<K_1(1). The complete proof appears in
PROOF; formalization is in progress and is not yet counted. This kills
the proposed universal first-kernel obstruction, not C15. Its positive
survivor supplies actual opposite column signs for the mixture problem.

C22 tests an explicit infinite positive-coefficient family obtained
from reciprocal Gamma products; its literal correlations reduce to
rationally weighted zeta-square integrals. Their sign and the full
coefficient-to-mixture audit remain open. No new scientific novelty
certification or upper-deficit producer is claimed. Goal ACTIVE.

### C21 positive survivor completed in Lean (2026-10-08)

`WeilWorkDeficitLowOrderSigns.lean` now proves all six exact claims:
the two product-kernel signs on x>=2, the two complete integer
correlation-column signs, and both opposite first-kernel energy gaps.
Target build23s/9886 jobs, final unchanged direct audit, and all six
exact-type/standard-only axiom audits passed; umbrella wired once.
Twenty-nine completed modules /113 public audits. The narrow failed
comparison is retired on its own failed-route card with this positive
survivor. C15 and the main spectral-deficit goal remain OPEN.

C22's N>=4 Gamma-weight subfamily now has a complete PAPER admissibility
proof: its normalized coefficients form an actual C15 probability
sequence with finite logarithmic moment, and its rows are exactly
R_N(n)/R_N(1). The logarithmic moment is paid explicitly from the Gamma
product and the audited unconditional linear zeta bound. This assembly
is not formalized; its signs, N=3 endpoint, and simultaneous cancellation
remain open. No novelty claim for this classical bridge.

### C22 literal Gamma density completed; C23 resonance on paper (2026-10-08)

`WeilWorkDeficitGammaDensity.lean` proves six unconditional claims for the
actual Xi-square/Gamma density: its entire Mellin continuation, exact
critical-line identity, rational zeta-square formula, common Poisson
envelope for every integer order at least four, absolute integrability,
and logarithmic integrability. Target-only build99s/8783 jobs, final
unchanged direct source audit, and six literal-type/standard-only axiom
audits passed. Umbrella wired once. Thirty completed modules /119 public
audits. This does not yet formalize the C22 coefficient-mixture assembly.

C23 now has a dependency-closed PAPER proof: the exact divisor-cosine
asymptotic forces eventual positive integer correlations for each C22
Gamma weight and every finite positive mixture of them. The uniform
strip estimate, conditional cosine-Mellin interchange, removable poles,
derivative jump and summable remainder are explicitly paid. The full
positive asymptotic survivor remains unformalized, so this family
obstruction is not marked closed. C24 proposes a compact-uniform
continuous-order extension; its boundary Mellin inversion remains OPEN.

Main spectral-deficit target and unrestricted C15 simultaneous
cancellation remain OPEN. These are classical-parent bridges; scientific
novelty is uncertified. Latest lint has eleven unrelated reachability
errors and no WP06 or forbidden-declaration finding.

### C23 exact symbol completed; C25 tail boundary on paper (2026-10-08)

`WeilWorkDeficitGammaSymbol.lean` adds three unconditional actual-object
theorems: the global reciprocal-Gamma recurrence, its complete
polynomial-clearing identity, and the exact Gamma/cosine/zeta-square
symbol on Re(s)=2. No singular argument is excluded from the global
clearing identities. The line-two formula retains the true Xi quotient;
no false equality at the totalized zeta pole is introduced.
Target-only build126s/8784 jobs, unchanged direct source audit and three
literal-type/standard-only axiom checks passed. Umbrella wired once.
Thirty-one completed modules /122 public audits. Full C23 inversion and
resonance asymptotic remain PAPER ONLY.

C25a conjectures that every cancelling C15 probability lacks every
positive exponential derivative-order moment; C25b asserts a counterexample.
Both remain OPEN. C25c/d now paper-prove a narrower necessary tail law:
with b_*=inf{|zeta|: |Im exp(i*zeta)|>=1/2},
limsup w_k^(1/(2k))>=2b_*/pi. Here 1/3<b_*<=pi/6. In particular the
moment sum w_k(2pi)^(2k) cannot be finite. The proof pays the Borel
representation, complex dilation of the actual product kernel, its
vertical growth bound and Carlson uniqueness. This extends beyond the
Gamma family, but remains a classical-parent BRIDGE with scientific
novelty uncertified, and is not yet formalized. No route is retired.

Main target remains ACTIVE/UNSOLVED. Latest lint reports nine unrelated
reachability errors; no WP06 or forbidden-declaration finding. All
owned commands terminal; completed proof scratch removed, audits retained.

### C23 endpoint jets and the moving-order correction — 2026-10-08

`WeilWorkDeficitGammaKernelJets.lean` now proves the literal rational
partial fractions, every lower endpoint cancellation, the first jump1,
and the next jump-(2N+4)^2/2. The endpoint statements concern actual
iterated derivatives of the inner polynomial and outer inverse-power
kernel pieces. No additional scientific premise or nonstandard axiom
was added. Targeted leaf build and final unchanged direct audit passed;
umbrella wired. All nine literal-type and axiom audits passed, using only
propext, Classical.choice and Quot.sound. Thirty-two completed owned modules,
131 public theorem audits.

The resulting paper research distinguishes three facts:

- C27: if Gamma order N and integer n tend to infinity with N^2/n->c>0,
  the correlation divided by16*pi^(9/2-2N)*n^(9/2-2N)*zeta(2N-4)^2
  tends to cos(c/pi). Thus arbitrarily late negative entries exist when
  order grows; C26's uniform positivity is false on paper.
- C28: every FIXED positive probability mixture of Gamma orders still
  has eventual positive integer correlations. A uniform shifted-line
  bound makes its least occupied order dominate the entire infinite tail.
- C29: probabilities w_k~C*k^-alpha,1<alpha<4, have positive normalized
  correlation limit C*(pi^2/2)^(1-alpha)*zeta(alpha)^2 on the scale
  n^(alpha-1/2)*log(n). This extends the obstruction beyond the Gamma cone.

All three are dependency-closed PAPER results, not Lean theorems. C27's
positive survivor must be formalized before retiring C26. C29 depends
on the complete C17 paper profile, not only its current G5–G7 Lean pieces.
Scientific novelty remains uncertified. Unrestricted C15 and the actual
linear spectral-deficit goal remain ACTIVE/UNSOLVED.


### Actual rational-kernel inversion and coefficient-tail phase — 2026-10-08

`WeilWorkDeficitGammaKernelMellin.lean` proves six unconditional actual-object
statements: kernel absolute integrability, line-two Mellin absolute
integrability and exact rational transform, global continuity, rational
vertical absolute integrability, and Mellin inversion on positive arguments.
The inversion uses the literal piecewise kernel from GammaKernelJets.
Its vertical bound uses the already-proved zero residue sum and an integrable
C/(1+t^2) envelope. No scientific premise is added.

Leaf build (45s/8786 jobs), final unchanged `lake --old env lean`, and all
six exact-type/axiom audits passed. Final source diagnostics are empty;
axioms are only propext, Classical.choice, Quot.sound. Umbrella wired once.
Thirty-three completed modules /137 public theorem audits. The C23 cosine
transform and actual Xi-density contour shift still await Lean formalization.
This is a classical Mellin BRIDGE, not a scientific novelty claim.

Further dependency-closed PAPER results, all still unformalized:

- C30: continuous nonnegative periodic modulation of a power-law tail on
  the square-root order scale cannot cancel every integer row. The signed
  local convolution can change sign, but the normalized correlation has
  positive Cesàro mean and is positive on a set of positive lower density.
- C31: for arbitrary oscillatory probabilities bounded by C*(k+1)^(-alpha),
  1<alpha<4, a smooth weak transfer identity forces every cancelling
  probability to satisfy X^(-1)*sum_(X<=k<=2X) k^alpha*w_k ->0.
  This does not exclude sparse tails with vanishing weighted block mass.
- C32: for w_k~C*k^(-alpha)*exp(-tau*sqrt(k)), alpha>1,tau>0, the actual
  integer correlations S(n) satisfy
  n^(alpha-1/2)*log(n)*exp(tau*sqrt((pi^2/2)*n))*S(n)
  -> C*(pi^2/2)^(1-alpha)*exp(tau^2/16)*cos(pi*tau^2/32).
  The proof includes the moving Mellin-line estimate, far-head complex
  dilation bound, both order tails and the full divisor sum. Thus tau=4*sqrt(2)
  gives an explicit positive probability with eventually negative rows.
  Cancellation in this asymptotic class requires tau=4*sqrt(2j+1), j>=0;
  no sign or cancellation conclusion is drawn at those exceptional rates.

C29's signed local limit has been corrected to integer arguments; its
absolute bounds remain valid for real arguments. Actual divisor inputs
are integers, so its integer-row conclusion survives.

C33 now asks whether an actual C15 cancelling probability can satisfy
w_k~C*k^(-alpha)*exp(-4*sqrt(k)), or whether all such probabilities are
excluded. Both alternatives remain OPEN. The vanishing C32 leading term
requires a subleading analysis; the known energy equivalent is not an
all-order expansion. Ivić's Gaussian mean-square formula has an O(log T)
remainder too coarse to settle that issue as stated. Scientific novelty
of C30–C32 is not certified. No broader route is retired before its exact
positive survivor is formalized. C15 and the assigned deficit goal remain
ACTIVE/UNSOLVED.

### Exact positive interpolation at the critical tail — 2026-10-08

C34 now has a dependency-closed PAPER proof: for every alpha>1 and every
prescribed sequence of lower thresholds, there is a strictly positive
probability w_k~C*k^(-alpha)*exp(-4*sqrt(k)), C>0, cancelling the ACTUAL
correlation at infinitely many adaptively chosen integer rows. The proof
controls all earlier and later coefficient bands, preserves strict positivity,
and solves the infinite interaction system by an explicit contraction.

C36 strengthens this to any sequence of prescribed finite patterns
floor(N_j+c*sqrt(N_j)), c in C_j. Each finite set C_j is fixed before its
height N_j is chosen; its size may grow with j. A finite weighted Gram
inverse gives actual coefficient controls, and the block contraction pays
every cross-pattern interaction. Classical translate independence is the
parent mechanism. Both results remain unformalized because the full C17/C32
analytic dependencies are still PAPER. Scientific novelty is unestablished.

This does not prove cancellation on consecutive blocks of length sqrt(N),
where the number of constraints depends on the height. That is C35's open
quantitative problem. For the limiting critical operator H(u)=exp(sqrt(pi)*u)
J_a(u), its explicit Fourier multiplier has a simple zero at frequency zero
and Gaussian decay at large frequencies. Nonvanishing elsewhere gives no
bounded inverse. The next construction must price inversion for the actual
arithmetic error, rather than arbitrary data. C33/C15 all-row cancellation
and the main spectral-deficit target remain ACTIVE/UNSOLVED.

### Actual cosine Mellin transform and exact normalization — 2026-10-08

Six further public statements are now formalized. GammaKernelJets proves
rational partial fractions throughout -2<Re(s)<3. GammaKernelMellin proves
absolute weighted admission, the exact rational integral throughout that
strip, and zero total kernel mass. The new GammaCosineMellin module defines
the literal transform B_N(x)=integral phi_N(u)*cos(2*pi*x*u)du and proves
its absolute Mellin transform throughout -2<Re(s)<0. With
q_N(s)=s(s-1)/P_(N+3)(s), the value is

`-(2*pi)^(-s)*q_N(s)*pi/[2*Gamma(1-s)*sin(-pi*s/2)]`.

The actual zero-mass identity permits cosine subtraction; existing absolute
Mellin convolution pays Fubini. No undamped conditional interchange is used.
The exact physical normalization is also proved:

`integral_0^infinity x^(-2)*B_N(x)dx=-2*pi^2/P_(N+3)(-1)`.

All three targeted leaf builds and final unchanged direct
`lake --old env lean` audits passed; final diagnostics are empty. All21
public declarations in the affected modules were re-audited by literal
type and `#print axioms`, with only propext, Classical.choice and Quot.sound.
The six new declarations bring the total to34 modules/143 public theorems.
Umbrella imports occur once. Specialized API audit passed. Formal lint
reports five unrelated reachability errors, none in WP06.

Classification: BRIDGE; scientific novelty unestablished. Positive-strip
continuation, cosine decay, the actual Xi-density contour shift, and full
C23 resonance remain unformalized. The exact transform does not produce
small spectral deficit. Main goal ACTIVE/UNSOLVED.

## G10: exact signed-profile transform and critical simple zero

`WeilWorkDeficitChirpLaplace.lean` proves the absolute complex Laplace
transform of the normalized signed Gaussian saddle profile `j`:

`∫ exp(z*u) j(u) du = exp(z²/π) cos(z²/2)` for every complex z.

Consequences include total mass one, zero mass under the critical tilt
`exp(sqrt(π)*u)`, and the exact real phase
`exp(τ²/16) cos(πτ²/32)` at tilt `τ sqrt(π)/4`. For the critically tilted
Fourier multiplier, the only real-frequency zero is zero itself, and its
complex derivative there is `i sqrt(π) exp(1)`.

All seven public statements have no mathematical hypotheses. Targeted leaf
build, unchanged final direct `lake --old env lean`, and literal-type/axiom
audits passed. Final source log is empty; only standard Lean foundations
occur. Umbrella wired exactly once. Total:35 modules/150 public audits.
Classification: **CLASSICAL ANALYTIC BRIDGE**; no scientific novelty claim.
This does not formalize the actual Xi-kernel saddle limit or its relative
tails, and does not provide a bounded inverse of the multiplier.

C37 now has a paper construction of one strictly positive critical-tail
probability with exact cancellation on arbitrarily long consecutive integer
blocks: each finite length is prescribed before its height is chosen. The
proof pays fixed-order finite differences of the actual kernels and every
past/future block interaction. It does not control length against height.
Full C17/C32/C37 formalization remains owed; scientific novelty remains
unestablished. C35's square-root-length blocks, C33's all-row question,
and the actual spectral-deficit target remain OPEN.

## C38 paper advance: weak transport excludes the alpha>1 critical tail

This supersedes the preceding C33-open entry on PAPER only. For any
probability `w_k~C k^-alpha exp(-4 sqrt(k))`, C>0,alpha>1, and any smooth
compactly supported test psi on the positive line, the actual row average

`X^-1 sum psi(n/X) n^alpha log(n) exp(4 sqrt(kappa*n)) S_w(n)`

has limit

`-C exp(1) kappa^(1-alpha) (alpha-1/4)/sqrt(2) * integral psi`,
where kappa=pi²/2. The proof averages rows before applying the coefficient
asymptotic. No derivative, monotonicity, or convergence rate for w is
assumed, and only the leading E_k asymptotic is used. The first correction
of the actual Mellin saddle, weighted tails, shifted-lattice quadrature,
and full divisor sum are paid in PROOF.md.

Consequently no such probability cancels all integer rows. Every fixed
proportional interval contains a negative row once its height is large;
all-zero block lengths must be o(starting height). C37's arbitrarily long
blocks remain possible, and C35's square-root-length blocks remain open.

The positive survivor is the exact weak transport law. C17/C32/C38 full
Lean formalization remains owed; no route card is retired, and scientific
novelty is unestablished. New C39 tests existence versus nonexistence at
tail `C k^(-1/4) log(k+2) exp(-4 sqrt(k))`; the exponent-range extension
and logarithmic refinement remain conjectural. The unrestricted C15 and
actual spectral-deficit target remain OPEN. Formal counts remain35/150.

## C40/C41 paper boundary: both power and logarithm are forced

The weak critical transport law now extends to every real alpha,delta
for tails `w_k~C k^-alpha (log k)^delta exp(-4 sqrt(k))`. Its row weight
uses `(log n)^(1-delta)` and its limit retains the factor `alpha-1/4`.
Thus all-row cancellation in this entire class forces alpha=1/4.

Keeping every E_k exact gives a further positive survivor: the averaged
renormalized coefficient flux has a finite limit with O(X^-1/8) error.
This forces delta=1, since every other logarithmic power either diverges
or vanishes more slowly than the proved error. Coefficient smoothness,
monotonicity, energy derivatives and subleading energy asymptotics are
not assumed. The complete paper proof is in PROOF.md, C40/C41.

C39 remains OPEN at the surviving shape. C42 proposes an exact positive
candidate whose renormalized coefficient is constant at every order;
its actual integer-row cancellations remain unverified. Full C17/C32/
C38/C40/C41 formalization remains owed. No route retirement or scientific
novelty certification. The spectral-deficit goal remains OPEN.

## G11 verified: global actual Mellin amplitude

`WeilWorkDeficitGlobalMellinAmplitude.lean` proves three premise-free
statements for every derivative order k. With the sigma-four saddle
T=(2k+7)/(pi/2), B=T^(2k+7)*exp(-(pi/2)*T), the literal Mellin integral
of the actual product kernel obeys, for every real height t,

`|M_k(4+it)| <= exp(7*pi/2)*B*exp(-(pi/4)*(sqrt(|t|)-sqrt(T))^2)`.

It is absolutely integrable over all real heights, with total norm at
most `20*exp(7*pi/2)*B*sqrt(T)`. Zero height and both tails are included.
The proof uses exact Gamma reflection and a global square-root Laplace
inequality. No local asymptotic or unstated integrability premise is used.

Targeted leaf build, unchanged final direct `lake --old env lean`, and
all three literal-type/axiom audits passed. Source diagnostics empty;
only `propext`, `Classical.choice`, `Quot.sound`. All36 finished modules
are imported exactly once; total153 public theorem audits. Current
formal lint has five unrelated HTGeometry reachability errors, none in
WP06. No full or umbrella build was run.

Classification: **CLASSICAL ANALYTIC BRIDGE**. This closes a vertical
integrability dependency; the actual critical-line saddle limit, its
differentiated tails, energy asymptotics and C40/C41 formalization remain
owed. No upper spectral-deficit bound or external novelty claim.

## C43 paper advance: constant flux has a negative residual

C42's literal constant-flux candidate fails on PAPER. Its actual row
response is negative somewhere in every sufficiently large fixed
proportional interval. The second weak transport coefficient is
`D=(67-4*pi^2)/96>0`; this includes the actual Gamma correction.

More generally, if the exact C41 flux has expansion
`v_k=v0*(1+d/sqrt(T_k)+o(T_k^-1/2))`, the second weak row limit is
`-v0*pi*exp(1)/2*(D+sqrt(pi)*d/2)*integral(y^-1/2*psi(y))`.
Hence all-row cancellation in this refined class forces
`d=(4*pi^2-67)/(48*sqrt(pi))`. No regularity or derivative of the
coefficients or energies is assumed beyond that stated expansion.
This does not assert every C39 candidate has such an expansion.

The exact transport identity is the positive survivor. Full actual
C17/C32/C43 Lean formalization remains owed; no failed route is retired.
Scientific novelty remains unestablished. C44 adds the forced first
correction to C42, giving a strictly positive probability whose actual
integer responses remain OPEN. C39/C15 and the spectral-deficit target
remain OPEN.

## G12 verified: actual product-kernel inversion

`WeilWorkDeficitProductKernelInversion.lean` proves absolute inverse
Mellin integration, exact recovery of the actual product kernel at every
positive argument, and the explicit spatial bound

`|K_k(x)| <= (10/pi)*exp(7*pi/2)*B_k*sqrt(T_k)/x^4`.

Here T_k=(2k+7)/(pi/2), the sigma-four saddle from G11. All three public
statements have no extra mathematical hypotheses; positive arguments
are the natural domain. Continuity and both inversion integrability
conditions are proved for the literal kernel. Leaf build, unchanged
final direct source audit, and all three exact-type/axiom audits passed.
Source log empty, standard foundations only. Umbrella import exactly
once; total37 modules/156 public theorem audits. Current formal lint
reports seven unrelated reachability errors, none in WP06.

Classification: CLASSICAL ANALYTIC BRIDGE. C43's two finite polynomial
moment identities also passed an auxiliary Lean check; its actual weak
transport theorem remains paper-only. G13 now has a paper proof reducing
critical-line integrability to G11 by the beta-Gamma inequality; its Lean
formalization has not started. No spectral-deficit bound or RH closure.

## G13 verified: actual critical-line inversion and all height moments

`WeilWorkDeficitCriticalMellin.lean` closes absolute vertical integration
on Re(s)=1/2 and exact inverse Mellin recovery of the actual product
kernel. The beta integral gives an all-height comparison with G11's
sigma-four transform. Raising derivative order is exactly multiplication
by an even height power; every natural height moment, including in the
inverse integral, is integrable. All seven public statements have no
extra mathematical hypotheses. Positive x is the natural domain.

Leaf build, unchanged final direct source audit, and all seven exact
public-type/axiom audits passed. Final log empty; only propext,
Classical.choice and Quot.sound. All38 modules imported exactly once;
163 public theorem audits. Current global lint has11 unrelated umbrella
reachability findings and none in WP06. No full/umbrella build.
Classification: CLASSICAL ANALYTIC BRIDGE.

## C45 paper advance: positive actual rows can pass every algebraic-order test

One strictly positive probability w now has a dependency-closed PAPER
construction with, for every M, the actual integer rows satisfying

`|S_w(n)| = O_M(n^-M * exp(-4*sqrt(kappa*n)))`.

The SAME probability works for every M. It has one full critical flux
expansion, including C43's forced first correction. No energy asymptotic
or coefficient regularity is assumed: weights are constructed from
positive angular moments, normalized by the exact actual energies.
G12's spatial bound pays every derivative-order/divisor interchange.

The key law is triangular boundary transport. A density
`u^6*exp(-pi/u)*V(u)` near angle pi/2 has two automatic real cancellations;
its jth smooth Taylor coefficient first changes the real row at order
j+1, with nonzero coefficient `-j*r^(j+1)/2`, r=1/sqrt2. Recursion plus
one positive smooth Borel realization cancels every remaining algebraic
coefficient. C25's angular transport is reused explicitly; arbitrary
positive Taylor series are NOT asserted to be moment mixtures.

This moves the PAPER frontier from one forced correction to one positive
candidate passing all finite asymptotic orders simultaneously. Exact
zero rows are still open: beyond-all-orders errors can remain. Full C45
Lean formalization is owed, as are earlier actual asymptotic survivors.
Scientific novelty remains unestablished against classical transport and
Borel theory. The spectral-deficit goal remains ACTIVE/UNSOLVED.
