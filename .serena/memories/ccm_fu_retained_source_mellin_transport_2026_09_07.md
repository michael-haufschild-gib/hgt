# CCM-FU retained-source Mellin transport — COMPLETE bridge, RH OPEN

Active unbudgeted /goal: unconditional kernel-checked RH proof/falsification via CCM-FU. Full chain: Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH. This goal turn made substantial progress: 43 new public declarations, five modules, exact arithmetic and continuous Mellin transport. Do not mark goal complete or blocked. SD1, PE4/PE4G/PE4C, arbitrary finite retained cone fullness and exhaustive uniform cofinal source coverage remain OPEN.

## Validation — do NOT repeat
All five modules passed scratch development and exact-file `lake env lean` checks. Only their five needed oleans emitted with `lake env lean -o ... file`. All 43 public declarations axiom-audited ONCE via /tmp scratch: only propext, Classical.choice, Quot.sound. Global formal lint PASS (existing large-file warnings). `formal_tools.py index` refreshed generated Lean API/gaps/overview and search index. All five imports unique in RHTower umbrella, never built. Own links/whitespace passed. No numerics/RunPod run, no computational proof premise. Exact arithmetic identities and convolution mechanism are predictable; do not run experiments for them. All owned Lean processes completed; scratch/log cleanup at end. Other users/tasks edit and commit shared tree, including updating frontier from our files, so use fresh narrowly scoped doc substitutions; do not revert others or kill their processes. No commits by us.

Paper/certificate: docs/drafts/pipeline/3-formalized/ccm-fu-retained-source-mellin-transport.md. Open card: docs/drafts/pipeline/1-in-progress/ccm-fu-finite-source-cone-exhaustion.md. Frontier/current state, adaptive-prime-ceiling, earlier spectral paper remaining-gates, universal STATUS updated. New universal entry MUST-TRANSPORT-DISCRETE-SIGNS-TO-CARRIERS. Older completed 28 declarations in mem:ccm_fu_finite_retained_spectral_separation_2026_09_07; never recheck them.

## Exact new APIs — namespace RHTower
Files under formal/GaloisForLFunctions/RHTower.

### RetainedPrimeMobiusEulerIdentity (17 public)
`retainedPrimeMobiusCoefficient P y n := (mu n:Complex)*y(n.primeFactors ∩ P)` — complete infinite source, P:Finset Nat, y:Finset Nat→Complex. P need not all primes for coefficient bound/recursions where not explicitly required.
`primeSourceDilation p f n := if p∣n then f(n/p) else0`.
`LSeries_primeSourceDilation hp f hf0 s`: hp:0<p, hf0:f0=0 ⇒ L(dilation)=p^(-s)*L(f), no summability assumption necessary.
`primeFreeSourcePart p f n := if p∣n then0elsef n`.
Zero simp lemmas for both coefficient/freepart.
`retainedPrimeMobiusCoefficient_mul_prime P y hp hpP hpn`: p prime, p∉P, p∤n ⇒ coefficient(p*n)=−coefficient(n).
`..._mul_prime_of_dvd P y hp hpn`: p∣n ⇒ coefficient(p*n)=0.
`..._eq_primeFree_sub_dilation P y hp hpP` exact old sequence recursion.
`..._insert_eq_primeFree_sub_dilation P y hp` exact inserted P recursion with y and R↦y(insert p R); does NOT need hpP.
`norm_retainedPrimeMobiusCoefficient_le P y n`: norm≤ΣR∈P.powerset norm(yR).
`LSeriesSummable_retainedPrimeMobiusCoefficient P y hs` for Re(s)>1.
`one_sub_cpow_mul_LSeries_retainedPrimeFree P y hp hpP hs` and `..._retainedPrimeMobius_insert` matching infinite recursions.
`retainedPrimeDirichletNumerator_insert P hP y hp hpP s` finite numerator recursion.
`prod_euler_mul_LSeries_retainedPrimeMobiusCoefficient P hP y hs` ⇒ E_P*L=P_y/zeta.
**`LSeries_retainedPrimeMobiusCoefficient_eq P hP y hs`** ⇒ L(f_y,s)=finiteDirichletPolynomial(retainedPrimeDirichletCoefficients P y)s / (riemannZeta s * ∏p∈P,1−p^(-s)), Re(s)>1.

### RetainedPrimeDivisorConvolution (11 public)
`retainedPrimeMobiusAF P y : ArithmeticFunction Complex` is the coefficient above.
`retainedPrimeDivisorConvolution P y := retainedPrimeMobiusAF P y * halfSelectionDivisorSourceAF`. Despite old name, halfSelectionDivisorSourceAF is the GENERIC complex lift of literal primeFreeDivisorIncrementAF. No need recreate it.
`LSeriesSummable_retainedPrimeDivisorConvolution P y hs` Re(s)>3/2.
`LSeries_retainedPrimeDivisorConvolution_eq_product P y hs`: Lconv=LweightedMu*divisorSourceDirichlet.
`sum_retainedPrimeDivisorConvolution P y N`: sum n∈Icc1N convn =sum d∈Icc1N f_y(d)*(D(N/d):Complex).
`retainedPrimeSourceMean P y M := sum d∈Icc1M y(pf(d)∩P)*(mobiusDivisorDilationChannel M d:Complex)`.
**`retainedPrimeSourceMean_eq_convolution_abel P y M`**: exact Σk∈Icc1(M−1) (sqrt(k+1)−sqrt k)*Σn∈Icc1k convn, including all clipped endpoints. Not yet formally grouped into mobiusDivisorSelectionFibre; actual all-channel pairing is exact by definition.
`LSeries_completedPrimePolarGammaAtom hs`: Re(s)>1, Lactualatom=−zeta'/zeta−zeta+2gamma.
`divisorSourceDirichlet_div_zeta_eq_completed_source hs`: Re(s)>3/2, Dseries/zeta = simplePrimeDivisorContinuedSource(s+1/2)+2gamma.
**`LSeries_retainedPrimeDivisorConvolution_eq_completed_source P hP y hs`**: Lconv(s)=P_y(s)*(simplePrimeDivisorContinuedSource(s+1/2)+2gamma)/E_P(s), Re(s)>3/2.
**`retainedPrimeDivisor_normalized_LSeries_eq_Mellin Q y hs`** Q:Finset Nat.Primes, P=Q.image(fun p:Nat.Primes=>(p:Nat)), hs:2<s.re; Lconv(P,y)(s−1/2)/(2*s*(s−1/2))=finiteDirichletDivisorMellin(retainedPrimeDirichletCoefficients P y) Q (2gamma) s.

### SquareRootSummatoryMellin (8 public)
Imports old SuzukiMellinConvolution and StepProfileMellinLSeries, whose needed oleans existed.
`mellinRayOne := (Set.Ioi(1:Real)).indicator(fun _=>1:Real→Complex)`.
`hasMellin_mellinRayOne hs`: Res>0 ⇒ HasMellin rayOne (−s) (1/s).
`squareRootSummatoryProfile b := Ioi1.indicator(fun x => (x:Complex)^(1/2)*(Σn∈Icc1 floorx,bn)/2)`.
`measurable_squareRootSummatoryProfile b`.
`hasMellin_squareRootSummatoryProfile hC hb hs hθs hsum`: summatory norm≤C*N^θ, C≥0, Res>1/2, θ<Res−1/2, LSeriesSummable b(s−1/2) ⇒ Mellin at−s = Lb(s−1/2)/(2*(s−1/2)).
`squareRootSummatoryPrimitive b := positiveMellinConvolution (squareRootSummatoryProfile b) mellinRayOne`.
**`hasMellin_squareRootSummatoryPrimitive`** same hypotheses ⇒ HasMellin primitive (−s) [Lb(s−1/2)/(2*s*(s−1/2))]. Includes ABSOLUTE integrability, proved with existing Mellin convolution product, no new Fubini engine.
**`squareRootSummatoryPrimitive_eq_integral b x`** every real x: H(x)=∫t∈Ioo1x, ((t:Complex)^(1/2)/(2*t))*Σn∈Icc1 floor(t),bn. Hence H=0 below1 and actual sqrt-weighted primitive above1.

### RetainedPrimeSourceMellin (2 public)
**`norm_sum_retainedPrimeDivisorConvolution_le P y N`** unconditional allP,y,N:
‖Σn∈Icc1N convn‖ ≤ (24*ΣR∈P.powerset‖yR‖)*N^(3/2).
Uses finite coefficient bound, literal |D(N/d)|≤24sqrtN, N-term sum. No assumed source growth.
**`hasMellin_retainedPrimeSourcePrimitive Q y hs`** Q:Finset Nat.Primes, P=image Nat, hs:2<s.re ⇒
HasMellin (squareRootSummatoryPrimitive (retainedPrimeDivisorConvolution P y)) (−s)
 (finiteDirichletDivisorMellin (retainedPrimeDirichletCoefficients P y) Q (2gamma) s).
This is the SOURCE-SPECIFIC exact absolutely convergent Mellin identity, not a candidate. Re(s)>2 suffices for germ at4; don't waste work sharpening initial domain.

### RetainedPrimeSourceInterpolation (5 public)
Imports RetainedPrimeSourceMellin plus mathlib AbelSummation, Sqrt, Complex.RealDeriv.
Private sqrtIntegrationKernel x=(1/(2sqrtx):Real):Complex. Private continuity/integrability and FTC; public statements hide private definitions.
**`squareRootSummatoryPrimitive_nat b M`** H(M)=Σk∈Icc1(M−1) (sqrt(k+1)−sqrtk:Complex)*Σn∈Icc1k bn, everyM incl0/1.
**`squareRootSummatoryPrimitive_between b hk hkx hxk`** hk:1≤k, k≤x≤k+1 ⇒ H(x)=H(k)+(sqrtx−sqrtk:Complex)*Σn≤k bn.
**`squareRootSummatoryPrimitive_re_nonneg b hN hx`** hN:∀N0≤H(N).re, hx:1≤x ⇒0≤H(x).re. Exact affine monotone-clock proof, no positivity of coefficient slope needed.
**`squareRootSummatoryPrimitive_retained_nat P y M`** Hconv(M)=retainedPrimeSourceMean P y M.
**`retainedPrimeSourceMean_re_nonneg_ray P y hN hx`** nonnegative real integer source means ⇒ nonnegative real primitive on whole ray. Does NOT assert such nonzero y exists.

## Next actual mathematical work
Need positive measure/MGF and pole contradiction before asserting arbitrary finite cone fullness. For real y, H_y should be real; prove this from literal source means and interpolation (or real convolution coefficients). Source mean with complex lift of real y is manifestly real. Can derive reality of slope from the two endpoint values and nonzero sqrt step; then Hreal on ray. Positivity comes from new retainedPrimeSourceMean_re_nonneg_ray under hypothesized one-sided functional.
Use carrier centered at4: μ=(volume restricted to Ioi1).withDensity(ENNReal.ofReal(H_y(x).re*x^(-5))), X=logx. Need 0 interior integrableExpSet X μ; source HasMellin for Res>2 gives all real tilts near0. Identify complexMGF X μ z=M_y(4−z) in a germ at0 by exact exponential/cpow algebra and integral-withDensity transport. Old `LandauIntegralTransfer.landau_complexMGF_integrable_transfer` takes X≥0 a.e., 0 interior integrableExpSet, G differentiable closedBall0R, Ggerm=complexMGF, 0≤rho<R. Old finiteDirichletDivisorPoleSurvival gives G(z)=M(4−z) differentiable closedBall0R for every R<7/2. Thus all real tilts<7/2 integrable and MGF analytic on Re z<7/2. Establish identity with meromorphic M throughout Re s>1/2; high surviving poles at s=1+it contradict analyticity. This gives no nonzero one-sided y, then finite-dimensional separation/compactness yields cutoff witnesses and uniform margin for FIXED P. Need bind literal retained field to existing mobiusDivisorSelectionFibre (its label is pf(d)\processed, while ours is pf(d)∩retained; processed=activePrimes\retained). Full cofinal coverage as P changes remains a separate hard gate even after fixed cone proof.

## Efficiency / API pitfalls learned
- Only one owned foreground Lean process. No umbrella builds, no repeat audits of completed modules, no independent agents absent explicit delegation. No numerics this turn; mandatory experiments only bounded surprising RunPod ones per scientific-method.md already read.
- `ArithmeticFunction.LSeries_mul'` MUST supply `(f:=...) (g:=...)` explicitly or coercion unification deterministically times out isDefEq200000. Don't raise heartbeats.
- Q.image needs `(fun p : Nat.Primes => (p:Nat))`, otherwise elaboration may infer domainNat and rejectQ.
- Division nesting use `rw [div_div]` instead of ring, which expands denominators and may fail equality.
- In pointwise set/interval integral congruence goals, `dsimp only` before rw to beta-reduce fun application. Unpack ht.1 before linarith (membership opaque to linear arithmetic).
- `intervalIntegral.sum_integral_adjacent_intervals_Ico` requires `(μ:=volume)` to avoid stuck NullSingletonClass; its hint membership hk is Set.Ico, use hk.1, not Finset.mem_Ico.
- Nat.measurable_floor and measurable_of_countable are exact names. Complex cpow_add y z hx0. HasDerivAt.ofReal_comp handles sqrt toComplex.
- Indicator Mellin simp creates a fresh IntegrableOn layer; a SECOND simp only [IntegrableOn, Measure.restrict_restrict_of_subset hsubset] removes nested restriction.
- `field_simp` without supplied cast nonzero proofs won't clear denominators. For sqrt ratios use div_eq_div_iff and 2*cast(sq_sqrt).
- Never huge glob all RHTower lean files or unbounded Mellin grep (corpus massive). Research fts no-refresh for discovery, then targeted reads.
- Serena manual was read and remains applicable; task memory list structuredContent.result is JSON STRING, parse before filter, never dump all memory names.
