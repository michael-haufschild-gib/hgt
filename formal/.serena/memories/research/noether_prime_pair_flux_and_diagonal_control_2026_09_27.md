# Prime-pair energy, arithmetic flux, and diagonal control (2026-09-27)

## Status
Active goal remains proving RH / controlling the FULL signed logarithmic Chebyshev deficit at square-root scale. RH has NOT been proved or falsified. Do not mark goal complete or difficulty-blocked. This batch adds 7 modules and 44 public theorems. All seven leaf modules passed final `lake --old env lean <file> -o <corresponding .olean>` audits; all 44 theorem axiom reports contain only propext, Classical.choice, Quot.sound. No sorry/new axioms/native_decide/#eval/heartbeat changes/numerical experiments. All 7 imports wired exactly once in GaloisForLFunctions/RHTower.lean. No full or umbrella builds, no commit/push/subagents.

Repository /Users/michael/Documents/code/hgt/formal. Preserve concurrent work. One own foreground Lean process at a time. Use direct Lean and formal_tools.py research (no cards).

Previous batch details remain in research/noether_prime_deficit_critical_work_and_scale_descent_2026_09_27.

Let D(t)=ccmLogChebyshevDeficitPrimitive t, E(t)=exp(-t)D(t)^2.
The full bound |D(t)| <= C exp(t/2) is still unproved.

## New sources

### CCMPrimeEntryOverlapKernel.lean (13 public theorems)
Imports only Mathlib.Analysis.SpecialFunctions.Integrals.Basic.
tent(a,t)=max(t-a,0).
K_T(a,b)=integral_0^T exp(-t) tent(a,t) tent(b,t).
K_infinity(a,b)=exp(-max(a,b)) (2+|a-b|).
For 0<=max(a,b), a<=T, b<=T:
K_T=K_infinity-exp(-T)[(T-a)(T-b)+2T-a-b+2].
This retains an essential boundary correction.
K_T>=0 for T>=0, symmetric, <=K_infinity.
K_infinity=exp(-(a+b)/2) * ratioKernel(a-b),
ratioKernel(s)=(2+|s|) exp(-|s|/2), even.
K_infinity(log n,log n)=2/n for n>0.
Exact weighted tent integral:
integral_0^T exp(-t)tent(a,t)=exp(-a)-exp(-T)(T-a+1).
Exact background/tent overlap and background squared energy also proved.

### CCMPrimeDeficitPairEnergy.lean (5 public theorems)
prefix(N,t)=sum_{1<=n<=N} Lambda(n) tent(log n,t).
For t>=0, floor(exp t)<=N:
D(t)=exp(t)-1-prefix(N,t). Future entries vanish exactly.
Pair(T,N)=double sum Lambda(n)Lambda(m)K_T(log n,log m).
Background(T,N)=sum Lambda(n)[(T-log n)^2/2-exp(-log n)+exp(-T)(T-log n+1)].
Literal squared prefix integral equals Pair.
For T>=0, N=floor(exp T):
integral_0^T E = exp(T)-exp(-T)-2T-2 Background(T,N)+Pair(T,N).
No correlation discarded.

### CCMPrimeDeficitFluxBalance.lean (9 public theorems)
Incoming r(t)=exp(-t/2)D(t).
Constructed state h(t)=exp(t/2)[gamma+1-integral_0^t exp(-s)D(s)ds].
Outgoing o(t)=h(t)-r(t).
All three are continuous; r^2=E and h(0)=gamma+1.
h'=h/2-r EVERYWHERE (D is continuous).
(h^2)'=o^2-E EVERYWHERE.
For every finite a,b:
integral_a^b o^2 - integral_a^b E = h(b)^2-h(a)^2.
Consequently for every T:
integral_0^T E <= integral_0^T o^2 +(gamma+1)^2.
This is actual arithmetic flux/storage balance, not an assumed conserved positive mechanical energy.

### CCMPrimeDeficitWeilFlux.lean (4 public theorems)
Exact finite integration of weighted common prime prefix.
For T>=0, N=floor(exp T):
integral_0^T exp(-t)D(t)dt = T-mertensSum(N)+exp(-T)[psi(exp T)-D(T)].
Thus
o(T)=exp(-T/2)[exp T-psi(exp T)+exp T(mertensSum(N)-T+gamma)].
For T>0, identification with ACTUAL existing Weil lag Phi:
o(T)=weilLagFunctionReal T + exp(-T/2)[log(2*pi)-trivialZeroSeriesReal(exp T)].
Full archimedean correction retained. Note S(1)=1-log2 (not twice that).

### CCMPrimeDeficitFluxBoundary.lean (3 public theorems)
Mertens theorem with Euler constant and PNT give, unconditionally:
lim_{T->infinity} integral_0^T exp(-t)D(t)dt = gamma+1.
Hence exp(-T/2)h(T)->0.
For EVERY real T:
lim_{U->infinity} integral_T^U exp(-(t-T)/2)r(t)dt = h(T).
This proves the actual future convolution limit and excludes the growing homogeneous state term. This module proves convergence of finite improper integrals; it does NOT add an IntegrableOn/absolute-integrability theorem. Do not silently assert one from the limit alone.
Uses existing WeilLagFunctionFrontier.mertensSum_eq_Icc_zero and MertensVonMangoldtEulerConstant.tendsto_real_sum_vonMangoldt_div_sub_log, tendsto_chebyshevError_div plus prior D/exp limit.

### CCMPrimeDeficitWeilEnergy.lean (4 public theorems)
Let A=|log(2*pi)|+1.
For t>0, |o(t)-Phi(t)|<=A exp(-t/2), squared difference<=A^2 exp(-t).
For T>=0, integral_0^T (o-Phi)^2<=A^2.
Actual unconditional full energy comparison:
integral_0^T E <= 2 integral_0^T Phi(t)^2 dt +2A^2+(gamma+1)^2.
No bound on the lag energy itself is assumed/proved.

### CCMPrimeDeficitDiagonalControl.lean (6 public theorems)
Diag(T)=sum_{n<=floor(exp T)} Lambda(n)^2 K_T(log n,log n).
CenteredOff(T)=expT-exp(-T)-2T-2 Background(T,N)+(Pair(T,N)-Diag(T)).
For T>=0:
0<=Diag(T)<=2*Sieve.vonMangoldtHarmonicSquareSum(N)<=T^2+78T+50.
Uses existing sharp harmonic square moment asymptotic, including all prime-power weights.
Exact split integral_0^T E=Diag(T)+CenteredOff(T).
For T<log2, Diag(T)=0.
For 0<T<log2, CenteredOff(T)>0, using strictly positive initial deficit energy.
This rigorously rejects the candidate global sign CenteredOff<=0. It does NOT reject a fixed positive upper budget.

## Mathematical next target
Try to PROVE an actual fixed upper bound CenteredOff(T)<=C (or another polynomial/subexponential upper estimate), preserving continuous background and signed mixed work. Do not replace it by an assumed premise and claim square-root control.
Quadratic diagonal growth is NOT an RH obstruction. Under RH one expects integrated E=O(T) while Diag is roughly T^2, so centered correlations must cancel most of the diagonal. A polynomial integrated E estimate can plausibly feed Laplace continuation to RH; this batch has NOT formalized that receiver for D, nor proved the needed correlation estimate.
The stronger CenteredOff<=0 conjecture failed symbolically in the prime-free chamber; the next candidate needs a finite positive allowance.
Equivalent algebraic candidate with budget (gamma+1)^2:
integral_0^T o^2 <= h(T)^2+Diag(T).
This is only a CONJECTURE, not proved. General conservation or PNT alone cannot supply critical control; actual arithmetic correlations must be used.
Future filter interpretation: for exponential mode exp(lambda t), transfer r->o has factor (1/2+lambda)/(1/2-lambda). It preserves magnitude for purely imaginary lambda, can amplify positive real part. This observation is not formalized in this batch and does not exclude growing arithmetic modes by itself.
Relevant existing RH receiver: riemannHypothesis_of_regularizedCriticalMellinDefect_extension, or WeilLagFunctionPositivePart.riemannHypothesis_of_lagPositivePart_integral_subexponential. Do not confuse other Mobius source energy criteria with this D without an exact bridge.

## Validation / cleanup
All seven .olean objects checked newer than source after final audits.
A scratch importer printed axioms for all 44 public theorems and passed using plain lake --old env lean. Every report standard 3 axioms only.
Another process's targeted shared rebuild temporarily removed imported .olean files. To avoid repeated races, temporarily hard-linked existing imported objects into a task-owned LEAN_PATH FALLBACK; only WeilFlux/FluxBoundary needed this during leaf audits. Final 44-theorem axiom audit used normal import paths after the external build ended. All fallback hard links and own audit scratch/log were removed. No live own Lean/build sessions remain after this batch.
Index refreshed twice (second exit0, 0 source changes, regenerated metadata after race).
Last repository lint failed on UNRELATED unwired concurrent modules:
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, XiGaussianNormalizedOrbit, XiGaussianNormalizedOrbitTail, ZetaZeroDensityPowerSaving, HTGeometry.GammaHalfIntegerLineBound.
It also reported stale LEAN_OVERVIEW; index was refreshed afterward. Do not claim global lint passed. Own 7 imports each present once; git diff --check for umbrella passed.

## Lean proof details
- intervalIntegral.continuous_primitive needs explicit lower endpoint 0 when used as a term.
- Type interval-integrability of fun t => f t ^2 explicitly; a Pi.pow function can prevent rw integral_sub matching.
- dsimp only [local_def,...] handles beta-redexes under integral_congr; unfold alone can leave (fun x => ...) t that rw misses.
- exp_nat_mul leaves Nat casts: normalize Nat.cast_ofNat before exact exponent rewrite.
- For multiplying exp cancellation by a symbolic expression, factor then rw; nlinarith from the unmultiplied identity alone need not infer higher-degree products.
- No heartbeat changes or computation tactics used to hide missing mathematics.
