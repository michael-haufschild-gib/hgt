# Exact factorial ramp prime-log diagonal (2026-10-18)

Goal remains unconditional RH in Lean; NOT achieved. The actual optimized ramp diagonal A - M^2/(4D) is still not proved nonnegative. Parent card stays `docs/drafts/pipeline/1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md`. Completed exact-identity child is `docs/drafts/pipeline/3-formalized/factorial-ramp-prime-log-diagonal-2026-10-18.md`.

Four new leaves, all under `formal/GaloisForLFunctions/BiScaleUncertainty`, all public theorems in namespace `GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar`:

1. `ClampedPrimeLogResummation.lean` (6 public theorems).
   - `weighted_prime_rectangle_eq_log`: if K <= M and w k = 0 for k > K, then sum_{m=1}^M Lambda(m) sum_{j=1}^K w(j*m) = sum_{k=1}^K log(k)*w(k). Exact divisor-fibre resummation using sum_{d|k} Lambda(d)=log(k).
   - `clampedPrimeFactorialSum_eq_log`: exact logarithmic sum, including collar endpoints, when (1+epsilon)*v <= K+1.
   - `logWeightedFactorialLift epsilon K u` = exp(u/2) sum_{j=1}^K log(j)*clampedRamp epsilon (j*exp(u)/K), with continuity.
   - `atomic_smoothFactorialLift_eq_log`: actual atomic field equals this lift for epsilon>0, u>=0, K>=1, K<=M, epsilon*K<=1.
   - `factorialRampLogField n` is the normalized 1,-4,4 combination at scales 4N,2N,N, N=n+1, with the actual source collar.
   - `atomicSource_factorialRamp_eq_log`: actual ramp atomicSource equals this field for u>=0 and 4N<=K+2. No arithmetic hypothesis or new positivity premise.

2. `CompactAutocorrelationPolarMoment.lean` (1 public theorem).
   `integral_polar_autocorr_eq_moments f` for every real continuous compactly supported f:
   integral_{x>=0} polarDensity(x)*autocorr(f)(x) = (integral exp(u/2)*f(u))*(integral exp(-u/2)*f(u)). Both polar branches are present. Proof uses paperFT_weilTest and evenness; no C^2/finite-jump premise.

3. `FactorialBiNullPolarSign.lean` (5 public theorems).
   - `chebyshevBiNullProducer_eq_log_binomial`: C_N = log choose(4N,2N) - 2*log choose(2N,N).
   - `chebyshevBiNullProducer_nonneg`: C_N>=0 for every natural N, by Vandermonde and the central summand.
   - For actual factorialRampSource n, N=n+1, epsilon its source collar, H_N=harmonicCorrection N:
     P_N := integral_{x>=0} polarDensity(x)*autocorr(f)(x) = -(1+epsilon/2)*H_N*C_N/N.
   - `integral_polar_autocorr_factorialRamp_nonpos`: P_N<=0.
   - `abs_integral_polar_autocorr_factorialRamp_le`: |P_N| <= 2*(5*log(4N+1)+1)/N.
   The actual polar contribution lowers this diagonal. Its O(log N/N) upper envelope cannot by itself justify dropping it into the smaller Gram-error envelope O(log^2 N/N^2).

4. `FactorialRampDiagonalIdentity.lean` (7 public theorems).
   - Integrability of f*factorialRampLogField.
   - Actual autocorrelation vanishes for x>=log(4N+1).
   - Exact finite prime quadratic sum and literal infinite prime sum both equal I_N := integral f(u)*factorialRampLogField(n,u).
   - `fullPairing_autocorr_factorialRamp_eq_log`: fullPairing(autocorr f)=I_N+(1+epsilon/2)*H_N*C_N/N.
   - Reflection identity for factorialSourceLeft autocorrelation.
   - `factorialSpanWeil_ramp_eq_log`: the literal actual A_n=factorialSpanWeil n 1 0 equals gammaBracket(0)*autocorr(f)(0)+biScaleLevyEnergy(f)-2*I_N-2*(1+epsilon/2)*H_N*[log choose(4N,2N)-2 log choose(2N,N)]/N.
   This is a genuine unconditional formula with prime weights eliminated, not a hypothesis wrapper. Its sign is NOT proved.

Verification completed:
- All 4 direct leaves compiled using `lake --old env lean -j 1`; logs `/tmp/bsu-<ModuleName>.log` all empty.
- All 19 public theorems individually audited in `/tmp/biscale_ramp_diagonal_axioms.lean`, log `/tmp/bsu-ramp-diagonal-axioms.log`; every theorem uses only propext, Classical.choice, Quot.sound.
- Complete source hashes/theorem coverage and results: `/tmp/bsu-ramp-diagonal-verification.json`.
- All 4 imports wired into `formal/GaloisForLFunctions/BiScaleUncertainty.lean`.
- `scripts/formal_tools.py index` passed, log `/tmp/bsu-ramp-diagonal-index.log`.
- Global `lint --check-generated` exited 1 on FOUR unrelated missing area imports: EndpointCycleDeterminant, SharpCycleGramRealization, SharpGramDetectionOrder, StationaryResolventMarkovPositivityAndNodalDefectProducer. No error named these four leaves. Full lint log `/tmp/bsu-ramp-diagonal-lint.log`. Do not report global lint as passed.

Cache issue and cleanup:
A separate `lake build ...StationaryResolventMarkovPositivityAndNodalDefectProducer` repeatedly removed/rebuilt required dependency objects during our direct checks. Direct restoration of unchanged DivisorSliceFixedPart and WeilPositivityFiniteLevelExistence passed. To finish, 8,737 existing dependency objects were copied with APFS clone copies into an owned /tmp cache, and the final leaf plus axiom audit used `--setup` with explicit ModuleSetup.importArts paths. Header imports and options were retained. Appending LEAN_PATH alone does NOT work: Lean chooses one root per package, not a fallback per missing module. The preserved cache was removed after successful checks. No dependency source edits, no umbrella/full build, one own Lean process at a time. All own Lean jobs have finished. Setup JSON files now refer to the removed temporary cache; recreate paths if needed rather than reusing those files blindly.

Source-level follow-up search:
`/tmp/bsu-ramp-copoisson-boundary-search.json` is partial: source retrieval interrupted, decomposition disconnected, semantic coverage unmeasured, background index refresh incomplete. Inspected source: BurnolCoPoissonIndicatorSeed proves actual L2 integrability, not a Weil truncation bound; BurnolCoPoissonRawZeroAnnihilator annihilates only the raw source closure at a right-strip zeta zero, not the cosine-closed enlargement; deningerContinuousEnergy_zero_on_boundaryClosure assumes the needed continuity and vanishing. None was applied as a Lean dependency here. Do not identify this factorial ramp with a co-Poisson/theta kernel or pass the full Weil form through an L2/pointwise Mellin limit without the missing proofs.

Lean API pitfalls already resolved:
- `factorialRamp_full_moments` gives interval integrals, despite its name. Convert with `factorialRamp_integral_eq_interval n weight` before using whole-line moments.
- `integral_comp_abs` is root namespace. `integral_zero` needs explicit domain/codomain (`integral_zero ℝ ℝ`). `integral_neg_eq_self` needs explicit volume.
- In support rewrites specify `(u := u+x)`; otherwise rw may target the wrong occurrence.
- Expose both integrands with `change` before pointwise zero simplification.
- Space after absolute-value syntax (`|x| * ...`) avoids tokenizing `|*`.

Next mathematical objective: prove an actual coupled archimedean/logarithmic/polar lower bound strong enough for A_n >= factorialWeilGramError n, or directly A_n-M_n^2/(4D_n)>=0. Prior Gram decoupling is in `mem:biscale/factorial-weil-gram-decoupling`. Neither A_n>=0 alone nor polar decay alone closes this objective. RH remains unproved.