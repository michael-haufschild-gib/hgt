# Divisor source, reciprocal reflection, uniform correlation bound

Active RH goal remains ACTIVE and UNPROVED. This turn proves an actual auxiliary signed cancellation estimate, not the full Möbius-signed square-root deficit bound. Continue from `mem:research/noether_short_quadratic_reconstruction_and_source_matrix_2026_09_27` and `mem:research/noether_coprime_signed_balance_and_row_control_2026_09_27`.

## Verification / ownership
Repo `/Users/michael/Documents/code/hgt/formal`. Added eight modules below; modified `LogarithmicEntryIntegration.lean` to support merely interval-integrable forces while preserving continuous wrappers. 37 new public theorems (35 in new modules + 2 generalized entry-integral theorems). All nine changed/new leaves checked with foreground `lake --old env lean FILE -o .lake/build/lib/lean/...olean`, one own Lean process at a time. Final outputs exit 0 without warnings. All objects fresh, each module wired exactly once into `GaloisForLFunctions/RHTower.lean`. No full/umbrella build, no sorry/custom axioms/numerical experiments/heartbeat increase.

Final scratch `DivisorReflectionAudit.lean` imported final leaf and #print axioms for all 37 new plus 2 preserved wrappers: 39 checks exit 0, each only `[propext, Classical.choice, Quot.sound]`. Scratch audit deleted. No own live process. Metadata index refreshed, then refreshed once after concurrent race. Last lint --check-generated reports ONLY 20 unrelated unwired modules (other chats), no stale generated-file errors. Do not claim whole repository clean or wire unrelated unfinished modules. Preserve prior cast fix in LogarithmicMobiusShortReconstruction: `(a * b : ArithmeticFunction ℝ)` must remain typed arithmetic convolution, not coerced pointwise function multiplication.

## Exact source
1. `LogarithmicDivisorDilation.lean` (3 theorems):
- sum_log_divisors_eq_half_card_mul_log: sum_{d|n} log d = tau(n) log n / 2, all natural n including0.
- logarithmicDilationSum_twice_eq_divisor_weighted: Z(Z f)=tau-weighted dilation f.
- logarithmicDilationSum_log_weighted: Z(log-weighted dilation f)=(tau(n)logn/2)-weighted dilation f.
Proof uses Nat.sum_divisorsAntidiagonal and complementary divisor pairing, no heavier sieve cardinal import.

2. `CCMPrimeDeficitDivisorSource.lean` (4 theorems):
H(T)=ccmPrimeDeficitDivisorSource T = expT sum_{n<=expT}tau(n)/n - sum tau(n) - (1/2)sum tau(n)logn(T-logn).
Proves Z G=H; equivalently sum tau(n) D(T-logn)=H(T), all realT. Exact actual short B(T)=2 P_U(T)-sum_{a,b<=U}mu(a)mu(b)H(T-log(ab)), U=floor exp(T/2), T>=0. Thus complete divisor source now explicit and retains real signs/main terms.

## Integrable quadrature infrastructure
`LogarithmicEntryIntegration.lean`: added intervalIntegrable_mul_logarithmicEntrySum_of_intervalIntegrable and integral_mul_logarithmicEntrySum_of_intervalIntegrable. Existing Continuous versions delegate to these. Reuses indicator/common-prefix proof, no duplicate whole machinery.

3. `LogarithmicDilationPrimitiveQuadrature.lean` (4 theorems):
For g interval-integrable on0..T, T>=0:
Z (u -> integral_0^u g)(T) = integral_0^T g(T-s) floor(exp s) ds
= expT integral_0^T exp(-t)g(t)dt - integral_0^T g(T-s)fract(exp s)ds.
Also proves integrability of reverse force times fractional part. API pitfalls: global `natCast_floor_eq_intCast_floor`, not Nat namespace; explicit f needed in integral_comp_sub_left when integrand is product; beta reduce integrands using dsimp only before rw.

4. `CCMPrimeDeficitDivisorQuadrature.lean` (4 theorems):
g(t)=ccmPrimeDeficitCenteredDilationForce t=F(t)-(gamma+1)exp t+c, c=log(2pi)/2.
kappa_T=ccmPrimeDeficitDivisorMainCoefficient T=integral_0^T exp(-t)g(t)dt.
W(T)=ccmPrimeDeficitDivisorFloorWork T=integral_0^T g(T-s)fract(exp s)ds.
Actual R=ccmPrimeDeficitDilationRemainder, R=int g. Proves ZR=expT kappa_T-W. Initial |W|<=T^2/4+2T; improved below. kappa_T is TIME DEPENDENT; do not present as an already proved fixed limiting coefficient.

## Uniform reciprocal correlation: genuine new corpus estimate
5. `LogarithmicSawtoothCorrelation.lean` (6 theorems):
b(t)=logarithmicCenteredSawtooth t=fract(exp t)-1/2.
C(T)=logarithmicReciprocalSawtoothCorrelation T=integral_0^T b(T-s)b(s)ds.
Measurability/integrability and |b|<=1/2. Reflection exactly removes variable weight:
integral_0^T (T-s-1)b(T-s)b(s)ds=(T-2)C(T)/2.
Initial |C(T)|<=T/4. Reflection is discrete algebraic symmetry; no new Noether theorem claimed.

6. `LogarithmicSawtoothTail.lean` (3 theorems):
For k>=0,a<=b:
|integral_a^b exp((1-k)t) b(t)dt| <= exp(-k a)/4.
Specializations: |int_a^b b(t)dt|<=exp(-a)/4;
|int_a^b exp(-t)b(t)dt|<=exp(-2a)/4.
Proof private continuous primitive q_k(t)=exp(-kt)bernoulliPeriodic(exp t), right derivative exp((1-k)t)b(t)-k q_k(t), |q_k|<=exp(-kt)/8. Uses ArithmeticClockFirstVariation's right derivative and interval FTC. Preserves signed cell cancellation before bounding, no numerical evidence.

7. `LogarithmicSawtoothCorrelationBound.lean` (2 theorems):
C(T)=2 integral_0^{T/2} b(T-s)b(s)ds, all realT.
For T>=0, **|C(T)|<=5/4** (line43).
Proof on H=T/2 decomposes b(s)=exp s-floor(exp s)-1/2. Smooth weighted term <=1/4 by exp-weighted tail bound. Full floor-entry sum <=1/4: at most expH terms, each signed tail <=exp(-(T-H))/4, and expH*exp(-(T-H))=1. Constant term <=1/8. Half correlation<=5/8; double<=5/4. This is an unconditional uniform bound for this actual reciprocal sawtooth kernel.

## Application back to actual divisor source
8. `CCMPrimeDeficitDivisorReflection.lean` (9 public theorems):
J(T)=ccmPrimeDeficitReciprocalErrorWork T=integral_0^T ForceError(T-s)b(s)ds.
Uses previous |ForceError(t)|<=3exp(-t). Proves |J(T)|<=3/2.
Exact reflection:
W(T)=R(T)/2+(T-2)C(T)/2+J(T).
Thus **ZR(T)=expT kappa_T-R(T)/2-(T-2)C(T)/2-J(T)** (line110).
Absolute reflected error <=3/2.
Combining previous |R|<=7/2, new |C|<=5/4, |J|<=3/2:
**|W(T)|<=5T/8+9/2**, hence **|ZR(T)-expT kappa_T|<=5T/8+9/2**.
Actual explicit divisor source connection (allT):
H(T)-(gamma+1)Z(exp-1)(T)+c Z(id)(T)=ZR(T).
Therefore same linear centered bound for H (line177). This sharpens source-level quadratic error to linear. It DOES NOT prove B(T)=O(exp(T/2)), nor RH.

## Next mathematical target
Keep working on actual B=2P_U-sum mu_a mu_b H(T-logab); keep explicit main terms coupled. New reflection identity and uniform C are ingredients, not a bound on the signed double sum. Taking absolute values over all U^2 matrix entries loses target scale. Earlier source matrix determinant=-1 blocks arbitrary-vector PSD arguments, but does not test actual Möbius vector.
Possible concrete continuation: formalize exact finite convolution factorization of the short Möbius sum of reciprocal C into integral F_U(s)F_U(T-s), where F_U(t)=sum_{n<=min(U,exp t)}mu(n)b(t-logn). For t<=logU the full arithmetic identity gives F_U(t)=exp(t)sum_{n<=exp t}mu(n)/n-1-M(exp t)/2. This is an UNPROVED NEXT IDEA here; must search existing corpus, prove finite Fubini/entry cutoffs, and retain main-term cancellations before any estimates. Positivity/large-sieve claims need actual proof; no independent-phase assumption.
Another unproved auxiliary option: replace kappa_T by a fixed improper-integral coefficient using |g|<=t/2+2. Exponential tail gives expT|kappa_infty-kappa_T|<=T/2+5/2 and hence a fixed-coefficient linear source bound. Do not confuse this with solving signed cancellation.
