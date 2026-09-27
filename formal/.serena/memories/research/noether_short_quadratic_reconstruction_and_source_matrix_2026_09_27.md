# Short quadratic reconstruction of full prime deficit (2026-09-27)

## Status and rules
Active goal is actual RH proof; NOT achieved. Full signed square-root bound remains open. This turn made verified progress: 16 new public theorems in three new Lean modules, all compiled and axiom-audited. Do not mark complete/blocked for difficulty. Continue actual signed bound, not merely creating more criteria.

Repository /Users/michael/Documents/code/hgt/formal. User requires one own foreground Lean process at a time, targeted `lake --old env lean FILE` audits, no full/umbrella builds, no numerical experiments/#eval/native_decide/sorry/custom axioms/heartbeat hacks, wire finished leaves, clean scratch, no commits/pushes/subagents. Search formal_tools.py research then direct Lean (no cards). Other chats actively edit/build same checkout; preserve their work.

## Prior notation and input
D(T)=ccmLogChebyshevDeficitPrimitive T, actual integrated Chebyshev error. G(T)=ccmPrimeDeficitDilationSource T=zeta-delay D. R(T)=G(T)-(gamma+1)(expT-1)+cT, c=log(2pi)/2. Already proved |R(T)|<=7/2 for T>=0, actual limit L=ccmPrimeDeficitDilationLimit, |R(T)-L|<=exp(-T)(T+14)/4. Prior transient short head |sum_{n<=floor exp(T/2)} mu(n)(R(T-logn)-L)|<=(T+14)/4. Prior coprime balances still do NOT bound full D.

## New generic exact reconstruction
File LogarithmicMobiusShortReconstruction.lean (6 public theorems, 171 lines).
Reuses Sieve.HeathBrownIdentity, specifically truncatedMoebius, moebiusZetaDefect, VanishesBelow, vanishesBelow_mul, moebiusZetaDefect_pow_vanishesBelow. No duplicate support infrastructure.
For U natural, M_U=truncatedMoebius U, Z=zeta, E=1-M_U*Z. mu*Z=1 and mu*E^2 vanishes below (U+1)^2. Therefore, for n<(U+1)^2:
  mu(n)=2 M_U(n)-(M_U*(M_U*Z))(n).
This is moebius_eq_short_square_correction. Multiplication here is DIRICHLET convolution, not pointwise.
Define logarithmicShortMobiusInverse U f T = logarithmicWeightedDilation (truncatedMoebius U) f T, retaining full terminal cutoff inside each application.
Public:
- logarithmicMobiusInverse_eq_short_correction U f hU (floor expT<(U+1)^2): full inverse=2 short f-short(short(zeta-delay f)).
- floor_exp_lt_succ_floor_exp_half_sq T: threshold holds with U=floor exp(T/2), all real T.
- logarithmicMobiusInverse_eq_half_correction f T: exact half-cutoff version, arbitrary f and all real T.
- logarithmicShortMobiusInverse_eq_prefix U f hU: if U<=floor expT, short transform is literal sum n=1..U.
- logarithmicShortMobiusInverse_twice_eq_square f hT: for T>=0, both factors range independently over SAME U interval, giving sum_{a,b<=U} mu(a)mu(b) f(T-log(ab)). No omitted product-boundary terms. Proof U*a<=U^2<=expT.

Lean lessons: explicitly annotate `(a*b : ArithmeticFunction ℝ)` when passed to weighted dilation; without annotation expected function type causes coercion BEFORE multiplication and silently asks for pointwise multiplication. Private dilation_arithmetic_mul is FUNCTION equality (no T argument), allowing rewriting partially applied nested transforms. Use explicit `change` to unfold bare short-transform function arguments; simp alone did not eta-unfold them. sq_lt_sq₀ is iff, use .2. Final generic leaf passed exit0 with no warnings/output.

## New actual short work and full critical error bound
File CCMPrimeDeficitShortQuadraticWork.lean (8 public theorems, 167 lines).
Let U=floor exp(T/2), P_U(T)=ccmPrimeDeficitShortMainWork T:
  (gamma+1)[expT sum_{n<=U}mu(n)/n - sum_{n<=U}mu(n)]
  - c sum_{n<=U}mu(n)(T-logn).
Define B(T)=ccmPrimeDeficitShortQuadraticWork T:
  2 P_U(T) - short_U(short_U(zeta-delay G))(T).
Equivalent literal rectangular form:
  B(T)=2P_U(T)-sum_{a,b<=U}mu(a)mu(b) H(T-log(ab)), H=zeta-delay G.
ALL Möbius coefficients in this formula are <=U; G and H are elementary harmonic/logarithmic sources, with no long Möbius tail hidden in them.

Verified public results (T>=0 where indicated):
1. logarithmicShortMobiusInverse_dilationSource: short G=P_U+short R.
2. ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork: D-B=2 short R, exactly.
3. abs_logarithmicShortMobiusInverse_dilationRemainder_le: |short R|<=(7/2)exp(T/2).
4. abs_ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_le: |D-B|<=7exp(T/2), unconditional actual arithmetic estimate.
5. ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_sub_limit: D-B-2L sum_{n<=U}mu(n)=2 transientShortHead.
6. abs_ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_sub_limit_le: absolute value of previous difference <=(T+14)/2.
7. ccmPrimeDeficitShortQuadraticWork_eq_square: literal rectangular formula above.
8. riemannHypothesis_iff_shortQuadraticWork_bound:
   RiemannHypothesis iff exists C>=0, forall T>=0, |B(T)|<=C exp(T/2).
This uses existing riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound in CCMRestrictedWeilPoleCompressionRHCriterion.lean:238. Each direction increases bound constant by 7. This is an unconditional equivalence, NOT an RH proof or a bound for B. No analytic premise was smuggled into arithmetic results.
All explicit main terms MUST remain paired with the quadratic correction; neither part separately is known controlled at critical scale.

## Failed positivity conjecture, verified on actual source
File CCMPrimeDeficitShortSourceMatrix.lean (2 public theorems).
H=zeta-delay G. Exact private evaluations G(0)=0, G(log2)=1, H(0)=0, H(log2)=1, proved symbolically via two-term finite sum and exp/log identities.
Define actual source matrix on indices 1,2 at terminal time T=2log2:
  K_ij=H(2log2-log((i.val+1)*(j.val+1))), i,j:Fin2.
Last diagonal is H(0)=0; both off-diagonals H(log2)=1. Hence determinant exactly -1, regardless of first diagonal.
Public det_ccmPrimeDeficitShortSourceTwoPointMatrix and ccmPrimeDeficitShortSourceTwoPointMatrix_not_posSemidef prove this.
This refutes positivity for ARBITRARY coefficient vectors. It does NOT prove a negative value on the actual Möbius vector and does NOT falsify RH. Next bound must exploit actual Möbius signs/constraints and explicit main-term cancellation. Do not discard quadratic work as nonnegative.
Lean repair: unfold matrix and normalize finite-index casts before determinant rewrite; bare change was not definitionally equal. Final leaf compiled with no warnings/output.

## Promising next source analysis (NOT YET FORMALIZED)
I derived the candidate elementary identity, for x=expT, N=floor x, tau(n)=n.divisors.card:
 H(T)=x sum_{n<=N} tau(n)/n - sum_{n<=N}tau(n)
      -(1/2) sum_{n<=N}tau(n)logn(T-logn).
Reason: G=zeta-delay(exp(t)-1)-log-weighted delay(id). Apply another zeta delay; zeta*zeta has coefficient tau(n), and sum_{d|n}logd=tau(n)logn/2 by pairing complementary divisors. Search found no direct logarithmic divisor-sum identity; check before proving.
Potential route: retain hyperbola structure and actual double Möbius signs when using divisor error estimates. A termwise O(sqrt(x/(ab))) bound followed by absolute values LOSES the desired scale; do not claim it controls B.
Existing direct Lean sources located/read in part:
- DirichletDivisorAsymptotic.lean:24 abs_sum_div_sub_dirichlet_le N hN: |sum_{d<=N} floor(N/d)-NlogN-(2gamma-1)N|<=20 sqrtN. Read through line50.
- DivisorCenteredHyperbola.lean:26 sum_floorDivisor_eq_centeredHyperbola: exact centered modular-ramp split. Read through line44. Has centeredDivisorHyperbolaAbel_bounds at93.
- DivisorSecondCenteredHyperbola.lean (declaration names only read): centeredDivisorHyperbolaAbel_second_bounds94, sqrt_log_bounds125, tends atBot210, positive smooth channel lower bounds241/255, unsigned-dilation lower bounds314/325. Beware unsigned loss.
- DivisorSmoothSourcePositivity.lean:102 divisorHyperbolaSmoothRemainder_nonneg (declaration location only; do not assume solves signed B).
These may help create actual signed control; they are not a completed argument.

## Verification/cleanup
Three targeted final leaf audits `lake --old env lean FILE -o .lake/build/lib/lean/...olean` all passed. No full/umbrella builds or fallback cache this turn. All three objects fresh and each import appears once in RHTower.lean. Forbidden-construct and whitespace scans clean; umbrella git diff --check clean.
Final axiom audit `lake --old env lean /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/AuditShortQuadraticWork.lean` passed exit0. All 16 public theorems depend ONLY on propext, Classical.choice, Quot.sound. No sorryAx, custom axiom or Lean.ofReduceBool. Audit coverage checked complete. Deleted own temporary AuditShortQuadraticWork.lean afterward. No own process left running.
Index refreshed twice because other chats edited files during lint. Both index commands succeeded. Final global lint still failed for 17 unrelated unwired modules and concurrently stale LEAN_API/LEAN_GAPS/LEAN_OVERVIEW. Own three leaves have no lint/wiring errors. Preserve other chats' work; do not chase metadata races indefinitely. Latest unrelated failures: RHTower CCMActualPrimeBandMassLimit, CCMActualPrimeUniformBandSaving, MobiusCubicGammaAtomJets, MobiusCubicGammaNorm, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ResolventDivisionDecay, STCCofinalTriangleHolonomy, STCPrimeWindowPackets, ZetaZeroDensityPowerSaving; HTGeometry EntireAlgebraicRatioRational, FirstOrderRelationLaurentBranch, FirstOrderWimanRootBaseChange, LaurentCoefficientEulerDerivation, LaurentOutputJacobianLead, MeromorphicRationalRelativeClosure. No commits/pushes.
