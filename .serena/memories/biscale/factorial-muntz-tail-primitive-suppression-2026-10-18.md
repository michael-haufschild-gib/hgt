# Actual factorial Muntz tail primitive suppression — 2026-10-18

Mission/goal remains unconditional RH in Lean; active and unachieved. This turn completed a substantial actual-tail estimate, not RH or all-source RW. Read the persistent objective attachment before the next goal turn. No web/novelty audit/numerical experiments; use Lean corpus and direct single-thread leaf checks.

Formalized card: docs/drafts/pipeline/3-formalized/factorial-muntz-tail-primitive-suppression-2026-10-18.md. Parent docs/drafts/pipeline/1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md remains active and now links this result. Predecessors: `mem:biscale/factorial-muntz-tail-phase-mass-2026-10-18`, `mem:biscale/factorial-muntz-tail-prime-polar-budget-2026-10-18`. All four predecessor hashes (PhaseCells, Mass, Smoothing, PrimePolarBudget) still match prior verified versions.

New leaves, all namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar:
- ClampedLatticePrimitive.lean — ce8fdee4077c1bd31c4bd1448ae3485fcd4f32a23e6753bee4a4ac0aac07e7d2
- FactorialMuntzTailPrimitive.lean — 6a11a6428e6a29cda762633f1e801fc5b96325b6d7efc84c28a684a5088cd2f1
- FactorialMuntzTailReadoutDecay.lean — 3481995d1a05bc36599ff8b0b9751b5810e540d91aa6b5fa0aeaeeda9912330b
- FactorialMuntzTailPrimitiveEnergy.lean — e69024b614e07ebab34a3200eec08c178fb5e392172a42f2005621ff26b05c12

Write N=n+1, epsilon=sourceFactorialCollar N, T_n=factorialMuntzCorrectedTail n, U_nk=factorialMuntzSmoothedTail n k.

Exact mechanism:
- For positive y, clampedLatticeRemainder R(y)=-RHTower.bernoulliPeriodic(y). Existing B=RHTower.DeletionMixedRefinement.bernoulliCenteredPrimitive satisfies |B|<=1. New bernoulliCenteredPrimitive_hasDerivAt derives B'=bernoulliPeriodic+1/12 from its public integral definition, including integer joins.
- clampedLatticePrimitive epsilon a y = B(a*y)/a-B(a*(1+epsilon)*y)/(a*(1+epsilon)); for epsilon>=0,a>0,y>0 its derivative is R(a*(1+epsilon)*y)-R(a*y), and its absolute value <=2/a.
- factorialMuntzTailRemainder is the literal dyadic combination of R-differences with coefficients 1/4,-2,4. factorialMuntzSum_add_half_eq_remainder: M_n(t)+1/2 = t/(N*epsilon)*P_n(N/t), t>0.
- factorialMuntzTailLatticePrimitive C uses the same coefficients, C'=P, |C|<=12. factorialMuntzTailPrimitive V_n(x)=C(N*exp(-x)) is continuous and differentiable globally, |V_n|<=12.
- factorialMuntzTailPrimitiveScale A_n=1/(N^2*epsilon*sqrt(N)) is positive and <=15/(N*sqrt(N)). Actual T_n(x)=-A_n*exp(5*x/2)*V_n'(x) for x<=0.

Readout endpoints (no abstract source or boundary hypotheses):
- factorialMuntzCorrectedTail_readout_eq_primitive for Re(s)>-1: integral exp((s-1/2)x)*T_n(x) = A_n*((s+2)*integral_Iic0 exp((s+2)x)*V_n(x)-V_n(0)). Both integrability obligations and the zero limit at negative infinity are proved. The endpoint V_n(0) is retained.
- factorialMuntzCorrectedTail_readout_decay: norm <=180/(N*sqrt(N))*(1+norm(s+2)/(Re(s)+2)), Re(s)>-1.
- factorialMuntzCorrectedTail_readout_decay_of_nonneg_re: norm <=360*(1+|Im(s)|)/(N*sqrt(N)), Re(s)>=0.
- factorialMuntzCorrectedTail_paperFT_decay n tau: norm of real-frequency Fourier transform <=360*(1+|tau|)/(N*sqrt(N)).
- factorialMuntzSmoothedTail_paperFT_decay n k tau (ReadoutDecay line183): <=360*exp(1)*(1+|tau|)/(N*sqrt(N)), EVERY n,k,tau. Existing exact convolution readout and kernel bound provide the smoothing factor.

Weighted primitive energy:
- factorialMuntzTailPrimitiveBudget C=32*(360*exp(1))^2*pi, C>0.
- factorialMuntzSmoothedTail_primitive_integrable proves integrability of norm(paperFT U_nk tau)^2/(tau^2+1/4)^2.
- factorialMuntzSmoothedTail_primitive_mass_bound (Energy line72): integral of that density <=C/N^3 for EVERY n,k.
- factorialMuntzSmoothedTail_primitive_mass_relative (Energy line90): for each fixed n, eventually in k the same integral <=(512*C/N^2)*integral U_nk(x)^2 dx. This uses the exact phase-cell mass predecessor. Threshold may depend on n; no common smoothing threshold for all n is claimed.
- Scalar majorant proved: (1+|tau|)^2/(tau^2+1/4)^2<=32/(1+tau^2), whose integral is 32*pi.

Verification:
- Four direct `lake --old env lean -j 1 -o ...` leaf commands exited0, final logs empty. No umbrella/full build, heartbeat increases, commits, pushes, server, or dependency-source edits.
- Combined /tmp/bsu-tail-primitive-axioms.lean checks mathlib APIs plus #print axioms for ALL29 public declarations (23theorems+6definitions). Exit0, all exactly standard propext/Classical.choice/Quot.sound.
- Each new module imported once in formal/GaloisForLFunctions/BiScaleUncertainty.lean (lines334–337). Source hashes, predecessor hashes, log emptiness, axiom inventory, imports, and card links independently verified by /tmp/bsu-tail-primitive-finish.py.
- scripts/formal_tools.py index exited0. Initial lint found unrelated imports plus stale LEAN_API.md; one index refresh resolved generated staleness. FINAL lint --check-generated exited1 solely on unrelated missing umbrella reachability for GaloisForLFunctions.BiScaleUncertainty.FiniteCoprimeMomentCalculus. 381 existing size warnings; none names our leaves. Do not modify unrelated concurrent work.
- Evidence: /tmp/bsu-tail-primitive-verification.json; /tmp/bsu-clamped-primitive-leaf.log; /tmp/bsu-tail-primitive-leaf.log; /tmp/bsu-tail-readout-decay-leaf.log; /tmp/bsu-tail-primitive-energy-leaf.log; /tmp/bsu-tail-primitive-axioms.log; /tmp/bsu-tail-primitive-index-final.log; /tmp/bsu-tail-primitive-lint.log. First lint preserved with -lint-first.log.
- All own process handles are terminal. No cache snapshots/setup maps or background Lean jobs were created.

Remaining work:
Actual low-frequency suppression and primitive smallness are discharged. Existing RHTower.ExposingRayPrimitive.logarithmic_mass_ratio_bound in RHTower/WeilWorkExposingRayPrimitiveSharpness.lean still has compact C² support hypotheses. No domain bridge to the actual noncompact U_nk was proved. Inspect whether compact support is used only for integrability/Plancherel, or justify compact approximation. Original ramp mixed terms, sufficient diagonal margin, all-source RW, and RH remain unproved.

Lean pitfalls:
- Cast derivatives explicitly as ((deriv (factorialMuntzTailPrimitive n) x : ℝ) : ℂ); expected ℂ otherwise drives polymorphic deriv to an incorrect function codomain.
- `simpa ... using!` resolves definally equal Real group/module structures; exponential derivative simplification needed id_eq, Complex.ofReal_one, mul_one, one_mul, mul_comm.
- Complex.ofNat_re/ofNat_im do not exist here; use `change` or normal simp/norm_num for numeral components.
- In simp only, give Real.sq_sqrt an explicit nonnegative radicand, not an unconstrained `by positivity`. field_simp can close the final budget identity entirely; a subsequent bare ring causes No goals to be solved.