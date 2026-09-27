# Global residual reflection and literal prime forcing (2026-09-27)

Active goal remains proving RH by arithmetic conservation/action identities. RH UNPROVED. No global square-root bound has been obtained. This turn removes the earlier thin-boundary restriction from the exact signed reflection representation.

Repo /Users/michael/Documents/code/hgt/formal. Sequential foreground final leaf checks use lake --old env lean FILE -o matching .olean. No full/umbrella builds, subagents, commits, pushes, numerical computations, sorry/custom axioms, or heartbeat overrides.

## New exact impulse law in the old boundary window
From mem:research/noether_boundary_reflection_oscillator_and_impulse_balance_2026_09_27:
w=tail_m mu; q=actual ccmPrimeDeficitBoundaryPosition, capped at m+3k.
Define ccmPrimeDeficitBoundaryImpulseWork(m,k,T)
= sum_{n<=m+3k} w(n) exp(-log(n)/2) q(T-log(n)).
For all m,k,T this equals exp(-T/2) times the existing boundary reflection integral.
For m>0,3k<=m,0<=T<=2log(m+k):
exp(-T/2)(D(T)-A_m(T)) = this exact signed impulse work.
Also proved one reflected-current entry jump: changing reflected prefix M to M+1 adds
v(M+1) exp(-log(M+1)/2) q_N(T-log(M+1)).
The finite impulse identity avoids assuming a global smooth field across its impulses.

## New global factorization
Kexp(t)=max(exp(t)-1,0); Klin(t)=max(t,0).
Both have proved finite-profile reflection factorizations:
Z_w Z_v Kexp(T) = integral_0^T Fexp_w(s) Fone_v(T-s) ds;
Z_w Z_v Klin(T) = integral_0^T Fone_w(s) Fone_v(T-s) ds.
Finite profiles use horizon floor(exp T). Generic identities hold for all real T.

Define, for arbitrary signed w:
R_w(n)=sum_{d|n} w(d) = logarithmicDivisorTransform w n.
L_w(n)=sum_{d|n} w(d) log(n/d) = logarithmicLogDivisorTransform w n.
Complete divisor source H factors as
H = Z_1 Z_1 Kexp - Z_1 Z_log Klin.
Consequently, exactly for every w and T:
Z_w Z_w H(T) = Z_Rw Z_Rw Kexp(T) - Z_Lw Z_Rw Klin(T).
All operator commutations and finite sum rearrangements are proved.

For actual w=tail_m mu:
r_m=ccmPrimeDeficitResidualCoeff m;
s_m=ccmPrimeDeficitResidualLogCoeff m.
F_m,U(t)=Fexp_r_m,U(t)-Fone_s_m,U(t)
  = ccmPrimeDeficitResidualForce m U t.
C_m,U(t)=Fone_r_m,U(t)
  = ccmPrimeDeficitResidualCountProfile m U t.
For EVERY natural cutoff m and EVERY T>=0, U=floor(exp T):
D(T)-A_m(T)=integral_0^T F_m,U(s) C_m,U(T-s) ds.
There is no 3k<=m or near-square condition on this theorem.
This keeps the complete logarithmic prime correction rather than extrapolating the old H=Kexp window.

## Identifies existing sieve infrastructure, not a new substitute residual
r_m(n)=Sieve.moebiusZetaDefect m n,
where the existing arithmetic function is 1 - truncatedMoebius m * zeta.
s_m(n)=(Sieve.moebiusZetaDefect m * vonMangoldt) n
= sum_{d|n} r_m(d) Lambda(n/d).
All products here are Dirichlet convolutions; explicit ArithmeticFunction type annotations protect against accidental pointwise multiplication.
At zero cutoff: r_0(n)=if n=1 then1 else0; s_0(n)=Lambda(n).
Proof reuses Sieve.HeathBrownIdentity and Mathlib ArithmeticFunction.VonMangoldt, including zeta_mul_vonMangoldt.

## Causality
r_m(n)=0 for n<=m, via existing Sieve.moebiusZetaDefect_vanishesBelow.
s_m(n)=0 for n<2(m+1), via Sieve.vanishesBelow_mul and Lambda's lower support 2.
Thus corresponding finite count profiles vanish before these entry cutoffs.
The entire logarithmic reflected correction Z_s_m Z_r_m Klin(T) vanishes if
floor(exp T)<2(m+1)^2.
Below that threshold, D-A_m is exactly the exponential residual reflection, for arbitrary m and T>=0.
These are lower support thresholds, not assertions that every first allowed coefficient is nonzero.

## Six new leaves / 34 public theorems
- CCMPrimeDeficitBoundaryImpulseWork: 3.
- LogarithmicLinearEntryConvolution: 6.
- CCMPrimeDeficitResidualPairing: 10, plus generic transforms and actual residual coefficients.
- CCMPrimeDeficitResidualReflection: 4, plus residual force/count profiles.
- CCMPrimeDeficitResidualPrimeForce: 7.
- CCMPrimeDeficitResidualCausality: 4.
Each leaf passed final foreground audit and has one umbrella import. Verification details appended after combined audit and lint.

## Remaining mathematical task
The global signed reflection integral and retained action A_m still need a square-root bound.
Neither source work nor prime work was assumed small. The new equation is an exact representation, not an RH proof.
A plausible next focus is exploiting the relation s_m=r_m*Lambda to compare the two work terms across scales. The prime correction cannot be discarded once its interaction threshold is reached.

## A new coefficient-choice conjecture to investigate (NOT formalized here)
Complete a finite Euler product instead of using a numerical sharp cutoff:
a_P(n)=mu(n) if n divides P, else0, with P>0.
Expected exact divisor identity for n>0:
(a_P*zeta)(n)=1_{Coprime(n,P)}.
Then for w_P=mu-a_P, residual R_P=w_P*zeta satisfies
R_P(n)=delta_{n=1}-1_{Coprime(n,P)}, hence R_P<=0 (handle n=0 separately).
Its prime force R_P*Lambda is also <=0.
This moves the sign difficulty into the difference of two nonnegative reflection works.
Taking P=m! matches mu on every n<=m (n=0 harmless), so the existing affine head-extension action symmetry may transfer D to this coefficient choice when m reaches the usual square-root cutoff.
Do not assume this sign cone bounds either work or solves RH. Large positive works may still cancel badly.
Corpus searches for "moebius coprime divisor" in Sieve and "moebius gcd coprime" in RHTower found no directly matching projector theorem; broader search still required before implementing.
Mathlib Nat.divisors filter/gcd identities and sum_moebius_divisors should prove the divisor identity without computations.
Other possible direction: a global reflected impulse law combining the exponential and linear ramp components, with literal prime forcing, rather than only the old boundary impulse law.

## Lean fixes
- Partial logarithmicDilationSum f under another operator may not unfold with rw [logarithmicDilationSum]; use change with logarithmicWeightedDilation (fun _=>1).
- Nat.sum_divisorsAntidiagonal often needs its explicit two-variable function supplied; bare rw could not infer the function in the prime divisor-sum theorem.
- After logarithmicWeightedDilation_comp and unfolding the outer sum, dsimp only is needed to beta-reduce the coefficient lambda before rw by a finite-sum equality.
- Keep (F*G : ArithmeticFunction Real) explicit when the result is supplied/coerced as a sequence.


## Final validation and workspace state
All six final leaf audits passed using lake --old env lean FILE -o matching .olean, sequentially in the foreground. Combined 34-public-theorem #print axioms audit exited 0: only [propext, Classical.choice, Quot.sound]. Fresh object timestamps and exactly one umbrella import per new module verified. No forbidden constructs or trailing whitespace in new leaves; umbrella git diff --check passed.
Scratch /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/ResidualReflectionAxiomAudit.lean deleted.
Index refreshed twice (initial plus one retry). Final global lint exited 1: 24 unrelated unreachable modules and stale formal/LEAN_API.md. No own module errors. Do not retry this checkpoint's lint again or claim global lint clean.
At last status six new leaves were untracked and GaloisForLFunctions/RHTower.lean modified. No commits or pushes; concurrent work preserved. No own process remains live.
Goal remains ACTIVE. RH unproved; signed global reflection and retained action remain unbounded at the needed scale.
