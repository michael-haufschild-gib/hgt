# Prime-sieve phase confinement of the actual arithmetic remainder

**Stage:** 1-in-progress; the independent exclusion law remains open. **Completed audit:** J and K numerically rejected; exact identity, L, and M formalized in `ArithmeticPrimeSievePhase`. [Full proof and certificate](../3-formalized/arithmetic-prime-sieve-phase.md). RH remains unproved.

## Frozen candidates

For `sigma=Re(s)>0`, `s!=1`, let `u=conjugate(s)`, `D=u(u+1)`, and retain the actual ordinary remainder `R_s(n)` and deletion remainder `W_d` from the global minimum audit. For the first `k` primes, with squarefree product `M_k` (`M_0=1`), define

`U_k(s)=sum_(d|M_k)mu(d) W_d/(dD)`.

The corpus mechanisms `tsum_coprime_eq_sum_divisors_moebius`, finite Boolean divisor cancellation in `MobiusRoughLambertBoundary`, and finite prime-insertion factorization suggest the exact alternative representation

`U_k(s)=sum_(n>=1,gcd(n,M_k)=1) n^(-s)conjugate(R_s(n))/D`.

This is a signed complex sum; no positive kernel, spectral operator, or completed zeta factor is introduced. As `k` increases its limit should be `R_conjugate(s)(1)/D`. At a zero this is `Q(s)=-1/[2u(1-u)]`, whose imaginary part is positive at a strict-right zero of positive height.

**Conjecture J — finite prime-sieve phase confinement.** At every open-strip zeta zero of positive height, `Im(U_k(s))<=0` for every `k>=0`. Together with the exact limit this would exclude strict-right zeros. A corresponding strict-left exclusion and a complete RH proof are not claimed.

**Conjecture K — directed prime-insertion phase.** Independently test the stronger structural hunch that, at every such zero, `Im(U_(k+1)(s))>=Im(U_k(s))` for every `k>=0`. At critical-line zeros the limit is zero; this would imply J there. The nesting of the surviving arithmetic support motivates the test, but the complex summands have no known sign at small indices.

Both statements are frozen before numerical evaluation. They concern natural initial prime segments, not subsets selected by observed signs. Do not replace either failed statement with an eventual version without naming a new conjecture.

## Falsification experiment

On the specified Runpod, evaluate the first 96 critical-line zero approximations, horizontal nonzero controls, and initial prime segments through 29. Use the rough-index representation with direct ordinary power-sum heads and the full complex Euler--Maclaurin tail. Vary head length and tail order. Independently verify selected sign violations using high-precision Hurwitz tails and the finite divisor-side formula. No computed value enters Lean.

The finite phases and their changes are not determined by the current tail limit. This experiment tests those unknown signs; it does not test RH through a finite zero sample or claim literature novelty.

**Outcome:** 213 positive zero/cutoff phases and 341 decreasing prime-insertion steps in the stated sample. Independent 90-digit divisor-side checks reproduce a positive phase at the nineteenth zero after deleting prime 2, and a decrease at the fourth zero when inserting prime 3 after 2. J and K fail these diagnostics. They are not recorded as Lean counterexamples: no interval-certified zero theorem or numerical certificate enters the formal proof. All scripts, downloaded results, limitations, and interpretation are in the [Runpod report](../2-fully-proven/computations/arithmetic-prime-sieve-phase/REPORT.md).

## Positive-residue obligation

The proved first coefficient predicts a surviving statement even if the global signs fail: the imaginary part of each normalized weighted remainder is eventually negative at every parameter with positive real part and positive height. Establish exactly what this implies for late prime removal, including the unit term and the remaining rough tail. Freeze that statement separately if needed, prove it from the literal source, and retain the distinction between an approach direction and the sign of its limiting value.

## Independently frozen conjecture L

At every parameter with `Re(s)>0`, `Im(s)>0` (without a zero equation), the finite prime-sieve imaginary sums eventually increase strictly whenever a new prime is removed, remain strictly below the imaginary part of their unit-term limit, and converge to that limit. The cutoff may depend on `s`. This is a new structural statement, not a repair of J or K's all-cutoff assertions.

Paper mechanism: after normalization, the weighted ordinary remainder multiplied by `n^(2 Re(s)+1)` tends to `-1/[12(conjugate(s)+1)]`, whose imaginary part is strictly negative. All sufficiently large summands therefore have negative imaginary part. Once the sieve has removed every nonunit integer up to that threshold, its residual tail consists entirely of negative imaginary terms. Removing a further prime deletes such terms, including that prime itself, so the imaginary sum increases strictly but stays below its unit term. Absolute convergence proves the limit. A prime not dividing a fixed modulus supplies a surviving term, so the strict inequalities are not vacuous.

Even if L is proved, it gives an approach direction, not the sign of the limiting value. At a zero that value is `Im(s)(2 Re(s)-1)/(2|conjugate(s)(1-conjugate(s))|^2)`. No independent nonpositive ceiling is supplied by L.

## Independently frozen conjecture M

At a positive-height strip zero, eventual nonpositivity of the factorial sieve phases is equivalent to `Re(s)<=1/2`. Factorial sieving removes precisely the primes up to its cutoff. Forward: pass the eventual inequality to the exact unit-term limit and use the positive denominator and positive height. Reverse: L puts every sufficiently late phase strictly below the nonpositive limit. The equality case is therefore included without a simplicity or multiplicity assumption.

This sharp classification is a new consequence to prove, not an independent arithmetic reason for the right-hand condition. It identifies exactly the missing input if an eventual version of J is proposed. No zero is excluded merely by proving the equivalence.

## Positive residue and remaining problem

The exact finite-divisor/coprime identity, factorial-sieve limit, L, and M now have closed paper proofs and checked Lean proofs. L holds at nonzeros as well, and formally covers any positive modulus containing every prime below a parameter-dependent cutoff, followed by insertion of any missing prime. M includes the equality case through strict approach from below. All eight public theorems and both definitions use only Lean's standard logical axioms; the leaf build, separate axiom audit, and formal lint gate passed.

The independent arithmetic inequality needed to force `Im(g_s(1))<=0` at every positive-height strip zero is still missing. Universal late monotonicity cannot be supplied as that inequality. The numerical early-prime sign failures do not prove impossibility of other finite-prime constraints. Reopening either all-cutoff conjecture requires a genuinely different, separately frozen statement; the eventual versions have already been classified exactly.

## Corpus mechanism provenance

The search combined signed conservation, cancellation involutions, refinement commutators, signed pairings, source divided differences, coprime inversion, prime telescoping, signed transport, partition reconstruction, subset Möbius inversion, first-prime cancellation, and rough tails. These were idea searches followed by `rg` reads of definitions and proofs, not claims of exhaustive corpus coverage or literature novelty. The operative mechanisms were `tsum_coprime_eq_sum_divisors_moebius` in `CommonProfileAnchorResponseMobius`, finite divisor-support cancellation in `MobiusRoughLambertBoundary`, and finite prime insertion in `MobiusPrimeRenewalDefectBoundary`. Only their elementary arithmetic mechanisms were used; their downstream classic-route receivers were not adopted. The asymptotic input was read from the already checked `EulerDeletionRemainderFirstCoefficient` source.
