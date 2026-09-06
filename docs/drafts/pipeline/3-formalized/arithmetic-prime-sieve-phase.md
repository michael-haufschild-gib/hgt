# Exact prime-sieve remainder identity and phase classification

**Stage:** 3-formalized. **Scope:** frozen survivors L and M, including the exact finite-divisor identity and infinite limit. RH remains unproved. [Candidates and corpus sources](../1-in-progress/arithmetic-prime-sieve-phase.md); [numerical rejection of J and K](../2-fully-proven/computations/arithmetic-prime-sieve-phase/REPORT.md).

## Source and exact decomposition

Let `sigma=Re(s)>0`, `s!=1`, `u=conjugate(s)`, and `D=u(u+1)`. Retain the literal ordinary remainder

`R_s(n)=sum_(1<=j<=n)j^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2`.

Define `g_s(n)=n^(-s)conjugate(R_s(n))/D` and `W_d=d^(1-s)sum_(n>=1)n^(-s)conjugate(R_s(dn))`. For every positive modulus `M`, Lean proves

`C_M(s)=sum_(n>=1,gcd(M,n)=1)g_s(n)=sum_(d|M)mu(d)W_d/(dD)`.

The proof uses the finite identity `sum_(d|gcd(M,n))mu(d)=[gcd(M,n)=1]`, positive-index reindexing of multiples, and absolute convergence of the literal remainder. No infinite inclusion-exclusion limit or unproved Möbius cancellation is assumed. The formula includes `M=1` and nonsquarefree moduli.

For `M=N!`, each fixed nonunit integer is eventually removed. Absolute summability of `g_s` supplies a bound independent of `N`, so dominated convergence gives

`C_(N!)(s) -> g_s(1)`.

Factorial sieving removes exactly the primes up to the integer cutoff; multiplicities in the modulus do not change its coprimality condition. On the open strip the limit is exactly

`g_s(1)=Q(s)-conjugate(zeta(s)/(s(s+1)))`,

`Q(s)=-1/[2u(1-u)]`.

Both complex components are retained.

## Strict approach direction without a zero equation

The previously proved first coefficient of the ordinary remainder gives

`n^(2 sigma+1)g_s(n) -> -1/[12(u+1)]`.

If `Im(s)>0`, the limiting imaginary part is strictly negative. Since the real scaling factor is positive, there exists an integer `N_s` such that `Im(g_s(n))<0` for all `n>=N_s`.

The formal strict-phase theorem applies to **any** positive modulus `M` divisible by every prime at most `N_s`. Any nonunit surviving index must exceed `N_s`: otherwise a prime divisor of that index would also divide `M`. Thus every surviving nonunit imaginary summand is negative. There is a surviving prime, by taking a prime greater than `M`; consequently

`Im(C_M(s)) < Im(g_s(1))`.

If `q` is any prime not dividing `M`, replacing `M` by `Mq` removes only nonpositive imaginary summands and removes the strictly negative term at `q`. Absolute convergence and strict comparison of sums give

`Im(C_M(s)) < Im(C_(Mq)(s))`.

This proves L without assuming that `s` is a zero and without assuming a finite or uniform numerical cutoff. It also covers arbitrary later prime insertion orders, once all primes below the parameter-dependent threshold have been removed.

## Exact boundary of an eventual sign law

For every parameter with positive real part and positive height, Lean proves

`[eventually Im(C_(N!)(s))<=0] iff Im(g_s(1))<=0`.

Forward: pass the eventual inequality to the limit. Reverse: the strict approach theorem puts every sufficiently late phase below its nonpositive limit, including when that limit is zero.

At an open-strip zero with positive height,

`Im(g_s(1))=Im(s)(2 Re(s)-1)/(2|u(1-u)|^2)`.

The denominator is positive, so M is proved exactly:

`[eventually Im(C_(N!)(s))<=0] iff Re(s)<=1/2`.

No simplicity or multiplicity condition is used. Critical-line zeros are included in the equality case, where late phases are strictly negative. This is a classification of the proposed sign condition, not an independent proof that the condition holds for every zero. A complete RH proof, including exclusion on both sides and all required cases, is not supplied.

## Falsified candidates and surviving content

J asserted nonpositivity at **every** prime cutoff. K asserted monotonicity at **every** insertion. Both were frozen before evaluation. Runpod diagnostics found 213 positive zero/cutoff phases and 341 decreasing insertion steps in the tested sample; independent 90-digit calculations reproduced selected violations, including after prime 2 had been removed. J and K are numerically rejected, not formally disproved by certified exact zero counterexamples.

L and M were frozen separately. Their paper proofs are dependency-closed and their exact statements are formalized. The positive residue consists of the finite Möbius/coprime identity, infinite unit limit, universal late direction, and sharp eventual-sign classification. It supplies no new sign constraint on the unit value. No general impossibility theorem for arithmetic RH proofs or literature novelty claim is made.

## Lean certificate

Module: `GaloisForLFunctions.RHTower.ArithmeticPrimeSievePhase`; namespace: `RHTower.DeletionMixedRefinement`.

- `tendsto_normalizedWeightedRemainder_scaled`
- `eventually_normalizedWeightedRemainder_im_neg`
- `coprimeRemainder_eq_sum_divisors`
- `tendsto_coprimeRemainder_factorial`
- `eventually_coprimeRemainder_strict_phase`
- `normalizedWeightedRemainder_one_eq_boundary`
- `eventually_coprimeRemainder_im_nonpos_iff`
- `eventually_coprimeRemainder_im_nonpos_at_zero_iff`

The module additionally defines `normalizedWeightedRemainder` and `coprimeRemainder`. The scratch file and published source passed `lake env lean`; the single leaf passed `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticPrimeSievePhase`. The module is wired into `RHTower.lean`; no full or umbrella build was run.

All ten public declarations passed a separate `/tmp` `#print axioms` audit. Only `propext`, `Classical.choice`, and `Quot.sound` were reported. No unproved arithmetic premise, added mathematical axiom, numerical output, or computational certificate enters these proofs. The statements retain their explicit parameter domains and the zero equation where a conclusion concerns zeros.

The corpus index retrieves the final equivalence, and `scripts/formal_tools.py lint --check-generated` passed with exit code 0, reporting existing large-file warnings. All owned Lean invocations completed; no owned Lean process remained after the checks.
