# Next gate: critical odd source and the full head cost

Status: OPEN CONJECTURE, DEFERRED after cycle17 utility audit. No counterexample or no-go for arbitrary corrections is claimed. The main WP02 universal lower inequality remains the objective.

## Exact candidate

Use the actual compactSource G_L from WeilWorkExposingRayCriticalOddSource. Put this seed in the nonnegative mixture with coefficient 1/(2*pi). For every finite N and every epsilon>0, conjecture that some sufficiently large L>=0 and a finite nonnegative family of actual polar corrections f_i, with apertures at most L+2, satisfy BOTH

    2*pi*sum_i alpha_i*atomCoeff(f_i,n)
      = -exposingWeightTrunc(N,n)-atomCoeff(G_L,n),  for every integer n>=2,

and

    archEnergy(G_L)/(2*pi)+sum_i alpha_i*archEnergy(f_i)
      <= -archimedeanExposingThreshold+exposingTail(N)+epsilon.

Thus the total family, including its prescribed odd seed, realizes the whole negative truncated exposing ray at the required cost. The correction signs are nonnegative; its atom traces need not be. No assumption of RH, cone nonemptiness, PrimeBlindPositive, or an energy sign is permitted.

This is a focused strengthening of the existing OPPOSITE-RAY-CONJECTURE, not a reformulation of an already proved theorem. It may be too strong. Test that possibility before committing to another implementation cycle.

## What the new source actually pays

The complete full-source defect is

    r(n) = atomCoeff(source,n)+exposingWeight(n)
         = atomCoeff(residual,n)+sum_(k>=1) 2^-k e_k(n).

Every term is retained. Its absolute value has every exponential rate below 2*pi*exp(-3/2), and source/w tends to -1. This makes the tail summable with the box cost and allows its far tail to be made small. It does not make the fixed finite head small. The exact compact energy identity retains archEnergy(compactResidual L); it supplies no sign or smallness for that term.

The existing arbitrary-trace repair theorem only charges the full weighted absolute defect. Applying it blindly leaves a fixed head debit. A fixed positive debit cannot be absorbed into exposingTail(N)->0. Showing bounded cost or another fast cutoff error is insufficient for this conjecture.

## Utility and circularity audit before new Lean

1. Audit the limiting finite-head debit using the literal source, all signed cross terms, and the full archimedean symbol. Look for a joint correction that cancels cost, not independent boxes charged by absolute values.
2. Audit whether the prescribed seed needlessly strengthens the actual WP02 task. Weak duality shows that cheap opposite-ray realization also forces a lower exposing-value constraint on every Weil-positive weight system. Do not presume that stronger cone rigidity is necessary to prove the original positive-ray lower bound.
3. Do not treat nonnegative energy of zero-trace mixtures as free. It is the existing PrimeBlindPositive condition, equivalent at all apertures to existence of a Weil-positive weight system. The exact receiver is WeilPositivityPrimeBlindDuality.lean:558; the strong linear dual receiver is WeilPositivityLinearDuality.lean:355.
4. Repeated half-step shortening is not a vanishing-residual argument. Every emitted odd filter vanishes at real frequency zero, so the even seed's value there survives. Identify and pay the resulting residual before passing to an infinite iteration.
5. If this seed cannot pay the head cost, preserve the verified boundary construction and record the obstruction's strongest positive survivor. Then change conjecture toward the universal lower estimate. Do not spend another cycle merely packaging an existing conditional receiver or an elementary filter invariant.

The cycle16 corpus audits recovered the exact prime-blind and dual receivers and existing short-source capacity bounds; they did not supply the demanded correction or its cost. Search coverage and the misleading zeroTerm_nonneg hit are documented in CRITICAL-WIDTH-ODD-CONJECTURE.md. External scientific novelty remains unestablished.

## Cycle17 utility verdict

Write L_N(lam) for the finite exposing pairing and T for the literal threshold. For any Weil-positive lam, weak duality gives E_total >= -L_N(lam) >= -exposingValue(lam)-tau_N for a negative-ray realization. The proposed upper bound therefore implies T-exposingValue(lam) <= 2*tau_N+epsilon. Taking N to infinity and epsilon to zero forces EVERY existing cone point to attain T, hence to equal Lambda by the existing exposed-point theorem. WP02 requires SOME cone point attaining T. Neither statement provides cone nonemptiness for free.

This consequence was already anticipated in OPPOSITE-RAY-CONJECTURE.md. Revalidation is a route audit, not new mathematics. No strict cone point was constructed, so this is not a disproof. The prescribed critical odd seed additionally restricts an already stronger construction problem. Its exponentially decaying residual does not remove the finite-head debit. Defer this route until an actual joint signed-cost mechanism appears.

The proposed single differential-source exposer is also deferred: even if its Green/Jensen comparison closes, it changes the exposure characterization without producing an attaining cone point. Ordinary near-radical cutoff estimates and scalar factorization likewise do not pay the universal inequality. Existing scalarization is explicitly recorded as rediscovered in WP01 PROOF.md. No conditional receiver is added to Lean for these observations.
