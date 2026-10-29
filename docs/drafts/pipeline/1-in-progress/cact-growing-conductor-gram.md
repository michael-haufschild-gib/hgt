# Arithmetic cancellation in growing conductor Gram matrices

## Target

Replace the existing harmonic Ramanujan-family Gram error proportional to
sum(m^2) by a bound that retains arithmetic cancellation. Aim for lower frame
control at a conductor cutoff governed by the square root of the integer
horizon, with explicit loss and original Ramanujan profiles.

## Established inputs

- SAHT/GrowingRamanujanFamiliesHaveAUniformGramBudget: ordinary-horizon Gram
  comparison with error (1+2 sum(m^2)) times coefficient square mass.
- SAHT/TheArithmeticResidualBudgetIsUniformInTheHorizon: uniform actual Mertens
  budget and all-family prime residual bound. These are existing results.
- RHTower/EulerDeletionReflectedLogarithmicGram: exact deletion Gram residue
  gcd(p,q)-1 and finite part logp+logq-gcd(p,q)loglcm(p,q). Coprime finite part
  vanishes. A prime-only restatement in Ramanujan coordinates is not new.

## Candidate mechanisms, not yet proved

1. Lift the exact deletion finite part through the Mobius divisor formula.
   For normalized Ramanujan conductors, expect finite-part off-diagonal entries
   only when one conductor divided by the other is a prime power. The entry
   for m dividing n should be -Lambda(n/m)*sqrt(phi(m)/phi(n)); diagonal should
   be -logm+tameDifferent(m), relative to harmonicN. This exposes a signed
   conductor operator instead of summing absolute pairwise periods.
2. Alternatively use the separated reduced additive characters underlying
   Ramanujan modes. A two-sided discrete large-sieve estimate at spacing M^-2,
   followed by harmonic summation starting above M^2, should give a lower Gram
   bound of the form log(N/M^2)-C. Need find and inspect the exact corpus tools.

Neither estimate is yet claimed. A useful result must improve the whole-family
bound, not merely re-express existing pairwise limits. A new Gram estimate does
not itself control the completed source residual or prove RH.

## Status

Novelty and analytic investigation. No paper proof or Lean result claimed.

## Selected analytic mechanism

The corpus already proves the sharp two-sided window estimate
`abs_window_rootsOfUnity_sub_le` with discrepancy Q(Q-1). Normalize each primitive
root of conductor m by c_m/sqrt(phi(m)); different primitive orders are disjoint,
so the coefficient square mass is exactly sum c_m^2. This gives, for the actual
Ramanujan packet f(n), cumulative mass >= (N-Q(Q-1)) sum c_m^2.

Nonnegative cumulative mass also gives the positive part of that lower bound.
Harmonic summation by parts therefore compares f(n)^2 with the delayed constant
sequence 1_{n>Q(Q-1)} sum c_m^2. Expected exact target:

 (H_N-H_{Q(Q-1)}) sum c_m^2
   <= sum_{1<=n<=N} (sum_m c_m ramanujanPoleProfile(m,n))^2.

A logarithmic corollary is (logN-2logQ-1) sum c_m^2 on the left. This is useful
for whole families with Q below a constant times sqrtN, not only fixed conductors
or families whose sum m^2 is small relative to logN. No completed-source sign
claim follows from this Gram lower estimate alone.
