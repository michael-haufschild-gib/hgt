# Route PM: actual complementary cancellation of the growing prime sector

- **ID:** pm-complementary-prime-sector-cancellation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** actual natural Ramanujan cutoff, audited growing-cofactor sector, signed complementary source bounds.
- **Lean:** `PMRamanujanComplementaryCancellation.lean`, eight public declarations.

## Exact result

For fixed 0<epsilon<1/2 let S_P(N)=Z_(P^2-1)(N). Let L_P be the whole large-prime sector: primes P<p<=2P, with every cofactor 1<=r<=P^2/p. Let C_P be the literal sum over remaining denominators 2<=q<=P^2. On 1<=N<P, with the original weight 1/[N(N+1)],

    E(S_P)/E(L_P) -> 0,
    E(C_P)/E(L_P) -> 1,
    Re <L_P,C_P>/E(L_P) -> -1.

The sector lower bound is c_epsilon P^(1-2epsilon)/log^2 P. Both branches have divergent energy, but their actual signed interaction cancels that leading contribution. The complement is identified with S_P-L_P using literal cutoff membership and uniqueness; no coefficient or mixed term is discarded.

## Dependency-closed paper proof

The source-bound leaf proves the exact hyperbola split, for Y<=N:

    D_epsilon(N) = -sum_(d<=Y) mu(d)d^(-epsilon) fract(N/d)
      + sum_(k<=N/(Y+1)) sum_(Y<d<=N/k) mu(d)d^(-epsilon)
      - N sum_(d>Y) mu(d)d^(-1-epsilon).

Write H(k)=sum_(d<=k) mu(d)/d. If |H(k)|<=B for k>=Y, interval harmonic sums have norm at most 2B. Increasing-weight Abel bounds a damped interval sum by 4B(X+1)^(1-epsilon); decreasing-weight Abel bounds the signed infinite density tail by 2B(Y+1)^(-epsilon). Choose Y=floor(N/log^8 N), eventually at least sqrt(N). The corpus's harmonic log-power theorem with exponent 16 gives

    |D_epsilon(N)| <= 1+C_epsilon N^(1-epsilon)/log^4 N.

The actual natural Ramanujan tail is controlled by the coefficient moment: for 0<=beta<epsilon and N<=Q,

    |Z_(Q-1)(N)-D_epsilon(N)|
      <= N Q^(-beta) [sum_(m>=1) m^(-(1+epsilon-beta))]^2.

This follows from exact Mobius multiples inversion, preserving the cofactor tail. At beta=3epsilon/4 and Q=P^2 its anchored error energy is O(P^(1-3epsilon)).

For the source energy split at floor(sqrt(P)). A global power bound controls the lower window by O(P^((1-2epsilon)/2)); the logarithmic source bound controls the upper window by O(P^(1-2epsilon)/log^8 P). Consequently

    E(S_P) log^2(P)/P^(1-2epsilon) -> 0.

Divide by the audited sector lower bound. Weighted Cauchy--Schwarz gives |<L_P,S_P>|/E(L_P)<=sqrt(E(S_P)/E(L_P))->0. Exact polarization with the literal complement then yields the ratios -1 and 1.

## Frontier contribution and boundary

This closes an actual signed-cancellation problem exposed by the growing-sector obstruction. It does not prove PM admission or RH: the remaining absolute estimate retains positive-power energy growth at epsilon<1/2. The hard producer is still a common complete signed-energy bound for arbitrarily small positive damping, preserving moving denominator boundaries and all mixed terms. Improving fixed logarithmic powers alone cannot supply it.

## Audit — 2026-10-02

- Targeted `lake --old build GaloisForLFunctions.RHTower.PMRamanujanComplementaryCancellation`: exit 0; only this leaf built.
- Final actual-file `lake env lean GaloisForLFunctions/RHTower/PMRamanujanComplementaryCancellation.lean`: exit 0, no diagnostics.
- All eight public declarations: `/tmp` axiom audit exit 0, only `propext`, `Classical.choice`, `Quot.sound`.
- Three source-bound exports separately passed targeted old-mode build, actual-file and standard-axiom audits.
- Exported the previously private sector mass bound with unchanged proof; its leaf rebuild, actual-file and new-name axiom audit passed.
- Umbrella imports exactly once; no umbrella build. Global lint reports eleven unrelated unreachable modules and no finding for these leaves.
- No added axiom, sorry, conjectural admission premise, heartbeat increase, numerical experiment or subagent.

Corpus searches 123--127 checked candidates, source arguments and proposed ingredients. Searches 126/127 were complete, with complete inventory, mixed compiler freshness and unmeasured semantic coverage. Search127 locates complete-period covariance and exact mean identities but no anchored small-damping energy producer; its suggested period-diagonal chain does not control the reciprocal clock correction.
