# TG diffuse neutral Möbius work

- **ID:** TG-C9.25
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TG, actual signed arithmetic source
- **Statement:** A diffuse harmonic-neutral extension of the literal square-root Möbius head preserves the actual prime-deficit action. Complete pole subtraction pays its entire linear channel and absolute diagonal at critical scale; the full signed quadratic channel remains open.

## Literal construction

For an integer N, write h_N=sum_(1<=n<=N) mu(n)/n. Define

    a_N(n)=mu(n)                  when n<=N,
    a_N(n)=-(n/N)*h_N             when N<n<=2N,
    a_N(n)=0                     when n>2N.

The definition is total at N=0; the actual cutoff N=floor(exp(T/2)) has N>=1 for T>=0. No Möbius coefficient in the head changes.

Let c=1+gamma, F=ccmPrimeDeficitDilationSource, and use the complete divisor remainder R proved in C9.24A. Put

    F0(t)=F(t)-c exp(t),
    L(T)=2 sum_(n=1..2N) a_N(n) F0(T-log n),
    Q(T)=sum_(m,n=1..2N) a_N(m)a_N(n) R(T-log m-log n),
    Bdiag(T)=sum_(n=1..2N) a_N(n)^2 |R(T-2log n)|.

The final theorems prove, unconditionally,

    sum_(n=1..2N) a_N(n)/n = 0,
    D(T)=L(T)-Q(T),
    |L(T)| <= K1 exp(T/2)(T+1)^2,
    Bdiag(T) <= K2 exp(T/2)(T+1)^4,

for fixed positive constants K1,K2 and every T>=0. D is the literal ccmLogChebyshevDeficitPrimitive. Both channels include the full diffuse tail. Every mixed and negative shifted-time term remains in Q.

## Dependency-closed paper proof

1. Split [1,2N] into [1,N] and [N+1,2N]. Each of the N tail terms contributes exactly -h_N/N to the harmonic moment; its sum cancels h_N. The zero case is immediate.
2. The coefficient vector is exactly a logarithmicMobiusHeadExtension. The corpus's stationary head-extension theorem identifies its full reconstruction action with D(T).
3. For a causal source and coefficients supported on [1,2N], extend the moving dilation sum to that entire interval. Terms above the physical cutoff vanish by causality. Applying this twice expands the actual quadratic action into the full finite square, retaining all pairs.
4. The exponential moment equals the harmonic moment. Its vanishing removes c exp(t) from the complete linear source and removes both exponential coefficients from H's complete finite-pair pole. C9.24A's global R, including negative times, gives exactly D=L-Q.
5. The corpus's uniform centered dilation remainder gives F0(t)=O(t+1) for t>=0. For t<0, F(t)=0 and |F0(t)|<=|c|. Thus |F0(t)|<=C(max(t,0)+1) globally, with a fixed positive C.
6. The elementary inequalities |mu(n)|<=1 and harmonic(N)<=1+log N give |h_N|<=1+log N. On the diffuse tail, n/N<=2; hence all coefficients on [1,2N] satisfy |a_N(n)|<=2(1+log N)+1.
7. At the actual cutoff, N<=exp(T/2) and log N<=T/2. Counting all 2N labels gives sum |a_N(n)|<=6 exp(T/2)(T+1) and sum a_N(n)^2<=18 exp(T/2)(T+1)^2.
8. Since every n>=1, both max(T-log n,0) and max(T-2log n,0) are at most T. Apply the global F0 envelope to the l1 mass for L. Apply C9.24A's global quadratic envelope to the squared mass for Bdiag. These prove the stated critical-scale budgets.

No RH assumption, square-root Möbius bound, sign condition on cross terms, numerical experiment, or new axiom enters this proof.

## Learning and exact remaining gap

The first single-point completion a(N+1)=-(N+1)h_N gives the same harmonic cancellation, but places squared mass (N+1)^2 h_N^2 into one coefficient. The diffuse construction avoids that unpaid diagonal. It does not suppress the entire tail block: correlations can still carry exp(T)h_N^2. Every such term remains in Q.

A two-tail attempt to force Q to vanish would require a coefficient constraint containing the unknown head quadratic value. No independent bound followed from that construction. This was a failed proof idea, not a falsification of the arithmetic target.

The corpus's reciprocal sawtooth pairing and first-half formula were inspected. Reflection doubles a symmetric half-integral; it does not cancel it. The actual first-half profile is

    exp(t)*sum_(n<=exp(t))mu(n)/n - 1 - (1/2)*sum_(n<=exp(t))mu(n).

Separating these terms loses the required cancellation. Search ingredients involving diagonal bounds or midpoint symmetry do not prove an upper bound for the complete signed work.

The hard open target is an unconditional critical-scale polynomial estimate for this specific Q(T), retaining all unequal-label terms and the original head. This card supplies no such bound and no native soninPrimePolarGridEnergy summability. Full joint Hardy cubic compatibility and strict contraction also remain open. Further coefficient-tail redesign or another equivalence wrapper would not discharge the missing signed estimate.

## Corpus evidence

/tmp/tg-c925-neutral-work-search.json and /tmp/tg-c925-midpoint-work-search.json completed nonpartial with complete source inventories; background compiler refresh remained incomplete. Candidate lemmas, source arguments, proof ideas and ingredient sets were inspected. Relevant source statements were checked against their Lean files and the final leaf.

## Lean certificate

Leaf: formal/GaloisForLFunctions/RHTower/CCM/CCMPrimeDeficitNeutralWork.lean, 367 lines, four public theorems and five definitions:

- ccmPrimeDeficitNeutralCoefficient_harmonic
- ccmLogChebyshevDeficitPrimitive_eq_neutral_work
- ccmPrimeDeficitNeutralLinearWork_critical_bound
- ccmPrimeDeficitNeutralDiagonalBudget_critical_bound

Final foreground lake --old env lean GaloisForLFunctions/RHTower/CCM/CCMPrimeDeficitNeutralWork.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCM/CCMPrimeDeficitNeutralWork.olean: exit 0, no diagnostics. Import wired in RHTower. Separate /tmp axiom audit: exit 0, all four theorems use only propext, Classical.choice and Quot.sound. Index: exit 0; all nine API entries verified. Authoritative scripts/formal_tools.py lint: exit 1 on sixteen unrelated unreachable modules, with no finding for this leaf. Logs: /tmp/tg-c925-neutral-work-{final,axioms,index,lint}.log. Audit source: /tmp/tg-c925-neutral-work-axioms.lean.
