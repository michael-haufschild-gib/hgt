# BAG growing coprime cofactor limit

For primes up to N and L=log N, put s=1-u/L, with nonzero complex
parameter u. The actual coprime principal-character cofactor satisfies

C_N(s) -> -exp(-gamma-P(u))/u,
P(u)=integral_0^1 (exp(u*t)-1)/t dt.

The integrand is extended continuously with value u at zero, using
u*dslope(exp,0,u*t). This is an actual growing-cutoff law; no RH premise.
The nonzero parameter is represented by the domain Complex units.

Proof. Complex prime-window weak convergence follows from the corpus real
weak limit applied to real and imaginary parts. Thus sum_(p<=N)
(exp(u*log(p)/L)-1)/p tends to P(u). For q=p^(-1+u/L), the logarithmic
error log(1-q)+q has norm at most 2|q|^2 once |q|<=3/4. The corpus radial
bounds give |q|^2<=p^(-3/2) eventually, uniformly in p. The difference
from the balanced error vanishes termwise and is dominated by 4*p^(-3/2).
Dominated convergence therefore proves the full logarithmic ratio limit.
Exponentiating the finite sum, with each factor nonzero, proves
product_(p<=N)(1-p^(-1+u/L))/(1-1/p) -> exp(-P(u)). No logarithm of a
product or unstated branch identity is used. The zeta residue gives
(-u/L)*zeta(1-u/L)->1. The exact corpus cofactor identity and Mertens'
product law A_N*L->exp(-gamma) finish the displayed limit.

Corpus dependencies: MertensPrimeWindowWeakConvergence,
MertensThirdTheorem, SquarefreeCriticalNormalCone,
ChiRamanujanCofactorPole. All proof steps now have Lean proofs in
ChiRamanujanMovingCofactorLimit. The complete two-variable labelled
source and physical pole/near-cone/tail cancellation remain open.
