# RP-49: native prime-entry signed correlation

Status: active paper attempt; no new estimate or Lean theorem.
Route: RP, unconditional native history floor.

RP-48 supplied no critical bound. This attempt retains arithmetic jumps
when testing the midpoint/terminal energy, rather than applying the smooth
convolution diagnostic directly to the native source.

Plan: identify the exact signed prejump work from the corpus, try a joint
estimate with the continuous drift and full terminal state, then formalize
only a dependency-closed new arithmetic bound. The squared jumps are
already paid by CCMPrimeEntryJumpBudget and are not the open problem.
No positive-square admission, martingale orthogonality of actual jumps,
RH premise, or missing source-domain transfer may be assumed.

The existing CCMPrimeDeficitChronologicalWork balance is positive causal
storage plus integrated critical energy equals2+2*work+jumpBudget.
Work is the full continuous forcing minus ccmPrimeEntryPrejumpWork; the
latter samples D(log n)+2*(n-psi(n)+Lambda(n)) with weight Lambda(n)/n.
Every proper prime power and the self-jump must remain. Positivity yields
a lower bound for work, while the required estimate is an upper bound.

The corpus also has an exact residue-martingale split. Its orthogonal part
is bounded, but predictableDrift is retained. Check the actual coefficient
and measure definitions before attempting to use it on the RP source.
No estimate for that drift has yet been derived in this attempt.

## Finite jump calculation (paper, not a new formal theorem)

Set F_n=psiDefect n and c_n=Lambda(n)-1 for n>=2. Then
F_n=F_(n-1)+c_n. For the literal floor profile q(t)=exp(-t)*F_floor(exp t),
put a=1-epsilon,0<epsilon<1. Between entries q'=-q. At log n its
jump is c_n/n and its left value is F_(n-1)/n. Keeping the endpoint
after its jump gives, for T>=0 and N=floor(exp T),

    exp(a*T)*q(T)^2 + (2-a)*integral_0^T exp(a*t)*q(t)^2 dt
      = F_1^2 + 2*sum_(2<=n<=N) F_(n-1)*c_n/n^(1+epsilon)
                + sum_(2<=n<=N) c_n^2/n^(1+epsilon).

Thus the integer entries omitted by a prime-only smooth model are included.
The squared-jump term is paid by the existing logarithmic-square Mangoldt
budget plus the harmonic integer budget, with positive damping. The new
estimate sought is an upper bound for the signed middle sum, uniformly in
N. No such upper bound was proved.

This calculation also diagnoses why a direct Cauchy estimate fails.
Pairing with the admitted squared-jump sum leaves the state trace
sum F_(n-1)^2/n^(1+epsilon), whereas the continuous energy has cell weight
of order n^(-2-epsilon). Using the latter weight instead makes the other
Cauchy factor sum c_n^2/n^epsilon. Its uniform admission for0<epsilon<1
does not follow from the jump budget. No missing factor of n is dropped.

Weighted telescoping does not resolve the covariance. With w_n=n^(-1-epsilon),
for N>=2 it gives exactly

    2*sum_(2<=n<=N) w_n*F_(n-1)*c_n + sum_(2<=n<=N) w_n*c_n^2
      = w_N*F_N^2-w_2*F_1^2
          +sum_(2<=n<N) (w_n-w_(n+1))*F_n^2.

The right side retains the positive terminal square and all state energy.
It provides no upper estimate from the already-paid jump term. The actual
profile relation g'=q/2-3*g/2 transfers a bound for the weighted q energy
to g, but supplies no bound for q itself. Another wrapper of these exact
balances would not move the arithmetic frontier.

## Residue-martingale carrier audit

Read EulerDeletionResidueMartingale's sourceVec_energy,
source_eq_martingale_add_drift, source_drift_norm_gap, and
signedInnovation_eq_zero_of_not_prime. The source is the residue carrier
with raw coefficients mu(n), in the cell measure with weight
1/((j+1)*(j+2)). Its scalar products are not the native chronological
jump products. The norm gap to predictableDrift is at most sqrt(2), so
the bounded orthogonal component does not estimate that drift. No transfer
to the RP physical head or estimate of the retained drift was established.

The actual critical Abel autocorrelation also has cofinally negative
values, already proved in MobiusDivisorCriticalCorrelationTailSign.
Replacing signed delay products by a blanket eventual positivity assertion
would conflict with this source theorem. Its continued transform is not
an admission certificate for the critically weighted square.

Current outcome: no new critical estimate, Lean theorem, RH proof, or
falsification. The live arithmetic obligation is the signed prejump sum
with its full terminal square; squared-jump summability and a martingale
identity do not pay it. This is not a retirement theorem for Route RP.

The follow-up drift search located stronger existing results: the entire
possibly unbounded drift reduces to one signed logarithmic-clock quotient,
with bounded innovation and vanishing high-clock error. The quotient's
norm is retained in that inequality. Another existing theorem rules out
energy-exponent uniform integrability of the raw drift and localizes its
failure of strong convergence beyond every fixed physical cutoff. This
does not prove unbounded norms, nor does it decide RP's native history.
No compactness or uniform-integrability completion is substituted for the
missing signed quotient estimate.
