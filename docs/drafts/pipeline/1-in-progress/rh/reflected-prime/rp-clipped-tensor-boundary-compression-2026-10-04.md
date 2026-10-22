# RP-65: exact compression of the clipped tensor boundary

Route RP. Hard targets remain positive-damping negative work,
signed high-LCM control, and both native history debts. RP-63
gave verified projection sharpness; RP-64 gave no critical payment.
This trial attacks the joint differences at the physical cutoff,
without replacing their lower faces by fixed-core limits.

## Initial conjecture and source check

Candidate mechanism: the zero product faces at d>=M might make the
high-order Schur remainder a small boundary contribution, permitting
the fixed-core profile estimate to extend to the native moving core.

The corpus distinguishes zero top fibres from zero mixed differences:
MobiusDivisorSmallCoreInteractions proves zero joint fibres when
p*q>=M, while retaining lower-face interactions; its exact mixed
energy cutoff filtering does not set those interactions to zero.
MobiusDivisorAllOrderBooleanSign proves alternating signs at the
empty processed core. Its extension to a late core requires the
residual-head sign explicitly. This cannot be used as unconditional
positivity at every intermediate core.

## Exact regrouping of every boundary face (paper)

Keep the RP-64 notation. For R subset P put r=product R and

    H_R^+(M)=sum_(d|r,d<M) mu(d)*A(M,d)/theta(d).

The superscript here denotes amplified coefficients, not positivity.
Expanding the definition of D_R, including every zero top channel,
gives exactly

    D_R a=(-1)^|R|*theta(R)*H_R^+(M),
    E_P(M)=sum_(R subset P) pi_P(R)*H_R^+(M)^2,
    pi_P(R)=theta(R)^2*gamma(P\R),
    sum_R pi_P(R)=product_(p in P)(theta_p^2+gamma_p)=1.

Thus the full boundary is an exact square average of amplified
heads retained with coordinate probability theta_p^2. A product
r>=M does not make H_R^+ vanish: its proper divisors below M
remain. This is not a negligible omitted-face remainder.

For an additional coordinate p with all its source coefficients
zero, the two Schur terms combine by

    gamma_p*(D_R a)^2+(-theta_p*D_R a)^2=(D_R a)^2.

Zero coordinates redistribute energy between Schur grades rather
than eliminate it. Any estimate that drops the high grade on the
basis of its zero top coefficient is invalid.

To remove artificial tensor coordinates completely, expand the
square average and sum its finite product probabilities. For active
squarefree d,e<M, the resulting coefficient is

    theta(d union e)^2/(theta(d)*theta(e))
      =theta(d)*theta(e)/theta(gcd(d,e))^2.

Writing beta(r)=product_(p|r)(theta_p^(-2)-1), expand
theta(gcd)^(-2)=sum_(r|gcd)beta(r) and retain the actual cutoffs:

    E_P(M)=sum_(squarefree r<M) beta(r)*F_r(M)^2,
    F_r(M)=sum_(d<M,r|d)mu(d)*theta(d)*A(M,d),

when P contains all active primes. This is exactly RP-63's positive
divisor-fibre decomposition. No boundary term has disappeared and
no new negative term pays its mean-head square F_1^2.

This defeats the proposed shortcut through zero top faces; it does
not disprove the full covariance bound. Both exact decompositions
are paper calculations here, not a new Lean-certified estimate.
The full moving-cutoff conjecture remains active.

## Further source check: signed clock transport

MobiusDivisorCriticalClockProductTransport keeps the copied diagonal,
earlier boundary, and signed mixed correlation exactly. Its squarefree
density cancellation makes the density-weighted energy change plus
the signed mixed term equal a nonpositive boundary surplus. It does
not bound the mixed term from below. Substituting the existing
RP-52 undamped balance would restore the unpaid negative work,
not pay it at positive damping.

CoupledFloorMobiusCriticalBoundaryCancellation does prove a critical
L2 cancellation, but for Suzuki's shifted coupled error with parameter
0<omega<1/2 and normalization exp(-(1+omega)t). Its header and
statement retain the graph/source-order debt. It is not an estimate
for the native RP head or this covariance. No transport between these
different sources has been assumed.

## Remaining direct attack

Independent Cauchy recovery is sharp (RP-63). Tensor completion
returns the same actual cofactor heads, with their cutoff intact.
The remaining target is a joint estimate for those heads, retaining
their arithmetic relations across r; neither decomposition bounds
them independently. A useful next test is to expand the exact
prime-deletion recursion simultaneously for several cofactors and
retain its cross terms before applying any norm inequality.

That test produced the now-formalized native comparison recorded in
`../../../3-formalized/rp-native-biased-covariance-window-comparison-2026-10-04.md`.
On a finite log window, causal prime translation has norm at most
1/sqrt(p). Exact inverse deletion therefore costs
(1-theta_p/sqrt(p))^(-1), rather than the pointwise Schur recovery
cost from RP-63. Summing the covariance costs gives an Euler product
with summable O(p^(-2)) increments. A second, reversible Euler
correction has summable O(p^(-3/2)) increments and compares the
biased mean with the original native head. Both directions keep
the terminal cutoff. The result removes an additional covariance
norm debt but does not bound native square energy. Lean audit pending.

No critical debt paid this turn, no RH proof or falsification, and
no external blocker. No conditional bound has been promoted to an
unconditional theorem.

## Search audit

Joint-boundary deep search: generation 1220706, coverage
1220721/current 1220722, 65070 files; partial=false, no errors or
unfinished stages. Candidate lemmas, source arguments, and proposed
ingredient sets inspected. The ingredients did not supply a native
joint estimate.

Direct history-floor search: generation 1220725, coverage
1220740/current 1220741, 65072 files; partial=true because
semantic_retrieval hit its runtime deadline. Available hits were
used. The suggested floor chain explicitly invoked
routeP_history_linear_floor_of_RH and therefore was circular for
this goal; the credit-escape theorem was an upper bound, not the
required lower payment. No retry solely for partial coverage.

Both searches reported unmeasured semantic coverage, incomplete
background refresh, and predominantly pending/stale/unavailable
compiler states. Current source statements were inspected directly.
