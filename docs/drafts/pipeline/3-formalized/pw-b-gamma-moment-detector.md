# PW-B complete signed high-order moment detector

- **ID:** PW-B-GAMMA-MOMENT-DETECTOR-2026-09-11
- **Status:** Paper proof, Lean scratch verification and targeted leaf build passed; formal lint passed.
- **Route:** PW-B remains live. RH is not proved.
- **Depends on:** [reciprocal Gamma moment bounds](pw-b-gamma-reciprocal-moments.md).
- **Continuation:** [actual reversible pairing](../1-in-progress/pw-b-gamma-reversible-pairing.md).

## Actual source theorem

For every complex z and natural k, the original integral

`J_k(z)=integral_(x>0) [exp(-x)/x^(k+3)]*[M_z(1/x)/Q(1/x)-1] dx`

is absolutely admitted. Its complete signed series is

`J_k(z)=sum_(n>=0) c_n(z)*I_(k+2)(n+1)`,

where `c_n(z)=mu(n+2)*sqrt(n+2)*exp(-z*log(n+2))` is the actual
arithmetic coefficient, and the positive endpoint moment I is defined
in the preceding card. No term is discarded.

The claimed detector is

`J_k(z)/(k+1)! -> c_0(z)=-sqrt(2)*exp(-z*log(2)) != 0`.

Consequently every sufficiently high J_k(z) is nonzero, for each fixed z.
No uniform starting order in z is asserted.

## Complete proof mechanism

Choose N with norm(z)<=N. The source coefficient theorem gives
`norm(c_n(z)) <= 2^(N+1)*(n+1)^(N+1)`.
The arbitrary-power positive-kernel bound with l=N gives

`norm(c_n(z)*I_(k+2)(n+1)) <= C_(N,k)/(n+1)^2`,

where `C_(N,k)=2^(N+1)*(k+3+N)!*N!`. This proves admission at every
fixed k. The integral of the norm of each signed kernel atom is exactly
the norm of its integrated atom, because its real kernel is positive.
Their norm-integral sum is therefore finite. Integrable-series assembly
and Bochner interchange identify the full series with J_k(z), using
the exact original normalized source expansion.

For all k>=N+1, the sharper Gamma squeeze gives the order-independent
bound

`norm(c_n(z)*I_(k+2)(n+1)/(k+1)!) <= 2^(N+1)/(n+1)^2`.

The n=0 normalized mode tends to one; each n>=1 normalized mode tends
to zero. Dominated convergence for the entire series recovers c_0(z).
Its nonzero value follows from mu(2)=-1, sqrt(2)>0 and the nonvanishing
of the complex exponential. Convergence to this nonzero value implies
eventual nonvanishing of J_k(z).

## What this resolves and what remains

This resolves the high-order moment-detection step for the actual signed
source, with the Lean scratch proof closed. It does not
extract moments from the original reciprocal-current cutoff. That
extraction remains necessary before excluding the unit-ground-corrected
scalar ansatz. Full source adjoints/common domains, actual Xi occurrence
and independent fixed-grade Ward balance also remain open.

For the next attack write S_z(t)=M_z(1/t)/Q(1/t)-1 and
`C_z(v)=integral_(h>0) exp(-h)*(S_z(v+h)-S_z(v))/h dh`.
Split at h=v. The existing complete kernel flat bound controls 0<h<v
at arbitrary powers of v. On h>=v put t=v+h and expand 1/(t-v) as a
finite geometric sum. Its remainder is bounded by
`2*v^(m+1)*integral_(t>0) exp(-t)*norm(S_z(t))/t^(m+2) dt`.
The omitted 0<t<2v moment pieces and S_z(v) times the logarithmic loss
are flat by the complete source exponential-series bounds. This should
give

`exp(-v)*C_z(v)=sum_(j<=m) B_j(z)*v^j+O(v^(m+1))`,

with `B_j(z)=integral_(t>0) exp(-t)*S_z(t)/t^(j+1) dt`.
The already proved all-power current flatness would force all B_j=0,
contradicting the high-order detector B_(k+2)=J_k. This cutoff expansion
and its induction are not yet Lean theorems.

## Verification and searches

Scratch passed with exit code 0. Exact source is promoted in `ThetaCuspHawkingParikhWilczekGammaMobiusMomentDetector`, with one umbrella import. The targeted leaf build passed in 175 seconds; dependencies were replayed. Formal lint passed. One informational ring-normalization suggestion was emitted; there were no proof errors.
The coefficient deep/method search is retained with the
[kernel search records](../1-in-progress/pw-b-gamma-reciprocal-moments-searches.json).
Its actual Abe/Tannery source requires precisely a fixed summable majorant;
its generated Julia-volume ingredient plan does not prove the source claim.
The third deep search on finite geometric cutoff remainders returned partial coverage of 730859 indexed declarations with no reported errors. All twenty candidate and twenty source-argument statements were inspected. Its analytic-series approximation requires a premise that is unavailable here; its generated geometric/cutoff plan does not supply the actual moving-boundary estimates.
No axiom-print checks or numerical experiments are used.


## Convergent-series attempt fails; finite asymptotics survive

The [moment-series obstruction](../5-failed/pw-b-convergent-endpoint-moment-series.md)
is now proved in Lean with targeted leaf build passed: for every nonzero complex w, the actual
terms J_k(z)*w^k fail to tend to zero. Multiplying a hypothetical zero
limit by the reciprocal factorial/geometric factor would contradict
the verified nonzero normalized moment limit. Therefore a convergent
power-series API cannot supply the desired endpoint coefficient
extraction. The finite asymptotic expansion and explicit remainder
mechanism above remain the next mathematical attack. This says nothing
about analyticity of the actual current until that extraction is proved.
