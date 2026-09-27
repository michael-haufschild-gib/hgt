# Signed boundary reflection and forced Noether balance (2026-09-27)

Active goal: prove RH through arithmetic conservation/action identities. RH is UNPROVED. This turn makes verified structural progress on the actual signed boundary defect; it does not prove a global cancellation bound.

Repo /Users/michael/Documents/code/hgt/formal. No subagents, commits or pushes. Sequential foreground leaf checks with lake --old env lean FILE -o matching .olean. No full/umbrella builds, computations, custom axioms, sorry, or heartbeat overrides.

## Mathematics
Notation from mem:research/noether_cubic_shortened_cutoff_and_boundary_variation_2026_09_27:
D actual integrated prime deficit; A_m full-source coefficient action retaining mu through m; w=tail_m mu; H actual divisor source; m>0 and 3k<=m.
For T<=2log(m+k), H(T-log(ab)) = max(exp(T-log(ab))-1,0) whenever a,b>m.

Generic kernel:
K(t)=max(exp t-1,0).
K(T-p-q)=integral_0^T [1_{s>=p} exp(s-p)] [1_{T-s>=q}] ds, p,q>=0, all real T.
Finite signed coefficients w,v and any U:
sum_{a,b<=U} w(a)v(b)K(T-log(ab))
= integral_0^T Fexp_w(s) Fone_v(T-s) ds.
All integrability and finite interchange proved. No infinite interchange or loss of signs.

Actual profiles capped at U=m+3k:
X(t)=ccmPrimeDeficitBoundaryExpProfile m k t;
Y(t)=ccmPrimeDeficitBoundaryCountProfile m k t.
For 0<=T<=2log(m+k):
D(T)-A_m(T)=integral_0^T X(s)Y(T-s) ds.
OffDiagonal = same integral minus previously bounded Diagonal.

## Autonomous oscillator on a frozen arithmetic prefix
M_N=sum_{1<=n<=N} w(n); R_N=sum w(n)/n.
q_N(t)=exp(t/2) R_N - exp(-t/2) M_N.
p_N(t)=(exp(t/2) R_N + exp(-t/2) M_N)/2.
Proved q'_N=p_N and p'_N=q_N/4.
Action S[q,p;a,b]=integral_a^b (p^2+q^2/4) dt.
Translation identity S[q(.+r),p(.+r);a,b]=S[q,p;a+r,b+r].
These are the autonomous Euler-Lagrange equations for this Lagrangian.
Energy E_N=p_N^2-q_N^2/4=R_N M_N, derivative zero.
This is local/frozen-prefix conservation; arithmetic entries force the system.

At t_n=log(N+1):
q_{N+1}(t_n)=q_N(t_n).
p_{N+1}(t_n)-p_N(t_n)=w(N+1) exp(-log(N+1)/2).
Energy jump =
w(n)(R_{n-1}+M_{n-1}/n)+w(n)^2/n.

## Actual moving field and reflection
N(t)=min(m+3k,floor(exp t)).
Actual q(t)=exp(-t/2)(X(t)-Y(t)), p(t)=exp(-t/2)(X(t)+Y(t))/2.
These equal q_{N(t)}(t), p_{N(t)}(t) for actual w.
Actual q is continuous at all times, via finite ramp sum:
q(t)=exp(-t/2) sum_{n<=U} w(n)K(t-log n).
Momentum impulses are retained, not assumed absent.

Critical identity:
exp(-T/2)(D(T)-A_m(T))
= integral_0^T [p(s)p(T-s)-q(s)q(T-s)/4] ds.
Proof symmetrizes X(s)Y(T-s), uses reflection invariance of the interval integral, and exp(-s/2)exp(-(T-s)/2)=exp(-T/2).
Every moving cutoff remains literal.

## Exact signed Noether forcing balance
W_N=sum_{1<=n<=N} w(n)(R_{n-1}+M_{n-1}/n), independently defined from prefix sums.
J_N=sum w(n)^2/n >=0.
R_N M_N = W_N + J_N, proved by telescoping actual entry jumps.
For w=tail_m mu and N<=m+3k:
0<=J_N<=3k/m<=1.
Thus for every real t and m>0,3k<=m:
|p(t)^2-q(t)^2/4-W_{N(t)}|<=1.
This controls charge minus actual signed work, NOT signed work or full charge separately.

On every pair of frozen prefixes:
d/ds [q_N(s)p_M(T-s)] = p_N(s)p_M(T-s)-q_N(s)q_M(T-s)/4.
d/ds [p_N(s)p_M(T-s)+q_N(s)q_M(T-s)/4]=0.
The current and conserved bilocal charge have different signs. Do not confuse them.
Global integration of current jumps for the moving field has not yet been separately formalized.

## Five leaves, 36 public theorems
- LogarithmicExponentialEntryConvolution: 6 public. Generic causal ramp/entry integral, finite signed profile pair integrability and equality.
- LogarithmicMellinPrefixOscillator: 12 public. Action translation, ODEs, charge, jumps, entry continuity, conversion from finite profiles to actual partial sums.
- CCMPrimeDeficitBoundaryReflection: 4 public. H=ramp, actual profile integrability, full defect reflection, offdiagonal reflection.
- CCMPrimeDeficitBoundaryOscillator: 6 public. Moving-prefix correspondence, actual charge, reflected density, integrability, exact normalized defect identity.
- CCMPrimeDeficitBoundaryNoetherBalance: 8 public. Actual position ramp sum/continuity, reflected current and charge derivatives, global entry-work balance, diagonal nonnegativity/budget, uniform <=1 residual balance.

## Limits and next work
No RH proof; retained action A_m and actual signed cross work remain uncontrolled. The Noether energy is indefinite. Translation invariance is with translated endpoints and frozen arithmetic prefix; do not claim full forced system has autonomous global time-translation symmetry. No abstract Noether theorem was invoked to infer a missing bound: flow/action/charge identities are derived directly.

Next concrete route:
1. Integrate the reflected current piecewise across actual entry times, keeping every jump, to derive an explicit reflected impulse-work law. Then seek cancellation in that actual work using mu*1=delta.
2. Extend beyond the local H=ramp window. H is a divisor-weighted exponential ramp minus a log-weighted linear ramp. Formally expect tail pairing to factor through residual coefficients r=w*1 and s=w*log=r*Lambda:
Q_H = integral [Fexp_r(s)-Fone_s(s)] Fone_r(T-s) ds.
For w=mu this gives r=delta, s=Lambda, recovering the full prime deficit. This general-cutoff reflection formula has NOT been proved in these five leaves and should first be searched in the corpus. It may connect the presently uncontrolled retained action to a forced oscillator with literal prime forcing.
Never assume the signed-work bound or positivity.

## Lean fixes
- Continuous.sub_const absent in this import environment; use continuous_id.sub continuous_const.
- Avoid a newline before field notation .const_mul.
- For explicit derivative formulas use HasDerivAt.congr_deriv then ring, avoiding convert generating needless function-equality goals.
- Derivative of reflected products leaves Function.comp_apply; simp only [Function.comp_apply] before ring.
- sq_le_one_iff_abs_le_one is available.
- IntervalIntegrable.comp_sub_left reverses endpoints; use .symm then simpa for [0,T].
- integral_comp_sub_left f T (a:=0)(b:=T) establishes reflection symmetry without extra hypotheses.


## Validation checkpoint
All five leaves passed final foreground lake --old env lean FILE -o ... audits.
Combined #print axioms audit covered all 36 public theorems and exited 0; dependencies only propext, Classical.choice, Quot.sound.
Fresh object timestamps, exactly one RHTower umbrella import per leaf, no forbidden constructs/trailing whitespace, and umbrella git diff --check verified.
Scratch /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/BoundaryNoetherAxiomAudit.lean removed. No own Lean or lint process remains.
Index refreshed, then refreshed once again after a stale-metadata report. Global lint still reports 26 unrelated unreachable modules plus stale formal/LEAN_API.md amid concurrent work. Do not claim global lint clean or modify unrelated unfinished modules.
Current five leaves are untracked and umbrella modified (concurrent commits may later change this). No commit/push performed.

## Immediate algebraic conjecture to test next
An exact reflected impulse-work identity should follow directly from the proved ramp sum, without first developing a piecewise integration theorem:
exp(-T/2)(D(T)-A_m(T)) =
sum_{n<=m+3k} w(n) exp(-log(n)/2) q(T-log(n)).
Here q is the actual ccmPrimeDeficitBoundaryPosition, w=tail_m mu; same boundary-window conditions apply.
Expand q with ccmPrimeDeficitBoundaryPosition_eq_ramp_sum, expand sums, and combine exp(-log n/2)*exp(-(T-log n)/2)=exp(-T/2).
The remaining double sum is exactly the established defect ramp pairing.
This was derived on paper but NOT yet formalized or claimed verified. It would make the actual forcing target explicit before attempting its arithmetic cancellation.
