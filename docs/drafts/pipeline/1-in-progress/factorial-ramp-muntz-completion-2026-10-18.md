# Factorial-ramp arithmetic completion

Status: IN PROGRESS. Route: RW; framework: BiScaleUncertainty.
Ultimate goal remains unconditional RH in Lean; this card does not redefine it.

## Current evidence

`FactorialWeilGramDecoupling.lean` leaves the literal ramp diagonal unsigned.
`CCMBVMuntzSummation.lean` proves that the arithmetic sum of a bounded,
compact, bounded-variation, zero-mean seed has Mellin transform zero at every
zeta zero in the right half-plane. No matching seed for the actual factorial
ramp is presently identified by the inspected source.

## Conjecture and hostile audit

Let N=n+1, epsilon=sourceFactorialCollar N, and r=clampedRamp epsilon.
Set b_N(t)=1_(t>0)[r(t/(4N))-4r(t/(2N))+4r(t/N)].
Conjecture: its full arithmetic sum A_N(t)=sum_(j>=1) b_N(jt)
is an explicit zero-mean Muntz completion of the actual ramp:

* exp(x/2) A_N(exp x)/sqrt(N)=sourceFactorialRamp N x for x>=0;
* A_N is uniformly bounded independently of N;
* its Mellin transform vanishes at every right-half-plane zeta zero;
* the omitted negative-logarithmic tail has an explicit O(1/N) square mass.

The seed is arithmetic and independent of zeros. No RH or Weil sign is assumed.
The positive/negative tail split must be justified; identifying a null completion
does not make either truncated piece null or positive. The previous balanced
source coercivity cannot supply the pure-ramp sign because the tent cancels.
Verdict: SURVIVES PRELIMINARY ATTACK as a source identification and tail producer,
not yet a solution of the diagonal-sign problem.

## Plan and proof obligations

1. Prove seed support, bounded variation, and exact zero integral before Lean.
2. Identify the entire positive-logarithmic half with the actual compact ramp,
   retaining cutoff endpoints and the positive collar.
3. Prove the uniform arithmetic-sum bound, quantitative missing-tail bound,
   and source-specific Muntz annihilation theorem.
4. Audit direct leaf modules, axioms, imports, index, and formal lint.

## Dependency-closed paper proof

Write p_a(t)=1_(t>0) r(t/a), a>0. It is measurable, bounded between zero
and one, and supported in (0,a(1+epsilon)]. On the whole real line,
p_a(t)=r(t/a)-1_(t<=0). Each term on the right is antitone with range
[0,1], hence has variation at most one. For
b=p_(4N)-4p_(2N)+4p_N, the shared step has coefficient -1, so the
triangle inequality for finite partition variations gives Var(b)<=10.
There is no numerical experiment in this estimate.

Scaling Lebesgue measure gives integral p_a=a integral p_1. Therefore
integral b=(4N-8N+4N) integral p_1=0. Its support is (0,L],
L=4N(1+epsilon). The corpus Muntz theorem now applies with every seed
premise discharged. It gives Mellin(A)(rho)=0 at every zeta zero with
Re(rho)>0. Its Riemann-sum estimate also gives |A(t)|<=Var(b)<=10.

For x>=0, t=exp(x)>=1. For j>K, with K in {N,2N,4N}, the collar
budget epsilon K<=1 implies jt>=K+1>=K(1+epsilon), so p_K(jt)=0.
Thus each infinite sum truncates exactly at K, including all atomic
endpoints. Distributing the three finite sums gives
exp(x/2) A(exp x)/sqrt(N)=rampBiNull epsilon N x, precisely the actual
sourceFactorialRamp N. For x<=0 the latter is identically zero.

Define F(x)=exp(x/2) A(exp x)/sqrt(N), and T(x)=1_(x<0) F(x).
The previous equality and the zero value at x=0 prove F=R+T pointwise.
Measurability follows from locally finite arithmetic sums. On x<0,
|T(x)|<=10 exp(x/2)/sqrt(N), so T squared is integrable and
integral T(x)^2 dx <=100/N, since integral_(-infinity,0) exp(x) dx=1.
This establishes every claimed source identity and tail estimate without
an arithmetic or spectral sign premise. The full Weil sign remains open:
small L2 tail mass does not control the singular archimedean energy.

Paper status: proved as above. Lean status: pending. In particular no claim
of a proved compact-source Weil sign or RH is made.

### Exact compact-source readout

For Re(s)=sigma>0, the logarithmic readout of F is
integral exp((s-1/2)x)F(x) dx = Mellin(A)(s)/sqrt(N), by t=exp(x).
It is an admitted integral: F vanishes above log L and its weighted absolute
value is at most 10 exp(sigma x)/sqrt(N) below log L.
The compact ramp readout is admitted by continuity and compact support.
The tail readout is consequently admitted as their difference. At any
right-half-plane zeta zero rho, the full readout vanishes, so the actual
compact-ramp readout equals minus the omitted-tail readout. Moreover,
its absolute value is at most
10/sqrt(N) integral_(-infinity,0) exp(Re(rho)x) dx
=10/(sqrt(N) Re(rho)). This also supplies a quantitative source-specific
zero-readout producer, without assuming RH or dropping the omitted tail.

## Constraints

Corpus only; no web or novelty claim; no numerical experiments. README files and
RH frontier map remain read-only. No full/umbrella build, added axioms, proof
debt, heartbeat increase, commit or push. Existing concurrent ramp-diagonal and
cycle work is outside this card's write scope.
