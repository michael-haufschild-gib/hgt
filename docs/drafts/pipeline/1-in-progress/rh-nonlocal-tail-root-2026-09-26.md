# Nonlocal theta-tail sign: coupling and the joint rank boundary

- **ID:** RH-NONLOCAL-TAIL-ROOT-20260926
- **Stage:** 1-in-progress
- **Type:** [BRIDGE] mechanism tests; RH unresolved
- **Owner:** root; facts in `rh-reflection-source-sign-2026-09-26-facts.md`
- **Target:** produce the literal full-source kernel sign in every rank.

## Scientific interrogation and plan

The fixed finite local Gram ansatz is excluded in Lean. A scientist should now test
a genuinely nonlocal representation, preserving the full theta source. The obstacle
is positivity as a quadratic form, not entrywise positivity or an upper bound.
The new primitive under examination is a symmetric source coupling. No universal
conjecture or successful RH producer is claimed.

1. Audit the coupling identity and distinguish Markov positivity from positive spectrum.
2. Attack a candidate positive tail model uniformly in rank, rather than only at fixed rank.
3. Prove the strongest exact surviving rank law, then formalize it and audit hypotheses.

## Coupling calculation — paper candidate, not yet a theorem

Let phi be a normalized even source, and put
`K(x,y)=integral_(s>0) (x+y+2s) phi(x+s) phi(y+s) ds` and
`K_e(x,y)=(K(x,y)+K(x,-y))/2`. Corpus already proves the literal theta K is
nonnegative and supplies its double Laplace transform. The proposed zero-biased
marginal is `H(x)=integral_x^infinity u phi(u) du`; total mass is the second moment.
This makes K a candidate reversible Markov coupling after marginal normalization.
Even if verified, that construction alone permits negative eigenvalues.

For `q=-phi'`, x>=y>=0, a differentiation/IBP calculation proposes

```
d_x d_y K_e(x,y)
 = (1/2) integral_0^infinity (x+y+2s)
       [q(x+s)q(y+s)-q(x+y+s)q(s)] ds
 + (1/2) integral_0^y (x-y+2s) q(x+s)q(y-s) ds.
```

Log-concavity of q would make this nonnegative and produce a coupling of
size-biased radii. Neither that actual-theta derivative condition nor the full
identity is Lean-proved here. The retrieved likelihood-score concavity concerns
a different function. **Route consequence:** do not pursue this upper-bound
condition as if it supplied the missing lower sign.

## Frozen mechanism C2: a rank-uniform Cauchy tail approximation

The literal source first-atom approximation suggests, at large common shift R,
the normalized leading kernel

`C_R(x,y)=(2R+x+y)/(exp(2x)+exp(2y))`.

Its fixed-rank leading term is a positive Cauchy matrix. The full-source
asymptotic transfer is still an unproved dependency in this card. The mechanism
test is whether its displayed first correction can retain positivity in every
rank. This is a derived test, not an independently formed universal conjecture.

Set `u=exp(2x)`, `v=exp(2y)`, then use Cayley coordinates
`u=u0*(1+z)/(1-z)`, `v=u0*(1+w)/(1-w)`. After a positive diagonal congruence,
the kernel becomes

`[L + atanh(z) + atanh(w)]/(1-z*w)`, `L=2R+log(u0)`.

Its coefficient matrix has diagonal L and off-diagonal `1/|i-j|` for odd
`|i-j|`, zero for nonzero even difference. This is the exact symbolic model
being attacked; it is not identified with the actual theta kernel.

## Paper attack and positive survivor

Write `h_m=sum_(j<m) 1/(2j+1)` and let Q be this coefficient form on 2m
coordinates. For the alternating vector `a_i=(-1)^i`, direct grouping by lag gives

`Q(L,m,a)=2m*(L+1-2*h_m)`.

For every vector, `|Q(L,m,a)-L*sum a_i^2| <= 2*h_m*sum a_i^2`.
Indeed at lag k, Cauchy's elementary `2|ab|<=a^2+b^2` bounds the correlation
by the full energy. Therefore L>=2h_m implies PSD, whereas for m>0,
L<2h_m-1 gives an explicit negative direction. Since h_m diverges, no fixed
L works in every rank. The transition is trapped in an interval of width one.

**Whole route:** a positive fixed-rank Cauchy limit cannot justify deleting the
correction in an all-rank proof. The joint rank/shift boundary is explicit.
This neither falsifies RH nor excludes the complete nonlocal coupling route.
Next proof work must control the literal theta correction at growing rank;
source-tail transfer and positive factorization remain open.

**Status:** exact coefficient-form proof and its formal-series equation now pass
Lean scratch and the named `LogarithmicCauchyRankBoundary` build. The stronger
survivor identifies the minimizing sign pattern, excludes every uniformly
energy-bounded repair, and proves `2h_m-log m -> 2log 2+gamma`. All 36 public theorem axiom reports are standard-only;
final global lint passes. No global novelty claim.

## Next literal-source attack: moving-tail asymptotics

The exact common-shift formula makes
`K(R+x,R+y)=integral_R^infinity (2r+x+y) Phi(r+x)Phi(r+y) dr`.
The complete first-log-jet bounds in
`ThetaCuspFullReflectionFourthTuran` give the leading logarithmic slope with a
uniform bounded error. L'Hopital against `R*exp(-2R)*Phi(R+x)*Phi(R+y)` should prove

`K(R+x,R+y)/(R*exp(-2R)*Phi(R+x)*Phi(R+y)) -> 1/(pi*(exp(2x)+exp(2y)))`.

The leading bridge now passes Lean scratch. The stronger C4 below also proves
the constant correction; relative `o(1)` alone would not have justified it.
Rank-uniform transfer remains the hard source-sign problem.

The resulting C3 target is stronger than entrywise convergence: for every fixed
finite set of distinct real nodes, the literal kernel matrix becomes positive
definite after sufficiently large common translation. The threshold depends on
the whole node set. The positive Cauchy determinant and the existing
`posDef_eventually_of_tendsto` close its finite-dimensional paper step.
Scratch proof `/tmp/rh-tail-cauchy-limit.lean` passes. The leaf
`ThetaTailCauchyAsymptotic.lean` is wired; named build and all 16 public theorem
axiom audits pass. Final global lint passes.

**Route test:** C3 would include arbitrarily close fixed nodes, extending the
existing separated-packet stratum. It would not give one translation threshold
for all ranks or propagate the sign back to the seam. The existing literal
common-translation Loewner no-go still prevents that propagation argument.

## Frozen C4: retain the first correction of the literal source

Derived bridge conjecture, before Lean testing:

`K(r+x,r+y)/(exp(-2r)*Phi(r+x)*Phi(r+y))`
`  - (2r+x+y)/(2*pi*(exp(2x)+exp(2y))) -> 0`.

Set `A=pi*(exp(2x)+exp(2y))`, `d=x+y`, `P=Phi(r+x)*Phi(r+y)`,
`E=exp(-2r)`, `D=E*P`, and `T=E*(P'/P-2)`. The complete first-log-jet
bounds from `ThetaCuspFullReflectionFourthTuran` imply
`T=-2A+E*b(r)` with `|b(r)|<=16` eventually. This uses the full higher
likelihood correction; a first-atom truncation is unnecessary.

For `N=K-D*(2r+d)/(2A)`, direct differentiation gives
`N'/D'=-[(2r+d)*(T+2A)+2E]/(2A*T) -> 0`.
Both N and D tend to zero, so L'Hopital predicts C4. Its fixed-node
correction is exactly the logarithmic-Cauchy model up to a positive scalar.
**Whole route:** C4 supplies the missing two-term bridge at fixed nodes.
It does not control a rank-dependent jet or exchange rank and tail limits.
No all-rank sign follows without that next estimate.

C4 is formalized and audited as `kernel_two_term_limit`; the every-fixed-polynomial
score-error bound is also formalized. Paper proof and exact scope are in
`../3-formalized/rh-theta-tail-cauchy-root-2026-09-26.md`. Final audits pass.

## Next joint-limit input, source audited

The model law `L=2r+log(u0)` and `2h_m-log(m)->2log(2)+gamma` places its
rank transition at `m` proportional to `exp(2r)`. This is a model scale, not a
literal-theta negative direction.

`ThetaCuspFirstAtomAllOrderApproximation` fixes derivative order before taking
its limit. However, subsequent focused retrieval also found an existing
quantitative input: `ThetaCuspSupportScaleReflectionApproximation` proves

`|(Phi^(n)-first^(n))/first| <= 3*(12q)^n*epsilon`

for `q>=6`, `n+3<=q`; it also bounds the native reflection jet by
`[18*(16q)^n*epsilon+9*(24q)^n*epsilon^2]*first^2`.
Here q is the first-atom Morse scale and epsilon is the literal
`regimeOneLikelihoodScale`. The definitions and source inequalities were read;
these are existing corpus results, not new root claims. Applicability to the
kernel's Cayley coefficients and its quadratic-form energy is still unproved.
The next experiment must perform that conversion or expose its precise failure,
rather than reprove a fixed-order source approximation.

## Frozen C5: first omitted term as a growing-rank repair

[BRIDGE] Derived mechanism candidate, not a primary universal conjecture.
The exact full-source first-log jet suggests the next signed term

`[K(r+x,r+y)/D(r)-(2r+x+y)/(2A)] / [r*exp(-2r)] -> 7/(2*A^2)`,

where `A=pi*(exp(2x)+exp(2y))`, `D=exp(-2r)*Phi(r+x)*Phi(r+y)`.
The expected constant is from two source prefactors `9/2+9/2`, minus the
normalizing derivative 2. This claim is frozen before Lean checking.

After the same Cayley congruence, the squared-Cauchy factor becomes
`(1-z)(1-w)/(1-z*w)^2`. Its coefficient form is expected to equal
`sum_(n>=0) (n+1)*(a_n-a_(n+1))^2` for finitely supported a. It is positive
and unbounded relative to ordinary coefficient energy.

**Whole-route test:** the model excludes only bounded repairs. If C5 closes,
the literal source supplies a positive first repair of precisely the unbounded
kind. The question becomes control of the full remainder in this weighted
coefficient form, rather than falsely transporting model negativity using
pointwise small error. No growing-rank positivity or RH conclusion is assumed.

## C6: uniform repair by a squared-Cauchy term — derived proof candidate

[BRIDGE] This statement arose during the C5 proof attack; no primary-conjecture
or global novelty claim. For positive nodes u_i, consider

`H_(L,c)(u,v)=[L+(log u+log v)/2]/(u+v)+c/(u+v)^2`.

Candidate uniform theorem: `0<c<=1` and `L+log c>=2` imply every finite
matrix of H is PSD, independently of rank and node spacing.

Paper argument to audit: for a finite real exponential sum
`f(s)=sum a_i exp(-u_i*s)`, put `E=integral_0^infinity f^2` and
`M=integral_0^infinity s*f^2`. The logarithmic term's quadratic form is
`L*E + integral_0^infinity [exp(-t)*E-C(t)]/t dt`,
`C(t)=integral_0^infinity f(s+t)*f(s) ds`.
Cauchy--Schwarz and the first moment give
`C(t)<=E` and `C(t)<=sqrt(E*M/t)`. Split at `T=1/c>=1`.
The short part is bounded below by `-(1+log T)*E`; the long part by
`-2*sqrt(E*M/T)`. Adding c*M therefore gives

`Q_H >= (sqrt(c*M)-sqrt(E))^2 + (L+log(c)-2)*E >= 0`.

The cancellation at t=0 and all integral interchanges must be proved; a raw
split into separately divergent integrals is forbidden. The finite exponential
sum allows termwise Frullani identities after retaining this cancellation.

**Whole route:** this would supply an actual all-rank repair theorem for the
explicit asymptotic model, not merely rescue one alternating vector. At C5's
source scale the positive correction has c proportional to r*exp(-2r), so
`L+log c` grows like log r. Literal-source remainder control in the same form
would still be necessary. Neither the repair theorem nor its source transfer
is yet claimed as a Lean result.

### C5 verified; C6 scaling improvement

C5 is Lean-closed; exact proof and audit in
`../3-formalized/rh-theta-tail-first-correction-root-2026-09-26.md`.
C6's restriction c<=1 is unnecessary: substitute u=c*v and multiply the
kernel by c to reduce to c=1 and level L+log c. The sufficient condition is
therefore **c>0 and L+log c>=2**, at every positive node and every finite rank.

For formalization, weighted Young avoids square roots of E and M. At t>=1,
choose lambda=t^(-1/2). Since shifted tail energy is <=M/t,
`C(t)/t <= (E+M)/2 * t^(-3/2)`. Integrating gives <=E+M.
On 0<t<=1 the cancelled Frullani integrand is >=-E, using C(t)<=E and
exp(-t)>=1-t. Thus Q_log+M >=(L-2)*E. This is a paper proof candidate;
the actual-source remainder comparison remains open.

### C6 closed; next falsification experiment

C6 and its quantitative reserve are Lean-closed, named-build and axiom audited
(9 public theorems). Exact paper proof:
`../3-formalized/rh-log-cauchy-uniform-repair-root-2026-09-26.md`.
C7 tests whether the exact first atom itself has a negative center energy,
using its existing Wigner moment identities; the full source's evenness is
retained as an explicit scope boundary. Frozen experiment:
`rh-first-atom-tail-audit-root-2026-09-26.md`.

## C7b/C8 change the whole-route target

C7b is fully audited: the exact first atom has a negative finite real Gram
packet on every real tail. The complete theta L2 realization is also closed;
its finite negative-index profile is invariant under every real-tail restriction.

C8 then attacks the complete source itself. Lean scratch proves that no c>0
makes `K_Phi >= c*Phi(x)*Phi(y)/(exp(2x)+exp(2y))` hold at all ranks on any tail.
Exact reflection sends the complete diagonal into a scale that forbids the
corresponding analytic rank-one feature; density transports that obstruction
back to every outgoing tail. Named build, 17 public axiom audits, and final lint pass.

**Decision:** C6's strict Cauchy reserve cannot survive intact in the literal
source. Stop seeking a comparison with a strictly positive residual Cauchy
gap. An exact semidefinite cancellation leaving zero, or a reference norm
compatible with the incoming reflected envelope, remains open. Do not turn
the strict-coercivity no-go into a false claim that the full kernel is indefinite.

Proof and survivor: `../5-failed/rh-full-theta-positive-cauchy-reserve-root-2026-09-26.md`.
