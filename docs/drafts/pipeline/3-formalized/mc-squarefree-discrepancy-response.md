# MC squarefree discrepancy: exact signed response and absolute comparison gap

- **ID:** MC-C12.93-response
- **Stage:** 3-formalized; final direct and axiom audits passed.
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/mc-scaled-liouville-density-cone.md`.
- **Scope:** actual squarefree counting discrepancy; no RH-critical Liouville bound.

## Exact statements

Let A(x)=sum_(1<=n<=floor(x))mu(n)^2, rho=6/pi^2, and E(x)=A(x)-rho*x.
The two leaves define these literal objects, including the floor and lower endpoint.
For Re(s)>1/2 the integral

    M(s)=integral_1^infinity E(x)*x^(-s-1) dx

converges absolutely and is holomorphic. Its pole-cleared identity is

    (s-1)*s*M(s)*zeta(2*s)
      = zetaResidueUnit(s)-rho*s*zeta(2*s).

Away from s=1 this yields M(s)=zeta(s)/(s*zeta(2*s))-rho/(s-1).
For0<Re(a)<1/2 define q(a)=a/rho*M(1-a). Then

    q(a)=1+a*zeta(1-a)/(rho*(1-a)*zeta(2-2*a)),
    q(a)=1 iff zeta(1-a)=0.

For real0<a<1/2, q(a)<1 and q(a)->1 as a increases to1/2.
Write b(a)=a/rho*integral_1^infinity |E(x)|*x^(a-2) dx. The stronger uniform
comparison statement is

    exists eta>0, forall1/4<=a<1/2, q(a)+eta<=b(a).

Consequently b(a)>1 throughout some left neighborhood of1/2.
These are unconditional facts about the actual counting source, with only the displayed
parameter-domain conditions. No RH, cancellation, spectral or integrability premise is added.

## Dependency-closed paper proof

1. The full square-root count bound plus floor error gives |E(x)|<=4sqrt(x) for x>=1.
   The count is measurable and bounded on compact intervals, so the restricted kernel is
   locally integrable. The bound gives absolute Mellin convergence and holomorphy for Re(s)>1/2.
2. In Re(s)>1, Abel summation of the actual nonnegative mu-square series gives its integral
   identity, using sum mu(n)^2/n^s=zeta(s)/zeta(2s). Clearing the pole at1 with the analytic
   residue unit extends the identity over the connected half-plane. zeta(2s) is nonzero
   there by absolute convergence. This proves the exact complex classification.
3. On the real subcritical axis zeta(1-a)<0 and zeta(2-2a)>0, hence the signed deficit is
   positive. Replacing the latter denominator by zetaResidueUnit(2-2a)/(1-2a) exhibits a
   continuous extension with value1 at a=1/2. This is an Abelian limit; it asserts no ordinary
   endpoint integral convergence.
4. Since1/2<rho<1, choose1/rho<u<v<2 and c=rho*u-1>0. For x in[u,v], floor(x)=1, so
   E(x)=1-rho*x<=-c. For1/4<=a<1/2, x^(a-2)>=x^-2>=1/4 there. Thus
   (|E|-E)*x^(a-2)>=c/2 on[u,v], and it is nonnegative everywhere x>1.
   Its full integral is at least d=(v-u)c/2>0. Multiplication by a/rho gives the fixed
   gap eta=d/(4rho). Combining that gap with q(a)->1 proves b(a)>1 eventually.

Every integral comparison uses proved integrability. No full tail, floor term, or endpoint
is removed. No numerical mathematical experiment is used.

## Lean certificate

Namespace `RHTower.SquarefreeDiscrepancy`.

- `SquarefreeDiscrepancyMellin.lean`: `moment_identity`, `moment_eq_quotient`, `response_eq`,
  `response_eq_one_iff`, with actual-source measurability and integrability infrastructure.
- `SquarefreeDiscrepancyCriticalGap.lean`: `realResponse_lt_one`, `tendsto_response_half`,
  `tendsto_realResponse_half`, `exists_uniform_absolute_gap`,
  `eventually_one_lt_absoluteResponse`, with real integral identification and integrability.

Both targeted `lake --old build` leaf checks passed. Both leaves are wired into RHTower;
no umbrella build. Both required final `lake --old env lean <leaf>.lean` audits passed with empty output.
All23 public theorem `#print axioms` checks, run from /tmp, passed with only
`propext`, `Classical.choice`, and `Quot.sound`.

## No-go closure and survivor

Only the proposed absolute derivative-envelope contraction near one half is excluded.
This is not a lower bound for every possible operator norm, a failure of signed estimates,
a disproof of the finite-prime K sign, or an RH falsification.
The positive survivor is the exact signed Mellin response, its real deficit and critical
limit, and the complex unit-mode classification. The new insight is that the loss from
absolute values remains uniformly positive as the signed deficit vanishes. Checking real
power modes alone also misses precisely the reflected zeta-zero modes.

## Validation and search ledger

2026-10-04,1005k. Three documented deep searches: signed-work, negative-part, signed-energy.
Partial flags false/true/false; inventoried files65161/65165/65179; compiled43 and stale2660
in each; pending49138/49141/49151; snapshot/current generations
1222056/1222066,1222091/1222091,1222497/1222498. All report semantic coverage unavailable,
background refresh and no method invalidation pending; signed-work/energy also warn older
snapshot generation. All candidate statements, source arguments and ingredient proposals
were inspected; proof_ideas were empty. No search completeness claim beyond reported coverage.
Pointwise lambda*mu-square multiplication was not confused with Dirichlet convolution.
The generated squarefree-functional/clock chain supplies neither a vanished discrepancy
nor a signed source bound; geometric resolvents and conditional RH energy bounds are not
Liouville cancellation producers. Exact signed-cofactor dilation retains the nondivisible
remainder, whose sign remains open.

Global lint exited1 on13 unrelated umbrella-reachability errors, none for these two leaves:
CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
CCMRetainedChainKernelLower, MertensProductDiamondPintz, MoebiusMollifiedCriticalMoment,
MoebiusMollifiedErrorThreeLines, RoutePLatePrimeIncrementJumps,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving, and
HTGeometry.CompactMonoidMeasureAlgebra. Generated Lean indexes refreshed successfully.
No added axiom, placeholder, heartbeat increase, subagent, full build or commit.

## Remaining hard problem

For the actual K=J_lambda-t*J_lambda', establish the signed lower bound

    integral_1^infinity E(x)*K'(t*x)/x dx >= -C_epsilon*t^(-1/2-epsilon).

The exact paper source equation rho*K(t)=t*exp(-t)+t*that_integral then gives the required
half-power lower bound for K and J_lambda. Neither that estimate nor RH was proved here.

**Process correction:** an axiom audit was accidentally started while the second direct audit
was still running. The axiom-audit child and wrapper were terminated by their exact owned
PIDs39784/39721; exit143 and process absence confirmed. The direct audit then exited0.
Only afterward was the axiom audit rerun; it exited0 with the23 standard-only results above.
No simultaneous build was launched, but the temporary overlap of two Lean audit processes
violated the intended one-process discipline and was corrected. No process remains owned.


**Fourth search / signed-record continuation:** `Liouville power barrier minimum signed dilation discrepancy`
completed with partial=true:65188 files,43 compiled,49156 pending,2660 stale;
snapshot/current generations1222610/1222615; older-generation and semantic-coverage warnings,
background refresh, no pending method invalidation. All candidate statements, source arguments
and ingredient sets inspected; proof_ideas empty. The generated rational-approximation
Liouville/Fokas–Lenells chain concerns different sources and was rejected. Actual retrieved
prime-two multiplicativity and signed-cofactor residual identities retain the full odd source;
they do not prove the record-work sign. The record subtraction and compensated sampling
formula are paper diagnostics in the active C12.93 card, not new Lean receivers or bounds.
