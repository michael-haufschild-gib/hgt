# BAG complete pointwise mixed-frequency source

01ar. Dependency-closed paper proof of M1; Lean assembly pending.
No uniform parameter limit or physical cancellation is asserted.

## Claim and source

Fix u in complex units, v complex and nonzero real tau. Let L=log N,
alpha=u/L, beta=v/L+i*tau, P_N=primes<=N. For the ORIGINAL
`criticalCompletedConeEuler P_N (1+alpha) (1+beta)`, including both growing
coprime cofactors, both label exclusions and allowed first/second coincidence,

  criticalCompletedConeEuler / L^2 -> exp(-2*gamma)*G(u),
  G(u)=exp(P(u))*(1-E(u))^2/u.

P,E,G are the exact profiles in `ChiRamanujanMixedProfileCancellation`.
This is pointwise in u,v,tau; in particular tau stays fixed and nonzero.

## Unlabelled factorization and limit

Write Q_N(delta)=product_(p<=N)(1-p^(-1-delta)) and
M_N=Q_N(0). The exact local factorization proved in
`ChiRamanujanJointBaseLimit.moving_local_factor` applies to alpha,beta
once their real parts are smaller than1/16 in absolute value. Its proof
uses only those real-part conditions; no imaginary-part restriction occurs.
Taking the original finite product yields

  H_N=C_N*Q_N(beta-alpha)*Q_N(alpha-beta)/(Q_N(-alpha)*Q_N(-beta)),

where H_N is the complete two-cofactor local Euler product and
C_N=product_(p<=N)cubicPrimeFactor p 1 alpha beta.

The corpus normal convergence of C_N is locally uniform on cubicTube,
whose defining conditions involve real parts only. The moving point tends
to (1,0,i*tau), inside that tube. Hence C_N tends to
cubicEulerCorrection 1 0 (i*tau)=1.

The audited actual moving boundary Euler law gives

  Q_N(beta-alpha) -> 1/zeta(1+i*tau),
  Q_N(alpha-beta) -> 1/zeta(1-i*tau),
  Q_N(-beta) -> 1/zeta(1-i*tau).

All these limits are nonzero. The audited near-pole Euler-ratio law and
Mertens normalization give

  Q_N(-alpha)=M_N*criticalMovingEulerRatio u N,
  L*Q_N(-alpha) -> exp(-gamma)*exp(-P(u)).

Consequently H_N/L -> exp(gamma)*exp(P(u))/zeta(1+i*tau), nonzero.
This also proves eventual simultaneous nonvanishing of every local H
factor: the finite product is nonzero, so each factor is nonzero.

Attaching the two original cofactors is exactly the identity used in
`ChiRamanujanJointBaseLimit.completed_trace_eq`. It yields

  completed unlabelled trace = zeta(1+alpha)*zeta(1+beta)*H_N.

The first zeta factor divided by L tends to1/u by the residue theorem.
The second tends to zeta(1+i*tau) by continuity away from the pole.
Their exact factors cancel the inverse-zeta limit above. Thus

  completed unlabelled trace / L^2 -> exp(gamma)*exp(P(u))/u.

The first cofactor point differs from1 eventually since u!=0; the second
differs from1 eventually since its limit1+i*tau differs from1. Their
real parts are positive eventually. These facts discharge the domain
conditions of the exact cofactor identities.

## Labels and normalization

P2 `bag-mixed-frequency-label-rows` proves the actual normalized row
limits A/L->1-E(u), B/L->1, C/L->1-E(u), D/L->1-E(u), and each of the
four exact collision moments K_j/L->0. This proof retains the compact
prime phase and the original cutoff; it does not substitute an unbounded
displacement into a fixed-displacement theorem.

The exact masked expansion is

  masked response = A*B*C + C*K_0 - A*K_1 - B*K_2 + K_3.

Divide by L^3. Each pair correction is a product of bounded normalized
rows, vanishing normalized collisions and1/L; the triple correction uses
1/L^2. Hence the original masked response/L^3 tends to(1-E(u))^2.

The corpus exact completed response assembly is

  completed labelled source = M_N^3 * masked response * completed trace.

Its nonzero-local-factor conditions were proved above, including all
primes in the original growing cutoff. Since L*M_N->exp(-gamma), division
by L^2 gives exp(-3*gamma)*(1-E(u))^2*exp(gamma)*exp(P(u))/u, exactly the
claimed exp(-2*gamma)*G(u).

## Audit and next hard problem

Relevant corpus sources read01ar: JointBaseLimit, GrowingLabeledSource,
MovingLabelRows, MovingResponseWindow, WeightedCubicTrace cubicTube,
MovingCofactorLimit normalization, OscillatoryLogWindow, plus the newly
audited BoundaryEulerProduct. Search4018 retrieved the actual masked
response expansion; coverage/freshness recorded on the label-row P2 card.
No new external estimate, dropped factor, convergence premise, numerical
experiment or RH hypothesis enters this paper proof. Formalize the exact
unlabelled mixed factorization and completed labelled assembly next.

After pointwise M1, the hard frontier is uniformity and source-faithful
integration with the actual moving physical profile across the joint
near-pole region, mixed sectors and complete remaining tails. The proved
zero signed vertical integral of G pays only its leading profile; it
does not dominate or cancel the full moving physical remainder by itself.
Growing moments/cofactors and common-height return remain open.
