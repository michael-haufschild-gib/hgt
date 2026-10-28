# The archimedean spacing correction on Ramanujan packets

- **ID:** ramanujan-spacing-archimedean-rank-one-limit
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** formalized full-prime Ramanujan quasimodes; SSHA separated-atom pairing and Robin constant
- **Statement:** On every fixed finite Ramanujan packet, the spacing-scale archimedean cross correction has rank one, with opposite net pole corrections in the Markov and complete Weil forms.
- **Count:** uncounted; no completed paper proof or Lean formalization

## Goal

Supply the missing archimedean cross-term density and identify the complete
spacing-scale form on arithmetic excitation packets. This is an exact mixed-form
limit, not a proposed improvement of a numerical critical constant. It must retain
the actual Gamma term and both pole moments. It does not assert exhaustion of the
full Weil-test carrier or RH.

## Gates

- [ ] Well-posedness, exact normalization, full corpus/literature novelty audit
- [ ] Dependency-closed paper proof
- [ ] Exact Lean formalization, foreground final checks, transitive axiom audit, umbrella wiring

## Candidate statement

Fix a real C2 profile phi supported in [0,1], with M2=integral phi^2>0,
I=integral phi, beta=bumpRobin(phi,1), and 0<c<1/2. Put w_N=c/N.
For a fixed finite positive conductor set S and real coefficients b_m, set

`a(n)=sum_(m in S)b_m*c_m(n)/sqrt(phiEuler(m))`,
`x(n)=a(n)/sqrt(n)`,
`f_N(u)=sum_(1<=n<=N)x(n)*phi((u-log(n))/w_N)`.

Write b_1=0 if 1 is absent from S, and
`sigma_phi(c)=log(1/(2*pi*c))+beta/M2`.
The proposed limits are

`integral f_N^2/(w_N*log(N)) -> M2*sum_(m in S)b_m^2`,

`Markov(f_N)/(w_N*log(N))
 -> M2*sum_(m in S)b_m^2*(sigma_phi(c)+log(m)+tameDifferent(m))-c*I^2*b_1^2`,

`Re Weil(f_N,f_N)/(w_N*log(N))
 -> M2*sum_(m in S)b_m^2*(sigma_phi(c)+log(m)+tameDifferent(m))+c*I^2*b_1^2`.

Polarization would give every mixed entry on the packet. The range c<1/2
matches the inspected separated-atom inputs; widening it requires checking their
exact support and non-ratio-lag conditions. No optimal profile or global critical
constant is asserted.

## Mechanism to audit

The actual Levy density is exp(-s/2)/(1-exp(-2s)). For n>j>0 its pole-weighted
value should simplify exactly to

`omega(log(n/j))/sqrt(n*j)=n/(n^2-j^2)
 = (1/2)*(1/(n-j)+1/(n+j))`.

Thus the leading weighted cross sum is an additive harmonic convolution.
For fixed periodic a,b, its expected asymptotic is

`sum_(1<=j<n<=N)a(n)b(j)*n/(n^2-j^2)
 = (N*log(N)/2)*mean(a)*mean(b)+O(N+log(N))`.

Proposed proof: on each difference d=n-j, periodic averaging gives
`sum_j a(j+d)b(j)=(N-d)*R_ab(d)+O(1)` with a fixed-period error.
The correlation R_ab is periodic and its period mean is mean(a)*mean(b).
Periodic harmonic summation gives the leading logarithm. The n+j kernel costs
O(N). Every normalized Ramanujan mode has period mean zero except conductor one.

The existing pair estimate bounds the replacement of the actual atom-cross
integral by omega at the center. A uniform density-derivative bound on all
separated pairs should make the aggregate replacement error O(w_N^3*N^2),
which is negligible compared with w_N*log(N). This uniform bound and its exact
constants remain obligations; a fixed-pair O(w) statement alone is insufficient.

The proved actual prime residuals give the energy limit of every fixed packet.
The exact self-energy has coefficient log(1/w_N)+profileRobin(phi), so its
log(N) term cancels the prime divergence before taking limits. The identity
`2*gammaHardyPhaseRate(0)+archRobinConstant+gamma=-log(2*pi)` supplies sigma.
The two actual exponential pole moments should have product
`c*w_N*log(N)*I^2*mean(a)^2+o(w_N*log(N))`; their factor two reverses the
negative archimedean rank-one correction. These normalizations require a direct
source check and formal proof.

## Source and novelty audit so far

Read `SpacingScaleHarmonicAnalysis/TheArchimedeanPairingOfTwoAtoms.lean`
through its cross-term estimate and translated-integral proof (lines 1-245).
Its exact pair energy is self-energy twice minus twice the cross integral.
Read `RenormalizedArithmeticPotentialTheory/TheArchimedeanFinitePartIsMinusLogTwoPi.lean`
in full. It gives two-sided O(wN) control, not the proposed mixed-packet limit.
The current SSHA README still lists pole cross-term density as missing.
The corpus query for Ramanujan/archimedean/rank-one finite parts returned the
existing quasimodes and other harmonic/divisor kernels; no matching theorem was
identified among those inspected hits. This is only an initial audit.

The finite-packet algebra, ordinary periodic averaging, and scalar Robin identity
are excluded baselines. The new target is their actual Gamma/prime/two-pole
assembly. Full novelty review and all exact proof obligations remain open.

Further source reading: the rest of the pair estimate through line 290 and
`TheFinitePartOfTheMarkovFormAtTheSpacing.lean` through line 110 confirm the
pair orientation, the scalar self-energy cancellation, and the existing
cross-term payment by prime defect. The periodic harmonic-convolution search
returned other convolution and dilation kernels; no matching lattice asymptotic
was identified among the inspected statements.

A finite-packet quadratic-form limit does not imply full Markov or Weil spectral
exhaustion. The archimedean cross operator may create large rows near the top of
the horizon, even when its average on a fixed pole profile has a finite limit.
Any spectral upgrade must control those boundary corrections separately. The
present candidate claims only the actual mixed-form limit stated above.
