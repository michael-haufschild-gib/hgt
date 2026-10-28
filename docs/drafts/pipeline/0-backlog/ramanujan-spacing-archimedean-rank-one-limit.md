# The archimedean spacing correction on Ramanujan packets

- **ID:** ramanujan-spacing-archimedean-rank-one-limit
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** formalized full-prime Ramanujan quasimodes; SSHA separated-atom pairing and Robin constant
- **Statement:** On every fixed finite Ramanujan packet, the spacing-scale archimedean cross correction has rank at most one, with opposite net pole corrections in the Markov and complete Weil forms.
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

The full source of `TheRamanujanPoleProfilesAreAsymptoticallyOrthonormal.lean`
was reread for the periodic input. Its public `tendsto_periodic_harmonic_mean`
transfers the complete-period mean to logarithmic averaging, and
`periodMean_normalizedRamanujanMode_mul` gives exact normalized orthogonality.
Its ordinary-mean helper is private; the proof uses the existing
`abs_sum_range_le_of_periodic` zero-mean bound, which is the stronger useful
input for a uniform shifted-correlation error. Periodic averaging itself is
already proved baseline.

A concrete route for the still-unproved summed replacement bound avoids
logarithmic derivative estimates. The shifted weighted density is
`omega(log(n/j)-v)/sqrt(n*j)=exp(v/2)*n/(n^2-exp(2v)*j^2)`.
For |v|<=w=c/N, n>j, and c<1/2, the proposed elementary exponential bound
`exp(w)-1<=2w` gives
`n-exp(w)*j >= (1-2c)*(n-j)`.
Clearing the two positive denominators should bound the difference between
v=w and v=-w by `C_c*w*n/(n-j)^2`. Summing inverse squares then gives
`C_c*w*N^2`; multiplying by the bump's squared absolute integral gives the
required `O(w^3*N^2)` error. The fixed constant may depend on c and the profile,
which is sufficient for this fixed-ratio limit. These inequalities and all
finite-sum reindexings still need exact proofs.

Further novelty audit: [Suzuki, Weil's quadratic form via the screw function](https://arxiv.org/html/2606.09096v1),
introduction and main statements through Theorem 1.5, gives a literal restricted
Weil operator and a small-aperture ground-energy asymptotic. This is baseline
operator theory; it does not identify the present growing log-lattice packet
limit. The corpus already realizes that interval operator in
`RHTower/Suzuki/SuzukiWeilFriedrichsOperator.lean` (read through line 200),
and `RHTower/PaperRestrictedWeilSource.lean` (read in full) represents the exact
mixed form on its form domain. A future operator interpretation must use these
existing carriers rather than claim another abstract construction as new.

The numerical study [Kim et al., A Numerical Realization of Suzuki's Weil-Quadratic-Form Operator](https://arxiv.org/html/2607.24830v1)
was inspected in its introduction, operator definitions, and scope discussion.
Its main archimedean spectral formula concerns a small interval with no active
primes, and the stated symbol-to-spectrum passage lacks rigorous remainder
bounds. It supplies neither proof input nor evidence for this candidate's
growing-lattice limit. No numerical experiments are used here. The corpus
periodic-correlation search again found the existing harmonic mean theorem,
not the required triangular lattice asymptotic.

## Sharpened analytic obligations

For a common period q and bounds |a|<=A, |b|<=B, put
`R(d)=q^(-1)*sum_(j=0..q-1)a(j+d)b(j)`. Complete-period splitting gives,
uniformly in d and L,
`|sum_(j=1..L)a(j+d)b(j)-L*R(d)|<=2qAB`.
Also |R(d)|<=AB and mean(R)=mean(a)*mean(b), by interchanging the two finite
period sums and shifting a complete period. Reindexing n=j+d and including
the zero-length d=N row yields
`sum_(j<n<=N)a(n)b(j)/(n-j)
 = N*sum_(d=1..N)R(d)/d - sum_(d=1..N)R(d) + error`,
with |error|<=2qAB*H_N. The public periodic harmonic mean theorem handles
the first term; the others vanish after division by N*log(N). The complementary
kernel has absolute sum at most AB*N since 1/(n+j)<=1/n. These statements
still need exact finite-sum Lean adapters.

The pair replacement bound admits a fixed explicit majorant. Set kappa=1-2c>0.
For 0<w=c/N<=1/2 and d=n-j>=1, the inspected bound exp(1/2)<2 gives
`n-exp(w)*j >= d-2c >= kappa*d`.
Write Dplus=n^2-exp(2w)*j^2 and Dminus=n^2-exp(-2w)*j^2. Then
Dplus>=kappa*d*n and Dminus>=d*n. Subtracting the two rational weighted
densities splits their difference into
`(exp(w/2)-exp(-w/2))*n/Dplus`
and
`exp(-w/2)*n*(exp(2w)-exp(-2w))*j^2/(Dplus*Dminus)`.
The elementary exponential increment bounds give a total at most
`5*exp(1)*w*n/(kappa*d^2)`. Summing uses
`sum_(d=1..n-1)1/d^2<=2`, proved by telescoping
`1/d^2<=1/(d-1)-1/d` for d>=2. Thus the absolute aggregate error is bounded
by a fixed multiple of w^3*N^2, including signed periodic coefficients.
Its ratio to w*log(N) is bounded by a fixed multiple of 1/log(N), hence tends
to zero. Formal denominator, exponential, and reindexing proofs remain.

The exact diagonal identity is already public in
`TheFinitePartOfTheMarkovFormAtTheSpacing.lean`:
`integral_sub_shift_sq_atomicTest_eq` (source lines 129-160 inspected).
Its integral and support arguments through line 320 were read. They expose
the signed off-diagonal integrand before absolute-value estimates, so the new
limit can preserve cancellation. The existing inequalities alone do not give
the desired density.

The profile regularity does not need an additional Lipschitz premise:
`RHTower.CHMDDoobGraph.compact_source_lipschitz` in
`CHMDCompactSourceClass.lean` (read in full) constructs one from C2 and compact
support. Exact exponential translations are also already proved by
`atomPoleRow_zero_apply` and `atomPoleRow_one_apply` in
`ArithmeticLorentzianGeometry/TheUniformMarginPaysThePoleOnlyUpToARootLogarithm.lean`
(lines 188-212 read). For the present pole gauge they reduce the two moments
to `(integral g*exp(-u/2))*sum a(n)/n` and
`(integral g*exp(u/2))*sum a(n)`. After dilation, the atom factors divided by w
tend to integral phi. Ordinary and logarithmic periodic means then give the
claimed product limit. Exact integration and finite-sum adapters remain.
