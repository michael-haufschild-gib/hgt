# EDQ prime-count deformation: complex-neighborhood growth

Status: formalized in Lean. RH and the original endpoint
energy bound remain open. No numerical experiment is used.

## Target and attempted improvement

The EDQ chain needs a cofinal subpower bound for the complete physical
Möbius source at the actual endpoint. The existing all-order logarithmic
estimate has constants of factorial order three. Optimizing those constants
does not change the cutoff exponent. The proposed alternative was to obtain
better order control from the exact polynomial deformation

\[
 P_N(z)=\sum_{1\le n\le N}\mu(n)z^{\omega(n)}b_n,
 \qquad b_n=\operatorname{bdGen}(1/n).
\]

This is the original complete Hilbert carrier at every complex parameter;
in particular, it includes every physical time cell. At real parameters it
is `PrimeCountDamping.source N`, and at one its squared norm is the original
raw source energy. Bounds for derivatives in this deformation parameter are
different from bounds for the order of a logarithmic asymptotic expansion.

## Exact growth law

For every fixed complex center a, radius r>0, and epsilon>0, there are
positive constants c,C and an integer N0 such that, for every N>=N0,

\[
 cN^{1-\varepsilon}
 \le \max_{|z-a|=r}\|P_N(z)\|^2
 \le C N^{1+\varepsilon}.
\]

This concerns a maximum on a whole circle. It does not lower-bound the
value at z=1, nor exclude a subpower bound there.

## Paper derivation

Set D_N=max{omega(n):1<=n<=N}. For each fixed B>=1 and eta>0,

\[
 B^{D_N}\le C_{B,\eta}N^\eta.
\]

Indeed, choose an integer j>=1 with B<=2^j. Every choice of a subset of
the distinct prime factors gives a different divisor, hence
2^omega(n)<=d(n). The existing all-exponent divisor bound applied at
exponent eta/j gives B^omega(n)<=d(n)^j<=C^j n^eta. Choose an index
attaining D_N. This proof uses the integer cutoff N throughout.

The corpus already proves sum_(n<=N)||b_n||<=4 sqrt(N). On the circle,
|z|<=|a|+r, so the preceding bound gives

\[
 \|P_N(z)\|\le 4\sqrt N\,\max(1,|a|+r)^{D_N}.
\]

This supplies the upper estimate after choosing eta=epsilon/2.

For the lower estimate use the actual real aperture u_N selected in
`EulerDeletionPrimeCountAmplification`, rather than a freely chosen source.
The existing theorem gives u_N in [0,1/2] and

\[
 \|P_N(u_N)\|^2\ge N/(K(\log N)^4)
\]

eventually, with a fixed K>0. Let M_N be the maximum norm on the circle
about a. Taylor expansion of the finite Hilbert-valued polynomial about a,
followed by Cauchy's coefficient estimate, gives

\[
 \|P_N(u_N)\|
 \le M_N\sum_{j=0}^{D_N}(|u_N-a|/r)^j
 \le M_N(D_N+1)A^{D_N},
 \quad A=\max(1,(|a|+1)/r).
\]

No infinite Taylor remainder is introduced. Since D+1<=2^(D+1), the
transport factor is at most 2(2A)^D, hence at most C_eta N^eta by the
divisor bound. Take eta=epsilon/4 and absorb (log N)^4 into N^(epsilon/2).
The lower estimate follows. Continuity on the compact circle gives an
attaining point.

## Consequence for the attempted proof

A fixed complex neighborhood cannot have a subpower upper bound for this
whole deformation, even if the original endpoint eventually does. Thus a
Cauchy argument with that neighborhood bound as its input would require a
false strengthening of the EDQ target. This does not rule out estimates
on shrinking neighborhoods, subtraction of a specified source contribution,
or an argument acting directly at the original endpoint. None of those
supplies the missing endpoint estimate here.

The finite-degree transport law and circle growth law are formalized;
the endpoint estimate remains the hard arithmetic target. A claim about
arbitrary polynomial counterterms is not included in this result.

## External method checks

[Suzuki, 9 September 2026](https://arxiv.org/html/2609.10134v1) constructs a
Borel transform using large-order information and continued singularity
data for a specified quantum model. Its finite-order numerical agreement
does not establish an EDQ remainder estimate or identify a Borel transform
for the actual cutoff source. No computation or external premise is used.

[Li, 26 August 2026](https://arxiv.org/html/2608.25989v1) transfers optimal
linear Schatten constants to concave functions. Its bound still contains
the sum of the absolute input matrices. No identification controls that
quantity at the required EDQ scale; the transfer alone gives no signed
arithmetic saving.

## Formal status

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionPrimeCountCircleGrowth.lean`.
Namespace: `RHTower.PrimeCountDamping`.

The main theorem `complexSource_circle_energy_growth` quantifies over every
complex center, every positive radius and every positive epsilon. It supplies
positive lower and upper constants, and eventually an attaining point on
each circle with both stated energy bounds. Its arithmetic inputs are proved
theorems; it introduces no unproved arithmetic premise.

Supporting results include `complexSource_real`,
`pow_primeCountDegree_le_const_rpow`, `complexSource_energy_upper`, and
`aperture_circle_transport_subpower`.

Inputs used from the corpus:

- `EulerDeletionPrimeCountAmplification`: real deformation, actual aperture,
  complete-carrier norm upper bound and aperture energy lower bound.
- `RHTower.card_divisors_le_const_mul_rpow` (`DivisorBound`): all-exponent divisor bound.
- mathlib `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`:
  Cauchy estimate for complete complex Banach spaces.

Validation passed: foreground scratch `lake env lean`, then the single leaf
audit `lake build --old GaloisForLFunctions.RHTower.EulerDeletionPrimeCountCircleGrowth`.
The new leaf has no warnings. Lake replayed cached dependency messages.
The umbrella import is wired; no umbrella build ran. Generated indexes and
`scripts/formal_tools.py lint --check-generated` passed, with pre-existing
large-file size warnings. No numerical experiment or axiom-printing check ran.

This is an unconditional growth theorem for the actual deformation, not a
subpower estimate for its distinguished endpoint. The latter remains open.
