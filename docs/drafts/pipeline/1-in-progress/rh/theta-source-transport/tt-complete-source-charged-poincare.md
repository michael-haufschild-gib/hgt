# TT C52: complete-source charged Poincare comparison

- **ID:** tt-complete-source-charged-poincare
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** TT in `docs/reports/rh-current-frontier-map.md`; C51 parity packet centering.
- **Statement:** Prove the literal prime plus Gamma jump energy dominates the complete polar energy, retaining all mixed terms.

## Goal and existing bridge

The sign, not construction of a receiver, is the target. The current corpus
already identifies the full arithmetic form with the restricted Weil form:

- `RHTower.riemannHypothesis_iff_thetaGroundEnergyComparison` in
  `CCMThetaGroundRHCriterion.lean`.
- `RHTower.riemannHypothesis_iff_thetaThreeEnergyComparison` in
  `CCMThetaThreeEnergyComparison.lean`.
- `RHTower.ccmRestrictedWeilSourceQuadratic_eq_three_theta_energies` in the
  same module.

For every compact smooth source `u`, its exact profile is `chi=u/Phi`.
The three energies are precisely those in `ThetaPositiveScalingEnergies`
and `ThetaPrimeGammaScalingEnergy`. Their combination is

    Weil(u) = Eprime(chi) + Egamma(chi) - Epole(chi).

Here the compact-support aperture is not C51's exponential tilt parameter.
The compact smooth-profile results do not by themselves justify exchanges
for the unbounded profile `P(D)(exp(a*x)*Phi)/Phi`. Conversely, the existing
global Weil identification must not be rebuilt as supposed new progress.

## Exact polar reduction on paper

For the actual positive even complete source Phi, write

    Q = integral Phi(x)*cosh(x/2) dx,
    dmu(x) = Phi(x)*cosh(x/2)/Q dx,
    C = integral Phi(x)*cosh(x/2)*chi(x) dx,
    S = integral Phi(x)*sinh(x/2)*chi(x) dx,
    V = integral Phi(x)*cosh(x/2)*|chi(x)|^2 dx.

For Schwartz chi, all terms are absolutely integrable by the corpus source
decay. In particular Q is finite and positive, and mu is a probability
measure. The literal polar energy satisfies

    Epole(chi) = 2*Q*V - 2*|C|^2 + 2*|S|^2
               = 2*Q^2*(Var_mu(chi)
                   + |E_mu[tanh(x/2)*chi(x)]|^2).

Derivation: set y=x+u in the defining integral over u>0, then symmetrize
over the two half-planes x<y and y<x. The resulting full-plane kernel is
`cosh((y-x)/2)*Phi(x)*Phi(y)`. Expand the squared increment and use
`cosh((y-x)/2)=cosh(x/2)*cosh(y/2)-sinh(x/2)*sinh(y/2)`.
Evenness gives integral Phi(x)*sinh(x/2) dx=0. The two diagonal terms
give 2QV; the two cross terms give -2|C|^2+2|S|^2. The factors of two
are required by the original `2*cosh(u/2)` normalization.

No value of Q is assumed. This is an unsigned algebraic reduction, not
a proved comparison, and has not been banked as a Lean frontier result.

## Hard conjecture after reduction

With the literal prime coefficients Lambda(n)/sqrt(n), shifts log(n),
and Gamma density exp(-u/2)/(1-exp(-2u)), prove

    Eprime(chi)+Egamma(chi)
      >= 2*Q^2*(Var_mu(chi)+|E_mu[tanh(x/2)*chi(x)]|^2)

for every profile of a compact smooth source, without an additional
spectral, covariance, transport, or arithmetic premise. A strict reverse
inequality for one such source would instead falsify RH through the
existing audited receiver. Positivity of each energy separately does
not compare them. A coarse positive constant does not supply this sharp
inequality. The actual prime jump atoms cannot be replaced by their mean.

## Attempts and exact obstructions retained

1. A ground-state proof based on a pointwise off-diagonal kernel sign is
   unavailable: `ThetaGammaPolarKernelOrientation` already constructs
   disjoint positive compact profiles with positive continuous ground
   cross pairing beyond the kernel threshold, avoiding every prime-power
   shift. This is existing knowledge, not a new no-go.
2. `RHTower.ThetaSourceWard.thetaPrimeGammaCutEnergy_eq_tail` proves
   positivity of each single threshold cut. The arbitrary linear
   combination of cuts requires its mixed quadratic form. No inference
   from positive diagonal entries to that mixed sign is valid.
3. Translating the source legs in the Ward calculation returns the tail
   kernel with integrand
   `(2*r+x+y)*Phi(r+x)*Phi(r+y)`. This kernel and its moving-cut formula
   already exist in `ThetaTailCommonTranslationLoewnerNoGo`.
   Its negative common-translation derivative is not positive
   semidefinite: the exact two-node determinant is
   `-(x-y)^2*(Phi(a+x)*Phi(a+y))^2`.
   The entrywise positive tail integral therefore supplies no monotone
   matrix transport through the compact region.
4. `ThetaTailCauchyAsymptotic` already proves positive definiteness for
   every fixed finite distinct-node system sufficiently far out. Its
   threshold depends on that node system. Exchanging this quantifier
   with arbitrary rank or arbitrary nodes would add the missing claim.

## C52 follow-up: fold before expanding the prime atoms

The whole-line atom expansion must not silently interchange the critical
Mellin sum and integral. `ThetaCriticalBoundaryMellinCharge` and
`ThetaCriticalBoundaryFluxPotential` already identify the escaped
half-unit charge. In particular, zero charge at finite stages does not
converge to the completed charge. This is an existing obstruction, not a
new no-go or a reason to abandon the full energy comparison.

A different order of operations retains positive atom weights. The
following is a paper calculation, not a Lean certificate or a sign result.
First split chi into its even and odd parts. Reflection invariance of
each of the three quadratic energies makes the two parts orthogonal.
For either parity, reflect a link `(x,x+u)` to `(-x-u,-x)` and retain only
`x >= -u/2`, doubling its integral. Its larger endpoint then satisfies
`x+u >= u/2 >= 0`. Every theta atom at that endpoint is positive.

Write `phi_k(x)=thetaCuspSourceTerm x k`, with k positive. The existing
`RHTower.invSqrt_mul_thetaCuspSourceTerm_shift` gives

    phi_n(x+log m)/sqrt(m) = phi_(m*n)(x).

For fixed x and k put

    D_x(k) = {m : m divides k and log(m) >= -2*x},
    W_x(k) = sum_(m in D_x(k)) Lambda(m),
    M_(x,k) = sum_(m in D_x(k)) Lambda(m)*chi(x+log m)/W_x(k),

using M=0 when W=0. Folding first and then reindexing k=m*n gives

    Eprime(chi) = 2 integral_x Phi(x) sum_(k>=1) phi_k(x) *
      sum_(m in D_x(k)) Lambda(m)*|chi(x+log m)-chi(x)|^2 dx.

All summands retained before this reindexing are nonnegative: on the
folded domain `phi_(m*n)(x)=phi_n(x+log m)/sqrt(m)>0`. Thus Tonelli is
available there; this is not the invalid whole-line critical Mellin
interchange. Existing finiteness of Eprime bounds the resulting sum.
For each nonzero W the inner sum is exactly

    W_x(k)*|M_(x,k)-chi(x)|^2
      + sum_(m in D_x(k)) Lambda(m)*|chi(x+log m)-M_(x,k)|^2.

The W=0 case contributes zero. This keeps both a squared mean increment
and a divisor variance, rather than replacing the link values by a scalar
logarithmic mass. At x>=0 the divisor mass is log k; at x<0 the cutoff
remains. Even at x>=0 the shifted chi values cannot be removed by the
identity sum_(m|k) Lambda(m)=log k.

The Gamma and pole energies fold on exactly the same domain
`u>0, x>=-u/2`. Their atom expansions therefore have positive weights too,
but their difference is still signed. Dropping the divisor variance or
averaging the prime atoms does not establish the comparison. The open
step is to couple this complete folded divisor form with the folded
Gamma form so that their sum pays the exact polar variance and odd
charge. No such lower bound was proved in this pass.

The modular-derivative alternative was also checked against
`PrimeArchThetaModularDifferentialClosure`. Its actual source-positive
coordinates and polynomial jet recursion are already in the corpus.
Their positive coordinates alone do not sign the native current; the
covariant jet field contains subtractions. No Rankin--Cohen or modular
Gram identification with the physical signed current has been proved.

## Pointwise folded payment does not follow

The next attempted inequality was to pay the polar term at each folded
source coordinate x before integrating x. This is incompatible with the
existing kernel-orientation obstruction, even in the even sector.

Paper diagnostic: choose a bounded open interval I beyond
`screwSignThreshold`, disjoint from every log(m), m>=2. Such intervals
exist because those points are locally finite. Take a nonzero smooth
even profile chi supported in I union (-I). Then chi vanishes near zero
and at every log(m). At x=0 the folded prime density is exactly zero,
including its divisor-variance decomposition. The folded Gamma-minus-pole
density there is

    -2*Phi(0)*integral_(u>0)
        thetaGammaPolarScalingKernel(u)*Phi(u)*|chi(u)|^2 du < 0.

The strict sign uses the actual theorem
`RHTower.ThetaSourceWard.thetaGammaPolarScalingKernel_pos_iff_threshold`.
The profile's odd polar charge S vanishes by parity, so removing that
charge cannot repair this pointwise argument. There is no conclusion
about the sign after integrating x.

This is an application of the already formalized atom-free kernel-sign
obstruction, not a new Lean no-go or retirement of C52. The existing
`thetaThreeEnergy_explicitSupport_gap` and positivity of its support
threshold also leave a nontrivial positive range for sufficiently small
support at any fixed aperture. Negative source-coordinate densities
therefore must not be treated as falsification witnesses for RH.

Any further C52 proof must couple different source coordinates before
claiming a sign. A pointwise lower bound obtained by completing divisor
squares is too strong. The actual integrated Schur-plus-variance payment
in C48 is another formulation that preserves this nonlocal requirement.

The fourteenth center-jet diagnostic was checked against the available
seam formulas: `ThetaCuspEvenSeamJets` supplies orders through twelve,
while the order-fourteen source-faithful results inspected here give tail
limits. Neither gives the center sign. No sign of J_7(0), C48-S, or the
rank-eight integrated Schur complement was established in this pass.

## Assessment and next proof obligation

The pass has not proved a new signed-current inequality. Rank-eight
Schur positivity, C48-S, and the all-rank compact matrix correction remain
open. The polar expansion isolates a sharp variance plus an odd charge;
it does not pay either term. C52 stays open, not retired.

The next useful step is a source-specific lower bound for the complete
mixed prime--Gamma jump form with exactly the displayed polar payment.
Any candidate factorization must retain both endpoints of every link and
the odd charge; single-cut positivity, a pointwise sign, or a new
conditional receiver is not that step. If working directly on C48, the
same requirement is payment of the actual compact Schur remainder.

## Gates and audit

- [x] Source terms and the existing RH bridge identified in the corpus.
- [ ] Sharp comparison proved on paper with all dependencies discharged.
- [ ] Exact sign theorem formalized and audited in Lean.

2026-10-02: four completed corpus searches inspected; three nonpartial,
one partial. Coverage/freshness details are in the working log. No Lean
source changed, no new formal sign theorem, no numerical experiment.

2026-10-02 follow-up: source-jump-factorization and atom-divisor-modular
searches both completed with partial results. The folded divisor
calculation was checked against the literal prime-energy definition and
the exact integer-label shift theorem. Still no new sign theorem.

2026-10-02 second follow-up: three completed, partial corpus searches
inspected. Pointwise folded payment fails by the existing kernel-sign
mechanism; integrated payment remains open. No Lean source changed.

## Odd derivative-ground attempt: reflected prime links

2026-10-02. Paper candidate, not a new Lean sign certificate. The preceding
center/reflection symmetry attempt supplied no positivity. This attempt
keeps the complete source and all prime powers, and aims at the mixed sign
directly.

Put f=-Phi'. Strict logarithmic concavity and evenness, already used in
`ThetaCuspCenterCompensationSign`, imply f(x)>0 for x>0, f(0)=0,
and f(-x)=-f(x). The symmetric complete-source equation has constant
translation coefficients. Differentiating it therefore gives the same
homogeneous equation for f. This differentiation requires the compensated
Gamma integral, not its two separately divergent near-zero terms. The
all-order source decay supplies local uniform summability for the prime
derivatives and domination for the compensated continuous derivative.
No Lean theorem implementing this differentiated ground transform has
been checked in this pass.

For a smooth compact even profile psi, consider the actual odd source
u=f*psi. The ground-transform algebra on paper replaces Phi by f in the
signed jump form. Positivity of the ground source is not used by this
algebra. For L>0 its whole-line link is

    integral_R f(x)*f(x+L)*|psi(x+L)-psi(x)|^2 dx
      = 2*P_L(psi)-R_L(psi),

    P_L(psi)=integral_(x>0)
        f(x)*f(x+L)*|psi(x+L)-psi(x)|^2 dx,
    R_L(psi)=integral_(0<x<L)
        f(x)*f(L-x)*|psi(L-x)-psi(x)|^2 dx.

The two exterior intervals give 2*P_L; the central interval gives -R_L.
Both P_L and R_L are nonnegative, and R_L already counts both orientations
of the reflected pair. In particular its coefficient must not be doubled
again in the final prime sum.

Let

    gamma(v)=exp(-v/2)/(1-exp(-2v)),
    c(v)=gamma(v)-2*cosh(v/2),                 v>0.

Folding the continuous term gives the full-quadrant expression

    G(psi)=integral_(x,y>0)
      [c(|x-y|)-c(x+y)]*f(x)*f(y)*|psi(y)-psi(x)|^2 dx dy.

The diagonal is interpreted through the cancelled integrand, or discarded
as a null set. For x,y>0, x!=y, its coefficient is strictly positive:

    c(|x-y|)-c(x+y)
      = gamma(|x-y|)-gamma(x+y)+4*sinh(x/2)*sinh(y/2)>0.

Indeed gamma is strictly decreasing on the positive ray: its numerator
decreases and its positive denominator increases. The hyperbolic identity
follows from the addition formulas and evenness of cosh. Thus the pole
part contributes positively in this derivative-ground odd folding. This
does not sign the complete form: reflected prime links remain negative.

The exact sharp comparison to attack is

    sum_(n>=2) Lambda(n)/sqrt(n)*R_(log n)(psi)
      <= 2*sum_(n>=2) Lambda(n)/sqrt(n)*P_(log n)(psi)+G(psi).

The paper normalization of the proposed full odd quadratic is the right
side minus the left side. Its formal identification with the literal CCM
form, and the inequality itself, remain unchecked/unproved respectively.
This is not being added as an unsigned Lean receiver. It is not a claim
that either odd-sector positivity or RH has been established.

An attempted proof by a strictly positive path-comparison reserve meets
an existing obstruction: `TruncatedRiemannKernelWeilEnergy` and
`WeilNearRadicalDimension` already retain all derivative combinations in
the exact Xi radical and their compact approximations. In particular a
proof cannot silently turn the desired semidefinite form into a strict
gap on every nonconstant limiting profile. The candidate quotient
Phi'''/Phi' is even; its removable value at zero uses Phi''(0)!=0 from
strict log curvature. A relative-gap contradiction would still require
checking convergence of the separate folded energies for its cutoffs;
that check has not been performed here. No new no-go is claimed.

The unresolved mathematical payment is the complete reflected-prime
quadratic, including its cross terms and exact equality directions.
Reindexing a reflected link x+y=log n makes the two atom scales have
fixed product, but does not remove the shifted profile values or their
signed correlations. No absolute estimate or divisor-mass identity in
this pass pays that quadratic. C52, C53 and the all-rank TT sign stay open.

### Differentiated one-sided equation: forcing must stay

The subsequent sign attempt used the literal one-sided operator A from
`ThetaCuspPrimeArchSourceEquation`, whose source equation is A(Phi)=x*Phi.
On paper, translation-invariant differentiation gives

    A(Phi^(j))=x*Phi^(j)+j*Phi^(j-1),
    A(-Phi')=x*(-Phi')-Phi.

Thus the derivative source does not solve the same homogeneous one-sided
equation. Its reflected equation has the opposite forcing; the two
forcings cancel only in the symmetric operator used above. A proposed
one-sided payment of the reflected prime links must retain this Phi term.
No one-sided sign was deduced after retaining it.

The attempted Eisenstein completion also left the sign unresolved.
`ThetaWignerEisensteinCrossEnergy` supplies a positive-symbol completed
square with both primal and reciprocal-symbol energies, not a positive
identification of the physical mixed current. The complete-source cone
and product-fibre identities in `ThetaCuspWignerProductFiberNormalForm`
retain a signed integral, including actual negative pointwise regions.
Neither fact rules out a future global square identity, but neither
supplies one. No arithmetic boundary-channel estimate was proved.

Related prior art `CCMFirstClockHalfWaveReflection` already orients its
continuous reflection term and leaves a prime half-wave dominance law
equivalent to RH. That is a different test family from the derivative-
ground profiles here; it cannot be substituted for their comparison.
This pass adds no Lean sign theorem and does not retire C52.
