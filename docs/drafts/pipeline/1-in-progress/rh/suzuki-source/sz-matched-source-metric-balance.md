# Actual matched-source balance for the signed metric term

- **ID:** sz-matched-source-metric-balance
- **Stage:** 1-in-progress
- **Route:** SZ
- **Date:** 2026-10-02
- **Status:** actual odd balance Lean-closed; even, mixed-aperture and full-current obligations open

## Hard target

For actual matched odd energy O_a, physical squared norm N_o,a and prescribed
shift c_a, prove c_a*N_o,a-O_a -> 0. Build the same statement for the actual
matched even channel E_a,N_e,a. Then prove the signed cancellation

    c_a*(O_a*N_e,a-E_a*N_o,a) -> 0.

This targets the metric term in the original common-aperture determinant.
It retains the complete signed shell term as a separate open obligation;
it does not claim a cofinal Wronskian bound or shift removal.

## Corpus basis

Current searches1188058 and1188112 are partial/source_only. The first has a
snapshot inventory and proposes an inapplicable Neumann boundary-flux step;
the second has pending coverage and no ingredient set. Actual source hits
include SuzukiMatchedEvenSourceBound and the metric response identity in
CCMSuzukiCrossApertureRieszTransport:361. No absence or novelty claim is inferred.

Source inputs for the odd calculation:

- Actual finite Neumann vector/budget and exponentially small residual:
  CCMRestrictedWeilFiniteNeumannSource.
- Actual Gamma lift and its energy O(a*exp(-a)): CCMFiniteNeumannFormDecay.
- Uniform actual odd energy and exact Ta response-minus-test norm estimate:
  SuzukiMatchedOddSourceBound.
- Growing physical coercivity and the rescaled physical error: the immediately
  preceding target, P1:sz-growing-physical-coercivity. Its final audits are
  recorded there; do not assume a draft has passed.
- Uniform symbol cancellation and arbitrary-vector low-band/tail bound:
  CCMRestrictedWeilSourceContraction.
- Full-line norm bound D*exp(a), D=norm(kappa)+46:
  CCMRestrictedWeilRemainderMultiplier:205.
- Exact physical compression bound:
  CCMRestrictedWeilGroundFrequencyLocalization:293,
  `norm_ccmApertureCompression_le`.
- The literal interval operator is the unitary conjugate of the physical
  remainder (definition located in SuzukiWeilFriedrichsOperator:48).

## Odd-channel paper calculation to audit

Write u for the already constructed canonical Neumann vector, g for its actual
Gamma lift, w for the odd Ta response, z=w-FromForm(g), and f=Jw. Put
C0=2D and K0=2log(C0)+10. The current source estimates give

    norm(u) <= 2M0*exp(-a/2),
    V_u <= 2C0*exp((log(C0)-1/2)*a),
    norm(u-Q_exp(K0*a)u) <= (4C0/pi)*exp(-11a/2).

For every epsilon>0, the actual symbol is at most (epsilon/2)*exp(a)
on that fixed exponential band, eventually. The arbitrary-vector operator
split therefore implies

    abs(Re<B_a u,u>)
      <= 2*epsilon*M0^2 + C1*exp(-5a).

Since epsilon is arbitrary, the complete bounded-remainder quadratic on u
tends to zero. No prime or polar term is discarded individually, and no
infinite Neumann series is substituted for the actual finite vector.

The exact Ta residual norm is O(sqrt(a*exp(-a))), hence tends to zero.
The already proved uniform odd energy bounds norm(w)_Ta; triangle inequality
also bounds norm(FromForm(g))_Ta. Thus the difference of their squared Ta
norms tends to zero. The exact energy identity for FromForm(g) is

    norm(FromForm(g))_Ta^2
      = norm(g)_Gamma^2 + c_a*norm(u)^2 + Re<B_a u,u>.

The Gamma and bounded-remainder terms vanish, so O_a-c_a*norm(u)^2 -> 0.

The new rescaled approximation target gives exp(a)*norm(f-u)^2 -> 0.
Together with the displayed bound for u, the norm-square difference inequality
gives exp(a)*abs(norm(f)^2-norm(u)^2) -> 0. Exact unitary transport and
compression imply

    c_a <= 1+D*exp(a) <= (D+1)*exp(a).

Hence c_a*(norm(f)^2-norm(u)^2) -> 0. Combining the two limits proves
c_a*N_o,a-O_a -> 0.

## Even channel and signed consequence

### Shorter odd-channel source identity (2026-10-02)

Source inspection of SuzukiMatchedOddSourceBound:141 gives the exact private
identity O_a=Re<p_a,f_a>. Exposing this already proved identity will avoid the
separate comparison of squared Ta norms in the preceding paper calculation.
Indeed, r_a=p_a-(c_a I+B_a)u_a gives exactly

    O_a-c_a*norm(u_a)^2
      = Re<p_a,f_a-u_a> + Re<r_a,u_a> + Re<B_a u_a,u_a>.

The first term vanishes since norm(p_a)<=exp(a/2) and the rescaled physical
error tends to zero. The second vanishes by the actual residual/norm estimates.
The third is the same complete signed multiplier obligation above. Thus the
new route reduces odd metric balance to that single retained prime--polar
quadratic and the shift-weighted norm-square comparison. The latter now has
a complete epsilon proof drafted in scratch; no new premise is used.

The new arbitrary-Gamma tail theorem also shortens the remaining quadratic
proof. Let exp(a)*norm(u_a)^2<=M and norm(g_a)^2<=D*a*exp(-a),
with the already proved fixed M,D. At R=exp(K*a) it gives

    exp(a)*norm(u_a-Q_R u_a)^2 <= C_arch*D/K.

Choose K large first. The global remainder bound and Cauchy--Schwarz make
the complete high-frequency quadratic at most
normBound*sqrt(M*C_arch*D/K), uniformly for large a. For this fixed K,
the existing symbol theorem makes the low-frequency quadratic arbitrarily
small. Hence the full quadratic tends to zero without reopening or sharpening
the finite-exponential budget calculation. This is a new proof mechanism
deduced directly from the audited arbitrary-Gamma tail and actual form lift.

Search1188324 (partial, coverage pending, source_only) returned the exact
finite telescoping identity and form remainder decomposition, but no proof
idea or ingredient set for this limit. The mechanism above uses the actual
audited sources; no absence or novelty claim is inferred from the search.

The actual matched even source is (p_++p_-)/2. Both initial norm and finite
exponential budget obey the same scale exp(a/2). The general budget contraction
already applies to every certified source. Extend the finite recurrence,
canonical test vector, Gamma lift and residual comparison to this literal
source, reusing the common argument where possible. Its energy is already
uniformly bounded by 1/2 in SuzukiMatchedEvenSourceBound.

Only after both actual channel balances are proved, use the exact identity

    c_a*(O_a*N_e,a-E_a*N_o,a)
      = O_a*(c_a*N_e,a-E_a) - E_a*(c_a*N_o,a-O_a).

Uniform energy bounds then give this same-aperture signed determinant
cancellation. For bounded aperture increments b-a, the known shift lower
bound and now-proved upper bound give a bounded ratio abs(c_b-c_a)/c_a.
However this does not yet pay the actual discrete metric term: source
inspection at CCMSuzukiCrossApertureRieszTransport:361 shows that it contains
covariance at b applied to the extended response from a. An explicit
cross-aperture comparison is still needed, even for bounded increments.
Arbitrary cofinal increments and the complete signed shell Wronskian remain
unproved. The ratio bound alone must not be reported as metric-work closure.

## Checks

- [x] Corpus searches and exact compression/source inspection.
- [x] Verify interval-to-physical operator norm upper transport: scratch41623 passed.
- [x] Prove shift-weighted physical norm-square approximation: scratch41623 and final58443 pass; leaf wired.
- [x] Prove the complete B_a quadratic on actual u_a tends to zero: scratch55478 and final66228 pass; leaf wired.
- [x] Prove odd c_a*N_o,a-O_a tends to zero: final leaf16313 passes; leaf wired.
- [ ] Construct and audit the actual even-channel analogues.
- [ ] Prove the signed metric cancellation with both actual channels.
- [ ] Attack the retained complete shell Wronskian; preserve normalization and shift obligations.

## Audit checkpoint

MetricTransport scratch61966 found only an ambiguous operator-norm instance
at the upper-transport proof. Supplying the explicit physical remainder to
norm_nonneg fixed it; scratch41623 passes all three public results without
warnings. Final leaf58443 is running. This correction changes no mathematics.
The separate complete-remainder quadratic proof is drafted using the actual
Gamma lift and the arbitrary-width tail inequality, not a sharper source
budget. It awaits its sequential scratch audit.

Search1188435 finished (partial=false), but its complete source inventory
contains mostly pending/stale compiler metadata. Its odd-symmetry ingredient
set does not prove a projective energy ratio or its limit. Direct source
inspection identifies an important anchor distinction: the V2 first-mode
Wronskian identity at I uses actual energies at parameter1
(CCMSuzukiCrossApertureProjectiveWronskian:395), while this card proves
matched pole estimates at parameter1/2. Do not identify them. The current
work targets actual matched-source signed metric balance. Transfer to full
V2 source current and its canonical normalization remains a separate hard
obligation, even after that balance closes.

Complete-quadratic scratch69560 found three proof-engineering issues: norm
coercion was not normalized before squaring, one field_simp already closed
its goal, and the inner-product scalar field needed explicit vector arguments.
The mathematical inequalities stand unchanged. The next scratch audit uses
explicit mul_self_le_mul_self, removes the redundant tactic, and supplies
those vectors. An unconditional Tendsto root was added from the epsilon
statement. No heartbeat increase or numerical experiment.

Final MetricTransport58443 and CompleteRemainderQuadratic66228 pass without
warnings, and both leaves are wired. The latter imports only its two actual
CCM dependencies. The exact source-energy identity is being exposed by a
public wrapper over the existing private proof; its private name and all
previous proofs remain intact. The actual odd metric-balance epsilon and
Tendsto roots are drafted from the exact source equation and the two now
audited components. No actual even or full-current result is inferred.

## Next source-based conjecture exposed by the quadratic proof

For the same literal u_a, conjecture the vector statement

    exp(-a)*norm(B_a u_a)^2 -> 0.

The current audited split and actual Gamma lift give a dependency-closed
paper mechanism: if exp(a)*norm(u_a)^2<=M and Gamma energy<=D*a*exp(-a),
then for every fixed K>0 the retained Fourier tail satisfies
exp(a)*T^2<=C_arch*D/K. For every eta>0, eventually

    exp(-a)*norm(B_a u_a)^2
      <= 2*eta^2*M + 2*normBound^2*C_arch*D/K.

Choose K first, then eta. This is a vector-profile theorem, not a numerical
sharpening of the quadratic. With the existing exponentially small residual
and c_a>=exp(a)/2 it gives

    exp(a)*norm(u_a-p_a/c_a)^2 -> 0,
    exp(a)*norm(f_a-p_a/c_a)^2 -> 0.

The second line uses the now-audited physical response-minus-Neumann error.
Its actual even analogue would let mixed physical pairings be compared with
explicit pole-source pairings at two apertures, retaining parity cancellation.
For bounded aperture gaps, the known norm rescalings keep these comparison
errors bounded; arbitrary gaps still need uniform two-aperture estimates.
This is the next proposed attack on the actual mixed-response obligation.
It is not yet Lean-closed and does not identify the anchor1 V2 current.

Final odd balance audit16313 passed without warnings after replacing the
namespace-sensitive addition alias by explicit add_le_add. Public source
energy wrapper audit47712 also passed. Axiom audit58144 passes all eight new
public queries with only propext, Classical.choice and Quot.sound; exact
actual physical balance root signature checked. All three new leaves are
wired once. Global lint38139 reports twelve unrelated unreachable modules,
no prohibited proof declarations; exact names are on the P3 card. This is
verified progress on the odd channel, not a complete cross-aperture or RH
proof. Next conjecture is the explicit physical pole profile described above.

Vector-profile search1188650 is partial (deadline/filter-and-judge unfinished),
coverage pending and hits source_only. It retrieves the literal finite
Neumann identity/decay, the actual shifted operator, Gamma budget band, and
the newly audited complete-quadratic theorem as source arguments. It returns
no proof idea or ingredient set; no absence claim is inferred. These actual
sources support the next vector conjecture above.

## Vector-profile implementation, 2026-10-02 continuation

Current search1188716 finishes with complete source-inventory snapshot but
mostly pending/stale compiler metadata. The suggested odd-integral/chamber
ingredient set is inapplicable to the vector norm target. Direct current
source inspection confirms the actual Gamma lift, uniform exponential-band
symbol, and exact remainder compression used by the proof.

The strengthened CCMFiniteNeumannRemainderQuadratic final audit87163 passes
without warnings. It now proves exp(-a)*norm(B_a u_a)^2->0, and the prior
quadratic root is a corollary. A single Gamma-tail argument supplies both.
Scratch35259 found only a subtype-norm rewrite in the old-root corollary;
explicitly fixing the normed type before scalar algebra resolved it. The
module was already wired, so no additional import is needed.

The actual pole-profile module is drafted in scratch. Its finite-vector
identity is c_a*(u_a-p_a/c_a)=-(B_a u_a+r_a). The shift lower bound and the
new scaled remainder norm imply exp(a)*norm(u_a-p_a/c_a)^2->0. The existing
actual response-minus-Neumann result then gives the corresponding actual
response profile. Its sequential Lean audit is running.
