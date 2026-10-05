# BAG complete hyperbolic transition action

- Route: BAG, complete signed physical cubic.
- Parent: bag-three-frequency-ramanujan-source.md.
- Basis: C28.56ag.3 exact critical finite physical atom identity.
- Status: continuation01a8 paper attack; no new signed estimate or Lean theorem.
- Target: the complete projected critical atom action is o(N/log(N)^2).

## What is already closed

ChiPrimeGaussianCubicCriticalAtoms identifies the ORIGINAL physical cubic
exactly for every real N>=1. Both finite rational translation projectors,
all physical factors, and the whole integer band are retained. The source
selects prime logarithms exactly; no damping/composite approximation remains.
ChiPrimeGaussianCubicSharpEdges supplies actual smooth full-band cutoffs with
N^(1/4)-width edge strips and negligible comparison error. Neither result
proves the signed cubic estimate.

## Attempt and precise failure of its estimates

Attempt: replace the dual hyperbolic integral by its stationary value, then
use the existing complete critical rational trace. This cannot be justified
by the estimates presently proposed. For edge width H, the audited sharp
comparison has squared error at most C*(H+1)^2*N*(1+log(N+1)). Its normalized
upper bound therefore becomes small if H*log(N)^(5/2)/sqrt(N) tends to zero.
In contrast, the simplest two-coordinate Taylor/stationary expansion has
dimensionless edge parameter N/H^2 and would require H/sqrt(N) to grow.
These two sufficient conditions cannot hold together. At the corpus's
H=N^(1/4), that expansion parameter grows, rather than tending to zero.

This is a failure of THIS pair of estimates, not a theorem that no saddle
method, smoothing choice, or BAG proof can work. No route is retired. Do not
formalize a weak numerical bound or another receiver assuming cancellation.

## Candidate preserving the entire transition

Write e(t)=exp(2*pi*i*t). For a smooth compact physical slice A_r(p,q), define
its two-coordinate Fourier transform with negative sign, and the exact
Fourier multiplier action

    T_r A(s,t) = integral_(xi,eta)
      hat(A)(xi,eta) * e(s*xi+t*eta-r*xi*eta) dxi deta.

The candidate full kernel formula, for r>0, is

    integral_(p,q) A_r(p,q)*e(p*q/r+x*p+y*q) dp dq
      = r*e(-r*x*y) * (T_r A_r)(-r*y,-r*x).

Paper mechanism: let G(xi,q)=integral_p A_r(p,q)*e(-xi*p) dp.
Fourier inversion in the second coordinate gives

    T_r A(s,t) = integral_xi G(xi,t-r*xi)*e(s*xi) dxi.

At s=-r*y,t=-r*x, substitute q=-r*x-r*xi. Multiplication by
r*e(-r*x*y) yields exactly the original double integral, including its
amplitude. Schwartz decay supplies the integrability/Fubini obligations;
the Lean construction and those obligations are not yet discharged.
No nonintegrable integral of a bare plane wave is used as a delta function.

Thus the complete three-coordinate kernel should retain

    integral_r r*e(r*(z-x*y)) * (T_r A_r)(-r*y,-r*x) dr.

This keeps every edge transition instead of replacing T_r A by A. After
Poisson summation EVERY integer lift must remain. Apply the already literal
finite contraction projectors to this full expression. Their simultaneous
shift changes z-x*y by -(1+y)*a-(1+x)*b-a*b, and also shifts the evaluation
points of T_r A. Neither change can be dropped.

## Actual hard obligation

The desired result is a signed estimate of that ENTIRE lifted, projected
critical atom action with the actual N-dependent A_r, at o(N/log(N)^2).
Pointwise norm bounds multiplied by atom total variation do not establish
it. Nor does the unit modulus of the Fourier multiplier, a fixed-test
critical boundary, or an exact Poisson identity by itself. The whole
1/N-scale neighborhood of z=x*y and all transverse tails remain.

Next proof must either close this source-specific aggregate or supply a
uniform operator estimate that applies to the actual prime source and
actually reaches the target scale. Missing analytic infrastructure should
be built as part of that proof, without assuming its conclusions.

## Corpus audit

Four searches completed with all candidate/source statements, method
summaries, proof ideas and proposed ingredients inspected:

- critical-transverse: session42809, nonpartial65678/65678; the proposed
  unrelated cone-action pairing does not transfer to BAG.
- prime-trilinear-dispersion:25786, nonpartial65678/65678; Kloosterman
  reorganizations do not supply the required signed prime-cubic bound.
- physical-poisson-bridge:25834, nonpartial65678/65678; original chi-kernel
  estimates concern a different transform; phase translation alone is
  insufficient for the full new dual action.
- full-kernel-poisson:48887, nonpartial65680/65680; one-dimensional Schwartz
  Poisson is applicable infrastructure, not a proved nonseparable
  three-coordinate transfer or cancellation estimate.

All had incomplete refresh under the background indexer and source-only /
pending compiler metadata. Actual physical cubic, sharp-edge, finite-source,
one-dimensional Poisson and Fourier-dilation source files were inspected.
No conclusion is inferred from search absence or ranking. Search JSON is in
/tmp/bag-*-search-01a8.json. All jobs terminal; no Lean source changed in
this follow-on attack and no numerical experiment was run. RH goal ACTIVE.

## continuation01a9 — build the complete transition on actual separable slices

Mission: unconditional Lean RH proof/refutation through BAG. Prior turn
progress was evidence changing the next proof, not a cancellation estimate.
Current construction keeps the entire hyperbolic Fourier multiplier. Use
separable Schwartz slices and the actual physical window's Mellin inversion
to retain the nonseparable W(p*q/(r*N)) factor. This permits a full transition
proof using the corpus's one-dimensional Fourier inversion/Fubini APIs,
without assuming a multivariate Poisson or stationary approximation theorem.
All scale-dependent edges, Mellin tails, rational lifts and contractions
remain obligations of the actual physical assembly. The final target is
still the complete signed growing action, not this analytic representation.

## continuation01a9 final checkpoint — C28.56ag.4

The candidate exact continuum transition is now proved for the actual
window and Gaussian/logarithmic slices, including every Mellin frequency
and the complete moving edge profile. See P2/P3
bag-full-window-hyperbolic-transition.md. Two leaves,19 public declarations;
production59166/41307 and axiom56220 passed. Index35593 passed;18 names are
in generated LEAN_API, while the attributed apply lemma is verified by the
explicit axiom audit. Both imports occur once. Lint11175 has26 unrelated
unreachable modules only. No signed saving is claimed.

Contribution: the exact full physical continuum slice is constructed,
avoiding the failed edge-width Taylor substitution. The next genuine
obligation is complete lattice transfer with all three coordinates and all
integer lifts, then source-specific signed cancellation. The r-variable,
literal projectors, critical atom tensor, near-cone region and transverse
tails cannot be dropped. RH and all downstream BAG gaps remain open.

## continuation01aa — full physical Fourier summability, C28.56ag.5

The actual THREE-coordinate amplitude is now an audited Schwartz function,
with exact original integer coefficients and absolutely summable Fourier
values at every shifted full integer lattice. The unconditional family
retains the existing negligible edge comparison. This closes the omitted
r-coordinate regularity/convergence construction, not Poisson matching or
signed cancellation. See P3:bag-full-physical-fourier-lattice-summability
and P1:bag-complete-lattice-fourier-transfer for the next exact obligation.
Production19066, all12-name axiom14865 and index92591 passed; lint13216 has28
unrelated unreachable modules. No estimate uniform in growing N is claimed.

## continuation01ab — complete lifted signed action

The full Poisson identity and finite critical/projector matching now pass
production Lean audits. The actual smoothed signed cubic is exactly the
critical tensor acting on the complete shifted Fourier lattice, with BOTH
literal contractions and their intersection retained. The original sharp
cubic differs by the existing negligible normalized error. This closes the
representation gap in the previous checkpoints, not signed cancellation.
All12 public declarations passed standard-axiom audit11043; index18738
passed, all12 API entries/imports verified. Lint56265 reports31 unrelated
unreachable modules only. See P3:bag-complete-physical-poisson.

Next mathematical attack: derive the literal three-dimensional Fourier
coefficient from the audited full-window transition. For Fourier frequency
(xi,upsilon,zeta), the exact r-phase should be

    exp(-2*pi*i*r*(zeta+xi*upsilon)).

Its amplitude must retain the entire Mellin integral and the full
bagHyperbolicTransition at (r*upsilon,r*xi). The original reciprocal r
cancels the transition's r Jacobian on the actual positive support. Prove
this identity with actual integrability, retaining r-dependence and every
lattice lift; do NOT replace the transition by a stationary value or swap
the full lattice with the Mellin integral without a proof. This exposes
the precise transverse defect in the already matched complete action.
Then solve the signed near-cone/tail cancellation for that whole action.
The delta-small sector is not removable by an absolute Fourier estimate.
Growing moments, moving cofactors, common-height self-return and RH remain
open. This is the next conjecture, not an asserted Lean theorem.

## continuation01ac — full transverse coefficient

Previous turn is progress: audited complete signed lifted matching, without
an asymptotic estimate. This turn attacks the phase of that SAME full action.
Prove a volume-preserving (r,q,p) decomposition of the actual Euclidean
Fourier integral; use compact-support integrability for full Fubini. Then
insert bagCubicWindowKernel_eq_full_transition on the actual positive
r-support and cancel its exact Jacobian. Target the full nested r/Mellin
formula with defect zeta+xi*upsilon. All arithmetic actions/lifts remain
outside the proved coefficient integral unless an interchange is justified.

Search96344 completed with partial reranking deadline, full65714/65714
source inventory, background refresh incomplete, compiler mostly pending /
source-only. All20 candidates,20 source arguments, empty proof ideas and
proposed ingredients inspected. Generic convolution/near-zero kernel hits
do not prove the literal physical coefficient. Targeted lexical99026 found
the exact full-window theorem; source checked. Volume-preserving coordinate
and Fubini APIs also read directly. Coordinate lemma development99439 passes:
full r,q,p integral equality AND integrability of the outer integral. The
actual source coefficient and profile proof is now in development.

Final01ac checkpoint: ChiPrimeGaussianCubicTransverse passes production91858
and all8-name axiom90906 (standard axioms only). The unconditional full
transverse critical family retains every lift, both literal projectors and
the original negligible edge error. Index64921 passes, all8 API entries and
single import verified; lint19602 has33 unrelated unreachable modules.
See P2/P3:bag-complete-transverse-critical-action and C28.56ag.7.
The exact phase is now proved; signed growing-N cancellation is not.
Next arithmetic attack is recorded in bag-critical-distinguished-prime-source:
match the actual square-sieved derivative to distinguished prime shifts,
then derive the correct complete signed trace for those shifts.
