# Polynomial integer prefixes for the full collided metric

- **ID:** CDG-POLYNOMIAL-PREFIX-METRIC
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Conjugate-Diagonal Geometry question 2; fixed-strip source geometry.
- **Count:** Unaccepted. A possible stronger endpoint of the same finite-metric candidate, not an additional contribution.

## Obstacle and proposed advance

The current disc-based schedule pays a whole-plane Gaussian transform bound,
although every actual xi zero lies in the fixed strip `0<=Re s<=1`.
On a bounded real-part strip, the modulus of a bilateral theta integrand is
independent of the ordinate. A fixed strip cutoff stretched vertically can
therefore separate the two costs: polynomial test growth in the logarithmic
aperture, and a polynomial local logarithmic mass bound.

Target: a positive full-trace reading with a **polynomial number of integer
theta atoms**, uniformly over the normalized growing test family. This is
not a polynomial-time algorithm claim: integration and regulator precision
are separate costs. No smaller numerical constant is a separate result.

## Proposed exact construction

Let b be the existing fixed planar bump `sourceCutoff 0`, equal to one on
the unit disc and supported in the disc of radius two. For t=n+1 define

```
chiStrip_n(s) = b((Re(s)-1/2) + i Im(s)/(4t)).
```

It is identically one at every actual zero with `|Im(s)|<=n+2`, is supported
in `|Re(s)-1/2|<=2`, `|Im(s)|<=8t`, and hence in a disc of radius `11t`.
The first and second derivatives of the fixed bump give a constant M>=1
controlling the first derivatives and Laplacian of every `chiStrip_n`:
vertical differentiation only adds factors at most one. Let C be one fixed
positive integer at least M. Set

```
K_n = C t^20,
eta_n = exp(-K_n),
N_n = (C+4) t^20.
```

Use the literal reflected prefix through `N_n+1`, and its exact amplitude
and first moment from the checked finite-source construction, in the
positive curvature reading with cutoff `chiStrip_n`.

Conjectured universal coefficient B>=0, before all test/order/stage choices:

```
|QStrip_n(twist_tau f,L,j)-D_j(twist_tau f,L)| / 4^j
 <= S(f)^2 [B/(n+1)^2 + 40 sourceReferenceTail(n)]
 <= S(f)^2 [B/(n+1)^2 + (640/n)(C_xi+log(n+4))]
```

for n>=1, a>=0, support(f) in [-a,a], `|tau|<=n/2`,
`a+j|L|<=2log(n+1)`, with
`S(f)=4(integral|f|+integral|f''|)`.
The resulting uniform convergence has its stage threshold before all tests,
apertures, orders and motions. The cutoff and source prefix are prescribed
independently of all those choices and of the divisor.

## Paper mechanism to verify

1. Fixed bump derivatives are bounded by compact support. The anisotropic
   affine pullback above has horizontal derivative one and vertical
   derivative `1/(4t)`, so its first derivatives and Laplacian have one
   uniform actual constant. No derivative-control premise is introduced.
2. On the cutoff support and its unit complex neighborhoods,
   `|Re(s)-1/2|<=3`. Fourier decay gives the height-independent bound
   `|F_f(s-i tau) exp(u(s-1/2))|<=S(f)exp(3(a+|u|))`.
   Unit-radius Cauchy bounds give the same bound for the first holomorphic
   derivative. The existing squared-modulus Laplacian formula and exact
   second-translation recurrence therefore bound the cutoff moment
   Laplacian by `4^(j+1) M S(f)^2 exp(6(a+j|L|))`, hence by
   `4^(j+1) M S(f)^2 t^12` in the joint window.
3. The existing actual xi logarithmic-square estimate on discs, evaluated
   at a linear integer multiple of n, gives
   `integral_(disc 11t) (log|xi|)^2 <= C1 t^6` for one proved C1.
   The scalar regularization error and area at most `121pi t^2` then give
   `M * localPotentialError <= C2 t^-14` for eta=exp(-C t^20):
   the logarithmic term costs `8M/K`, and
   `exp(-K/2)<=2/K` controls the constant term. This leaves at most
   `C3 4^j S(f)^2 t^-2` after Green testing.
4. On the bounded real-part strip, the amplitude and its finite-prefix
   error have fixed constants, independent of ordinate. This follows from
   the literal integrand modulus, the existing positive-source envelope,
   and the relative integer tail. Potential stability gives a bound
   proportional to `M exp(K_n-(N_n+1)^2)`. The prescribed polynomial prefix
   bounds this by a fixed constant times `exp(-K_n)<=1/K_n`; disc area
   and the same test Laplacian leave a smaller `t^-6` error.
5. On every actual zero where `chiStrip_n != 1`, the old radial cutoff
   `sourceCutoff n` is zero. Thus the new omitted trace is bounded by the
   already proposed shared-aperture kernel majorant times the **old**
   `sourceReferenceTail(n)`. No new divisor summability or tail-rate input
   is needed. Normalization uses `2^j<=4^j`.
6. Add finite-source, regulator, and omitted-trace errors. All constants
   are obtained from the actual fixed bump, theta envelope and proved xi
   log-square mass; none is an analytic assumption at the endpoint.

## Status and dependencies

The existing finite-source stability/current chain is checked. Its fixed-test
full-trace endpoint now passes scratch and main leaf checks with standard
axioms only. The earlier
[all-test/all-order strengthening](../3-formalized/logarithmic-aperture-finite-theta-metric.md)
passes its source-only final check and all three standard-only axiom audits.
The present polynomial schedule has a closed paper proof and requires its
own exact Lean and novelty audits.

Corpus-first searches for strip cutoffs, Cauchy control, and existing
polynomial finite-source trace schedules are complete. The exact used
`SourceSquareCalculus`, `SourceCutoffControl`, and
`SourceMomentLaplacianBound` leaves have been read. No new mathlib search has been needed. The height-independent source
transform and first-derivative bounds are now drafted in
`cdg_source_strip_transform_bounds.lean`, using the exact existing
unit-circle Cauchy API; this draft is unchecked.

## Calibration

This remains a conjugate-diagonal metric, without successor charge or a
capacity sign theorem. A planted off-line packet contributes positive mass.
The source norm remains explicit, so uniformity does not assert zero
isolation. Finite atom count is polynomial in stage; numerical integration
complexity, precision, simplicity, RH, and fibre-selective positivity are
not claimed. The substantive candidate is the completed arithmetic metric
and its quantified source schedule, not a collection of rate corollaries.

## First overlap screen

The exact `XiCTaylorThetaTailUniformFiniteTranslationDefectCurrent` header and final uniform theorem (lines 320–385) were read. That result gives superpolynomial decay of a signed translation defect on a fixed spectral disc under a depth schedule; it does not state the growing-height collided-metric estimate proposed here. The related finite-shell and positive-current searches have not identified an exact counterpart. This is a scoped comparison, not a proof of novelty.

The strip geometry can reuse the old reference tail: if the new cutoff is not one at an actual zero, its ordinate exceeds n+2 and the old radial cutoff vanishes. The local log-square bound uses the existing theorem at integer index `11*n+9`, whose disc radius is exactly `11(n+1)` and whose sixth-degree factor is at most `11^6(n+1)^6`. No new zero-counting estimate is needed.

## Closed scalar accounting

Write `C1=11^6 C_xi,L2` for the existing planar log-square constant after the linear radius substitution, and `H=thetaAmplitudeEnvelope(3)`. Let `C0=C_tail H^2`. With C>=M>=1 and t>=2, K=Ct^20>=4. Since `exp(-K/2)<=2/K`, the area term in the M-weighted potential error is at most `121pi t^-18`; the log-square term is at most `8C1 t^-14`. Hence it is bounded by `(121pi+8C1)t^-14`.

The prescribed prefix has N>=K+4. Therefore `(N+1)^2>=3K`, and `M<=K<=exp K` yields `M exp(K-(N+1)^2)<=exp(-K)<=1/K<=t^-20`. Finite-source Green error is at most `242 C0 4^j S(f)^2 t^-6`. The regularization error is at most `(2/pi)(121pi+8C1)4^j S(f)^2 t^-2`. Since t>=1, a universal local coefficient is `B=242 C0+(2/pi)(121pi+8C1)`. Together with the inherited tail estimate this closes the proposed paper accounting. The fixed-bump pullback and its exact formal derivative/support statements remain Lean obligations, not assumed premises.

The anisotropic cutoff is now drafted in `cdg_strip_source_cutoff.lean`, including compact support, containment of the old radial support on the zero strip, exact affine derivative pullback and uniform first/Laplacian bounds from one fixed bump. It is unchecked. Corpus-first searches preceded mathlib API lookup; all new names still require scratch compilation before promotion.

`cdg_theta_strip_amplitude_bounds.lean` now drafts the required height-independent actual theta estimates. A shared dominated-integral helper transfers the checked disc integrand bound to a real-part strip; the full amplitude, finite amplitude, and Gaussian integer-tail endpoints discharge its hypotheses explicitly. The draft is unchecked.

The moment differential chain is drafted in `cdg_strip_source_moment_bounds.lean`: fixed-strip cutoff square, exact translation recurrence, and global bound `4^(j+1) M S(f)^2 (n+1)^12` in the joint aperture. The cutoff draft now includes the support-vanishing lemmas needed by Green testing. These drafts remain unchecked.

The exact polynomial scale, stretched-disc xi potential error, fixed-strip finite-potential stability, compact Green reading errors, and transfer to the old reference tail now have complete scratch drafts. Their dependency leaves remain under verification. No additional analytic premise was added; the universal constants are obtained from the fixed bump and the actual xi log-square theorem.

The full positive polynomial-prefix metric, universal homogeneous reference-tail bound, arithmetic logarithmic certificate, and uniform convergence endpoint are now drafted in `cdg_polynomial_theta_metric.lean`. The source-stage threshold precedes all test, order, aperture, and motion choices. Every polynomial-chain leaf is still unchecked.

## Renewed literature check

Rechecked [Haglund's primary paper](https://arxiv.org/abs/0910.5228) and
[Andersson, section 5.6](https://d-nb.info/1355764351/34). Finite theta
approximants and smooth positive approximations of divisor currents are
established ingredients, excluded from contribution counting. The remaining
candidate is the precise arithmetic schedule together with the full trace
and growing test-family estimate. Search results have not established its
novelty. New broad web queries returned mostly different zero criteria,
Laguerre positivity, or reciprocal-xi positivity; none supplies a substitute
for an exact statement-level comparison.

Corpus follow-up compared `ThetaCuspCenterMixedDivisorTomography.lean`
through its local-sign theorem. It proves exact multiplicity-sensitive
factorization and local transverse sign change of the completed squared-
modulus derivative. That is a different current and does not state the
polynomial-prefix full-trace estimate. Local divisor tomography and
multiplicity retention themselves are therefore not new claims here.

## Dependency-closed paper audit

The construction uses only the fixed bump in C and the stage in K, eta and
N. The comparison proof uses actual xi log-square mass and the previously
proved arithmetic reference tail. Neither the construction nor the theorem
assumes zero separation, an off-line zero exclusion, or an unevaluated
analytic bound. The Green normalization is `1/pi` times curvature because
`Delta(half log(|A|^2+eta))=2 eta |A'|^2/(|A|^2+eta)^2`.
The three errors are respectively of orders `4^j S^2 t^-6`,
`4^j S^2 t^-2`, and `2^j S^2 sourceReferenceTail(n)`.
The asserted endpoint follows after division by `4^j`. The case n>=1
ensures K>=4; all source definitions and finite-truncation estimates also
exist at n=0. This paper audit identifies no unproved analytic input.
Formal verification is still required for the exact drafts.

## Current formal verification

`SourceStripTransformBounds` passes scratch 4395 and main dependency check
95790 with standard axioms only. It is wired into the umbrella.
`StripSourceCutoff` is under scratch verification (31787). The remaining polynomial leaves are
still unchecked. The earlier aperture theorem is complete, but remains part
of this same unaccepted candidate.

## Local selection extension under audit

The same source schedule may resolve shrinking planar neighborhoods, instead
of only transform squares. This is a proposed application of the same metric
candidate, not a second contribution. Put `r_n=1/(16(n+1)^6)` and use the
actual rescaled fixed bump `b((s-z)/r_n)` in the finite curvature integral.
The target is one universal E with

```
|localReading_n(z) - sum_rho m_rho b((rho-z)/r_n)| <= E/(n+1)^2
```

uniformly for `0<=Re z<=1` and `|Im z|<=n/2`. The bump's Laplacian costs
at most `M/r_n^2`; its support lies in the fixed strip and the containing
source disc. Multiplying the proposed M-weighted local potential errors
by this cost gives the displayed order. This still requires an exact
support/scaling/current proof and a novelty audit.

If established, positivity and the bump's inner/outer radii would give

```
count(closedBall(z,r_n)) <= localReading_n(z)+E/(n+1)^2,
localReading_n(z)-E/(n+1)^2 <= count(closedBall(z,2r_n)).
```

For stages with error below 1/2, the level set `localReading_n>1/2`
contains every actual zero in the center window and lies within `2r_n`
of the actual divisor. This is neighborhood selection with multiplicities,
not a spacing lower bound, simplicity assertion, or numerical algorithm.
No zero-free boundary or known zero coordinate enters the reading.

Corpus comparison already excludes the counting bracket as new:
`RHTower/ModulusSlopeField.lean` gives exact two-radius xi-logarithm
brackets. Its definitions, Jensen difference, and upper/lower bracket proofs
were read through line 310. The full `SelbergPlanarTestScaling.lean` was
read; its actual inverse-square Laplacian and support laws provide existing
scaling infrastructure. The new obligation would be the literal finite
prefix, prescribed regulator, growing height, and shrinking radius together.
A further exact-overlap search surfaced `ArithmeticFiniteSourceContour.lean`,
now read in full. It proves finite Bernoulli-head multiplicity transport and
nearby zeros after choosing a zero-free circle and a sufficiently large
cutoff. It does not state this proposed uniform shrinking-disc schedule.
This scoped distinction does not establish novelty. No proof or contribution
credit is claimed for this extension.
