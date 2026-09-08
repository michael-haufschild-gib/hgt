# Selberg quarter bound: constructive conjecturing loop

- **ID:** SELBERG-QUARTER-CONJECTURING
- **Stage:** 1-in-progress
- **Goal:** An unconditional Lean proof of the all-congruence Maass cusp quarter bound.
- **Method:** Corpus-derived ingredients → precise conjecture → attempted proof or explicit failure → stronger surviving statement → pivot. Searches discover ingredients rather than stand in for mathematical work. Use wide `research ... --any` discovery batches; multiple terms without `--any` mean AND. Narrow AND queries follow specific leads, not replace wide discovery.

## Plan

- [x] Locate reusable exact cusp conjugation, ground-state factorization, and gluing/Schur identities.
- [x] Cycle 1 paper attempt: derive the complete cusp Hardy identity and test whether zero Fourier mean removes its boundary cost.
- [x] Cycle 2 paper attempt: test whether positive averaging of local quarter-energy half-densities preserves or improves their lower bound.
- [x] Cycles 3–4: change the averaging operation; prove the exact local correction and test translation descent.
- [x] Formalize the geometric-interpolation survivor and its strengthened translation obstruction against the genuine hyperbolic differential operator.
- [x] Cycles 6–8: classify the first-gradient kernel, recover its missing channel with a second moment, and formalize exact spatial recovery from first derivatives at two heights.
- [x] Formalize the boundary-corrected Hardy identity retained by cycle 1, including the stronger frequency-compensated cusp-tail bound from cycle 11.
- [ ] Formalize the harmonic-mixture identity retained by cycle 2.
- [ ] Formalize the normalized translation-average limit and loss of correction from cycle 5.
- [ ] Use that survivor to formulate and attempt the next arithmetic conjecture; keep the full Selberg goal unchanged.
- [x] Cycles 9–10: distinguish logarithmic-scale rate loss from ordinary-scale rate recovery, with actual integrability, set-integral evaluations, and complete range classification.
- [x] Cycle 12: derive the actual Maass constant-term Euler equation and decay at C² regularity, then prove constant-term vanishing throughout `0<lambda<1/4` at infinity.
- [x] Cycle 13: test integral cusp relocation as a covering shortcut; formalize its failure on an open band and the sharp orbit-height maximum as the positive survivor.
- [x] Cycle 14: derive the actual critical Bessel slope, classify its unique sign transition, and prove the exact compact-profile energy identity and improved sufficient tail cutoff.
- [x] Cycle 15: classify the finite adverse integer boundary block, prove its exact finite-packet cost identity, and test width-independent block size at fixed height.
- [x] Cycle 16: prove the exact trace-energy infimum using compact approximations and the necessary-and-sufficient isolated-tail cutoff.
- [x] Cycle 17: derive the source boundary growth envelope and its inverse-frequency correction without asymptotics.
- [x] Cycle 18: construct the actual Bessel correction as a compact diagonal operator and identify the exact frequency-weighted boundary-form domain.
- [x] Cycle 19: derive every actual Maass modal equation, uniform coefficient decay at infinity, and the fixed-height inverse-square frequency bound.
- [x] Cycle 20: construct the actual Maass Fourier trace in the sequence-space boundary-form domain, using the proved frequency bound.
- [x] Cycle 21: identify physical slice mass, both derivative energies, and quarter-energy by exact Parseval identities.
- [x] Cycle 22: prove actual mass/flux derivatives, exponential cusp mass decay, vanishing terminal flux, and finite physical tail energy at every positive height.
- [x] Cycle 23: prove the critical Bessel decomposition for actual noncompact complex Maass modes and its complete countable mode/height sum on the physical tail.
- [x] Cycle 24: construct integral translates of the actual C² Maass object, transport the boundary identity to every integral cusp, and construct the actual finite congruence trace with its exact unit-strip normalization and flux identities.
- [x] Cycle 25: prove the pointwise finite-trace energy identity, standard-area truncated-core Green theorem, and complete actual core-plus-cusp Bessel quarter form.
- [x] Cycle 26: prove strict physical mass and cutoff independence, test scalar-norm energy reconstruction, and formalize the exact actual radial/angular residual and its zero classification.
- [x] Cycle 27: construct actual normalized congruence directions and modular transport, prove weighted means and squared-distance separation, and test the zero-mean angular-energy shortcut against exact nodal reversal.
- [x] Cycle 28: derive actual regularized trace curvature, integrate it on standard modular area with full boundary flux, and classify the surviving nodal curvature on all intervals.
- [x] Cycle 29: construct smooth augmented source directions and exact mean/chord defect; prove actual path capacity and uniform variation costs; classify the nodal resistance singularity.
- [x] Cycle 30: construct the actual regularized amplitude-mean equation, prove its top-current limit from original cusp decay and source forcing, and extend the standard-area curvature balance to the full modular domain.
- [x] Cycle 31: prove a regulator-uniform full-domain amplitude-mass bound and identify the limiting retained curvature without dropping nodal concentration.
- [x] Cycle 32: identify actual limiting curvature on compact tests, prove its positive linear order structure and local order-zero bound, with local Green regularity and nodal charge retained.
- [x] Cycle 33: construct the unique actual regular curvature measure through common-compact approximation, prove continuous-test convergence, and recover the original C² identity with its error bound.
- [x] Cycle 34: prove modular covariance of the full regularized curvature and invariance of the actual regular curvature measure, retaining every measurable boundary contribution.
- [x] Cycle 35: prove dimension-two cutoff cancellation and atomlessness of actual curvature, including common source zeros and every countable exceptional set.
- [x] Cycle 36: construct actual normalized compact modular weights and the unique positive curvature functional on full compact orbit fields, with original regulator limits and seam/stabilizer multiplicities retained.
- [x] Cycle 37: compare the orbit functional with standard-cell curvature and prove its uniform finite signed budget using original cusp control; all source/build/axiom/lint audits passed.
- [x] Cycle 38: prove uniform original-source cusp tails and exact limiting total orbit mass; complete all source/build/axiom/index/lint audits.
- [ ] Cycle 39: test a geometric/arithmetic quarter lower comparison for the actual compact-orbit curvature, retaining original core, cusp, and nodal terms.
- [ ] Derive the remaining Fourier/cusp interfaces and test a core-plus-cusp argument that retains boundary flux and supplies genuine congruence-uniform control.

The unavailable `update_plan` tool is replaced by this card. No numerical experiments, unproved Lean assumptions, full builds, or commits are authorized.

## Corpus ingredients

- `RHTower/ThetaCuspHawkingBMCuspOperatorIntertwining.lean`: the actual shifted modular operator on compact logarithmic cusp tests becomes `(5/4-lambda)f-f''`.
- `RHTower/PrimeArchThetaMorseAnomalousDarboux.lean`: exact ground-state conjugation, with its Robin boundary defect retained.
- `HTGeometry/QuotientFusionProjectionGenesis.lean`: eliminating a shared boundary variable adds the weighted spread of local minimizers to the separate Schur complements.
- `HTGeometry/WeightedHardyInequality.lean`: a proved weighted Hardy estimate, useful for controlling tails after the boundary term has been identified.

These are ingredients, not an existing proof route. The new conjectures below will be derived explicitly from their mechanisms.

## Live mathematical notebook

The initial proposal is to glue local quarter-energy factorizations and use mismatch between local logarithmic derivatives to obtain a positive correction. Its two immediate risks are boundary flux at the compact/cusp seam and the sign of the averaging correction. Both must be calculated before any claim of a global inequality.

### Cycle 1 — does cuspidality remove the Hardy boundary cost?

**Conjecture:** zero horizontal mean makes the cusp Hardy factorization free of a boundary defect at a finite cutoff height.

**Attempt:** expand the square for a real smooth vertical profile on `[Y,B]`, with `Y>0`:

`integral (g'^2 - g^2/(4*y^2)) = integral (g' - g/(2*y))^2 + [g^2/(2*y)]_Y^B`.

The cross term is exactly the derivative of `g^2/(2*y)`. Integrating also in the horizontal coordinate retains the same identity with the squared boundary norm. A periodic trace `exp(2*pi*i*x)` has zero horizontal mean and squared norm one. Thus zero mean does not remove the lower boundary contribution. This disproves the proposed cancellation; it is not a counterexample to a full cusp energy inequality, since the horizontal derivative energy remains.

**Positive survivor:** an exact boundary-corrected factorization, with the lower seam cost explicit. The next conjecture must control that cost through gluing rather than discard it.

**Lean status:** the positive-ray compact `C¹` form is now closed as `SelbergCuspHardyBoundary.pure_hardy_boundary_identity`. Cycle 11 proves a stronger frequency-compensated identity and a cusp-tail quarter bound while retaining the lower boundary value.

### Cycle 2 — can a positive harmonic mixture supply the quarter bound?

The two local Poisson kernels at boundary points infinity and zero are `P_infinity=y` and `P_zero=y/(x^2+y^2)`. Their square roots are positive local quarter eigenfunctions.

**Conjecture:** `H=sqrt(P_infinity+P_zero)` has `Delta H >= H/4` for the positive hyperbolic Laplacian.

**Attempt and failure:** put `D=x^2+y^2`. Both summands are Euclidean harmonic. Applying the square-root chain rule gives

`(Delta H)/H = 1/4 - y^2/(D+1)^2`.

At `(x,y)=(0,1)` this is zero. In fact it is strictly below one quarter everywhere in the upper half-plane. This is a symbolic identity, not numerical evidence. Positive averaging of the squared half-densities introduces a variance term with the wrong sign.

**Positive survivor:** the exact local deficit `y^2/(D+1)^2`. It identifies the operation that loses the lower bound and motivates changing the mean.

### Cycle 3 — geometric interpolation reverses the variance sign

**Conjecture:** for every real `a`, the explicit field

`G_a(x,y)=exp((log y)/2 - (a/2)*log(x^2+y^2))`

satisfies the exact equation

`Delta G_a = (1/4 + a*(1-a)*y^2/(x^2+y^2))*G_a`.

**Paper proof:** its logarithmic gradient is `(-a*x/D, 1/(2*y)-a*y/D)`. The Euclidean Laplacian of its logarithm is `-1/(2*y^2)`, since `log D` is harmonic away from the origin. Adding the squared logarithmic gradient and multiplying by `-y^2` gives the displayed equation. All denominators are nonzero for `y>0`. For `0<a<1` the correction is strictly positive; at `a=0,1` it vanishes. This produces a genuine local supersolution family.

**Lean status:** the exact equation, real smoothness, endpoint eigenfunction predicates, positive symmetric correction, geometric-mean identity, and translation obstruction are now closed in `GaloisForLFunctions.RHTower.SelbergGeometricBlend`. The actual Frechet derivatives are proved against `positiveHyperbolicLaplacian`; the displayed gradient is not a hypothesis. [Paper proof and verification](../3-formalized/selberg-local-geometric-interpolation.md).

### Cycle 4 — can the local improvement descend?

**Conjecture:** the symmetric geometric interpolation `a=1/2`, which treats the two boundary kernels equally, is invariant under the modular translation.

**Failure:** `G_(1/2)(i)=1`, whereas `G_(1/2)(1+i)=exp(-log(2)/4)<1`. Symmetry between the two chosen boundary points does not give translation invariance. The local positive correction is therefore not a congruence spectral gap.

**Strengthening exposed during Lean:** for every natural `n`, `G_(1/2)((n+1)+i)<1`. The same symbolic logarithm proof covers every positive integer translation; this exact statement is now proved in Lean. It rules out all such translation periods of this field, not all possible gluing constructions.

**Next pivot:** seek an equivariant construction whose gluing defect is an operator on zero-mean boundary data, with its sign controlled after the constant channel is removed. The geometric-interpolation identity supplies the local correction to preserve; the failed translation test supplies an exact descent condition that must be repaired. No such repair is assumed in Lean.

### Cycle 5 — does a translation-orbit geometric average retain the gain?

**Conjecture:** normalizing translated quarter half-densities at `i` and taking larger geometric averages restores translation invariance while retaining a positive local correction in the limit.

For positive integers `k`, define

`H_k(x,y)=sqrt(y)*sqrt(k^2+1)/sqrt((x-k)^2+y^2)`

and, for `N>0`, `F_N=exp((1/N)*sum_(k=1)^N log H_k)`.

**Proof attempt:** at every fixed point, the ratio of the two quadratic expressions tends to one, so `H_k -> sqrt(y)` and `log H_k -> (log y)/2`. Split the average into a fixed initial segment and a tail whose terms differ from this limit by at most epsilon. The initial segment divided by `N` tends to zero; the tail contributes at most epsilon. Therefore `F_N -> sqrt(y)`.

For the local correction, put `D_k=(x-k)^2+y^2` and

`A_k=(-(x-k)/D_k, 1/(2*y)-y/D_k)`.

Directly from the translated endpoint differential identity, `y^2*|A_k|^2=1/4` and `A_k -> (0,1/(2*y))`. The exact finite geometric-mean chain rule gives

`(Delta F_N)/F_N = 1/4 + V_N`,

`V_N=1/4-y^2*|(1/N)*sum_(k=1)^N A_k|^2 >= 0`.

The same finite-head/tail argument shows `V_N -> 0`. No interchange of a limit and a derivative is needed: the finite differential identity is established first, then its explicit coefficient is passed to the limit.

**Outcome:** the proposed retained gain fails for this exhaustion. Its positive survivor is a precise limit classification: the normalized geometric means select the boundary-infinity quarter eigenfunction and lose their variance correction. This conclusion is proved on paper; formalization of this new limit statement is pending. A corpus Cesaro search provides reusable averaging infrastructure for that step, rather than a purported Selberg solution.

**Next conjecture to attack:** retain the centered boundary covariance as an operator before performing the group average, instead of averaging the scalar logarithmic gradients first. Test whether this order of operations preserves a nonzero correction on the mean-zero boundary channel and is compatible with both translation and inversion. Neither covariance persistence nor automorphic descent is assumed.

### Cycle 6 — does first-gradient covariance control all mean-zero boundary data?

Corpus ingredients: `SoninSemilocalDampedCovariancePositivity` retains the full Gram form instead of entrywise positivity; `GaussianJetPositivity` adds derivative features before taking a Schur complement; `SignedMomentSeparation` recovers finite coefficients from enough moments. These suggest testing the actual boundary feature map, including its kernel.

At `i`, the logarithmic gradients of the quarter half-densities based at infinity, zero, one, and minus one are respectively

`A_infinity=(0,1/2), A_zero=(0,-1/2), A_one=(1/2,0), A_minusOne=(-1/2,0)`.

**Conjecture:** their first-gradient Gram form is strictly positive on every nonzero mean-zero coefficient vector.

**Failure:** the vector `(1,1,-1,-1)` has zero mean and zero first gradient moment. This is a signed cancellation among distinct boundary directions, although the tangent covariance of the four directions is positive definite. Positivity on tangent vectors therefore does not give positivity on all boundary coefficients.

**Exact survivor:** for coefficients `(a,b,c,d)`, put `S=a+b+c+d`, `Q=a+b-c-d`, and `M=sum c_j*A_j`. Then

`|M|^2=((a-b)^2+(c-d)^2)/4`,

`a^2+b^2+c^2+d^2=S^2/4+2*|M|^2+Q^2/4`.

The first moment loses exactly the common coefficient channel and one alternating channel. No claim about full automorphic boundary data follows from this four-point test.

### Cycle 7 — does the trace-free second moment recover the missing channel?

**Conjecture:** add the actual directional second moment

`T=sum c_j*((A_j)_y^2-(A_j)_x^2)=Q/4`.

Then the exact centered norm is

`sum c_j^2-(sum c_j)^2/4 = 2*|M|^2+4*T^2`.

**Paper proof:** insert the four displayed gradients and expand squares. This holds for arbitrary real coefficients, with no mean-zero premise. The common kernel of `M` and `T` consists exactly of constant coefficient vectors. On the former blind vector, `T=1` and the centered norm is four. Thus second moments recover precisely the boundary information lost by first-gradient covariance in this configuration.

**Lean status:** proved in `GaloisForLFunctions.RHTower.SelbergBoundaryMomentChannels`, with the gradients derived from actual Frechet derivatives. The centered norm identity and exact kernel classification are closed. The next descent test must account for the fact that the four boundary points do not form a translation-invariant set. Higher moments repair local information loss; that alone does not establish global invariance or a Selberg bound.

### Cycle 8 — can spatial sampling replace the extra moment?

**Conjecture:** the missing alternating channel can be recovered using only first derivatives at two heights. This would connect moment recovery to spatial boundary response rather than require a separate second-order observation.

For centered coefficients `c'=c-S/4`, let `L_c'` be their weighted sum of the four actual logarithms. At `iy`, differentiating gives

`partial_x L_c'=(c-d)/(1+y^2)`,

`partial_y L_c'=(a-b)/(2*y) + (c'+d')*(1-y^2)/(2*y*(1+y^2))`.

Since `c'+d'=-Q/2`, at heights one and two the vertical derivatives are `(a-b)/2` and `(a-b)/4+3*Q/40`. Therefore

`T=(10/3)*(partial_y L_c'(2i)-(partial_y L_c'(i))/2)`.

Substituting into cycle 7 gives the exact two-height identity

`centeredNorm(c)=2*|grad L_c(i)|^2+(400/9)*(partial_y L_c'(2i)-(partial_y L_c'(i))/2)^2`.

**Paper outcome:** proved by differentiation and algebra. It identifies a concrete positive survivor: two spatial first-derivative observations recover all centered coefficients in this four-point configuration. It does not give a congruence-uniform global energy estimate. The next question is whether an analogous spatial recovery inequality has constants compatible with cusp gluing and increasing boundary configurations.

**Lean status:** `centeredNorm_eq_twoHeight` and `directionalSecondMoment_eq_heightDifference` are closed, and `squaredNorm_center` identifies the left side with the actual squared norm of centered coefficients. [Exact paper proof and verification](../3-formalized/selberg-boundary-moment-two-height-recovery.md). The first-gradient-only subroute is recorded with this positive survivor on its [failed proposal card](../5-failed/selberg-first-gradient-covariance.md).

### Next live attempt — replace a fixed pair of heights by all scales

The four-point recovery formula suggests testing a scale integral of the dyadic difference `P_(2y)f-P_y f`, where `P_y` is the actual half-plane Poisson operator. The candidate identity on the appropriate square-integrable boundary space is

`integral_(y>0) ||P_(2y)f-P_y f||_2^2 dy/y = log(9/8)*||f||_2^2`.

This is a **candidate for the next proof attempt**, not a theorem used above. Its modal factor is `(exp(-2*y*r)-exp(-y*r))^2`; the needed scale integral is a Frullani combination. The exact function space, convergence arguments, and bridge to the actual boundary operator must be established before claiming the identity.

Corpus ingredients now inspected/discovered:

- `HTGeometry.HalfPlanePoissonKernel`: source-defined Poisson convolution and conjugate Poisson semigroup laws.
- `HTGeometry.FrullaniIntegral`: actual complex integral and integrability theorems on the positive ray.
- `RHTower.XiWardMultiscaleHellingerCauchySeparator`: the explicit logarithmic dyadic kernel and its constant `log(9/8)` diagonal. The inspected module proves positive-entry and nonnegative-multiplicity energy estimates; those are not a signed boundary-data norm identity and are not imported as one.
- `RHTower.PoissonEulerSobolevNaturalCone`: literal boundary Fourier coefficients and exact Sobolev membership thresholds. This supplies a way to state and test the boundary-space requirement, not a premise that Maass boundary data belong to that space.

The subsequent Selberg step would need a justified relation between this boundary recovery and cusp energy. No such relation is assumed or asserted.

### Cycle 9 — does logarithmic-scale energy distinguish a small positive rate?

**Conjecture tested:** the modal dyadic square function, integrated over logarithmic scale, separates small positive spectral rates from rates above a fixed threshold.

For `r=exp(s)>0`, put `d_s(t)=exp(-r*t)-exp(-2*r*t)`. Expanding its square gives

`d_s(t)^2=exp(-2*r*t)-2*exp(-3*r*t)+exp(-4*r*t)`.

Divide by `t` and split into two convergent Frullani differences. Their integrals are `log(3*r)-log(2*r)` and `log(3*r)-log(4*r)`, so

`integral_(t>0) d_s(t)^2 dt/t=log(9/8)`

for every real `s`. **Failure:** this modal energy cannot by itself distinguish any positive rate, including arbitrarily small ones. This does not disprove the proposed boundary square-function identity; it shows that identity alone would not be a spectral-gap argument. No identification of this diagonal model with a congruence Maass spectrum is assumed.

### Cycle 10 — can a different scale moment recover the lost rate?

**Conjecture:** integrating the same squared response in ordinary scale retains the rate that logarithmic integration removes.

**Paper proof:** integrate the three exponentials separately. Their integrals are `1/(2*r)`, `1/(3*r)`, and `1/(4*r)`. Consequently

`integral_(t>0) d_s(t)^2 dt=1/(12*r)=exp(-s)/12`.

This moment determines `s` injectively, and multiplying it by `r` always gives `1/12`. The positive survivor is an exact distinction between a scale-invariant norm detector and a rate-sensitive moment. The next Selberg attempt must find a justified arithmetic or cusp-energy estimate on a rate-sensitive quantity, rather than infer a gap from the scale-invariant norm identity.

**Lean status for cycles 9–10:** complete in `SelbergPoissonScaleMoments`: actual integrability and set-integral values, connection to the existing diagonal Poisson multiplier, injectivity, exact positive range, and absence of a uniform ordinary-scale upper bound. Targeted build and eight capstone axiom checks passed. [Positive survivor](../3-formalized/selberg-poisson-scale-moments.md); [failed modal inference](../5-failed/selberg-log-scale-gap-detector.md).

### Cycle 11 — can horizontal frequency pay the cusp boundary cost?

This returns to cycle 1's actual boundary defect rather than impose an unsupported bound on an abstract semigroup. Corpus ingredients are the exact Morse/Darboux Robin defect, the native compact cusp profiles, and mathlib's bundled test functions and compact-support fundamental theorem of calculus.

For a real smooth compact profile `g` on the positive half-line, cutoff `Y>0`, and horizontal frequency `k`, test

`integral_Y^infinity (g'^2+k^2*g^2-g^2/(4*y^2))`

`= integral_Y^infinity (g'+(k-1/(2*y))*g)^2`

`  + integral_Y^infinity (k/y)*g^2 + (k-1/(2*Y))*g(Y)^2`.

The identity retains the complete lower seam term. Its paper derivation expands the square and integrates the derivative of `(k-1/(2*y))*g^2`; compact support removes the upper endpoint. It gives a quarter-energy bound for the isolated cusp tail when `k*Y>=1/2`. No estimate for the compact core or its gluing is assumed.

**Regularity refinement:** the proof uses only `C¹` regularity. Division by height extends as `C¹` through zero because the compact profile's support lies inside the positive ray. This refinement has been checked in the paper proof and formalized for mathlib's bundled `C¹` test functions.

**Lean status:** complete in `SelbergCuspHardyBoundary`. It proves the actual flux derivative, all integrability statements, the exact identity, the zero-frequency Hardy defect, and the quarter-energy inequality for `Y=exp(h)`, `k=(1/2+u^2)/exp(h)`. A closed range theorem shows that the frequency parameterization covers exactly `k>=1/(2*Y)`. The threshold is sufficient; necessity is not claimed. [Paper proof and verification](../3-formalized/selberg-cusp-hardy-boundary.md).

### Next live attempt — connect the tail inequality to actual Maass modes

The authoritative `MaassCuspAutomorphicCorrespondence` definition supplies actual smoothness, the hyperbolic eigen-equation, group invariance, and decay under every integral cusp scaling. Its cuspidality predicate is stated as decay, not as a zero-Fourier-coefficient field. The next concrete target is to derive the constant Fourier coefficient equation from those properties and prove the coefficient vanishes in the nonnegative sub-quarter spectral range. This must precede using a positive lowest horizontal frequency.

For a cusp of width `w`, the intended later assembly uses frequencies `2*pi*|n|/w` with `n != 0`, and cutoffs satisfying `k*Y>=1/2`. Fourier expansion/Parseval, passage beyond compact profiles, and the compact-core gluing estimate remain to be proved. No result for the existing unrelated abstract diagonal Poisson generator is silently identified with that Maass operator.

### Cycle 12 — actual zero Fourier coefficient from the Maass data

**Target:** for positive principal congruence level, form the actual horizontal period integral of a `MaassCuspEigenform`. Derive `-y^2*A''(y)=lambda*A(y)` and `A(y)->0` from its existing defining properties. Then test whether those two facts force `A=0` in the exceptional spectral range.

**Corpus ingredients:** `ThetaCuspHawkingBMCuspMeanDerivative` and `ThetaCuspHawkingBMCuspMeanLaplacian` differentiate an actual periodic cusp average and cancel the horizontal second derivative. Their supplied regularity is `C^infinity`; the Maass definition supplies only `C^2`, so the adaptation must prove exactly the required finite-regularity statements. Mathlib's `ModularGroup_T_pow_mem_Gamma` gives the actual principal-congruence translation, rather than assuming periodicity as a new field.

**Paper chain under test:** a compact positive-height rectangle bounds the first and second chart derivatives, justifying differentiation under the horizontal integral. The integral of the horizontal second derivative is the endpoint difference of the first derivative; periodicity makes it zero. The given hyperbolic eigen-equation then yields the Euler ODE. The actual cusp filter bounds the integrand uniformly in the horizontal coordinate, so the finite-width integral tends to zero.

For `lambda=alpha*beta`, `alpha+beta=1`, `0<beta<alpha`, logarithmic height gives `H''-H'+lambda*H=0`. Differentiating `(H'-beta*H)*exp(-alpha*t)` makes it constant. Swapping the two roots supplies the other coefficient. Multiplication by the inverse integrating factors and subtraction give the exact two-exponential representation. Multiplying by `exp(-alpha*t)` and taking the decay limit first kills the faster coefficient; multiplication by `exp(-beta*t)` then kills the other. Division by the nonzero root difference gives `H=0`.

**Paper outcome:** the conjectured vanishing is proved in the strictly positive sub-quarter interval. Choosing `nu=sqrt(1/4-lambda)` puts every `0<lambda<1/4` in the distinct-positive-root range. This proves zero constant term at the infinity cusp from the existing decay definition. It does not require a strengthened Maass record or an assumed ODE solution formula.

**Lean status:** `SelbergMaassFourierMean` proves actual congruence periodicity, both differentiations at C² regularity, the Euler equation, and decay. `SelbergExceptionalCuspMean` proves integrating-factor constancy, the forced exponential representation, decay rigidity, and `maassMean_subquarter_zero` for every actual positive-level principal-congruence Maass eigenform in the target exceptional interval. Both scratch and direct source checks passed without warnings. Targeted final audits are recorded below. No Selberg spectral bound is asserted.

**Remaining scope:** the current theorem concerns the infinity cusp. Covariance at other integral cusp scalings, nonzero-mode energy assembly, approximation beyond compact profiles, and a congruence-uniform compact-core gluing estimate remain to be proved.

### Cycle 13 — can integral cusp changes cover the missing core?

**Conjecture tested:** after removing the constant term, changing integral cusp coordinates can move every point into a height where the sufficient tail threshold applies.

**Source-derived test:** `ThetaCuspHawkingBMCompactModularPeriodization.modular_orbit_height_le` bounds the height of every actual modular translate by `max(y,1/y)`. On the imaginary axis this bound is attained: identity gives `y`, and inversion gives `1/y`. Therefore the exact maximal orbit height is `max(y,1/y)`; at `i` it is one. No integral change of cusp can move `i` above any cutoff greater than one. More strongly, points with height between `1/M` and `M` stay below `M` under every such change, for `M>=1`.

**Paper and Lean outcome:** the proposed covering shortcut fails for every cutoff greater than one. `SelbergCuspRelocation` proves the exact attained height maximum on the imaginary axis, a cutoff reachability equivalence, the reciprocal-band bound, and an explicit nonempty open set whose points remain strictly below the cutoff under every integral matrix. The positive survivor is an exact classification and a whole forbidden height band, rather than only a single uncovered point. This does not refute cusp-plus-core gluing or Selberg. It says a compact-core estimate cannot be replaced by integral cusp relocation alone.

The formal frequency-to-width bridge is still absent, so no numeric level threshold is being asserted as an already-proved Maass energy theorem. The next proof route must couple the cusp estimate to genuine core or arithmetic control.

[Exact positive survivor](../3-formalized/selberg-sharp-cusp-orbit-height.md); [failed covering shortcut](../5-failed/selberg-integral-cusp-relocation.md).

### Cycle 14 — replace the sufficient tail slope by the actual Bessel slope

**Conjecture under test:** the actual critical nonzero mode may supply a stronger boundary coefficient than cycle 11's elementary factorization, possibly removing its cutoff restriction.

**Inspected ingredients:** the corpus Schlaefli integral `realModifiedBesselKOrder`, its strict positivity and `K_1>K_0`, the arbitrary-order argument derivative in `ThetaCuspHawkingBMBesselArgumentDerivative`, and the exact order recurrence. These give a concrete function to differentiate, rather than a postulated boundary operator.

For `K_j(s)=realModifiedBesselKOrder s j`, test the dimensionless slope `q(s)=s*K_1(s)/K_0(s)`. The derivative and recurrence should give `q'(s)=(q(s)^2-s^2)/s`; the strict integral comparison then makes `q` strictly increasing. For the critical mode `g(y)=sqrt(y)*K_0(k*y)`, the proposed exact outgoing boundary slope is `(q(k*y)-1/2)/y`. The proof must establish these actual derivatives and their sign regimes before using a boundary-energy claim. No relationship to a general Maass nonzero Fourier mode is yet assumed.

**First outcome:** actual differentiation and the recurrence prove the Riccati law and strict monotonicity. The stronger all-positive-boundary-slope conjecture fails: there is a unique transition argument strictly between zero and one half, below which the actual outgoing coefficient is negative and above which it is positive.

**Positive survivor and new proof mechanism:** in logarithmic argument, `Q'=Q^2-exp(2t)` and `Q>0`. If `Q>=d>0` everywhere, then for `t<=log(d/2)`, `Q'>=d^2/2`. The function `Q(t)-(d^2/2)t` is nondecreasing on that left interval. Comparing two explicitly separated points forces `Q` to be negative, a contradiction. Thus there is no positive lower bound; strict monotonicity, the bound `q(s)>s`, and the intermediate value theorem give exactly one point at every positive target value. This avoids assuming a small-argument Bessel asymptotic.

**Lean status:** `SelbergBesselBoundarySlope` passes scratch/direct checks and its narrowed targeted final build (8659 dependency-graph jobs, one target rebuilt). It contains the actual derivative system, Riccati law, exact positive range, unique transition, critical mode differential equation, and full outgoing-sign classification. `SelbergBesselBoundaryEnergy` now passes its complete scratch and direct source checks. It proves actual integrability, the exact compact-profile boundary identity, the lower boundary estimate at every cutoff, the quarter inequality above the transition, and exact coverage of the sufficient cutoff range.

For a compact C¹ logarithmic-height profile `f`, put `r(t)=1/2-Q(a+t)` and `J(t)=exp(-t)*r(t)*f(t)^2`. The Riccati law gives

`exp(-t)*(f'^2+(exp(2*(a+t))-1/4)*f^2)`

`=exp(-t)*(f'-r*f)^2+J'`.

Compact support gives `integral_T^infinity J'=-J(T)`. Thus the exact seam term is `(Q(a+T)-1/2)/exp(T)*f(T)^2`, and the nonnegative square gives the lower bound. The unique coefficient transition `tau` yields a sufficient tail cutoff `T>=tau-a`, or `k*Y>=exp(tau)`, where `0<exp(tau)<1/2` is proved symbolically.

**Scope of sharpness:** the sign transition of the actual coefficient is exact. Necessity of the cutoff for nonnegativity of every compact test energy is not asserted: a negative seam coefficient alone does not construct a negative-energy test. Identifying arbitrary Maass nonzero Fourier coefficients, passing to their energy closure, and proving congruence-uniform core coupling remain open obligations in this route.

**Build correction:** an initial targeted slope build expanded through the existing Eisenstein imports and spawned parallel Lean workers. It was stopped, and its child processes were cleaned up. A premature energy scratch check failed because the slope olean did not yet exist. The source argument derivative and strict order comparison were extracted unchanged into `HTGeometry.BesselArgumentDerivative` and `HTGeometry.BesselOrderPositiveComparison`, preserving theorem names and existing wrapper imports. Both extracted modules passed scratch/direct checks and targeted builds; exact source-text comparison against their original proofs passed. Both compatibility modules passed direct compilation, including refreshed needed oleans. Missing dependencies in the retained compatibility import chain were compiled serially with `lake env lean`; no mathematical source in those dependencies was changed. Subsequent builds were serialized. The interrupted build is not a passing final audit.

### Next live attempt — isolate the finite set of adverse boundary modes

The exact coefficient transition suggests testing a finite-dimensional reduction of the still-missing core coupling. At fixed cusp width and cutoff, the nonzero integer frequencies grow with `|n|`, while the transition argument is a fixed positive constant. Therefore only finitely many modal seam coefficients should be negative, with an exact cutoff given by the proved Bessel transition. The next task is to derive this finite set and its boundary-form decomposition from actual integer mode frequencies, then test what the core Schur complement does to those channels. This is a new proof target, not an assumed positivity statement about that complement.

### Cycle 15 — count and retain the adverse integer channels

**Corpus-derived proposal:** `FiniteRankBoundarySchurIndex` retains the exact inertia and coupling cost of a finite boundary update; `CCMRestrictedWeilFiniteNegativeBlock` confines a different source's nonpositive directions to a finite block without inferring positivity. `ArithmeticStationaryFourierDilation` supplies a separate source example of an exact integer-frequency cutoff. Their mechanisms suggest extracting a literal finite seam block here before any core elimination.

For width `w=exp(b)` and cutoff `Y=exp(T)`, set `R=exp(tau)*w/(2*pi*Y)`. The actual critical seam coefficient for nonzero integer mode `n` should be negative exactly for `0<|n|<R`. Thus with `M=ceil(R)-1`, the adverse set should be `{-M,...,-1,1,...,M}`, of cardinality `2*M`. The complete finite-packet seam form should split exactly into a nonnegative part minus the weighted square form on this explicit finite set.

**Paper proof target:** use the already-proved Bessel sign classification, the logarithm/exponential equivalence, and the natural-ceiling characterization of strict integer inequalities. Split each real coefficient into its positive and negative parts, then sum over the finite packet. No positivity of a core response follows from this decomposition. Test also whether the adverse block size can be bounded independently of width at a fixed height; choosing widths to make `R` arbitrarily large should falsify that strengthening and expose the exact width/height scaling law.

**Outcome:** the exact signed interval, its cardinality, empty-block criterion, positive/negative form decomposition, and finite compact-packet energy identity are now proved in `SelbergBesselAdverseModes`. At fixed height, every even block size occurs at an explicitly chosen positive width. The stronger fixed-height uniform-count conjecture fails even along positive integer periods: choosing `N` beyond the explicit Archimedean threshold makes the cutoff for period `N+1` exceed any prescribed natural bound. The result concerns permitted frequency coefficients; it does not assert their excitation by an actual Maass eigenform.

[Exact positive survivor](../3-formalized/selberg-exact-adverse-cusp-modes.md); [failed uniform-count strengthening](../5-failed/selberg-uniform-adverse-mode-rank.md).

### Cycle 16 — next trace-constrained cusp-energy conjecture

**Target:** prove that the exact outgoing Bessel coefficient is the infimum of compact-profile quarter-energy excess under unit lower trace. This would strengthen the current lower estimate into an exact boundary response and determine necessity of the isolated-tail cutoff. Neither conclusion is used by the completed modules.

**Proposed proof mechanism:** let `G` be the actual positive critical profile, and multiply `G/G(T)` by a fixed smooth bump evaluated at `(t-T)/L`, with value one at zero. The square-completion remainder then contains only the derivative of that bump. The source derivative `K_0'=-K_1<0` bounds `exp(-t)*G(t)^2=K_0(exp(a+t))^2` on `t>=T` by its value at `T`. If the fixed bump and its derivative have compact support in `[-C,C]` and derivative bound `D`, the remainder is bounded by a constant times `L/L^2`, hence tends to zero. The bump also supplies compact support on the full log-height line while preserving unit trace.

Mathlib's inspected `exists_contDiff_tsupport_subset` supplies a smooth compact bump equal to one at its center; continuity and compact support of its derivative give a bound. `TestFunction` has the exact C¹/compact-support fields needed to bundle the product. The required rescaling derivative, support transport, integral bound, and limiting witness construction remain to be checked in Lean. This is a new proof attempt; the already-audited cycle 14 scope still does not claim optimality.

**Outcome and refinement:** the full scalar proof now passes scratch checking. Instead of a derivative supremum and interval-length estimate, the exact full-line change of variables gives `integral cutoffSlope^2=seedEnergy/exp(ell)`. Monotonicity of the actual `K_0` gives the normalized bound `exp(-t)*(G(t)/G(T))^2<=exp(-T)` on the tail. Thus the square remainder is at most `exp(-T)*seedEnergy/exp(ell)`, independently of frequency. The explicit scale `ell=log(1+exp(-T)*seedEnergy/exp(e))` makes it smaller than every positive tolerance `exp(e)`.

`SelbergBesselBoundaryTrace` constructs the actual compact C¹ unit-trace profiles, proves the exact infimum, and proves existence of compact negative-energy profiles if and only if `a+T<tau`. Consequently `a+T>=tau` is now necessary and sufficient for nonnegativity of every isolated compact tail profile. This strengthens cycle 14's earlier sufficient-only scope; the older module's theorem statements remain correct. No automorphic extension or core estimate is supplied by these isolated witnesses. Direct source/final audits follow below.

### Cycle 17 — test an asymptotic-free boundary growth envelope

The frequency-independent approximation error suggests a route to simultaneous boundary-channel approximation. To identify the resulting boundary form on an actual Fourier trace space, first test the missing upper growth bound on its source coefficient.

**Conjecture:** `exp(t)<Q(t)<exp(t)+1/2`. The lower inequality is already proved. For the upper inequality, put `V=Q-exp(t)>0` and `Z=V-1/2`. The actual Riccati equation gives `V'=2*exp(t)*V+V^2-exp(t)` and

`(exp(-2*exp(t))*Z)'=exp(-2*exp(t))*V^2>0`.

If `Z` is nonnegative at one point, this integrating factor propagates nonnegativity to every later point. Then `V'>=V^2`, so `(1/V)'<=-1`. Comparing `1/V+t` at two sufficiently separated later points forces `1/V<0`, contradicting positivity. This would give the exact source sandwich `k-1/(2*Y)<B(k,Y)<k`, with no large-argument asymptotic. The conjecture is not used until this differential contradiction is proved and checked.

**Second envelope candidate exposed by the same mechanism:** if the first upper bound is proved, then `D=1/2-V` lies in `(0,1/2)` and satisfies `D'=2*exp(t)*D-V^2`. Test `D<exp(-t)/8`. The derivative of `exp(-2*exp(t))*(D-exp(-t)/8)` is `exp(-2*exp(t))*(1/4-V^2+exp(-t)/8)>0`. A nonnegative value would propagate to the future, forcing `D'>=D*(1-D)>=D^2` and again contradicting reciprocal positivity. If checked, this yields `0<k-B(k,Y)<1/(8*k*Y^2)`, supplying an inverse-frequency bound on the exact boundary correction. This is a strengthened new target, not an assumed asymptotic formula.

**Outcome:** both upper-envelope conjectures are proved in `SelbergBesselBoundaryEnvelope`. Each comparison factor is proved strictly increasing, and each hypothetical crossing produces a nonincreasing reciprocal-plus-time function that becomes negative at an explicitly chosen later point. The final source coefficient has the strict bound `0<k-B(k,Y)<1/(8*k*Y^2)`. Scratch/direct checks and the targeted final build passed without warnings, rebuilding one target only. [Exact proof and audit](../3-formalized/selberg-bessel-inverse-frequency-correction.md).

Cycle 16 also passed its targeted final build. Its exact scalar trace result and frequency-independent compact approximation estimate are recorded in [the sharp trace-infimum card](../3-formalized/selberg-sharp-cusp-trace-infimum.md).

### Cycle 18 — next actual Fourier-boundary operator target

The two completed cycles now supply an exact scalar boundary response and an inverse-frequency correction. At period `w=exp(b)` and height `Y=exp(T)`, define the nonzero integer diagonal by `c_n=k_n-B(k_n,Y)`, with `k_n=2*pi*|n|/w`; omit the zero channel explicitly. The proved estimate is `0<c_n<w/(16*pi*Y^2*|n|)`.

**Next conjecture:** these literal coefficients define a positive compact diagonal operator on the square-summable nonzero Fourier boundary channels. `HTGeometry.BoundedDiagonalOperatorLp` has been read: it constructs the actual multiplication operator on complex `lp ... 2`, proves its norm bound, and proves compactness from cofinite coefficient decay using explicit finite diagonal truncations. The next work must instantiate that theorem with the Bessel coefficients, prove their cofinite decay and positivity on the actual sequence space, and identify the boundary quadratic form on its frequency-weighted domain. Its existing broad `import Mathlib` must be handled with targeted, serialized dependency compilation if any needed olean is absent.

The subsequent core operator still has to be constructed from congruence geometry and coupled to this exact response. Compactness of the correction by itself gives no global quarter bound. This obligation remains part of the original Selberg goal.

**Outcome:** the complete scratch proof passes. `SelbergBesselBoundaryOperator` defines the literal correction on complex `lp ... 2` over all integers, explicitly setting its zero coefficient to zero. The inverse-index estimate implies cofinite decay, hence compactness by the inspected diagonal construction. Real positive coefficients prove self-adjointness and positivity, and both its kernel and zero quadratic-response space are exactly the constant channel.

The correction quadratic series is summable for every square-summable vector, by the actual Hilbert inner-product series. Since `B_n=k_n-c_n`, summability of the outgoing energy series is equivalent to summability of the principal frequency energy series. On this exact domain, `B[u]=K[u]-Re <Cu,u>`, with strict inequality whenever a nonconstant coefficient is present. This is a source-defined sequence-space result; the actual Maass trace map and quotient-core coupling are not inferred. The module is wired; direct source and targeted final build passed without warnings, rebuilding one module. Twelve capstone axiom checks report only the standard three axioms. [Exact survivor](../3-formalized/selberg-compact-bessel-boundary-operator.md).

### Cycle 19 — connect every actual Maass Fourier coefficient to its modal equation

**Next source conjecture:** for the literal coefficient `a_n(y)=(1/w)*integral_0^w exp(-2*pi*i*n*x/w)*f(x+iy) dx` of a congruence Maass eigenform, the actual second height derivative satisfies

`-y^2*(a_n''(y)-(2*pi*n/w)^2*a_n(y))=lambda*a_n(y)`.

The corpus search found `DeningerFourierCoeffDeriv`: integration by parts with its literal periodic Fourier kernel proves the coefficient-of-derivative identity. The inspected `SelbergMaassFourierMean` already derives directional regularity, horizontal derivative periodicity, height differentiation under the integral, and the original Maass PDE in real coordinates. Reuse these mechanisms to prove both weighted height differentiation and the twice-integrated horizontal identity. This connects arbitrary actual coefficients to the modal source without assigning a Bessel ansatz or importing an assumed spectral conclusion.

The constant-index specialization must agree with the already-proved mean equation. The nonconstant equations will then supply an actual source for the subsequent energy/trace and quotient-core steps; they alone do not remove the global core obligation.

**Outcome:** the complete scratch proof passes in `SelbergMaassFourierModes`. Local compact domination justifies both height derivatives of the literal normalized coefficient. The inspected Fourier derivative theorem and the proved periodicity of the actual horizontal derivative give the squared-frequency multiplier. Integrating the source Maass PDE proves the modal equation at every index. The zero index agrees with the previously constructed mean after division by the positive period.

Two stronger source conclusions also pass: height decay is uniform in all integer indices, and at every positive height there is a nonnegative finite `M` such that `k_n^2*|a_n|<=M` for every index. The first uses the cusp filter and the normalized Fourier coefficient norm estimate; the second uses compact boundedness of the actual horizontal second derivative and the exact twice-integrated identity. Seven existing coordinate helpers were made public with unchanged proof bodies, so the new module reuses them. The module is wired; direct and targeted final audits passed. Twelve additional capstone axiom checks report only the standard three axioms, including the two preserved mean theorems; the existing exceptional-mean interface imports alongside the new module successfully. [Exact proof](../3-formalized/selberg-actual-maass-fourier-modes.md).

### Cycle 20 — next actual trace-domain conjecture

The new source frequency bound suggests proving that each actual Maass trace belongs to the already-constructed Bessel form domain. The whole-corpus search found `RHTower.deningerFourier_summable_inv_sq` in `DeningerFourierKothe`, which proves summability of `(1+|n|)^(-2)` on the integers using the shifted natural p-series and the positive/negative integer split. Mathlib's inspected `Memℓp` construction can then bundle the literal coefficient sequence.

**Proposed proof:** for nonzero integer `n`, `|n|>=1`, so `(1+|n|)^2<=4|n|^2`. Combine this with the new bound `k_n^2*|a_n|<=M`, and absorb the single zero coefficient into a finite constant, to obtain `|a_n|<=C/(1+|n|)^2`. Thus the actual coefficient norms are summable. Multiplying the squared-frequency bound by `|a_n|` shows summability of `k_n^2*|a_n|^2`; boundedness of the coefficients gives square summability. Finally `k_n<=1+k_n^2` yields summability of `k_n*|a_n|^2`. This should construct the actual trace in the exact form domain and specialize the compact-correction identity to it.

Identifying the resulting boundary series with a physical trace/energy theorem and controlling the quotient-core response are separate obligations. No inference of global positivity is made from summability.

**Outcome:** `SelbergMaassBoundaryTrace` proves the actual weighted coefficient bound, absolute coefficient summability, squared coefficient mass, squared-frequency energy, and first-frequency energy. It constructs the literal Maass sequence in complex `ell^2` at height `exp(T)`, bundles that same sequence into the exact Bessel form domain, and specializes the compact-correction identity to it. Scratch, direct source, targeted final build, axiom, index, lint, and whitespace audits passed. The module is wired. [Exact proof and audit](../3-formalized/selberg-actual-maass-boundary-trace.md).

### Cycle 21 — next physical Parseval identity

The actual trace-domain proof leaves a concrete analytic identification to establish. Corpus search found `DeningerFloquetMeasureEnergy`, whose proof applies Mathlib's literal-interval theorem `hasSum_sq_fourierCoeffOn`; `DeningerFourierBridge` identifies the interval kernel with the additive-circle Fourier character. Inspecting these proofs suggests a direct identity on each actual positive-height Maass slice, without postulating a sequence-space model.

**New target:** normalized horizontal integrals of `|f|^2`, `|partial_x f|^2`, and `|partial_y f|^2` equal respectively the sums of `|a_n|^2`, `k_n^2*|a_n|^2`, and `|a_n'|^2`. Source C² regularity supplies continuity and square integrability on every finite period. The already-proved weighted height derivative and one horizontal integration by parts should identify the derivative coefficients. Adding and subtracting these three absolutely convergent identities should yield the physical quarter-energy density as its literal modal series. This is a new proof target, not an assumed energy interface.

**Outcome:** `SelbergMaassParseval` proves the literal interval coefficient identification with the exact period normalization. The three physical Parseval identities are proved as `HasSum` statements, and adding/subtracting them proves the actual quarter-energy identity, including both derivative terms and the hyperbolic mass weight. The module is wired; scratch, direct source, targeted final build, axiom, index, lint, and whitespace audits passed. This closes the fixed-height physical mass and energy identification, not an interchange with an infinite height integral. [Exact proof](../3-formalized/selberg-maass-quarter-parseval.md).

### Cycle 22 — actual mass/flux and quantitative cusp decay: proved

The corpus-derived differential replacement for holomorphic frequency-gap decay survived proof. `SelbergMaassBoundaryFlux` derives literal source Hermitian pairing and horizontal Green identities, then `M'=2J`, `J'=G-lambda*M/y²`, the physical quarter-slice identity, `M->0`, and `G>=k²*M` for actual positive sub-quarter eigenforms.

`SelbergMaassCuspDecay` proves `M''>=k²*M` above `A=1/k`, then derives `M(y)<=M(A)*exp(-k*(y-A))` by secants and an integrating factor. Backward unit secants force `M'->0`, so actual terminal flux vanishes. The flux derivative is integrable above the cutoff.

`SelbergMaassTailEnergy` proves physical mass, hyperbolic mass, flux derivative, gradient energy, and quarter-energy integrable above **every** positive height. Its exact capstone is

`(1/w)*integral_Y^infinity quarterSlice = -J(Y)+(lambda-1/4)*integral_Y^infinity M/y²`.

No infinite-height Fourier interchange, terminal-flux assumption, or modal ansatz was used. Complete scratch/direct checks, three targeted final builds, and all 34 public theorem axiom audits passed. The latest global lint has three unrelated unwired HTGeometry errors, recorded below. [Exact result and dependency-closed paper proof](../3-formalized/selberg-maass-mass-flux-tail.md).

### Cycle 23 — actual noncompact Bessel squares and complete cusp boundary form: proved

The compact-real-profile interface mismatch was resolved directly in physical height. `SelbergMaassBesselRemainder` proves the actual Bessel response law `B'=B²-k²+1/(4*y²)` and limit `B->k`. Actual modal mass and derivative energy are integrable by physical Parseval domination. Expanding the complex square gives `|a'+B*a|²-energy=(B*|a|²)'`; actual coefficient decay kills the upper current. The improper FTC gives the exact single-mode infinite-tail identity. The exceptional constant coefficient and derivative are zero.

`SelbergMaassBoundaryForm` proves the countable mode/height interchange with majorant whose literal Parseval sum is `G+M/(4*y²)`, already integrable. The signed modal tail integrals therefore sum to the actual physical tail quarter-energy. Subtracting the summable actual seam series proves the complete nonnegative square series and

`quarterTail/w = boundaryForm(actualTrace) + sum_(n!=0) integral |a_n'+B_n*a_n|²`.

Substituting the prior flux identity proves the same right side equals `-J(Y)+(lambda-1/4)*integral M/y²`. The full actual cusp comparison is now proved. Complete scratch/direct checks, both targeted final builds, and all 28 public theorem axiom audits passed. The latest global lint passed with existing large-file warnings. [Exact statement and paper proof](../3-formalized/selberg-maass-bessel-boundary-form.md).

### Cycle 24 — actual integral transport and finite congruence trace

The C² pullback covariance conjecture succeeds. `SelbergMaassCuspTransport` constructs each literal integral translate as an actual Maass cusp eigenform at the same level and eigenvalue. Integral congruence normality supplies invariance, inverse translation supplies nonvanishing, and composition of scaling matrices supplies all cusp decay. The completed cusp Bessel identity and constant coefficient vanishing therefore hold at every integral cusp. The period used is the congruence level; no minimal cusp width is claimed.

Fresh whole-corpus searches for truncated Stokes identities found `ThetaCuspHawkingBMEisensteinActualFirstStokesIntegral.d4BM_actualFirstStokesPairedTruncatedBulk_eq_cuspTop`. Its source is an Eisenstein current; it cannot be substituted for a Maass source. Its explicit translation-side and paired-inversion-arc cancellations suggested summing the actual translated Maass squared norms over the finite congruence quotient.

That second conjecture also succeeds. `SelbergMaassCongruenceTrace` constructs the actual quotient family without a representative choice, then its nonnegative C² density `D(z)=sum_q |f_q(z)|²`. The density is positive somewhere, invariant under the full modular group, and tends to zero at infinity. Period one of its horizontal slices gives the exact unit-strip normalization `H(y)=integral_0^1 D=sum_q M_q(y)`. Its first two actual derivatives are `H'=2*sum_q J_q` and `H''=2*sum_q(G_q-lambda*M_q/y²)`. Tail integrability and finite summation of the actual cusp identity give `-sum_q J_q(Y)+(lambda-1/4)*integral_Y^infinity H/y² = sum_q BesselBoundary_q + sum_q FourierSquares_q`, with nonnegative convergent square contributions. No coset-to-distinct-cusp multiplicity formula is assumed.

The general second-chain-rule proof was extracted from the existing conformal-Laplacian module into narrow `HTGeometry.ComplexC2Laplacian`, with the old public theorem preserved as a checked wrapper. This shares the proof while avoiding the old wrapper's broad research dependency tree. [Exact statements, paper proof, and audit](../3-formalized/selberg-maass-integral-cusps-and-congruence-trace.md).

### Cycle 25 — actual standard-area core Green theorem and complete quarter form

Whole-corpus searches for `Laplacian square` found `ThetaCuspHawkingBMSquareSourceDifferential.fullSquarePotential_laplacian`. Its product-jet proof retains gradient forcing. The resulting actual Maass finite-trace conjecture is proved: `Delta D=2*(sum_q(|partial_x f_q|²+|partial_y f_q|²)-lambda*D/y²)`. The trace is not treated as an eigenfunction.

Differentiating the actual modular invariance of `D` gives its reciprocal-square Möbius Jacobian. Radial contraction reverses sign under inversion, hence cancels paired unit-circle arcs. Translation cancels side currents. Actual finite FTC gives the paired Stokes formula; reflection and period one turn its surviving top into the physical unit-period current. Differentiation of the actual trace mass identifies that current as `2*sum_q J_q`.

A fresh whole-corpus `Stokes` query found `ThetaCuspHawkingBMEisensteinActualFirstStokesFubini`. Its indicator-domain Fubini proof and exact lower-side geometry supplied the missing area identification. Adapted to the actual real Maass trace, standard two-dimensional integration over the truncated modular domain now satisfies `integral_core Delta D=2*sum_q J_q`. The previous paired-coordinate divergence integral is proved equal to this standard area integral. All regularity and integrability are derived from the original C² source; no specialized Eisenstein or broad research module is imported.

The complete actual quarter form is now proved. For `Y=exp(T)>=1`, core energy `Qcore=integral_core(G-D/(4*y²))`, core hyperbolic trace mass `Mcore`, actual unit-strip tail mass `Mtail`, full Bessel boundary sum `B`, and convergent Fourier square remainder `S>=0`,

`Qcore(Y)+B(T)+S(T)=(lambda-1/4)*(Mcore(Y)+Mtail(Y))`.

Thus `Qcore+B` has the corresponding **upper** bound. A nonnegative lower bound has not been proved. [Exact theorem, dependency-closed paper proof, and audit](../3-formalized/selberg-maass-core-stokes-and-quarter-form.md).

### Cycle 26 — strict physical mass and exact radial/angular residual

The strict mass conjecture succeeds. Corpus searches `integral positive continuous` and `fundamental domain`, followed by the actual definiteness proof in `PeterssonInnerProductLevelOne`, supplied continuity, modular reduction, and `fd=closure(fdo)`. Original nonvanishing therefore gives a positive interior trace value and a positive compact-core mass. Horizontal Fubini and the integrable cusp tail prove exact cutoff independence: `Mcore(Y)+Mtail(Y)=Mcore(1)+Mtail(1)>0` for every `Y>=1`. The actual exceptional source consequently forces `Qcore(exp T)+B(T)<0` for every `T>=0`. No nonnegative lower bound is assumed.

Queries `Gram determinant`, `Fisher phase`, and `Lagrange identity`, with source reads of `ProjectiveQuantumFisherValue`, `ConstitutivePolarAmplitudeFisherPhase`, and `SymmetricPickSchur`, suggested testing scalar-amplitude reconstruction and retaining its exact residual. The broad reconstruction shortcut fails: explicit smooth period-one fields `exp(i*c*Re z)` have identical squared norm one but different actual derivative energies for `c=0` and `c=2*pi`. These are not asserted to be Maass or cusp forms. In particular, the test does not contradict recovery from trace derivatives **together with the Maass equation and eigenvalue**.

The actual-source positive survivor is proved. With `C_v=D_v D`, `E_v=sum_q|D_v f_q|²`, and `R_v(c)=sum_q|D_v f_q-c*f_q|²`,

`R_v(c)=E_v-c*C_v+c²D`.

At `D>0`, its unique minimizing real slope is `c_v=C_v/(2D)`, with excess `D*(c-c_v)²`. Every residual vanishes exactly when all component derivatives are radial with that same real slope. Let `A=R_x(c_x)+R_y(c_y)>=0`. The actual scalar amplitude satisfies `G=|grad sqrt(D)|²+A` wherever `D>0`. The multiplied identity `D*G=(C_x²+C_y²)/4+D*A` holds everywhere, including trace zeros, without a smoothness assertion for the norm there. The actual source equation then yields

`D*Delta D=(C_x²+C_y²)/2+2D*A-2lambda*D²/y²`.

[Exact statements, paper proof, and audit](../3-formalized/selberg-positive-mass-and-radial-defect.md). [Failed shortcut and fully formalized positive survivor](../5-failed/selberg-scalar-norm-energy-reconstruction.md).

### Cycle 27 — actual directions, weighted distance, and nodal reversal

The zero-mean angular-energy conjecture fails. For a real differentiable profile, radial subtraction removes the full derivative away from its zeros. Exact cosine is smooth and periodic, has zero mean and positive squared mass, but its residual is integrable and zero almost everywhere. At a node the residual is one. Nodal reversal therefore defeats this angular-only inference. The toy is not claimed to be Maass, cuspidal, or inversion invariant.

The actual-source survivor succeeds. Normalize the literal finite congruence family by `rho=sqrt(D)`. Reconstruction and modular permutation covariance hold even at common zeros. On `D>0`, the actual derivative obeys `rho*partial_v u_q=partial_v F_q-c_v F_q`, so the retained residual is exactly `D*sum_q |partial_v u_q|²`. The original exceptional constant-term theorem gives `integral rho*u_q=0` on every shifted level period. In contrast, the amplitude mean is strictly positive around each positive source value.

The continuous source correlation has zero period integral and a positive diagonal. It therefore takes a strictly negative value within the centered level period. Both endpoint densities are positive, and the normalized squared distance is strictly greater than two. Original nonvanishing supplies such an actual same-height pair. More strongly,

`rho(w)*d(z,w)²=2*rho(w)-2*C(z,w)/rho(z)`

holds even at common zeros of the moving source. This weighted squared-distance slice is continuous and its mean over every level period is exactly twice the amplitude mean. It retains nodal direction reversal without asserting differentiability there. [Dependency-closed proof and full audit](../3-formalized/selberg-source-directions-and-nodal-reversal.md). [Failed shortcut and positive survivor](../5-failed/selberg-zero-mean-angular-energy.md).

The user renewed the requirement for wider searches and explicitly noted the default AND behavior. Subsequent discovery used `--any` for `nodal chord oscillation variance`, `coarea Cheeger conductance resistance`, `permutation transport holonomy expansion`, and grouped OR phrases for effective resistance, Dirichlet principles, spectral gaps, boundary transport, and zero mean. These spanned hundreds to thousands of modules. Exact result counts and the sources read are on the linked card; this does not claim every matching declaration was read.

### Cycle 28 — actual regularized curvature and surviving nodal charge

Broad OR searches (`--any`) for resistance/capacity, boundary transport, arithmetic amplification, and regularization reached `SchwartzPositiveCompactDiagonal.pointwiseMulConj_nonnegativeSquareRootRegularization_self`. Its retained cutoff error suggested adding a positive constant square to the actual trace. The resulting source conjecture is proved: `rho_e=sqrt(D+e²)` is C² and modular invariant through common zeros, its remainder is a sum of squares including the constant-coordinate correction, and

`rho_e*Delta rho_e = R_e-lambda*D/y²`.

The actual quarter density retains `R_e` and the explicit `e²/(4y²)` correction. Standard two-dimensional modular-area integration, with every side and circular current condition proved from the original source, gives

`integral_{Omega_Y} R_e/rho_e = top_e(Y)+lambda*integral_{Omega_Y} D/(y²*rho_e)`.

All integrability is proved; the right side is nonnegative. The original area module now shares the general C² Green slice proof, preserving its public statements.

The proposed pointwise-limit removal of the defect fails in the exact local nodal profile `h(x)=x`. The literal curvature `e²/(x²+e²)^(3/2)` tends to zero almost everywhere, but its integral on `[-1,1]` tends to two. The stronger positive survivor classifies every oriented interval: the limiting curvature is `b/|b|-a/|a|`, including endpoints at the node. This toy is not claimed to be Maass, cuspidal, periodic, or inversion invariant.

Further broad OR searches for nodal/curvature/defect measure/concentration/ground state returned 6310 declarations in 1042 modules. Sources read included the explicit square-root cutoff correction, approximate-identity concentration, and full logarithmic curvature decomposition. No Maass log-concavity or domination estimate was imported from those mechanisms. [Full paper proof and audit](../3-formalized/selberg-regularized-curvature-and-nodal-charge.md). [Failed shortcut and fully formalized positive survivor](../5-failed/selberg-dropping-nodal-curvature-by-pointwise-limit.md).

### Cycle 29 — augmented source capacity and surviving variation

The actual augmented source `(F_q,e)/rho_e` is now proved C² through original common zeros, with unit squared norm and literal modular permutation covariance. Its derivative energy is exactly the retained regularized remainder. Original coordinates retain amplitude-weighted mean zero; the added coordinate has the nonzero mean `e*(N+1)`. The exact weighted squared-chord mean includes the correction `-2e²*(N+1)/rho_e(z)`.

Original source nonvanishing and zero means supply fixed same-height points whose augmented squared chord exceeds two for every sufficiently small positive regulator. Integral square completion and actual FTC prove the source path comparison

`chord² <= (integral 1/rho_e)*(integral R_{e,1}/rho_e)`.

Every continuity and integrability condition comes from the original source. On a fixed ordered nondegenerate path, the same small regulators satisfy both `pathEnergy > 2/pathResistance` and `sum_j (integral |partial_x U_j|)² > 2`. The latter is the literal squared coordinate-variation sum and does not introduce resistance.

The proposed unqualified regulator-uniform resistance bound fails in the exact local nodal profile. Its resistance is `2arsinh(1/e)=2log(1+sqrt(1+e²))-2log(e)`, diverges, and has finite part `2log 2`; its capacity coefficient tends to zero. The strongest positive survivor includes that full singularity classification and the actual source's fixed variation cost. The toy is not claimed to be Maass, periodic, cuspidal, or modular invariant.

Broad OR corpus searches spanned 3041 modules for weighted/chord/resistance mechanisms, then 88 modules for weighted Cauchy and path energy, 27 for reciprocal-radius primitives, and 85 for variation/coarea/isoperimetry. Read source mechanisms included exact finite resistance completion, complex weighted Cauchy, the rescaled arsinh primitive, and finite projected coarea with explicit isotropy. No unproved isotropy or uniform resistance was transferred to Maass data. [Dependency-closed proof and audit](../3-formalized/selberg-augmented-chord-capacity-and-nodal-resistance.md). [Failed shortcut and formalized positive survivor](../5-failed/selberg-regulator-uniform-resistance.md).

### Cycle 30 — actual regularized cusp flux and full curvature budget

The actual real unit horizontal average is now differentiated twice using original C² source regularity. Source period one cancels the horizontal second derivative, so its second derivative is the mean planar Laplacian. Actual density decay gives radius and mean convergence to the positive regulator.

The stronger source forcing bound is proved with absolute eigenvalue, without a sign restriction:

Delta rho_e >= -abs(lambda)*rho_e/y².

The general new secant lemma proves actual derivative decay when the function has a finite limit and its second derivative is bounded below by -C/y². Correcting the derivative by C/y makes it monotone; forward and backward unit secants squeeze the derivative to zero. Applied to the actual source, this proves the literal centered Stokes top current tends to zero.

The actual full planar modular domain is constructed and its truncated domains are proved to exhaust its area. Original finite total mass bounds every core mass. Since rho_e>=e, the weighted mass D/(y²*rho_e) is genuinely integrable at fixed e. Source Stokes, the proved top-current limit, and nonnegative retained curvature then give full-domain remainder integrability and

integral_Omega R_e/rho_e = lambda*integral_Omega D/(y²*rho_e).

The full Laplacian is integrable and has zero integral. Original nonvanishing makes weighted mass and retained curvature strictly positive for every hypothetical exceptional source. This does not assert existence of exceptional sources.

Broad discovery used --any for secant/forcing mechanisms, then uniform tails, integrable majorants, and exhaustion. The broadest exhaustion query reached 2856 declarations in 1381 modules. Follow-up geometric/arithmetic discovery reached 3061 declarations in 541 modules. Counts describe index coverage, not reading every result. [Complete paper proof, source mechanisms, and audit](../3-formalized/selberg-regularized-cusp-and-full-curvature-budget.md).

### Cycle 31 — quantitative regulator removal and total curvature monotonicity

Actual full-domain amplitude mass is now proved integrable and strictly positive. The full modular domain lies in the unit strip above height one half. The literal primitive -1/y proves inverse-square ray integrability and its exact integral; genuine product integration gives strip hyperbolic area two, bounding full-domain hyperbolic area. Pointwise sqrt(D)<=(D+1)/2 then gives an integrable amplitude-mass majorant from original mass and this area.

The square-root conjecture is proved more strongly than the initial error-e proposal. For d>=0 and e>0, put a=sqrt(d), r=sqrt(d+e²). The exact identity

(a-d/r)*r*(r+a)=a*e²

and 2ae<=r*(r+a) give 0<=a-d/r<=e/2, including original zeros. Applying this to the actual source gives full-domain spectral-density L¹ error at most e. Consequently,

0 <= lambda*integral_Omega sqrt(D)/y² - integral_Omega R_e/rho_e <= lambda*e.

The positive-regulator limit filter is proved nontrivial. Actual total retained curvature converges to lambda times the strictly positive full amplitude mass. It is also antitone in e: decreasing the regulator increases the total curvature budget. This is total-integral monotonicity, not a claim of pointwise curvature monotonicity.

Broad --any discovery used the full corpus index: the first regularization/finite-volume/defect search reached 43095 declarations in 12403 modules; the next square-root/error/area search reached 2353 declarations in 1090 modules. Read mechanisms included exact square-root difference-of-squares remainder control and explicit retained regularization corrections. No numerical experiment or pointwise curvature-limit interchange was used. [Complete paper proof and audit](../3-formalized/selberg-quantitative-regulator-curvature-limit.md).

### Cycle 32 — local weak curvature with the nodal contribution retained

For every real eigenvalue and real C² compact test phi supported in the upper half-plane, the actual limiting curvature is now identified as

J(phi)=integral sqrt(D)*Delta phi + lambda*integral phi*sqrt(D)/y².

The original source requires C² regularity only in the upper half-plane. Compact support localizes every test/source product to that open set, making it globally continuous and integrable. First and second test derivatives retain the original support. Two literal directional integrations by parts therefore prove the actual tested source identity without assuming global smoothness of an ofComplex extension.

The scalar regulator bounds give the quantitative estimate

|J_e(phi)-J(phi)| <= e*(integral |Delta phi| + |lambda|/2*integral |phi|/y²).

The absolute eigenvalue strengthens the initial exceptional-only proposal to every real lambda. The actual nontrivial positive-regulator filter then gives convergence. Original nonnegative regularized curvature proves J(phi)>=0 on nonnegative tests. Actual integral linearity and test ordering pass to the limit, with all integral convergence established internally. No pointwise curvature-limit interchange is used.

The wider positive-functional and cutoff searches exposed a further strengthening. If |phi|<=c*psi, then |J(phi)|<=c*J(psi). Every compact K inside the upper half-plane has an actual nonnegative compact C² cutoff chi equal to one on K: square the smooth cutoff constructed by CompactSmoothCutoff. Its source curvature C_K=J(chi) is finite and nonnegative. Hence every C² phi supported in K with |phi|<=c, c>=0, satisfies |J(phi)|<=c*C_K. Compact support of phi follows from K rather than being assumed separately. This is a source-derived local order-zero bound; it uses no representing measure.

All broad discovery used --any. Local Green/nodal mechanisms reached 530 declarations in 95 modules; support/localization/product/continuity reached 26054 declarations in 7965 modules; positive functionals and local measures reached 182 declarations in 44 modules; order-zero/cutoff/domination reached 1088 declarations in 533 modules; compact smooth cutoffs reached 380 declarations in 217 modules. These are index-coverage counts, not claims to have read every result. Read proof mechanisms are recorded in the [dependency-closed proof and audit](../3-formalized/selberg-actual-weak-curvature.md).

### Cycle 33 — actual positive curvature measure from original regulator integrals

The actual continuous-test limit and its representing measure are now constructed for every real eigenvalue. A fixed compact cutoff localizes global smooth approximants to one common compact inside the upper half-plane. Its bounded norm rescales the approximation tolerance. A second nonnegative compact C² cutoff has bounded actual curvature values for small regulators, by the already proved smooth-test limit. Positivity bounds the difference between original and approximate test pairings. A complete four-term metric Cauchy argument then proves convergence of the original continuous-test integrals along the actual nontrivial regulator filter.

The resulting continuousCurvature is positive, real linear, monotone, and equals the original weakCurvature on admissible C² tests. Zero extension of every compact continuous upper-half-plane test is proved globally continuous and compactly supported at positive height. Restriction of a supported planar test is compact, and restriction followed by zero extension recovers it exactly. These constructions produce an actual positive linear functional on C_c(H,R), to which the current Riesz--Markov theorem applies.

The constructed curvatureMeasure is regular and finite on compact sets. Every compact continuous test is genuinely integrable, and its integral equals the actual regulator limit. The measure is unique among regular measures with those continuous-test source values. In particular, for every admissible C² planar test,

integral_H phi dmu = integral_C Delta(phi)*sqrt(D) + lambda*integral_C phi*sqrt(D)/y²,
|J_e(phi)-integral_H phi dmu| <= e*(integral |Delta phi|+|lambda|/2*integral |phi|/y²).

All broad searches used --any. Distribution/measure/approximation discovery reached 432 declarations in 241 modules; positive extension/common-support mechanisms reached 2199 declarations in 250 modules; Cauchy/uniform-approximation mechanisms reached 230 declarations in 120 modules; zero-extension/open-embedding/positive-functional mechanisms reached 282 declarations in 112 modules. Counts describe index coverage, not reading every result. [Complete paper proof, source mechanisms, and audit](../3-formalized/selberg-actual-curvature-measure.md).

### Cycle 34 — actual modular transport, proved

Next conjecture: original modular amplitude invariance induces invariance of the constructed measure, through literal change of variables on compact source tests. The checked radius_invariant source theorem is available. A broad modular-invariance/curvature-measure/boundary-charge/seam-crossing/coarea/transport query reached 8003 declarations in 2109 modules; promising mechanisms must be inspected and transferred with their source conditions proved.

Concrete proof attempt: complexify the actual real C² radius and reuse SelbergMaassCuspTransport.positive_laplacian_pullback to prove invariance of y² Delta(radius). Together with radius and trace-density invariance, curvatureWeight_eq then proves invariance of the actual hyperbolic density y² curvatureWeight. Transfer the corpus's planar/hyperbolic integral identity to real compact tests, use invariant hyperbolic volume, and pass through the already proved original regulator limits. Regular-measure uniqueness should identify the pushforward. No C-infinity regularity or null boundary charge is assumed. The explicit --any covariance/Jacobian search reached 1187 declarations in 299 modules; the hyperbolic-integral/invariant-density/complexification search reached 151 declarations in 96 modules. These are coverage counts, not claims to read every hit.

Vague convergence on compact continuous tests does not by itself permit replacement by a fundamental-domain indicator. Actual boundary concentration and stabilizer multiplicities must be retained in the quotient budget. Existing nodal curvature and endpoint classification provide evidence against silently deleting concentration, but do not classify the actual source's seam charge.

The complete proof now checks in two new modules: real-to-complex C² differentiation transfers the existing Möbius Laplacian theorem to the actual radius; the exact source decomposition proves invariance of the hyperbolic curvature density. Literal chart change of variables makes every original regularized compact-test pairing invariant. Its proved regulator limit and regular-measure uniqueness give invariance of the actual constructed measure. All measurable preimages retain their full curvature, including possible seam charge. [Dependency-closed paper proof and audit](../3-formalized/selberg-actual-curvature-transport.md).

### Cycle 35 — actual curvature has no point atoms

The next explicit --any searches reached 144 declarations in 51 modules for quotient/boundary/nodal mechanisms, 4445 in 410 for partitions/proper actions/stabilizers, and 406 in 120 for atomlessness/potential/capacity/flux mechanisms. The inspected modular fundamental-domain proof uses zero hyperbolic area of its boundary; it does not prove zero curvature measure there. This direct transfer is unjustified, not a proof of a false source theorem.

The initial proposals were continuous weighted partitions for quotient integration and a local curvature-growth estimate from the actual trace's radial square completion and Bottcher.Brolin.RieszFlux.integral_ball_laplacian_eq_boundary_flux. DeningerTransversePartition provides an exact partition-sum mechanism, but its clopen product setting does not itself build a modular partition. A regulator-uniform gradient estimate plus actual C² flux could prove stronger small-ball growth; that stronger estimate remains unproved. The cancellation pivot below establishes point-atom exclusion using continuity alone. Charge on seam curves remains possible.

Cycle 35 pivot proved: ScaledCutoff supplies a localization/scaling mechanism and Bottcher.Brolin.RieszLogIBP proves zero total Laplacian of compact C² tests from the flux identity. The actual proof uses the lighter existing local Green identity with constant source. For chi_r(z)=chi((z-z0)/r), subtract amplitude(z0) from the Laplacian pairing and exploit dimension-two cancellation between r^(-2) derivative scaling and r² area scaling. The Laplacian L¹ norm stays fixed while actual amplitude oscillation vanishes; the continuous spectral-weight term has vanishing r² mass. Positivity and chi_r(z0)=1 bound mu({z0}) by the vanishing actual test pairing. All scaling, support, integrability, and measure-limit passages now check in Lean. The constructed measure has NullSingletonClass and vanishes on every countable set, for every real eigenvalue and without pointwise source nonvanishing. [Complete paper proof and audit](../3-formalized/selberg-actual-curvature-no-atoms.md). Local-growth/flux/cutoff --any search reached 150 declarations in 72 modules; cancellation/continuous-potential search reached 6 in 6. Neither count means every result was read.

### Cycle 36 — actual positive compact-orbit descent, proved

Atomlessness removes point charges, not curvature carried by seam curves. The elliptic/proper-action/overlap search reached 32 declarations in 20 modules; the compact-orbit/weighted-descent search reached 185 in 66, both with --any. Inspected ThetaCuspHawkingBMCompactTestUnfolding gives finite translate support on the entire cell, including seams and fixed points; its integral unfolding still invokes hyperbolic-volume boundary nullity and cannot be applied unchanged to curvature. ThetaCuspHawkingBMCompactModularPeriodization.modular_orbit_height_le bounds the height of every orbit by max(y,1/y). Use these source mechanisms to test a positive modular cutoff divided by its orbit sum, with local finiteness, positivity, support, and stabilizer multiplicity proved. WeightedOrbitInvariantExistence's group-carrier mechanism has an injective orbit parametrization, which is not automatic for this action. No quotient budget or normalized partition is assumed.

Cycle 36 conjecture proved: actual curvature integrals of compact continuous tests depend only on their full modular periodization and are nonnegative whenever that periodization is nonnegative. The construction works directly with the SL(2,Z) sum so kernel and stabilizer multiplicities remain literal. Proper discontinuity makes compact-test orbit sums locally finite and mutually overlapping test products a globally finite family. The orbital pairing identity integral g*P(h) dmu = integral h*P(g) dmu follows by justified finite interchange and actual measure invariance. For each compact K, a nonnegative compact b equal to one on K gives w=b/max(1,P(b)). Then P(w)=P(b)/max(1,P(b)), globally between zero and one and exactly one on K. The pairing identity proves representative independence, positivity, and order comparison without a seam-null assumption. This constructs the unique positive real linear functional on the literal range of compact periodization, with convergence of every original regulator pairing. [Complete dependency-closed proof and audit](../3-formalized/selberg-actual-positive-quotient-curvature.md).

### Cycle 37 — standard-cell normalization and total quotient budget

The complete scratch proofs now establish the exact factor-two normalization of the full SL(2,Z) sum by the actual projective fibers {A,-A}. The modular height bound and proper discontinuity make every compact test's contributing translates finite over the entire closed cell, so real unfolding and its invariant-density version have all sum/integral interchange discharged. The original planar full domain is identified pointwise with the hyperbolic cell. Indicator transport and exact chart density cancellation then give both the original compact-pairing identity and the full-cell curvature budget.

The EinastoGammaMoments mechanism transfers concretely: the already proved positive original total-curvature integral, transported exactly to the hyperbolic cell, discharges cell integrability by Integrable.of_integral_ne_zero. The original amplitude mass M bounds that cell integral by lambda*M uniformly in the regulator. For every literal compact orbit field F with |F|<=1, the original regulator limit therefore gives 2|Q(F)|<=lambda*M. Every actual normalized compact weight obeys this same finite budget. Exhaustion is not needed for this upper bound; equality of limiting total mass remains separate. No seam-curve mass is dropped. [Paper proof and final audit](../3-formalized/selberg-full-cell-curvature-unfolding.md).

The --any pairing/normalization search reached 28 declarations in 20 modules; positive-descent/kernel search reached 15 in 12; total-mass/exhaustion/tightness search reached 155 in 25. Inspected GoldstoneFabriPicassoCorpusApplications has a distinct escaping-mass family despite local convergence; it does not supply a counterexample for the actual Maass source. ScheffeCounting's tail argument assumes equality of total mass and cannot be used circularly to infer the missing identity. LeafTightness derives tails from an established uniform moment, suggesting a source cusp-control analogue. Exact source core/cusp curvature balances and amplitude mass remain available from cycles 30–31.

The essential unsolved step remains the source-derived quarter lower comparison. The new signed finite functional budget supplies upper control only. Continue wide corpus-derived conjecture/proof/fail/pivot work on actual spatial geometry, retaining original compact-core and cusp/Bessel boundary contributions. Selberg remains unproved; the goal stays active.

### Cycle 38 — uniform original cusp control and exact total orbit mass, proved and audited

The initial conjecture sought uniform top-current decay for 0<e<=1 using the bound rho_e<=2. The actual-source proof strengthens it to every positive regulator: 0<=rho_e-e<=sqrt(D) and D/rho_e<=sqrt(D), while nonnegative retained curvature gives Delta rho_e>=-|lambda|sqrt(D)/y². Original amplitude decay supplies a uniform narrow strip for the horizontal mean and the common forcing constant |lambda| beyond one source height. Quantitative forward/backward secants of the corrected derivative then prove uniform mean-current decay, which the original source identity transfers to the literal centered Stokes current. All analytic premises in the secant auxiliaries are discharged by the actual Maass source.

Subtracting the integrable original full and truncated curvature balances gives the exact curvature-tail identity, including the top current. The fixed integrable amplitude dominates every regularized amplitude tail. Its original exhaustion limit and the new uniform current bound prove curvature tails vanish uniformly over every positive regulator. Compactness of the literal modular cell truncations then gives actual normalized compact weights with periodization one on each core and between zero and one globally. Such a weight loses at most the uniform original curvature tail. Passing through the actual regulator limits proves these compact orbit tests approach lambda*M/2 arbitrarily closely. Combined with cycle 37's upper bound, the supremum over the literal compact positive orbit fields is exactly lambda*M/2. A strictly positive compact test also proves the actual constructed curvature measure is nonzero. This does not assert finite total measure on the universal cover.

All four complete scratch proofs, needed source oleans, and serialized final single-module builds passed, without new module warnings. The four modules are wired, all 33 public declarations have only standard Lean axiom dependencies, refreshed index coverage is complete, and repository lint passed. The source results quantify over the original MaassCuspEigenform structure; they neither construct an exceptional eigenform nor prove its impossibility. The spectral quarter comparison remains open. [Dependency-closed proof and audit](../3-formalized/selberg-uniform-regulator-cusp-curvature.md).

The explicit --any bounded-functional/uniform-mass/compact-exhaustion/mass-escape/curvature-tail/moment-tail search reached 150 declarations in 42 modules. Inspected MomentWeakConvergence transfers a uniform mass bound to a test approximation bound on an already compact source space; it does not supply a cusp tail. Inspected SecondMomentTailBound obtains tails from an established second moment; such a moment of the Maass curvature was not supplied. The proof above instead derives tails from the original source's secant and amplitude mechanisms. Further --any uniform-secant/curvature/tail discovery reached 737 declarations in 176 modules, and total-mass/compact-cutoff/supremum discovery reached 540 in 364. Inspected WindowTotalSqueeze suggested a window-plus-tail argument; its needed source bounds are proved here. RadialLeakageArcsineMeasure relies on a known explicit density and was not treated as a Maass density identification. Counts describe index coverage, not full source inspection.

### User-directed Einasto discovery — cycle 37 input

The literal corpus query `research Einasto` returned 63 declarations across four modules; both result pages and all four source modules were inspected. EinastoGammaMoments contributes 16 declarations: exact Gamma evaluation of every natural moment, integrability, finite total mass, and the exact identity mass(r)=r^3*core(r), with a continuous unit-interval core. EinastoRadialGravity contributes 21: actual derivatives, exact density/slope curvature decompositions, and central limits. EinastoEnergyConditions contributes 18: logarithmic-coordinate slope/density comparison yields sharp necessary-and-sufficient radius thresholds. DilatonEinastoMoments contributes 8: the constructed quartic Schwartz ground-state squared norm equals einastoDensity 0 (-k/4) (-log 4) pointwise; this identity transfers every radial/absolute moment and its integrability.

The inspected dependency DilatonGroundStates classifies the full zero-energy Schwartz kernel by first-order factorization and a constant undressed amplitude. Candidate mechanisms for the active Selberg loop are exact rescaled integral factorization before a singular/noncompact limit, source-derived moment control before a tail passage, and first-order energy decomposition with every boundary term retained. These are proposed transfers, not proved identifications of the Einasto or dilaton fields with the Maass source. The shape index 1/4 in the Einasto identity supplies no spectral quarter inequality by itself. Earlier Selberg ground-state/cusp factorization work must be checked before repeating that mechanism.

The explicit --any follow-up on ground-state, supercharge, half-density, moment-control, and mass-factorization mechanisms reaches 2070 declarations in 437 modules. This is index coverage; only displayed result metadata and the named source mechanisms above were inspected. Artifacts: /tmp/selberg_einasto_corpus37.json, /tmp/selberg_einasto_corpus37_tail.json, /tmp/selberg_einasto_mechanisms37.json. The wider unfolding/periodization/fundamental-domain/orbit/measure query reaches 56520 declarations in 12321 modules; its displayed results exposed ThetaCuspHawkingBMCompactTestUnfolding's finite translates across the entire closed modular cell. That source proof was inspected for the next actual regulator unfolding step; no cell-integral identity for the new SL(2,Z) functional has yet been claimed.

### User-directed evaporation, then entropy discovery — cycle 38 input

Searches ran in the requested order: `research evaporation` returned 78 declarations in 8 modules; `research entropy` returned 1069 declarations in 218 modules. Evaporation results were expanded without the per-module cap; entropy discovery retained module diversity and exploration hits. These are index coverage counts. Selected proof bodies, not every entropy module, were inspected. Search artifacts: /tmp/selberg_evaporation38_all.json and /tmp/selberg_entropy38.json.

Inspected HawkingMassLossClock constructs the actual cube-root time curve and its derivative/entropy laws. Inspected ThetaCuspHawkingEvaporationSingularityOrderSelectionEndpoint gives exact geometric shell-load summability and finite-cutoff failure. Its proposed physical selector is explicitly falsified: inspected ThetaCuspHawkingMassDilationOrderBlindnessNoGo.thetaCuspHawkingMassDilationDyadicShellLoad_eq shows the actual mass-dilated mirror has a shell load proportional to M_n, summable for every order, rather than the proposed order-dependent singular exponent. Inspected CompleteEvaporationAggregateNoGo proves positive shell integration of a shell-independent phase/energy only multiplies it by total lifetime. Candidate transfer: derive an actual Maass shell law first; finite duration or relabeling a defect cannot establish its decay.

Inspected PartitionDivergenceBounds proves two-cell data processing and the lower bound D(sigma||pi)>=(1-a)log(1/pi(A))-log(2) from target mass at least 1-a. Inspected ThermodynamicAffinityFisherBound proves 2(p-q)^2/(p+q)<=(p-q)log(p/q) for positive populations, with exact zero classification. Inspected DeficitEntropyRate proves the subadditive split of rho*log(C/rho) and exponential-affine decay. These suggest testing source-derived finite-partition entropy for cusp mass and source-derived entropy/current control for congruence directions. No uniform Maass relative-entropy bound or sharp global constant has been established. The existing SelbergMaassTraceRadial source already has the full Fisher decomposition, so merely rephrasing that identity as entropy is not new progress. Nodal contributions remain part of the required source comparison.

An explicit --any follow-up across entropy tails, relative entropy, logarithmic Sobolev, Fisher information, dyadic shells, and uniform integrability reached 292 declarations in 98 modules. Displayed result metadata were inspected; the next mathematical test must discharge an actual source entropy or shell estimate, not assume it as an endpoint premise.

## Verification log

- Cycle 38: all four complete scratch proofs, needed source olean checks, and serialized final single-module builds passed. Each final build rebuilt only its target (secants 1.6s, uniform cusp 32s, uniform tails 14s, quotient mass 12s); the latter three replayed the existing EvenL2LogUnitary informational suggestion without new warnings. All 33 public declarations have only propext, Classical.choice, and Quot.sound dependencies. All four modules are wired exactly once, and index coverage includes all 33 public declarations plus 2 private helpers. Source/card/umbrella whitespace passed. **Repository formal lint passed**, with existing large-file warnings (/tmp/selberg_uniform_mass38_lint.log). All task-owned handles are terminal; final inspection found no Lean or Lake process. No task commit or push. [Exact paper proof and audit](../3-formalized/selberg-uniform-regulator-cusp-curvature.md). Uniform tails hold over every positive regulator, the actual compact-orbit total equals lambda*M/2, and the actual limiting curvature measure is nonzero for every original exceptional source. The spectral quarter lower comparison remains unproved; Selberg stays active.

- Cycle 37: both complete scratch proofs, needed source olean checks, and serialized final single-module builds passed. Each build rebuilt only its own target (unfolding 41s, actual cell curvature 4.0s), with the existing EvenL2LogUnitary informational replay and no new module warnings. All 21 public declarations passed the scratch axiom audit with only propext, Classical.choice, and Quot.sound. Both modules are wired; the refreshed corpus audit covers all 21 public declarations plus 3 private helpers. Source/card/umbrella whitespace passed. **Repository formal lint passed**, with existing large-file warnings (/tmp/selberg_cell_curvature37_lint.log), superseding cycle 36's unrelated wiring errors. All task-owned handles are terminal; final inspection observed separate Fokas-time and horizon-domain Lean checks, left untouched. No task commit or push. [Exact paper proof and audit](../3-formalized/selberg-full-cell-curvature-unfolding.md). Standard-cell normalization, original regulator convergence, and the uniform signed functional budget are proved; limiting total mass equality and the quarter lower comparison remained open at this stage. Selberg stays active.

- Cycle 36: all three complete scratch proofs, needed source olean checks, and serialized final single-module builds passed. Each final build rebuilt only its target (37s, 15s, 18s), with the existing EvenL2LogUnitary informational replay and no new module warning. All 40 public declarations passed the scratch axiom audit with only propext, Classical.choice, and Quot.sound. All three modules are wired, and the refreshed corpus audit contains all 40 declarations. Source/card/umbrella whitespace checks passed. **Repository formal lint failed only on unrelated, unwired HTGeometry.HawkingMassLossClock and HTGeometry.InformationSurfacePacking** (/tmp/selberg_quotient_curvature36_lint.log). Every task-owned Lean/build handle is terminal; another task's hb-outgoing-domain axiom check was left untouched. No task commit or push. [Exact paper proof and audit](../3-formalized/selberg-actual-positive-quotient-curvature.md). The unique positive functional on literal compact orbit fields is proved, including original regulator convergence; standard-cell total mass and the quarter comparison remain open. Selberg stays active.

- Cycle 35: both complete scratch proofs, needed source olean checks, and serialized final single-module builds passed. Each build rebuilt only its target (scaling 28s, atomlessness 10s), with an existing EvenL2LogUnitary informational replay and no new module warnings. All 27 public declarations, including NullSingletonClass, passed the scratch axiom audit with only standard Lean axioms. Both modules are wired/indexed; task-source/card/umbrella whitespace passed. **Repository formal lint passed**, with existing large-file warnings (/tmp/selberg_curvature_noatoms35_lint.log), superseding the prior unrelated wiring failure. Every task-owned handle is terminal; final inspection found no Lean or Lake process. No task commit or push. [Exact paper proof and audit](../3-formalized/selberg-actual-curvature-no-atoms.md). The actual curvature measure is atomless, including at common source zeros; quotient curve-boundary weights and the quarter comparison remain open. Selberg stays active.

- Cycle 34: both complete scratch proofs, needed source olean checks, and serialized final single-module builds passed. Each build rebuilt only its target (covariance 10s, transport 5.7s); both replayed an existing EvenL2LogUnitary informational suggestion, with no new module warning. All 16 public declarations passed the scratch axiom audit with only the standard three axioms. Both modules are wired and indexed; task-source/card/umbrella whitespace passed. **Repository lint failed only on unrelated, unwired HTGeometry.DilatonSchwartzTransform** (/tmp/selberg_curvature_transport34_lint.log). All task-owned Lean/build handles are terminal; another agent's DilatonOperator scratch process was left untouched. No task commit or push. [Exact paper proof and audit](../3-formalized/selberg-actual-curvature-transport.md). Actual modular curvature transport is proved; quotient boundary/stabilizer control and the quarter comparison remain open. Selberg stays active.

- Cycle 33: all four complete scratch proofs, needed source olean checks, and serialized final single-module builds passed without new warnings; each build rebuilt only its target. All 40 public declarations, including the regularity and compact-finiteness instances, passed the scratch axiom audit with only the standard three axioms. All four modules are wired and indexed; task-source/card/umbrella whitespace passed. **Repository lint failed only on unrelated, unwired RHTower.FokasLenellsHardyOrientation** (/tmp/selberg_curvature_measure_lint.log). All task-owned Lean/build handles are terminal; final inspection found no Lean or Lake process. No task commit or push. [Exact dependency-closed paper proof and audit](../3-formalized/selberg-actual-curvature-measure.md). The actual regular curvature measure, continuous-test convergence, uniqueness, C² source identity, and quantitative error are proved. Actual measure transport, quotient boundary control, and the quarter comparison remain open. Selberg stays active.

- Cycle 32: both complete scratch proofs, needed source olean checks, and serialized final single-module builds passed without new warnings; each build rebuilt only its target. All 54 public declarations passed the scratch axiom audit with only the standard three axioms. Both modules are wired and all declarations indexed; task-source/card/umbrella whitespace checks passed. **Repository lint failed only on unrelated HTGeometry.FokasLenellsOrbitDecay, FokasLenellsOrbitEntries, FokasLenellsOscillatoryOrbit, and FokasLenellsScatteringDecay**, recorded in /tmp/selberg_weak_curvature_lint.log. All task-owned Lean/build handles are terminal; final inspection found no Lean or Lake process. No task commit or push. [Exact paper proof and audit](../3-formalized/selberg-actual-weak-curvature.md). Actual positive weak curvature and its compact order-zero bound are proved for every real eigenvalue; the representing measure and quarter comparison remain open. Selberg stays active.

- Cycle 31: all three complete scratch checks and serialized final single-module builds passed, each rebuilding only its target. All 36 public declarations, including the regulator-filter instance, passed the scratch axiom audit with only the standard three axioms. All modules are wired/indexed, and task-source/card whitespace checks passed. **Repository lint failed only on unrelated HTGeometry.FokasLenellsScatteringContinuity and HTGeometry.FokasLenellsSpectralContinuity** (/tmp/selberg_regulator_mass_lint.log). All task-owned Lean/build handles are terminal. No task commit or push. [Exact paper proof and audit](../3-formalized/selberg-quantitative-regulator-curvature-limit.md). Quantitative regulator removal in the total curvature budget is proved; local weak curvature and the quarter comparison remain open. Selberg stays active.

- Cycle 30: all complete scratch/source checks and four serialized single-module final builds passed. First three rebuilt only their target; the full-budget build rebuilt its needed SelbergMaassTraceMass dependency and target. All 42 public declarations passed the scratch axiom audit with only the standard three axioms. All four modules are wired/indexed; whitespace checks passed. **Repository lint failed only on unrelated untracked, unwired RHTower.MobiusDivisorFibreCoareaVariance and HTGeometry.FokasLenellsContourSymmetry** (/tmp/selberg_full_curvature_lint.log). Final process inspection found no Lean or Lake process; all task handles are terminal. No task commit or push. [Exact paper proof and complete audit](../3-formalized/selberg-regularized-cusp-and-full-curvature-budget.md). The full standard-area budget is proved; regulator-uniform passage and the quarter comparison remain open. Selberg stays active.

- Cycle 29: all four complete scratch checks and four serialized single-module final builds passed without new warnings, each rebuilding only its named target. All four modules are wired/indexed. All 57 public declarations passed the scratch axiom audit with only the standard three axioms or none. Whitespace checks passed. **Repository lint failed only on unrelated untracked, unwired `HTGeometry.FokasLenellsUniformizedFrame`** (`/tmp/selberg_augmented_lint.log`). All task-owned handles are terminal; no task commit or push. [Full paper proof and audit](../3-formalized/selberg-augmented-chord-capacity-and-nodal-resistance.md). The unqualified uniform-resistance shortcut is retired with exact nodal and actual-source positive survivors. The global quarter estimate and Selberg remain unproved.


- Cycle 28: all complete scratch/source checks and six serialized single-module final builds passed, each rebuilding only its named target. The five new modules are wired and indexed. All 88 public declarations across the six audited modules passed the axiom audit with only the standard three axioms or none. Whitespace checks passed. **Repository lint failed only on unrelated untracked, unwired `HTGeometry.FokasLenellsLeftJost` and `HTGeometry.FokasLenellsScattering`** (`/tmp/selberg_regularized_lint.log`). All task-owned handles are terminal; no task commit or push. [Full paper proof and audit](../3-formalized/selberg-regularized-curvature-and-nodal-charge.md). The nodal-limit shortcut is retired with its full positive survivor; the source quarter comparison and Selberg remain unproved.


- Cycle 27: both complete scratch checks and both direct source checks passed without warnings. Both serialized `LEAN_NUM_THREADS=1 lake build <module>` audits passed, each rebuilding only its named target. All 35 public declarations passed the axiom audit with only the standard three axioms or none; modules are wired/indexed. **Latest repository lint failed only on unrelated untracked, unwired `HTGeometry.FokasLenellsSobolevEnergy`** (`/tmp/selberg_direction_nodal_lint.log`). Prior `FokasLenellsUniformization` lint error resolved concurrently. All task-owned handles are terminal; no task commit or push. [Full paper proof and audit](../3-formalized/selberg-source-directions-and-nodal-reversal.md). The combined core/Bessel lower bound and Selberg remain unproved.

- Cycle 26: strict physical total mass, cutoff independence, actual radial/angular square completion and zero classification, full source Fisher identity, and a scoped smooth-periodic norm-only reconstruction counterexample are proved in three narrow modules. All scratch/source checks and all three serialized targeted final builds passed; each final build rebuilt only its target. All 46 public declarations passed the axiom audit with only the standard three axioms or none. Sources are wired/indexed; whitespace checks passed. **Latest repository lint failed only on unrelated untracked, unwired `HTGeometry.FokasLenellsUniformization`** (`/tmp/selberg_mass_radial_lint.log`). All task-owned Lean/build handles are terminal; no task commit was made. [Full proof and audit](../3-formalized/selberg-positive-mass-and-radial-defect.md). The scalar-norm toy is not claimed to be Maass/cuspidal and does not contradict recovery using the actual eigenvalue equation. The combined core/Bessel lower bound remains unproved; Selberg stays active.

- Cycle 25: actual pointwise trace energy, modular current transport/cancellation, paired Stokes, standard-area Fubini, and the complete physical core-plus-cusp quarter form are proved across five narrow Selberg modules. All five scratch/source checks and serialized targeted final builds passed without new warnings; each final build rebuilt only its named target. All 94 public declarations passed the axiom audit with only the standard three axioms or none. Modules are wired/indexed; whitespace checks passed. **Latest repository lint failed only on five unrelated untracked, unwired HTGeometry modules:** `FokasLenellsJumpGeometry`, `FokasLenellsSingularPhase`, `InwardPlaneDisplacementReturn`, `InwardPlanePrescribedStream`, `PolyatomicSpectralRank` (`/tmp/selberg_core_quarter_lint.log`). All task-owned Lean/build handles are terminal; no task commit was made. [Full paper proof and audit](../3-formalized/selberg-maass-core-stokes-and-quarter-form.md). The missing combined core/boundary lower bound and strict total mass positivity are not assumed; Selberg remains unproved.

- Cycle 24: all-cusp transport and the finite congruence trace are proved in `SelbergMaassCuspTransport` and `SelbergMaassCongruenceTrace`. The existing general conformal proof is shared through new `HTGeometry.ComplexC2Laplacian`; its previous specialized statement is preserved and directly checked. All three final targeted builds passed, each building only its target. All 47 public declaration axiom checks passed with only the standard three axioms or none. New modules are wired and indexed; whitespace checks passed. **Latest repository-wide lint failed only on unrelated unwired `HTGeometry.GaussianDisplacedSpectralPole`**, currently untracked (`/tmp/selberg_cusp_trace_lint.log`). The first attempted transport audit spawned parallel dependency workers, violating one-worker discipline; that exact task-owned process tree was stopped and terminal exit 143 verified. Narrowing the shared import removed the cause; the subsequent final audits ran sequentially. All task-owned processes are terminal, and final inspection found no Lean/Lake build process. No task commit was made. [Exact proof, build logs, and full audit](../3-formalized/selberg-maass-integral-cusps-and-congruence-trace.md). Selberg and the compact-core Green/quarter estimate remain unproved.

- Cycle 23: complete scratch and direct source checks passed without warnings for `SelbergMaassBesselRemainder` and `SelbergMaassBoundaryForm`. Both serialized targeted final builds passed, each rebuilding only its target (`/tmp/selberg_maass_bessel_remainder_build.log`, `/tmp/selberg_maass_boundary_form_build.log`). All 28 public theorem checks in `/tmp/selberg_maass_bessel_form_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired and indexed; corpus queries return the capstones. Tracked/new task-file whitespace checks passed. **Latest repository-wide lint passed**, with existing large-file warnings (`/tmp/selberg_maass_bessel_form_lint.log`); the prior three unrelated unwired-module errors were resolved outside this task. Every task-owned process finished; a separate `DivisorTwentyTwoAnalyticBounds` Lean process was active during the final audit and was not touched. No commit was made by this task. [Exact result and paper proof](../3-formalized/selberg-maass-bessel-boundary-form.md). The global Selberg goal remains unproved.

- Cycle 22: complete scratch and direct source checks passed for `SelbergMaassBoundaryFlux`, `SelbergMaassCuspDecay`, and `SelbergMaassTailEnergy` without warnings. All three targeted final builds passed, serialized; the flux build rebuilt the needed `SelbergExceptionalCuspMean` dependency followed by its target, and the other builds rebuilt one target each. Logs: `/tmp/selberg_maass_flux_build.log`, `/tmp/selberg_maass_cusp_decay_build.log`, `/tmp/selberg_maass_tail_energy_build.log`. All 34 public theorem checks in `/tmp/selberg_maass_flux_decay_tail_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. All three modules are wired and indexed; tracked/new task-file whitespace checks passed. Every task-owned process finished; final process audit found no Lean/Lake process. This task made no commits. [Exact result and paper proof](../3-formalized/selberg-maass-mass-flux-tail.md). The full Selberg goal remains unproved.
- **Historical cycle 22 repository-wide lint failed on three unrelated unwired HTGeometry modules:** `BistochasticMixingMajorization`, `FiniteNoiseMixingApplications`, and `VolterraSourceRecovery`. No new Selberg module is named in an error; those concurrent modules were not edited or wired speculatively. Existing large-file warnings remain. Log: `/tmp/selberg_maass_flux_decay_tail_lint.log`. The previous passing lint below is historical.

- Cycles 20–21: complete scratch and direct source checks passed without warnings. Targeted final builds passed for `SelbergMaassBoundaryTrace` and `SelbergMaassParseval`, rebuilding one target each; logs `/tmp/selberg_maass_trace_build.log` and `/tmp/selberg_maass_parseval_build.log`. All task Lean invocations were serialized. Eighteen capstone checks in `/tmp/selberg_trace_parseval_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. Both new modules are wired, and refreshed corpus searches return their capstones. Tracked and new task-file whitespace checks passed. **Latest repository-wide formal lint passed**, with existing large-file warnings (`/tmp/selberg_trace_parseval_lint.log`); the prior seven unwired-module errors were resolved outside this task. Every task-owned Lean/Lake handle finished. Other agents' Coppo/CCM processes were active during the process audit and were not touched. This task made no commits. The full Selberg goal remains unproved.

- Cycles 18–19: complete scratch and final direct source checks passed without warnings. Targeted final builds passed for `SelbergBesselBoundaryOperator` (one target rebuilt) and `SelbergMaassFourierModes` (the changed `SelbergMaassFourierMean` dependency followed by the new target, sequentially). Logs: `/tmp/selberg_boundary_operator_build.log`, `/tmp/selberg_maass_fourier_modes_build.log`. All task Lean invocations were serialized. Twenty-four capstone axiom checks across the two `/tmp` audit files report only `propext`, `Classical.choice`, and `Quot.sound`; the Maass audit also imports the existing `SelbergExceptionalCuspMean` successfully. Both new modules are wired and indexed. Tracked and new task-file whitespace checks passed. All task-owned Lean/Lake handles are terminal; a separate agent's `QNMLorentzAuxiliary` build was active at the process audit and was not touched. No commit was made by this task.
- **Historical cycle 18–19 repository-wide lint failed on seven unrelated unwired modules:** RHTower `MobiusDivisorRemainingFrontTransport`; HTGeometry `CoppoFockRotation`, `CoppoJosephsonPotential`, `CoppoKerrPhaseGeometry`, `CoppoNonlocalNoise`, `CoppoPartnerEigenspaces`, `CoppoSSH`. No new Selberg module is named. Log: `/tmp/selberg_fourier_final_lint.log`. The intermediate cycle 18 audit had 23 unrelated unwired modules; concurrent work resolved those entries or changed the set. The cycle 20–21 passing audit above supersedes these historical failures.

- Cycles 16–17: both complete scratch proofs and final direct source checks passed without warnings. Targeted final builds passed for `SelbergBesselBoundaryTrace` and `SelbergBesselBoundaryEnvelope`, rebuilding one target each; logs `/tmp/selberg_bessel_trace_build.log` and `/tmp/selberg_bessel_envelope_build.log`. All Lean checks/builds in this continuation were serialized. Eighteen capstone checks in `/tmp/selberg_trace_envelope_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into RHTower and present in the refreshed corpus index. Tracked and untracked task-file whitespace checks passed. Final process audit found no Lean or Lake process. This task made no commits.
- **Cycles 16–17 repository-wide lint failed on seven unrelated unwired modules:** RHTower `BoundedPlaneDisplacementBatch`, `MobiusDivisorApproximateTwoReserve`, `MobiusDivisorSquareRootWindowCapacity`; HTGeometry `CPVClassicalDynamics`, `CPVSchwarzschildLimit`, `CPVThermalRadiation`, `CPVTwoModeFock`. These concurrent source modules were not edited by this task, and neither new Selberg module is named in the errors. They were not wired speculatively. Log: `/tmp/selberg_trace_envelope_lint.log`. The preceding continuation's passing lint entry is historical, not the current repository-wide result.

- Cycle 14: all four new modules passed scratch/direct checks and serialized targeted final builds. The energy build rebuilt one target (`/tmp/selberg_bessel_energy_build.log`). Both existing compatibility modules passed direct compilation. Fifteen capstone axiom checks in `/tmp/selberg_bessel_boundary_axioms.lean`, importing both old interfaces alongside the new energy module, report only `propext`, `Classical.choice`, and `Quot.sound`. [Exact survivor](../3-formalized/selberg-exact-bessel-boundary-energy.md); [failed all-positive-coefficient conjecture](../5-failed/selberg-always-positive-bessel-slope.md). The initial interrupted build is excluded from these passing audits.
- Cycle 15: complete scratch and direct source checks passed without warnings. Targeted `lake build GaloisForLFunctions.RHTower.SelbergBesselAdverseModes` passed, rebuilding only that module (`/tmp/selberg_bessel_modes_build.log`). Eleven capstone axiom checks in `/tmp/selberg_bessel_modes_axioms.lean` report only the standard three axioms. The module is wired into the umbrella. Combined cycle 14–15 index refresh, repository-wide formal lint, and tracked/untracked task-file whitespace checks passed. Lint retains existing large-file warnings; log `/tmp/selberg_bessel_boundary_final_lint.log`. The final process audit found no Lean or Lake process. This task made no commits; shared-tree commits by other work incorporated some already-finished files during the session.

- Foreground `lake env lean` checks passed for the scratch proof and final `SelbergGeometricBlend.lean` with no warnings.
- Targeted `lake build GaloisForLFunctions.RHTower.SelbergGeometricBlend` passed; the new module is wired into `RHTower.lean`. No full/umbrella build ran.
- Five capstone axiom checks passed in `/tmp/selberg_geometric_blend_axioms.lean`, with only `propext`, `Classical.choice`, and `Quot.sound`.
- Generated corpus indexes were refreshed. The full Selberg conjecture is still unproved; this loop remains active and has produced a genuine local differential theorem rather than a conditional Selberg wrapper.
- Formal lint passed after the first module, with existing large-file warnings elsewhere in the corpus.
- The second module passed scratch and final direct checks without warnings, and targeted `lake build GaloisForLFunctions.RHTower.SelbergBoundaryMomentChannels` passed. Both finished modules are wired into the umbrella.
- Six additional scratch axiom checks, including the actual logarithmic differential and both recovery capstones, report only `propext`, `Classical.choice`, and `Quot.sound`.
- Final index refresh and formal lint passed after both modules; lint reports existing large-file warnings. Both new Lean files pass whitespace checks. The process audit found no remaining Lean or Lake process; no unrelated process was terminated.
- Continuation: `SelbergPoissonScaleMoments` and `SelbergCuspHardyBoundary` each passed scratch and final direct checks without warnings, and each targeted final build passed. Both are wired into the umbrella. Fourteen further capstone axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.
- Final continuation index refresh and whitespace checks passed. The process audit found no Lean/Lake process. **The continuation's repository-wide lint did not pass:** it reported 11 unrelated modules unreachable from their theorem-area umbrellas. None of the errors names a Selberg module. The failures are five `ThetaCuspHawkingBMJoint` modules (`AngularEnergyTests`, `RadialFamilyAdmission`, `RadialFamilyData`, `RadialFamilyGreen`, `RadialFamilyLift`) and six HTGeometry modules (`BochnerL2HilbertTensor`, `BochnerL2ProductIsometry`, `CompactUniformL2Convergence`, `HilbertCompactJetApproximation`, `HilbertFiniteProjectionCompact`, `HilbertFiniteProjectionL2`). Those files were not edited by this task. Detailed output: `/tmp/selberg_scale_hardy_lint.log`. The earlier passing lint entry concerns the earlier pair of modules and is historical.
- Cycle 12: both complete scratch proofs and final direct checks passed without warnings. Targeted final builds passed for `SelbergMaassFourierMean` and `SelbergExceptionalCuspMean`, rebuilding one module each. Eleven capstone axiom checks in `/tmp/selberg_maass_mean_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into the umbrella.
- Cycle 12 index refresh and repository-wide lint passed. The earlier 11 unreachable-module failures no longer occur; they were resolved outside this task. Existing large-file warnings remain. Lint output: `/tmp/selberg_maass_mean_lint.log` (warnings were emitted on stderr). The process audit found no Lean/Lake process. [Exact result and paper proof](../3-formalized/selberg-exceptional-cusp-mean.md).
- Cycle 13 scratch and direct source checks passed without warnings. Targeted `lake build GaloisForLFunctions.RHTower.SelbergCuspRelocation` passed (3547 dependency-graph jobs), rebuilding the target and two needed source dependencies. Six further axiom checks report only the standard three axioms. The module is wired into the umbrella. Final index refresh, repository-wide lint, and whitespace checks passed; lint retains existing large-file warnings. Final lint log: `/tmp/selberg_mean_relocation_final_lint.log`. No Lean/Lake process remained.
