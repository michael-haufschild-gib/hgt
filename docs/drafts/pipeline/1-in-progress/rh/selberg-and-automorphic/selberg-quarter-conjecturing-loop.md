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
- [x] Cycle 39: test the scalar quarter-comparison shortcut; prove and audit the literal smooth modular family with every positive curvature/mass ratio and its exact scoped obstruction. The actual Maass comparison remains open.
- [ ] Cycle 40: test original source-current conservation, phase and pair-current energy identities, modular transport, and regulator forcing; retain original core, cusp, nodal, and arithmetic constraints in the quantitative comparison.
- [ ] Derive the remaining Fourier/cusp interfaces and test a core-plus-cusp argument that retains boundary flux and supplies genuine congruence-uniform control.
- [x] Cycles 56–61: arithmetic routes past 3/16 (density × multiplicity, per-type density, twist families, theta barrier, bilinear Kloosterman, large sieve over moduli) audited; open cores = Kl₁₅ moduli cancellation at fixed arguments, or new functoriality.
- [ ] Cycle 62+: attack the fixed-argument moduli cancellation for hyper-Kloosterman sums (smallest open case d ≥ 4), or find an input that fails for the weight-1/2 theta multiplier and gives a gain.

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

**Lean status:** the exact equation, real smoothness, endpoint eigenfunction predicates, positive symmetric correction, geometric-mean identity, and translation obstruction are now closed in `GaloisForLFunctions.RHTower.SelbergGeometricBlend`. The actual Frechet derivatives are proved against `positiveHyperbolicLaplacian`; the displayed gradient is not a hypothesis. [Paper proof and verification](../../../3-formalized/selberg-local-geometric-interpolation.md).

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

**Lean status:** `centeredNorm_eq_twoHeight` and `directionalSecondMoment_eq_heightDifference` are closed, and `squaredNorm_center` identifies the left side with the actual squared norm of centered coefficients. [Exact paper proof and verification](../../../3-formalized/selberg-boundary-moment-two-height-recovery.md). The first-gradient-only subroute is recorded with this positive survivor on its [failed proposal card](../../../5-failed/selberg-first-gradient-covariance.md).

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

**Lean status for cycles 9–10:** complete in `SelbergPoissonScaleMoments`: actual integrability and set-integral values, connection to the existing diagonal Poisson multiplier, injectivity, exact positive range, and absence of a uniform ordinary-scale upper bound. Targeted build and eight capstone axiom checks passed. [Positive survivor](../../../3-formalized/selberg-poisson-scale-moments.md); [failed modal inference](../../../5-failed/selberg-log-scale-gap-detector.md).

### Cycle 11 — can horizontal frequency pay the cusp boundary cost?

This returns to cycle 1's actual boundary defect rather than impose an unsupported bound on an abstract semigroup. Corpus ingredients are the exact Morse/Darboux Robin defect, the native compact cusp profiles, and mathlib's bundled test functions and compact-support fundamental theorem of calculus.

For a real smooth compact profile `g` on the positive half-line, cutoff `Y>0`, and horizontal frequency `k`, test

`integral_Y^infinity (g'^2+k^2*g^2-g^2/(4*y^2))`

`= integral_Y^infinity (g'+(k-1/(2*y))*g)^2`

`  + integral_Y^infinity (k/y)*g^2 + (k-1/(2*Y))*g(Y)^2`.

The identity retains the complete lower seam term. Its paper derivation expands the square and integrates the derivative of `(k-1/(2*y))*g^2`; compact support removes the upper endpoint. It gives a quarter-energy bound for the isolated cusp tail when `k*Y>=1/2`. No estimate for the compact core or its gluing is assumed.

**Regularity refinement:** the proof uses only `C¹` regularity. Division by height extends as `C¹` through zero because the compact profile's support lies inside the positive ray. This refinement has been checked in the paper proof and formalized for mathlib's bundled `C¹` test functions.

**Lean status:** complete in `SelbergCuspHardyBoundary`. It proves the actual flux derivative, all integrability statements, the exact identity, the zero-frequency Hardy defect, and the quarter-energy inequality for `Y=exp(h)`, `k=(1/2+u^2)/exp(h)`. A closed range theorem shows that the frequency parameterization covers exactly `k>=1/(2*Y)`. The threshold is sufficient; necessity is not claimed. [Paper proof and verification](../../../3-formalized/selberg-cusp-hardy-boundary.md).

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

[Exact positive survivor](../../../3-formalized/selberg-sharp-cusp-orbit-height.md); [failed covering shortcut](../../../5-failed/selberg-integral-cusp-relocation.md).

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

[Exact positive survivor](../../../3-formalized/selberg-exact-adverse-cusp-modes.md); [failed uniform-count strengthening](../../../5-failed/selberg-uniform-adverse-mode-rank.md).

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

**Outcome:** both upper-envelope conjectures are proved in `SelbergBesselBoundaryEnvelope`. Each comparison factor is proved strictly increasing, and each hypothetical crossing produces a nonincreasing reciprocal-plus-time function that becomes negative at an explicitly chosen later point. The final source coefficient has the strict bound `0<k-B(k,Y)<1/(8*k*Y^2)`. Scratch/direct checks and the targeted final build passed without warnings, rebuilding one target only. [Exact proof and audit](../../../3-formalized/selberg-bessel-inverse-frequency-correction.md).

Cycle 16 also passed its targeted final build. Its exact scalar trace result and frequency-independent compact approximation estimate are recorded in [the sharp trace-infimum card](../../../3-formalized/selberg-sharp-cusp-trace-infimum.md).

### Cycle 18 — next actual Fourier-boundary operator target

The two completed cycles now supply an exact scalar boundary response and an inverse-frequency correction. At period `w=exp(b)` and height `Y=exp(T)`, define the nonzero integer diagonal by `c_n=k_n-B(k_n,Y)`, with `k_n=2*pi*|n|/w`; omit the zero channel explicitly. The proved estimate is `0<c_n<w/(16*pi*Y^2*|n|)`.

**Next conjecture:** these literal coefficients define a positive compact diagonal operator on the square-summable nonzero Fourier boundary channels. `HTGeometry.BoundedDiagonalOperatorLp` has been read: it constructs the actual multiplication operator on complex `lp ... 2`, proves its norm bound, and proves compactness from cofinite coefficient decay using explicit finite diagonal truncations. The next work must instantiate that theorem with the Bessel coefficients, prove their cofinite decay and positivity on the actual sequence space, and identify the boundary quadratic form on its frequency-weighted domain. Its existing broad `import Mathlib` must be handled with targeted, serialized dependency compilation if any needed olean is absent.

The subsequent core operator still has to be constructed from congruence geometry and coupled to this exact response. Compactness of the correction by itself gives no global quarter bound. This obligation remains part of the original Selberg goal.

**Outcome:** the complete scratch proof passes. `SelbergBesselBoundaryOperator` defines the literal correction on complex `lp ... 2` over all integers, explicitly setting its zero coefficient to zero. The inverse-index estimate implies cofinite decay, hence compactness by the inspected diagonal construction. Real positive coefficients prove self-adjointness and positivity, and both its kernel and zero quadratic-response space are exactly the constant channel.

The correction quadratic series is summable for every square-summable vector, by the actual Hilbert inner-product series. Since `B_n=k_n-c_n`, summability of the outgoing energy series is equivalent to summability of the principal frequency energy series. On this exact domain, `B[u]=K[u]-Re <Cu,u>`, with strict inequality whenever a nonconstant coefficient is present. This is a source-defined sequence-space result; the actual Maass trace map and quotient-core coupling are not inferred. The module is wired; direct source and targeted final build passed without warnings, rebuilding one module. Twelve capstone axiom checks report only the standard three axioms. [Exact survivor](../../../3-formalized/selberg-compact-bessel-boundary-operator.md).

### Cycle 19 — connect every actual Maass Fourier coefficient to its modal equation

**Next source conjecture:** for the literal coefficient `a_n(y)=(1/w)*integral_0^w exp(-2*pi*i*n*x/w)*f(x+iy) dx` of a congruence Maass eigenform, the actual second height derivative satisfies

`-y^2*(a_n''(y)-(2*pi*n/w)^2*a_n(y))=lambda*a_n(y)`.

The corpus search found `DeningerFourierCoeffDeriv`: integration by parts with its literal periodic Fourier kernel proves the coefficient-of-derivative identity. The inspected `SelbergMaassFourierMean` already derives directional regularity, horizontal derivative periodicity, height differentiation under the integral, and the original Maass PDE in real coordinates. Reuse these mechanisms to prove both weighted height differentiation and the twice-integrated horizontal identity. This connects arbitrary actual coefficients to the modal source without assigning a Bessel ansatz or importing an assumed spectral conclusion.

The constant-index specialization must agree with the already-proved mean equation. The nonconstant equations will then supply an actual source for the subsequent energy/trace and quotient-core steps; they alone do not remove the global core obligation.

**Outcome:** the complete scratch proof passes in `SelbergMaassFourierModes`. Local compact domination justifies both height derivatives of the literal normalized coefficient. The inspected Fourier derivative theorem and the proved periodicity of the actual horizontal derivative give the squared-frequency multiplier. Integrating the source Maass PDE proves the modal equation at every index. The zero index agrees with the previously constructed mean after division by the positive period.

Two stronger source conclusions also pass: height decay is uniform in all integer indices, and at every positive height there is a nonnegative finite `M` such that `k_n^2*|a_n|<=M` for every index. The first uses the cusp filter and the normalized Fourier coefficient norm estimate; the second uses compact boundedness of the actual horizontal second derivative and the exact twice-integrated identity. Seven existing coordinate helpers were made public with unchanged proof bodies, so the new module reuses them. The module is wired; direct and targeted final audits passed. Twelve additional capstone axiom checks report only the standard three axioms, including the two preserved mean theorems; the existing exceptional-mean interface imports alongside the new module successfully. [Exact proof](../../../3-formalized/selberg-actual-maass-fourier-modes.md).

### Cycle 20 — next actual trace-domain conjecture

The new source frequency bound suggests proving that each actual Maass trace belongs to the already-constructed Bessel form domain. The whole-corpus search found `RHTower.deningerFourier_summable_inv_sq` in `DeningerFourierKothe`, which proves summability of `(1+|n|)^(-2)` on the integers using the shifted natural p-series and the positive/negative integer split. Mathlib's inspected `Memℓp` construction can then bundle the literal coefficient sequence.

**Proposed proof:** for nonzero integer `n`, `|n|>=1`, so `(1+|n|)^2<=4|n|^2`. Combine this with the new bound `k_n^2*|a_n|<=M`, and absorb the single zero coefficient into a finite constant, to obtain `|a_n|<=C/(1+|n|)^2`. Thus the actual coefficient norms are summable. Multiplying the squared-frequency bound by `|a_n|` shows summability of `k_n^2*|a_n|^2`; boundedness of the coefficients gives square summability. Finally `k_n<=1+k_n^2` yields summability of `k_n*|a_n|^2`. This should construct the actual trace in the exact form domain and specialize the compact-correction identity to it.

Identifying the resulting boundary series with a physical trace/energy theorem and controlling the quotient-core response are separate obligations. No inference of global positivity is made from summability.

**Outcome:** `SelbergMaassBoundaryTrace` proves the actual weighted coefficient bound, absolute coefficient summability, squared coefficient mass, squared-frequency energy, and first-frequency energy. It constructs the literal Maass sequence in complex `ell^2` at height `exp(T)`, bundles that same sequence into the exact Bessel form domain, and specializes the compact-correction identity to it. Scratch, direct source, targeted final build, axiom, index, lint, and whitespace audits passed. The module is wired. [Exact proof and audit](../../../3-formalized/selberg-actual-maass-boundary-trace.md).

### Cycle 21 — next physical Parseval identity

The actual trace-domain proof leaves a concrete analytic identification to establish. Corpus search found `DeningerFloquetMeasureEnergy`, whose proof applies Mathlib's literal-interval theorem `hasSum_sq_fourierCoeffOn`; `DeningerFourierBridge` identifies the interval kernel with the additive-circle Fourier character. Inspecting these proofs suggests a direct identity on each actual positive-height Maass slice, without postulating a sequence-space model.

**New target:** normalized horizontal integrals of `|f|^2`, `|partial_x f|^2`, and `|partial_y f|^2` equal respectively the sums of `|a_n|^2`, `k_n^2*|a_n|^2`, and `|a_n'|^2`. Source C² regularity supplies continuity and square integrability on every finite period. The already-proved weighted height derivative and one horizontal integration by parts should identify the derivative coefficients. Adding and subtracting these three absolutely convergent identities should yield the physical quarter-energy density as its literal modal series. This is a new proof target, not an assumed energy interface.

**Outcome:** `SelbergMaassParseval` proves the literal interval coefficient identification with the exact period normalization. The three physical Parseval identities are proved as `HasSum` statements, and adding/subtracting them proves the actual quarter-energy identity, including both derivative terms and the hyperbolic mass weight. The module is wired; scratch, direct source, targeted final build, axiom, index, lint, and whitespace audits passed. This closes the fixed-height physical mass and energy identification, not an interchange with an infinite height integral. [Exact proof](../../../3-formalized/selberg-maass-quarter-parseval.md).

### Cycle 22 — actual mass/flux and quantitative cusp decay: proved

The corpus-derived differential replacement for holomorphic frequency-gap decay survived proof. `SelbergMaassBoundaryFlux` derives literal source Hermitian pairing and horizontal Green identities, then `M'=2J`, `J'=G-lambda*M/y²`, the physical quarter-slice identity, `M->0`, and `G>=k²*M` for actual positive sub-quarter eigenforms.

`SelbergMaassCuspDecay` proves `M''>=k²*M` above `A=1/k`, then derives `M(y)<=M(A)*exp(-k*(y-A))` by secants and an integrating factor. Backward unit secants force `M'->0`, so actual terminal flux vanishes. The flux derivative is integrable above the cutoff.

`SelbergMaassTailEnergy` proves physical mass, hyperbolic mass, flux derivative, gradient energy, and quarter-energy integrable above **every** positive height. Its exact capstone is

`(1/w)*integral_Y^infinity quarterSlice = -J(Y)+(lambda-1/4)*integral_Y^infinity M/y²`.

No infinite-height Fourier interchange, terminal-flux assumption, or modal ansatz was used. Complete scratch/direct checks, three targeted final builds, and all 34 public theorem axiom audits passed. The latest global lint has three unrelated unwired HTGeometry errors, recorded below. [Exact result and dependency-closed paper proof](../../../3-formalized/selberg-maass-mass-flux-tail.md).

### Cycle 23 — actual noncompact Bessel squares and complete cusp boundary form: proved

The compact-real-profile interface mismatch was resolved directly in physical height. `SelbergMaassBesselRemainder` proves the actual Bessel response law `B'=B²-k²+1/(4*y²)` and limit `B->k`. Actual modal mass and derivative energy are integrable by physical Parseval domination. Expanding the complex square gives `|a'+B*a|²-energy=(B*|a|²)'`; actual coefficient decay kills the upper current. The improper FTC gives the exact single-mode infinite-tail identity. The exceptional constant coefficient and derivative are zero.

`SelbergMaassBoundaryForm` proves the countable mode/height interchange with majorant whose literal Parseval sum is `G+M/(4*y²)`, already integrable. The signed modal tail integrals therefore sum to the actual physical tail quarter-energy. Subtracting the summable actual seam series proves the complete nonnegative square series and

`quarterTail/w = boundaryForm(actualTrace) + sum_(n!=0) integral |a_n'+B_n*a_n|²`.

Substituting the prior flux identity proves the same right side equals `-J(Y)+(lambda-1/4)*integral M/y²`. The full actual cusp comparison is now proved. Complete scratch/direct checks, both targeted final builds, and all 28 public theorem axiom audits passed. The latest global lint passed with existing large-file warnings. [Exact statement and paper proof](../../../3-formalized/selberg-maass-bessel-boundary-form.md).

### Cycle 24 — actual integral transport and finite congruence trace

The C² pullback covariance conjecture succeeds. `SelbergMaassCuspTransport` constructs each literal integral translate as an actual Maass cusp eigenform at the same level and eigenvalue. Integral congruence normality supplies invariance, inverse translation supplies nonvanishing, and composition of scaling matrices supplies all cusp decay. The completed cusp Bessel identity and constant coefficient vanishing therefore hold at every integral cusp. The period used is the congruence level; no minimal cusp width is claimed.

Fresh whole-corpus searches for truncated Stokes identities found `ThetaCuspHawkingBMEisensteinActualFirstStokesIntegral.d4BM_actualFirstStokesPairedTruncatedBulk_eq_cuspTop`. Its source is an Eisenstein current; it cannot be substituted for a Maass source. Its explicit translation-side and paired-inversion-arc cancellations suggested summing the actual translated Maass squared norms over the finite congruence quotient.

That second conjecture also succeeds. `SelbergMaassCongruenceTrace` constructs the actual quotient family without a representative choice, then its nonnegative C² density `D(z)=sum_q |f_q(z)|²`. The density is positive somewhere, invariant under the full modular group, and tends to zero at infinity. Period one of its horizontal slices gives the exact unit-strip normalization `H(y)=integral_0^1 D=sum_q M_q(y)`. Its first two actual derivatives are `H'=2*sum_q J_q` and `H''=2*sum_q(G_q-lambda*M_q/y²)`. Tail integrability and finite summation of the actual cusp identity give `-sum_q J_q(Y)+(lambda-1/4)*integral_Y^infinity H/y² = sum_q BesselBoundary_q + sum_q FourierSquares_q`, with nonnegative convergent square contributions. No coset-to-distinct-cusp multiplicity formula is assumed.

The general second-chain-rule proof was extracted from the existing conformal-Laplacian module into narrow `HTGeometry.ComplexC2Laplacian`, with the old public theorem preserved as a checked wrapper. This shares the proof while avoiding the old wrapper's broad research dependency tree. [Exact statements, paper proof, and audit](../../../3-formalized/selberg-maass-integral-cusps-and-congruence-trace.md).

### Cycle 25 — actual standard-area core Green theorem and complete quarter form

Whole-corpus searches for `Laplacian square` found `ThetaCuspHawkingBMSquareSourceDifferential.fullSquarePotential_laplacian`. Its product-jet proof retains gradient forcing. The resulting actual Maass finite-trace conjecture is proved: `Delta D=2*(sum_q(|partial_x f_q|²+|partial_y f_q|²)-lambda*D/y²)`. The trace is not treated as an eigenfunction.

Differentiating the actual modular invariance of `D` gives its reciprocal-square Möbius Jacobian. Radial contraction reverses sign under inversion, hence cancels paired unit-circle arcs. Translation cancels side currents. Actual finite FTC gives the paired Stokes formula; reflection and period one turn its surviving top into the physical unit-period current. Differentiation of the actual trace mass identifies that current as `2*sum_q J_q`.

A fresh whole-corpus `Stokes` query found `ThetaCuspHawkingBMEisensteinActualFirstStokesFubini`. Its indicator-domain Fubini proof and exact lower-side geometry supplied the missing area identification. Adapted to the actual real Maass trace, standard two-dimensional integration over the truncated modular domain now satisfies `integral_core Delta D=2*sum_q J_q`. The previous paired-coordinate divergence integral is proved equal to this standard area integral. All regularity and integrability are derived from the original C² source; no specialized Eisenstein or broad research module is imported.

The complete actual quarter form is now proved. For `Y=exp(T)>=1`, core energy `Qcore=integral_core(G-D/(4*y²))`, core hyperbolic trace mass `Mcore`, actual unit-strip tail mass `Mtail`, full Bessel boundary sum `B`, and convergent Fourier square remainder `S>=0`,

`Qcore(Y)+B(T)+S(T)=(lambda-1/4)*(Mcore(Y)+Mtail(Y))`.

Thus `Qcore+B` has the corresponding **upper** bound. A nonnegative lower bound has not been proved. [Exact theorem, dependency-closed paper proof, and audit](../../../3-formalized/selberg-maass-core-stokes-and-quarter-form.md).

### Cycle 26 — strict physical mass and exact radial/angular residual

The strict mass conjecture succeeds. Corpus searches `integral positive continuous` and `fundamental domain`, followed by the actual definiteness proof in `PeterssonInnerProductLevelOne`, supplied continuity, modular reduction, and `fd=closure(fdo)`. Original nonvanishing therefore gives a positive interior trace value and a positive compact-core mass. Horizontal Fubini and the integrable cusp tail prove exact cutoff independence: `Mcore(Y)+Mtail(Y)=Mcore(1)+Mtail(1)>0` for every `Y>=1`. The actual exceptional source consequently forces `Qcore(exp T)+B(T)<0` for every `T>=0`. No nonnegative lower bound is assumed.

Queries `Gram determinant`, `Fisher phase`, and `Lagrange identity`, with source reads of `ProjectiveQuantumFisherValue`, `ConstitutivePolarAmplitudeFisherPhase`, and `SymmetricPickSchur`, suggested testing scalar-amplitude reconstruction and retaining its exact residual. The broad reconstruction shortcut fails: explicit smooth period-one fields `exp(i*c*Re z)` have identical squared norm one but different actual derivative energies for `c=0` and `c=2*pi`. These are not asserted to be Maass or cusp forms. In particular, the test does not contradict recovery from trace derivatives **together with the Maass equation and eigenvalue**.

The actual-source positive survivor is proved. With `C_v=D_v D`, `E_v=sum_q|D_v f_q|²`, and `R_v(c)=sum_q|D_v f_q-c*f_q|²`,

`R_v(c)=E_v-c*C_v+c²D`.

At `D>0`, its unique minimizing real slope is `c_v=C_v/(2D)`, with excess `D*(c-c_v)²`. Every residual vanishes exactly when all component derivatives are radial with that same real slope. Let `A=R_x(c_x)+R_y(c_y)>=0`. The actual scalar amplitude satisfies `G=|grad sqrt(D)|²+A` wherever `D>0`. The multiplied identity `D*G=(C_x²+C_y²)/4+D*A` holds everywhere, including trace zeros, without a smoothness assertion for the norm there. The actual source equation then yields

`D*Delta D=(C_x²+C_y²)/2+2D*A-2lambda*D²/y²`.

[Exact statements, paper proof, and audit](../../../3-formalized/selberg-positive-mass-and-radial-defect.md). [Failed shortcut and fully formalized positive survivor](../../../5-failed/selberg-scalar-norm-energy-reconstruction.md).

### Cycle 27 — actual directions, weighted distance, and nodal reversal

The zero-mean angular-energy conjecture fails. For a real differentiable profile, radial subtraction removes the full derivative away from its zeros. Exact cosine is smooth and periodic, has zero mean and positive squared mass, but its residual is integrable and zero almost everywhere. At a node the residual is one. Nodal reversal therefore defeats this angular-only inference. The toy is not claimed to be Maass, cuspidal, or inversion invariant.

The actual-source survivor succeeds. Normalize the literal finite congruence family by `rho=sqrt(D)`. Reconstruction and modular permutation covariance hold even at common zeros. On `D>0`, the actual derivative obeys `rho*partial_v u_q=partial_v F_q-c_v F_q`, so the retained residual is exactly `D*sum_q |partial_v u_q|²`. The original exceptional constant-term theorem gives `integral rho*u_q=0` on every shifted level period. In contrast, the amplitude mean is strictly positive around each positive source value.

The continuous source correlation has zero period integral and a positive diagonal. It therefore takes a strictly negative value within the centered level period. Both endpoint densities are positive, and the normalized squared distance is strictly greater than two. Original nonvanishing supplies such an actual same-height pair. More strongly,

`rho(w)*d(z,w)²=2*rho(w)-2*C(z,w)/rho(z)`

holds even at common zeros of the moving source. This weighted squared-distance slice is continuous and its mean over every level period is exactly twice the amplitude mean. It retains nodal direction reversal without asserting differentiability there. [Dependency-closed proof and full audit](../../../3-formalized/selberg-source-directions-and-nodal-reversal.md). [Failed shortcut and positive survivor](../../../5-failed/selberg-zero-mean-angular-energy.md).

The user renewed the requirement for wider searches and explicitly noted the default AND behavior. Subsequent discovery used `--any` for `nodal chord oscillation variance`, `coarea Cheeger conductance resistance`, `permutation transport holonomy expansion`, and grouped OR phrases for effective resistance, Dirichlet principles, spectral gaps, boundary transport, and zero mean. These spanned hundreds to thousands of modules. Exact result counts and the sources read are on the linked card; this does not claim every matching declaration was read.

### Cycle 28 — actual regularized curvature and surviving nodal charge

Broad OR searches (`--any`) for resistance/capacity, boundary transport, arithmetic amplification, and regularization reached `SchwartzPositiveCompactDiagonal.pointwiseMulConj_nonnegativeSquareRootRegularization_self`. Its retained cutoff error suggested adding a positive constant square to the actual trace. The resulting source conjecture is proved: `rho_e=sqrt(D+e²)` is C² and modular invariant through common zeros, its remainder is a sum of squares including the constant-coordinate correction, and

`rho_e*Delta rho_e = R_e-lambda*D/y²`.

The actual quarter density retains `R_e` and the explicit `e²/(4y²)` correction. Standard two-dimensional modular-area integration, with every side and circular current condition proved from the original source, gives

`integral_{Omega_Y} R_e/rho_e = top_e(Y)+lambda*integral_{Omega_Y} D/(y²*rho_e)`.

All integrability is proved; the right side is nonnegative. The original area module now shares the general C² Green slice proof, preserving its public statements.

The proposed pointwise-limit removal of the defect fails in the exact local nodal profile `h(x)=x`. The literal curvature `e²/(x²+e²)^(3/2)` tends to zero almost everywhere, but its integral on `[-1,1]` tends to two. The stronger positive survivor classifies every oriented interval: the limiting curvature is `b/|b|-a/|a|`, including endpoints at the node. This toy is not claimed to be Maass, cuspidal, periodic, or inversion invariant.

Further broad OR searches for nodal/curvature/defect measure/concentration/ground state returned 6310 declarations in 1042 modules. Sources read included the explicit square-root cutoff correction, approximate-identity concentration, and full logarithmic curvature decomposition. No Maass log-concavity or domination estimate was imported from those mechanisms. [Full paper proof and audit](../../../3-formalized/selberg-regularized-curvature-and-nodal-charge.md). [Failed shortcut and fully formalized positive survivor](../../../5-failed/selberg-dropping-nodal-curvature-by-pointwise-limit.md).

### Cycle 29 — augmented source capacity and surviving variation

The actual augmented source `(F_q,e)/rho_e` is now proved C² through original common zeros, with unit squared norm and literal modular permutation covariance. Its derivative energy is exactly the retained regularized remainder. Original coordinates retain amplitude-weighted mean zero; the added coordinate has the nonzero mean `e*(N+1)`. The exact weighted squared-chord mean includes the correction `-2e²*(N+1)/rho_e(z)`.

Original source nonvanishing and zero means supply fixed same-height points whose augmented squared chord exceeds two for every sufficiently small positive regulator. Integral square completion and actual FTC prove the source path comparison

`chord² <= (integral 1/rho_e)*(integral R_{e,1}/rho_e)`.

Every continuity and integrability condition comes from the original source. On a fixed ordered nondegenerate path, the same small regulators satisfy both `pathEnergy > 2/pathResistance` and `sum_j (integral |partial_x U_j|)² > 2`. The latter is the literal squared coordinate-variation sum and does not introduce resistance.

The proposed unqualified regulator-uniform resistance bound fails in the exact local nodal profile. Its resistance is `2arsinh(1/e)=2log(1+sqrt(1+e²))-2log(e)`, diverges, and has finite part `2log 2`; its capacity coefficient tends to zero. The strongest positive survivor includes that full singularity classification and the actual source's fixed variation cost. The toy is not claimed to be Maass, periodic, cuspidal, or modular invariant.

Broad OR corpus searches spanned 3041 modules for weighted/chord/resistance mechanisms, then 88 modules for weighted Cauchy and path energy, 27 for reciprocal-radius primitives, and 85 for variation/coarea/isoperimetry. Read source mechanisms included exact finite resistance completion, complex weighted Cauchy, the rescaled arsinh primitive, and finite projected coarea with explicit isotropy. No unproved isotropy or uniform resistance was transferred to Maass data. [Dependency-closed proof and audit](../../../3-formalized/selberg-augmented-chord-capacity-and-nodal-resistance.md). [Failed shortcut and formalized positive survivor](../../../5-failed/selberg-regulator-uniform-resistance.md).

### Cycle 30 — actual regularized cusp flux and full curvature budget

The actual real unit horizontal average is now differentiated twice using original C² source regularity. Source period one cancels the horizontal second derivative, so its second derivative is the mean planar Laplacian. Actual density decay gives radius and mean convergence to the positive regulator.

The stronger source forcing bound is proved with absolute eigenvalue, without a sign restriction:

Delta rho_e >= -abs(lambda)*rho_e/y².

The general new secant lemma proves actual derivative decay when the function has a finite limit and its second derivative is bounded below by -C/y². Correcting the derivative by C/y makes it monotone; forward and backward unit secants squeeze the derivative to zero. Applied to the actual source, this proves the literal centered Stokes top current tends to zero.

The actual full planar modular domain is constructed and its truncated domains are proved to exhaust its area. Original finite total mass bounds every core mass. Since rho_e>=e, the weighted mass D/(y²*rho_e) is genuinely integrable at fixed e. Source Stokes, the proved top-current limit, and nonnegative retained curvature then give full-domain remainder integrability and

integral_Omega R_e/rho_e = lambda*integral_Omega D/(y²*rho_e).

The full Laplacian is integrable and has zero integral. Original nonvanishing makes weighted mass and retained curvature strictly positive for every hypothetical exceptional source. This does not assert existence of exceptional sources.

Broad discovery used --any for secant/forcing mechanisms, then uniform tails, integrable majorants, and exhaustion. The broadest exhaustion query reached 2856 declarations in 1381 modules. Follow-up geometric/arithmetic discovery reached 3061 declarations in 541 modules. Counts describe index coverage, not reading every result. [Complete paper proof, source mechanisms, and audit](../../../3-formalized/selberg-regularized-cusp-and-full-curvature-budget.md).

### Cycle 31 — quantitative regulator removal and total curvature monotonicity

Actual full-domain amplitude mass is now proved integrable and strictly positive. The full modular domain lies in the unit strip above height one half. The literal primitive -1/y proves inverse-square ray integrability and its exact integral; genuine product integration gives strip hyperbolic area two, bounding full-domain hyperbolic area. Pointwise sqrt(D)<=(D+1)/2 then gives an integrable amplitude-mass majorant from original mass and this area.

The square-root conjecture is proved more strongly than the initial error-e proposal. For d>=0 and e>0, put a=sqrt(d), r=sqrt(d+e²). The exact identity

(a-d/r)*r*(r+a)=a*e²

and 2ae<=r*(r+a) give 0<=a-d/r<=e/2, including original zeros. Applying this to the actual source gives full-domain spectral-density L¹ error at most e. Consequently,

0 <= lambda*integral_Omega sqrt(D)/y² - integral_Omega R_e/rho_e <= lambda*e.

The positive-regulator limit filter is proved nontrivial. Actual total retained curvature converges to lambda times the strictly positive full amplitude mass. It is also antitone in e: decreasing the regulator increases the total curvature budget. This is total-integral monotonicity, not a claim of pointwise curvature monotonicity.

Broad --any discovery used the full corpus index: the first regularization/finite-volume/defect search reached 43095 declarations in 12403 modules; the next square-root/error/area search reached 2353 declarations in 1090 modules. Read mechanisms included exact square-root difference-of-squares remainder control and explicit retained regularization corrections. No numerical experiment or pointwise curvature-limit interchange was used. [Complete paper proof and audit](../../../3-formalized/selberg-quantitative-regulator-curvature-limit.md).

### Cycle 32 — local weak curvature with the nodal contribution retained

For every real eigenvalue and real C² compact test phi supported in the upper half-plane, the actual limiting curvature is now identified as

J(phi)=integral sqrt(D)*Delta phi + lambda*integral phi*sqrt(D)/y².

The original source requires C² regularity only in the upper half-plane. Compact support localizes every test/source product to that open set, making it globally continuous and integrable. First and second test derivatives retain the original support. Two literal directional integrations by parts therefore prove the actual tested source identity without assuming global smoothness of an ofComplex extension.

The scalar regulator bounds give the quantitative estimate

|J_e(phi)-J(phi)| <= e*(integral |Delta phi| + |lambda|/2*integral |phi|/y²).

The absolute eigenvalue strengthens the initial exceptional-only proposal to every real lambda. The actual nontrivial positive-regulator filter then gives convergence. Original nonnegative regularized curvature proves J(phi)>=0 on nonnegative tests. Actual integral linearity and test ordering pass to the limit, with all integral convergence established internally. No pointwise curvature-limit interchange is used.

The wider positive-functional and cutoff searches exposed a further strengthening. If |phi|<=c*psi, then |J(phi)|<=c*J(psi). Every compact K inside the upper half-plane has an actual nonnegative compact C² cutoff chi equal to one on K: square the smooth cutoff constructed by CompactSmoothCutoff. Its source curvature C_K=J(chi) is finite and nonnegative. Hence every C² phi supported in K with |phi|<=c, c>=0, satisfies |J(phi)|<=c*C_K. Compact support of phi follows from K rather than being assumed separately. This is a source-derived local order-zero bound; it uses no representing measure.

All broad discovery used --any. Local Green/nodal mechanisms reached 530 declarations in 95 modules; support/localization/product/continuity reached 26054 declarations in 7965 modules; positive functionals and local measures reached 182 declarations in 44 modules; order-zero/cutoff/domination reached 1088 declarations in 533 modules; compact smooth cutoffs reached 380 declarations in 217 modules. These are index-coverage counts, not claims to have read every result. Read proof mechanisms are recorded in the [dependency-closed proof and audit](../../../3-formalized/selberg-actual-weak-curvature.md).

### Cycle 33 — actual positive curvature measure from original regulator integrals

The actual continuous-test limit and its representing measure are now constructed for every real eigenvalue. A fixed compact cutoff localizes global smooth approximants to one common compact inside the upper half-plane. Its bounded norm rescales the approximation tolerance. A second nonnegative compact C² cutoff has bounded actual curvature values for small regulators, by the already proved smooth-test limit. Positivity bounds the difference between original and approximate test pairings. A complete four-term metric Cauchy argument then proves convergence of the original continuous-test integrals along the actual nontrivial regulator filter.

The resulting continuousCurvature is positive, real linear, monotone, and equals the original weakCurvature on admissible C² tests. Zero extension of every compact continuous upper-half-plane test is proved globally continuous and compactly supported at positive height. Restriction of a supported planar test is compact, and restriction followed by zero extension recovers it exactly. These constructions produce an actual positive linear functional on C_c(H,R), to which the current Riesz--Markov theorem applies.

The constructed curvatureMeasure is regular and finite on compact sets. Every compact continuous test is genuinely integrable, and its integral equals the actual regulator limit. The measure is unique among regular measures with those continuous-test source values. In particular, for every admissible C² planar test,

integral_H phi dmu = integral_C Delta(phi)*sqrt(D) + lambda*integral_C phi*sqrt(D)/y²,
|J_e(phi)-integral_H phi dmu| <= e*(integral |Delta phi|+|lambda|/2*integral |phi|/y²).

All broad searches used --any. Distribution/measure/approximation discovery reached 432 declarations in 241 modules; positive extension/common-support mechanisms reached 2199 declarations in 250 modules; Cauchy/uniform-approximation mechanisms reached 230 declarations in 120 modules; zero-extension/open-embedding/positive-functional mechanisms reached 282 declarations in 112 modules. Counts describe index coverage, not reading every result. [Complete paper proof, source mechanisms, and audit](../../../3-formalized/selberg-actual-curvature-measure.md).

### Cycle 34 — actual modular transport, proved

Next conjecture: original modular amplitude invariance induces invariance of the constructed measure, through literal change of variables on compact source tests. The checked radius_invariant source theorem is available. A broad modular-invariance/curvature-measure/boundary-charge/seam-crossing/coarea/transport query reached 8003 declarations in 2109 modules; promising mechanisms must be inspected and transferred with their source conditions proved.

Concrete proof attempt: complexify the actual real C² radius and reuse SelbergMaassCuspTransport.positive_laplacian_pullback to prove invariance of y² Delta(radius). Together with radius and trace-density invariance, curvatureWeight_eq then proves invariance of the actual hyperbolic density y² curvatureWeight. Transfer the corpus's planar/hyperbolic integral identity to real compact tests, use invariant hyperbolic volume, and pass through the already proved original regulator limits. Regular-measure uniqueness should identify the pushforward. No C-infinity regularity or null boundary charge is assumed. The explicit --any covariance/Jacobian search reached 1187 declarations in 299 modules; the hyperbolic-integral/invariant-density/complexification search reached 151 declarations in 96 modules. These are coverage counts, not claims to read every hit.

Vague convergence on compact continuous tests does not by itself permit replacement by a fundamental-domain indicator. Actual boundary concentration and stabilizer multiplicities must be retained in the quotient budget. Existing nodal curvature and endpoint classification provide evidence against silently deleting concentration, but do not classify the actual source's seam charge.

The complete proof now checks in two new modules: real-to-complex C² differentiation transfers the existing Möbius Laplacian theorem to the actual radius; the exact source decomposition proves invariance of the hyperbolic curvature density. Literal chart change of variables makes every original regularized compact-test pairing invariant. Its proved regulator limit and regular-measure uniqueness give invariance of the actual constructed measure. All measurable preimages retain their full curvature, including possible seam charge. [Dependency-closed paper proof and audit](../../../3-formalized/selberg-actual-curvature-transport.md).

### Cycle 35 — actual curvature has no point atoms

The next explicit --any searches reached 144 declarations in 51 modules for quotient/boundary/nodal mechanisms, 4445 in 410 for partitions/proper actions/stabilizers, and 406 in 120 for atomlessness/potential/capacity/flux mechanisms. The inspected modular fundamental-domain proof uses zero hyperbolic area of its boundary; it does not prove zero curvature measure there. This direct transfer is unjustified, not a proof of a false source theorem.

The initial proposals were continuous weighted partitions for quotient integration and a local curvature-growth estimate from the actual trace's radial square completion and Bottcher.Brolin.RieszFlux.integral_ball_laplacian_eq_boundary_flux. DeningerTransversePartition provides an exact partition-sum mechanism, but its clopen product setting does not itself build a modular partition. A regulator-uniform gradient estimate plus actual C² flux could prove stronger small-ball growth; that stronger estimate remains unproved. The cancellation pivot below establishes point-atom exclusion using continuity alone. Charge on seam curves remains possible.

Cycle 35 pivot proved: ScaledCutoff supplies a localization/scaling mechanism and Bottcher.Brolin.RieszLogIBP proves zero total Laplacian of compact C² tests from the flux identity. The actual proof uses the lighter existing local Green identity with constant source. For chi_r(z)=chi((z-z0)/r), subtract amplitude(z0) from the Laplacian pairing and exploit dimension-two cancellation between r^(-2) derivative scaling and r² area scaling. The Laplacian L¹ norm stays fixed while actual amplitude oscillation vanishes; the continuous spectral-weight term has vanishing r² mass. Positivity and chi_r(z0)=1 bound mu({z0}) by the vanishing actual test pairing. All scaling, support, integrability, and measure-limit passages now check in Lean. The constructed measure has NullSingletonClass and vanishes on every countable set, for every real eigenvalue and without pointwise source nonvanishing. [Complete paper proof and audit](../../../3-formalized/selberg-actual-curvature-no-atoms.md). Local-growth/flux/cutoff --any search reached 150 declarations in 72 modules; cancellation/continuous-potential search reached 6 in 6. Neither count means every result was read.

### Cycle 36 — actual positive compact-orbit descent, proved

Atomlessness removes point charges, not curvature carried by seam curves. The elliptic/proper-action/overlap search reached 32 declarations in 20 modules; the compact-orbit/weighted-descent search reached 185 in 66, both with --any. Inspected ThetaCuspHawkingBMCompactTestUnfolding gives finite translate support on the entire cell, including seams and fixed points; its integral unfolding still invokes hyperbolic-volume boundary nullity and cannot be applied unchanged to curvature. ThetaCuspHawkingBMCompactModularPeriodization.modular_orbit_height_le bounds the height of every orbit by max(y,1/y). Use these source mechanisms to test a positive modular cutoff divided by its orbit sum, with local finiteness, positivity, support, and stabilizer multiplicity proved. WeightedOrbitInvariantExistence's group-carrier mechanism has an injective orbit parametrization, which is not automatic for this action. No quotient budget or normalized partition is assumed.

Cycle 36 conjecture proved: actual curvature integrals of compact continuous tests depend only on their full modular periodization and are nonnegative whenever that periodization is nonnegative. The construction works directly with the SL(2,Z) sum so kernel and stabilizer multiplicities remain literal. Proper discontinuity makes compact-test orbit sums locally finite and mutually overlapping test products a globally finite family. The orbital pairing identity integral g*P(h) dmu = integral h*P(g) dmu follows by justified finite interchange and actual measure invariance. For each compact K, a nonnegative compact b equal to one on K gives w=b/max(1,P(b)). Then P(w)=P(b)/max(1,P(b)), globally between zero and one and exactly one on K. The pairing identity proves representative independence, positivity, and order comparison without a seam-null assumption. This constructs the unique positive real linear functional on the literal range of compact periodization, with convergence of every original regulator pairing. [Complete dependency-closed proof and audit](../../../3-formalized/selberg-actual-positive-quotient-curvature.md).

### Cycle 37 — standard-cell normalization and total quotient budget

The complete scratch proofs now establish the exact factor-two normalization of the full SL(2,Z) sum by the actual projective fibers {A,-A}. The modular height bound and proper discontinuity make every compact test's contributing translates finite over the entire closed cell, so real unfolding and its invariant-density version have all sum/integral interchange discharged. The original planar full domain is identified pointwise with the hyperbolic cell. Indicator transport and exact chart density cancellation then give both the original compact-pairing identity and the full-cell curvature budget.

The EinastoGammaMoments mechanism transfers concretely: the already proved positive original total-curvature integral, transported exactly to the hyperbolic cell, discharges cell integrability by Integrable.of_integral_ne_zero. The original amplitude mass M bounds that cell integral by lambda*M uniformly in the regulator. For every literal compact orbit field F with |F|<=1, the original regulator limit therefore gives 2|Q(F)|<=lambda*M. Every actual normalized compact weight obeys this same finite budget. Exhaustion is not needed for this upper bound; equality of limiting total mass remains separate. No seam-curve mass is dropped. [Paper proof and final audit](../../../3-formalized/selberg-full-cell-curvature-unfolding.md).

The --any pairing/normalization search reached 28 declarations in 20 modules; positive-descent/kernel search reached 15 in 12; total-mass/exhaustion/tightness search reached 155 in 25. Inspected GoldstoneFabriPicassoCorpusApplications has a distinct escaping-mass family despite local convergence; it does not supply a counterexample for the actual Maass source. ScheffeCounting's tail argument assumes equality of total mass and cannot be used circularly to infer the missing identity. LeafTightness derives tails from an established uniform moment, suggesting a source cusp-control analogue. Exact source core/cusp curvature balances and amplitude mass remain available from cycles 30–31.

The essential unsolved step remains the source-derived quarter lower comparison. The new signed finite functional budget supplies upper control only. Continue wide corpus-derived conjecture/proof/fail/pivot work on actual spatial geometry, retaining original compact-core and cusp/Bessel boundary contributions. Selberg remains unproved; the goal stays active.

### Cycle 38 — uniform original cusp control and exact total orbit mass, proved and audited

The initial conjecture sought uniform top-current decay for 0<e<=1 using the bound rho_e<=2. The actual-source proof strengthens it to every positive regulator: 0<=rho_e-e<=sqrt(D) and D/rho_e<=sqrt(D), while nonnegative retained curvature gives Delta rho_e>=-|lambda|sqrt(D)/y². Original amplitude decay supplies a uniform narrow strip for the horizontal mean and the common forcing constant |lambda| beyond one source height. Quantitative forward/backward secants of the corrected derivative then prove uniform mean-current decay, which the original source identity transfers to the literal centered Stokes current. All analytic premises in the secant auxiliaries are discharged by the actual Maass source.

Subtracting the integrable original full and truncated curvature balances gives the exact curvature-tail identity, including the top current. The fixed integrable amplitude dominates every regularized amplitude tail. Its original exhaustion limit and the new uniform current bound prove curvature tails vanish uniformly over every positive regulator. Compactness of the literal modular cell truncations then gives actual normalized compact weights with periodization one on each core and between zero and one globally. Such a weight loses at most the uniform original curvature tail. Passing through the actual regulator limits proves these compact orbit tests approach lambda*M/2 arbitrarily closely. Combined with cycle 37's upper bound, the supremum over the literal compact positive orbit fields is exactly lambda*M/2. A strictly positive compact test also proves the actual constructed curvature measure is nonzero. This does not assert finite total measure on the universal cover.

All four complete scratch proofs, needed source oleans, and serialized final single-module builds passed, without new module warnings. The four modules are wired, all 33 public declarations have only standard Lean axiom dependencies, refreshed index coverage is complete, and repository lint passed. The source results quantify over the original MaassCuspEigenform structure; they neither construct an exceptional eigenform nor prove its impossibility. The spectral quarter comparison remains open. [Dependency-closed proof and audit](../../../3-formalized/selberg-uniform-regulator-cusp-curvature.md).

The explicit --any bounded-functional/uniform-mass/compact-exhaustion/mass-escape/curvature-tail/moment-tail search reached 150 declarations in 42 modules. Inspected MomentWeakConvergence transfers a uniform mass bound to a test approximation bound on an already compact source space; it does not supply a cusp tail. Inspected SecondMomentTailBound obtains tails from an established second moment; such a moment of the Maass curvature was not supplied. The proof above instead derives tails from the original source's secant and amplitude mechanisms. Further --any uniform-secant/curvature/tail discovery reached 737 declarations in 176 modules, and total-mass/compact-cutoff/supremum discovery reached 540 in 364. Inspected WindowTotalSqueeze suggested a window-plus-tail argument; its needed source bounds are proved here. RadialLeakageArcsineMeasure relies on a known explicit density and was not treated as a Maass density identification. Counts describe index coverage, not full source inspection.

### Cycle 39 — exact scalar curvature flexibility, proved and audited

Broad explicit OR searches over arithmetic, graph gaps, and source nodal geometry found no discharged congruence-uniform quarter estimate in the inspected sources: the weighted-graph gap is an explicit premise, while actual source chord energy retains its inverse-amplitude resistance. The next conjecture tested whether the scalar geometric package alone sufficed. The corpus's original positive Eisenstein series, global Fourier uniqueness, full joint smoothness, and differentiated summand bounds supplied an actual test family.

For every lambda>0 the literal model a=E(z,2)^(-lambda/4) is smooth, positive, modular, and decays uniformly at the cusp. Its actual curvature q=y²*Delta(a)+lambda*a is strictly positive and modular. Original summand bounds control q by a and the actual vertical current by (3lambda/2)y^(-lambda/2-1). Proved finite full-domain hyperbolic area gives integrability; exact modular boundary cancellation, literal Stokes, and original current decay yield integral(q)=lambda*integral(a)>0 on the standard cell. Hence the actual scalar-family ratio is every positive number. Choosing lambda=c/2 gives a closed obstruction to every positive uniform scalar comparison, including c=1/4.

All seven complete scratch/source checks and serialized final single-module audits passed; all 91 public declarations passed the final-artifact axiom audit with only standard axioms or none. The positive survivor is the full actual modular family and exact curvature/mass classification, not just a negative logical wrapper. [Complete paper proof and audit](../../../3-formalized/selberg-scalar-curvature-flexibility.md); [scoped failed-route record](../../../5-failed/selberg-scalar-quarter-comparison.md).

This retires only the stated scalar shortcut. Exponential Maass decay, original common component eigen-equations, weighted component zero means, and nodal constraints are not manufactured by the family. The full Maass quarter bound remains unproved. The [next source-current candidate](../../selberg-original-source-conserved-currents.md) comes from the corpus's actual Noether/Wronskian and Lagrange/Gram mechanisms. Its first source module now has nine public declarations with completed scratch, source, targeted-build, axiom, index, and lint audits: original common-eigenvalue current cancellation, a finite real wedge identity, and the distinct regulator forcing. No quotient exactness, period vanishing, or spectral gap is assumed.

### Cycle 40 — original pair-current conservation and regulator forcing audited; comparison open

The original congruence component fields retain the same actual planar eigen-potential -lambda/y². Actual differentiation of F*grad G-G*grad F cancels the mixed first derivatives, and the source eigen-equations cancel its full planar divergence, including at common zeros. The finite real Gram defect is exactly half the sum of squared pair brackets. The literal constant regulator coordinate instead produces divergence -(lambda/y²)*e*F; this forcing is proved from the actual augmented source and cannot be discarded by applying the shared-eigenvalue argument to every coordinate.

`SelbergMaassSourceCurrents` contains these nine audited public declarations. The full complex energy reconstruction is now also proved: D*E_v-(Re B_v)^2=(1/2)*sum|J_qr,v|²+(Im B_v)^2, with B_v=sum conjugate(F_q)*d_v F_q. `SelbergMaassPairPhaseEnergy` proves the finite identity, actual source radial/angular/Fisher instantiations, and component/total phase conservation. `SelbergMaassCurrentTransport` proves exact modular transport with both deck indices and the full Möbius differential. `SelbergMaassCurrentCurvature` proves the positive splitting `R_e³*curvatureWeight=C+e²*gradientDensity`, where C is the total pair-plus-phase square numerator. At every actual common zero, C=0 but the original curvature equals `gradientDensity/e`. All 29 public declarations in these three extensions passed complete scratch, source, final targeted-build, and post-build axiom audits. [Dependency-closed paper proof and certificate](../../../3-formalized/selberg-pair-phase-current-curvature.md).

The source-measure conjecture is now proved in four further modules: actual current-test integrals are antitone and bounded by the original full-curvature limit, so their finite supremum supplies positive and then signed-test limits. Positive functional representation gives `curvatureMeasure = currentMeasure + residualMeasure`. The residual is the actual regulator-gradient weak limit; compact source amplitude minima away from zeros give an O(e²) bound, and regularity plus compact cutoffs prove that the residual is concentrated on the literal common-zero set. All 47 additional public declarations passed final single-module builds and post-build axiom audits. [Dependency-closed proof and audit](../../../3-formalized/selberg-current-nodal-measures.md).

The next three modules identify the actual current density and both invariant source carriers. Extended-real monotone convergence establishes genuine integrability of C/(sqrt(D))³ against every compact test; signed dominated convergence identifies its actual regulator limit. Chart transport and compact cutoffs prove equality with hyperbolic volume weighted by y²*C/(sqrt(D))³. The current measure is absolutely continuous and gives no nodal mass, so current and residual are mutually singular. Exact restriction identities identify them with full curvature off and on the original nodal set. That set's source-derived invariance transports both measures separately. All 39 public declarations passed complete scratch/source checks, targeted final builds, and post-build axiom checks; repository lint passed. [Complete proof and audit](../../../3-formalized/selberg-current-density-identification.md). Residual singularity relative to volume and the congruence-uniform quarter comparison remain open. [Precise source candidate and next test](../../selberg-original-source-conserved-currents.md).

### Cycle 41 — actual quantitative source gap and small-level exclusion

The original first-frequency theorem is reused. Actual gradient covariance, full-cell Stokes with proved cusp-flux decay, and positive source mass are now connected to the literal comparison strip. Its cap maps into the modular cell by a single inversion, giving a factor-two energy bound. Full integrability, hyperbolic coordinate changes, and infinite-height Fubini retain every normalization. The resulting original-source theorem is `3*pi^2 <= 2*lambda*(N+1)^2`; it excludes exceptional principal-congruence sources at every level one through seven. Four audited modules supply 45 public declarations. [Complete positive proof and certificate](../../../3-formalized/selberg-maass-strip-gap.md).

### Cycle 42 — actual all-level deck cancellation and variance

The next conjecture is also proved. The scalar sum of the original deck fields is fully modular invariant, C2, cuspidal at all integral cusps, and has the original eigenvalue. A nonzero sum would be a literal level-one exceptional source, contradicting cycle 41. Thus the actual full scalar trace vanishes at every level. The corpus finite regular averaging operator now has a proved source instantiation: it annihilates the original deck-value vector, whose squared norm is exactly D. Its averaged group displacement energy is exactly D, with factor `1/(2*card Deck)`. `SelbergMaassDeckAverage` supplies 13 audited public declarations. The next positive target is a level-independent comparison of this actual finite-group energy with the physical gradient; no such comparison is assumed. [Proof and next target](../../../3-formalized/selberg-maass-strip-gap.md).

### Cycle 43 — exact original unipotent Fourier filter

The positive projection conjecture is proved. The literal normalized coefficient integral intertwines original integer upper motion with the standard character of the actual residue ring. Complete upper-unipotent averaging retains precisely indices divisible by the level; its complement retains every other index. Actual source continuity, finite-sum integration, and physical Parseval identify the complete arithmetic block variance with exactly the retained complementary Fourier mass, including every original deck coordinate and common zero. The original coefficient vector satisfies the exact finite-character eigenspace law. No path-length estimate or extra spectral hypothesis appears. `SelbergMaassUnipotentFourier` supplies 20 public declarations; its targeted build and all post-build axiom checks passed. The next positive candidate is the complete family of character-weighted filters and its actual inversion coupling. [Paper proof, corpus-derived next candidate, and audit](../../../3-formalized/selberg-unipotent-fourier-filter.md).

### Cycle 44 — all original residue channels and actual inversion coupling

The complete positive character-projection conjecture is proved. The actual congruence deck representation discharges every hypothesis of the corpus Connes projector. Complete character orthogonality and actual unitarity give pair annihilation, self-adjointness, a resolution of the identity, and exact energy conservation. Literal matrix reduction and parameter inversion prove Q_r = U_S P_-r U_S^-1, with the actual original source point S^-1 z retained.

The original coefficient vector is now identified with its vector-valued normalized integral, so every continuous linear readout commutes with its actual Fourier coefficients. Each upper residue projector keeps precisely n congruent to r modulo L. Physical Parseval identifies the full lower-channel mass with the literal finite transfer C_(-r,n mod L) a_n, where C_rs = P_r U_S^-1 P_s. Its complete two-parameter coordinate kernel and exact column-energy conservation are proved. Two modules supply44 audited public declarations. This identifies the actual finite coupling needed for the next quantitative Gram/frequency estimate; no uniform quarter comparison is inserted as a premise. [Dependency-closed positive proof and audit](../../../3-formalized/selberg-character-inversion-coupling.md).

### Cycle 45 — complete arithmetic fibres and actual Gram probability law

**Conjecture → proof:** complete upper–lower–upper collisions over any commutative ring are exactly annihilator translations `(a,c) -> (a+t,c-t)`, with `b*t=0`. The original character phase depends only on `b` and `a+c`, so every collision fibre preserves it. The actual Maass inversion Gram operator therefore has convolution kernel `K_rs(U(a)L(b)U(c)) = |Ann(b)|/L^3 * chi(r*b-s*(a+c))`, exact support given by these words, and diagonal coefficient `L^-2`, including composite levels.

**Stronger conjecture → proof:** `K_00(g)=|K_rs(g)|` and `sum_g |K_rs(g)|=1`. The exact source lower-channel mass is the countable sum of the actual Gram quadratic forms. Two modules add39 audited public declarations. Corpus discovery used explicit OR queries, with2086 declarations/515 modules for arithmetic-fibre leads and51/31 for phase/probability leads; source inspection and transfer reasoning are recorded in the [dependency-closed proof and audit](../../../3-formalized/selberg-inversion-gram-fibres.md).

**Next positive conjecture:** `||v||^2-||C_rs v||^2` equals one half of the normalized complete triple sum of squared displacements `||v-chi(r*b-s*(a+c))*U_(U(a)L(b)U(c))v||^2`. Polarization and the proved exact normalization supply its paper proof. Formalization and the original-source physical gradient estimate remain outstanding. The uniform coefficient four is a target to prove, never an assumed endpoint.

### Cycle 46 — actual phase displacement and complete physical gradient

**Conjecture → proof:** polarization of the actual cycle45 Gram average gives `||v||²-||C_rs v||²` as the complete normalized triple phase-displacement energy. Orthogonal projection splits it exactly into missing upper energy and missing lower energy of the upper projection. The original coefficient identity `P_(n mod L) a_n=a_n` removes the upper loss, reducing the full triple to one actual lower-block phase average. Complete Parseval identifies its convergent integer sum with the literal missing-channel source mass integral.

**Stronger conjecture → proof:** frequency-weighted phase loss equals the actual missing-channel horizontal derivative energy. Original C² regularity and periodicity pass to each literal linear source readout, so the derivative coefficient law and Parseval apply without an endpoint assumption. The retained and missing character fields split the complete original horizontal energy exactly.

**Further strengthening → proof:** the actual coefficient height vector is the derivative of the original coefficient vector, and differentiating its exact upper-character identity preserves the residue eigenspace. Vertical readout Parseval gives the exact missing and retained vertical energies as well. `source_full_gradient_phase_hasSum` combines the original frequency-weighted coefficient phase loss and height-vector phase loss into the complete physical missing-channel gradient. No low modes, derivative components, character phases, or composite-level fibres are removed. Two modules supply47 audited public declarations. [Dependency-closed paper proof, corpus mechanisms, and complete audit](../../../3-formalized/selberg-inversion-phase-energy.md).

**Next quantitative target:** estimate these actual mass and full-gradient phase measures jointly with original inversion gluing across the modular core and cusp. The level-independent coefficient-four full-domain comparison remains to be proved. The exact identities establish the source quantities to estimate; they do not assume the comparison.

### Cycle 47 — actual coherent character seam flux and its physical normal bound

**Conjecture → proof:** complementary projection corners give the exact actual identity `transferLoss = ||(P_s-Q_-r)v||² + ||(I-Q_-r)(I-P_s)v||²`. Thus original phase loss controls the complete coherent character-flux mismatch. Broad explicit OR discovery supplied728 declarations in179 modules; the inspected corner algebra and original Möbius current transport supplied the proof mechanism.

**Source strengthening → proof:** the complete original derivative vector is its actual chart Fréchet derivative. Inversion reverses the physical radial direction under its regular unitary. Actual character conjugacy therefore makes the paired upper-character radial flux exactly `Re <(P_r-Q_-r)F,D_z F>`. The flux is half the literal derivative of projected source mass.

**Energy strengthening → proof:** `||D_v F||²+||D_(i*v) F||²=|v|²*gradientDensity` retains the full original angular remainder. The complete arithmetic triple phase displacement then bounds the squared literal circle flux. Including the actual normal-direction and arc-length factors gives `pairedNormalCurrent² <= (16/3)*transferLoss*gradientDensity` on the original modular core arc, uniformly in level. Two modules supply29 audited public declarations. [Complete positive proof and audit](../../../3-formalized/selberg-character-seam-flux.md).

**Next positive test:** attach these currents to the integrated characterwise core–cusp energy identity with the actual Bessel forms, complete modes, and angular remainder retained. Prove the resulting bulk comparison from the original source; the spectral coefficient four remains a target and is not an input assumption.

### Cycle 48 — original projected dynamics, core Green identity, and complete observed cusp forms

**Conjecture → proof:** fixed continuous linear observations commute with both original real derivatives, preserve the actual Maass scalar potential, and yield the full projected-mass Laplacian `Delta M_r=2(E_r-lambda*M_r/y²)`. Actual block commutation and T transport discharge the characterwise physical side-matching condition.

**Integrated strengthening → proof:** ordinary two-dimensional Green integration retains the actual circular normal current. The original channel quarter energy is exactly `topCurrent/2 + pairedArcIntegral/2 + (lambda-1/4)*coreMass`, with all mass and derivative integrability proved from the source.

**Cusp strengthening → proof:** every fixed observation retains original congruence invariance, eigenvalue, and decay at every integral cusp. It is zero or a genuine same-level Maass cusp eigenform. Both cases give the complete observed Bessel boundary-square identity, convergence of both series, and the matching outgoing-flux/spectral-tail-mass identity. Three modules supply52 audited public declarations. [Complete positive proof, certificate, and remaining assembly](../../selberg-character-core-green.md).

**Next exact test:** sum over the actual character-coordinate observations and identify their total normalized outgoing flux with half the unit-period top current. Adjoin the proved core identity with its actual arc term, then test a source-derived quarter lower bound. The finite assembly and uniform quarter comparison remain unproved; no endpoint is assumed.

### Cycle 49 — complete character core–cusp gluing and integrated arithmetic seam control

**Normalization conjecture → proof:** summing every actual upper-character coordinate mass and using original unit-period transport removes the level-width normalization. Differentiating the physical mass equality proves `sum readoutFlux = topCurrent/2`. Genuine tail integrability, including zero observations, identifies the full observed tail sum with the literal unit-strip character mass.

**Gluing conjecture → proof:** every complete cusp boundary-square identity now attaches to the original character core. The cutoff current cancels exactly, leaving
`coreQuarter_r + boundarySum_r + squareSum_r = pairedArcIntegral_r/2 + (lambda-1/4)*(coreMass_r+tailMass_r)`.
Finite coordinate/infinite mode exchange also identifies the boundary form with the literal original projected Fourier-vector series and precisely its residue-class modes.

**Integrated estimate conjecture → proof:** source continuity supplies actual arc integrability. Square completion on the half-length arc and the exact phase-current bound prove `(pairedArcIntegral_r/2)^2 <= (2/3)*integral_arc(transferLoss_r*gradientDensity)`. Thus the full glued balance has a quantitative original-source seam estimate. One module supplies28 audited public declarations. [Full proof and audit](../../selberg-character-core-green.md).

**Next positive target:** use the original residue Fourier form and phase/angular decomposition to compare this coherent seam response with the positive bulk terms. The full uniform quarter comparison remains unproved; no trace-to-area or coercivity premise has been inserted.

### Cycle 50 — original conserved dilation stress and full physical Rellich identity

**Stress conjecture → proof:** the original Maass inverse-square potential forces only the vertical stress divergence. Contraction with the physical dilation vector cancels that forcing against the tensor trace. The source's C² regularity gives a C¹ conserved current, including at source zeros.

**Integration conjecture → proof:** both actual two-dimensional Fubini descriptions of the modular core yield the full Green formula with side jump, top, and complete curved arc. Applied to the conserved original stress, it proves `radialBoundary + lambda*massBoundary = angularBoundary + sideFlux(Y) + topFlux(Y)`. Angular energy and the inverse-cube spectral mass remain literal source quantities.

**Positive estimate → proof:** positive exceptional lambda and actual weighted arc mass give `radialBoundary <= angularBoundary + sideFlux(1) + topFlux(1)`. Three modules supply45 audited public declarations. [Proof, corpus provenance, exact audit, and phase-loss continuation](../../selberg-maass-dilation-stress.md).

**Next conjecture:** apply the exact identity to every original phased three-block displacement readout. Its full normalized norm and derivative sums recover inversion-transfer loss, providing an arithmetic radial/angular balance for the previous coherent-seam estimate. The sharp uniform full-domain quarter comparison remains unproved.

### Cycle 51 — actual arithmetic phase-loss Rellich integrals

**Fixed-observation conjecture → proof:** every three-block phase displacement and original deck coordinate is a fixed continuous linear readout. Its complete normalized squared sum is exactly inversion-transfer loss. Physical differentiation commutes with every readout, so the same arithmetic identity holds for the full radial and angular source derivatives.

**Integral conjecture → proof:** sum every original Rellich identity and justify all finite-sum/integral exchanges using source regularity. This gives the literal integral identity `radialPhaseLoss + lambda*massPhaseLoss = angularPhaseLoss + sidePhaseFlux + topPhaseFlux`, retaining both paired arc points and every original side/top contribution. Positive exceptional spectral mass gives the corresponding radial phase-energy estimate.

The module has25 public declarations and passed scratch/source, final targeted build, post-build standard-axiom, source-hash, API/search, and unique-wiring checks. Global lint initially caught two concurrently added, unrelated HTGeometry modules awaiting umbrella wiring. [Complete phase proof, audit status, and next mixed-loss square conjecture](../../selberg-maass-dilation-stress.md).

**Next strengthening:** prove a source-and-derivative transfer-loss bound for the coherent character mismatch. The card records two precise candidate positive square decompositions and their proposed bilinear consequence. This connects the phase Rellich bound to the seam estimate; the full uniform quarter comparison remains unproved.

### Cycle 52 — both transfer losses control the coherent seam and full quarter balance

**Square conjecture → proof:** exact original projection corners give two positive square decompositions, bounding the coherent mismatch diagonal between minus the transfer loss and phi times that loss. Real polarization, scalar rescaling, and the corpus's nonnegative-quadratic lemma prove `mismatchPair(v,w)^2 <= phi^2*lossEnergy(v)*lossEnergy(w)` with no angle or nonzero-loss premise.

**Original-source strengthening → proof:** the actual paired radial flux uses the same mismatch pairing. Its physical outward normal factor gives a nonnegative quadratic involving weighted source phase mass, the complete paired current, and radial phase energy. Both reflected arc points and their exact factor2 are retained. Source regularity proves all needed integrability.

**Integrated strengthening → proof:** `(integral pairedArcCurrent / 2)^2 <= (phi^2/4)*massPhaseBoundary*radialPhaseBoundary`. Substituting the actual phase Rellich identity retains the positive spectral phase-mass term and all angular, side, and top stresses. The exact original core–cusp balance substitutes for the seam response without removing any Bessel square or original mode. One module provides26 fully checked public declarations. [Complete proof, audit, and next phase-stress target](../../selberg-character-mixed-loss.md).

The full uniform quarter comparison remains unproved. Next identify aggregate phase stress and its actual unit-translation symmetry, evaluate the full vertical side flux, and connect that record to original cusp Fourier data.

### Cycle 53 — full phase stress, translation symmetry, and exact physical side/top flux

**Mixed Gram conjecture → proof:** polarizing the complete phase observation norm law recovers the original real mixed transfer loss. The actual transfer's input character gives exact upper-block covariance; both diagonal and mixed losses retain unitary invariance. All three physical phase stress components are thereby identified without dropping mixed derivative terms.

**Boundary conjecture → proof:** original source/derivative transport proves unit-translation symmetry of the complete tensor. Its horizontal and mixed stresses match at both vertical sides. The full dilation side jump is exactly horizontal phase stress. Source regularity justifies every finite-sum/integral exchange, giving the actual side integral and the top integral of `x*phaseStressXY+Y*phaseStressYY`.

**Original-source assembly → proof:** substitute this explicit physical boundary record into the exact phase Rellich identity and complete original core–cusp bound, retaining angular energy, spectral mass, Bessel squares, and every side/top term. One module supplies28 public declarations; full scratch/source/final/axiom/hash/API-search/wiring/index/lint audits passed. [Complete proof and next arithmetic kernel estimate](../../selberg-phase-stress-side-flux.md).

The full quarter endpoint remains unproved. Next express the mixed boundary Gram loss through the actual arithmetic convolution kernel and test its phase-sensitive weighted Fourier/Bessel estimate, retaining exact annihilator fibres.

### Cycle 54 — original arithmetic cross-frequency current and positive cusp-tail kernel

**Complex kernel conjecture → proof:** actual projector adjoints identify the full complex transfer Gram form. Its convolution formula retains first-slot conjugation and every composite-level arithmetic fibre phase. Original coefficient residue eigenspaces give exact off-residue cancellation.

**Wronskian conjecture → proof:** both actual modal ODEs cancel their shared Maass potential. The full complex mixed current has derivative `(k_n²-k_m²)*B(c_n,c_m)`. Original coefficient/derivative square integrability makes current and derivative integrable, proving current decay at infinity. Thus `W_nm(Y)=(k_m²-k_n²)*H_nm(Y)` for the actual infinite-tail kernel.

**Quantitative conjecture → proof:** the full finite complex quadratic of `H` equals the literal integrated transfer-loss energy, hence is nonnegative. A two-mode phase test yields `norm(H_nm)² <= Re(H_nn)*Re(H_mm)`, and the exact boundary law gives the corresponding squared-frequency-weighted bound for every original mixed current. Zero-loss, diagonal, opposite-index, and composite-level cases are retained. One module supplies30 public declarations. [Complete proof, verification, and next weighted top-boundary comparison](../../selberg-kernel-wronskian.md).

The full quarter endpoint remains unproved. Next derive the exact horizontal Fourier weight in the physical top stress and combine it with the new current/tail relation, retaining the complete signed-frequency quadratic.

### Cycle 55 — duplication audit stops reconstruction-first detour

The user challenged whether the route was repeating earlier work. Source inspection confirmed that actual Maass coefficient absolute summability (`SelbergMaassBoundaryTrace.coefficient_norm_summable`), complete horizontal/vertical readout Parseval and missing-channel gradient Fourier identities (cycle46), and full core–cusp gluing (cycle49 and earlier TraceArea) already exist. The new C1 helper was not shown to be an exact duplicate, but its necessity for the missing quarter estimate was not established. The unverified reconstruction scratch was not promoted or wired; no new Lean module or final build was produced in this attempt.

The valid cycle54 intermediate identities remain checked. Their positivity/Cauchy bound has not been proved to control the complete frequency-weighted boundary/core form. Require a dependency-closed paper inequality that improves that remaining all-level estimate before adding more infrastructure. [Audit evidence and deferred-draft record](../../selberg-weighted-top-fourier.md). Full Selberg remains active and unproved.

### Cycles 56–61 — arithmetic routes past 3/16: where each one stops (paper, 2026-09-25)

Pivot from cusp-energy routes (capped at bounded level, `3-formalized/selberg-strip-hardy-gap.md`) to arithmetic ones. Notation: exceptional parameter ν (λ = 1/4 − ν²), level q, vol(Γ(q)\H) ≍ q³. Sources read: Humphries, *Density theorems for exceptional eigenvalues for congruence subgroups* (arXiv 1609.06740, §5), Pascadi (arXiv 2404.04239, 2511.08445), Blomer–Pascadi (arXiv 2607.24311), Buttcane (arXiv 2205.14194), corpus `selberg-maass-symmetric-power-attempt.md` §6.

**Cycle 56. Conjecture:** Kuznetsov density for Γ(q) combined with the Sarnak–Xue multiplicity (corpus `half_pred_le_finrank`) goes past 3/16. **Attack.** Humphries: #{ν ≥ α₀} ≪ q^{2+ε}X^{−2α₀}(q + √X/q). In general, if the diagonal is q^f, the Kloosterman term is q^k√X and one exceptional form contributes multiplicity q^m, a contradiction needs α₀ > (f − m)/(4(f − k)). For Γ(q): f = 3, k = 1, m = 1, giving exactly 1/4, and the cap does not depend on X. The dominant local factor is S_{a(q)}(m,n;q²) = q·[m ≡ nā² (q)]: no cancellation exists there (Humphries: "we cannot do better than this when β = α"). **Verdict: REDISCOVERED (structural cap).** Survivor: the exponent law. Getting past 1/4 needs m > k, i.e. cancellation among the Kloosterman sums over moduli c′ coprime to q.

**Cycle 57. Conjecture:** density restricted to one SL₂(F_p)-type ρ at a time beats 3/16. Uniform per-ρ density p^{1−8α₀} would give ν ≤ 1/8. **Attack.** Project with P_ρ = (dim ρ/|G|)Σ_g χ̄_ρ(g)g. For (c,p) = 1 the ρ-projected Kloosterman sum factors as (dim ρ/|G|)·S(mp̄, np̄; c)·B_ρ, where the Bruhat form n(x)w_c n(y) gives B_ρ = p·[m ≡ n (p)]·Σ_s χ̄_ρ(w_c n(s))e(ns/p). For cuspidal ρ this is a torus Kloosterman sum, of size O(p^{3/2}). The projection admits every modulus c coprime to p, while the diagonal drops by dim ρ²/|G| ≍ p⁻¹. The ratio of Kloosterman term to diagonal therefore gets worse by ≍ p^{3/2}. **Verdict: FALSE.** Survivor: the factorisation, known from Bessel functions of GL₂(F_p).

**Cycle 58. Conjecture:** a different twist family in the Luo–Rudnick–Sarnak forced-zero argument beats the threshold 1 − 2/(d+1). **Attack.** The families tried are quadratic twists, cubic twists (Heath-Brown's cubic large sieve), class-group characters of Q(√−q), highly ramified twists χη⁸, and base change to totally real towers with bounded root discriminant. Each has thresholds ≥ 1, 1 − 1/d, 1 − 2/(dk), or only excludes |1 − 8ν| ≲ 1/log rd_L. The last holds because the forced zero has order n = [L:Q] but log conductor is also ∝ n (Stark–Odlyzko). **Verdict: FALSE.** Survivor: the family law σ₀ > log(C/F)/(log C + log F) (F = family size, C = conductor, Deligne-quality root-number averaging). Characters mod q with exact orthogonality are optimal among GL₁-twist families of one modulus.

**Cycle 59. Conjecture (theta barrier):** every argument whose inputs also hold in weight 1/2 with theta multiplier stops at 3/16. **Evidence.** In weight 1/2 the bottom eigenvalue (1/4)(3/4) = 3/16 (ν′ = 1/4) is attained by theta series. On Γ₀(4) ∩ Γ(p) the functions θ_f(z) = Σ_n f(n mod p)e(n²z), f even, span the even Weil representation of SL₂(F_p), of dimension (p+1)/2, at eigenvalue 3/16. Salié sums obey the same Weil-quality bounds. So the density × multiplicity count p ≤ p^{3−8·(1/4)} = p is *attained* in weight 1/2, and Selberg's Kloosterman-zeta abscissa 3/4 is a genuine pole there, caused by the global square roots x = ±√(mn). **Verdict: REDISCOVERED in essence** (the sharpness of 3/16 in weight 1/2 is classical). The multiplicity-saturation reading is not found in the screened literature. Survivor: a proof beyond 3/16 must use an input that fails for the weight-1/2 theta multiplier. Known inputs of that kind are GL₂ functoriality (Gelbart–Jacquet, Kim–Shahidi), Hecke operators at primes rather than p², and the SL₂ monodromy of Kl₂ at squarefree moduli. The weight-0 analogue of the Salié bias exists only at square moduli: S(m,n;p^{2j}) = p^j Σ_{y²≡mn (p^j)} e(2y/p^{2j}).

**Cycle 60. Conjecture:** amplified Kuznetsov with bilinear Kloosterman bounds (Kowalski–Michel–Sawin type) breaks the barrier. Such bounds avoid the theta barrier. **Attack.** Amplify one exceptional form by a = λ̄_π on [M,2M]. The spectral side is ≫ q⁻¹M²X^{2ν}. The geometric side is M + q⁻¹Σ_{c≤XM, q|c} c⁻¹|Σ_{m,n} a_m ā_n S(m,n;c)|. With M = c^θ, the argument beats 1/4 iff the bilinear form is ≪ √c·‖a‖²·M^{1/2}c^{−δ}. That means beating the Cauchy–Schwarz diagonal, a saving ≥ c^{θ/2} over Weil. The record is c^{1/32} at θ = 1/2 (Blomer–Pascadi 2026), against c^{1/4} needed; PV completion meets the threshold exactly at θ = 1 with no margin. Voronoi on n turns the needed input into shifted convolution sums Σ_m λ(m)λ̄(m + kc), k ≤ c/M. Their spectral theory is at level c ≡ 0 (q), which contains π. **Verdict: FALSE with current technology, and CIRCULAR after Voronoi.** Survivor: the sharp threshold "diagonal + c^δ" for type-II Kloosterman sums of length c^θ.

**Cycle 61. Conjecture:** the large sieve over moduli supplies the corpus hypothesis H_η for free. For K_q = Kl_d(·;q)/q^{(d−1)/2} and q ∼ Q prime, Σ_q |Σ_n b_n K_q(n)|² ≪ (N₀ + Q²log Q)‖b‖², because distinct moduli are quasi-orthogonal on intervals of length ≥ Q². This would give η = 1/2, i.e. ν ≤ 13/120 < 7/64. **Attack.** The forced zero is used through the pole of Γ(u) at u = 0, and the dual must be expanded on the line where L(1+δ−it, Λ̃⊗χ̄) converges absolutely. There its mass sits on the first terms n = 1, 2, …, whose weights ā(n)n^{−1−δ} are absolutely summable. The per-q dual is a fixed combination of Kl_d(n̄N; q) with n small, and a large sieve cannot make one fixed argument cancel over q. Balanced dual lengths on other contours need L-values inside the strip, i.e. the same family again. At even prime powers, stationary phase gives Kl_d(1; p^{2j}) = p^{j(d−1)}Σ_{y^d≡1} c_y e(dy/p^{2j}). When gcd(d, p−1) = 1 the root y = 1 alone gives |Kl_d(1;p^{2j})| = p^{j(d−1)}, a non-oscillating full-size term. So prime-power moduli must be left out of the family. **Verdict: FALSE.** Survivor: the open core is exactly moduli cancellation of Kl₁₅ at fixed arguments m ≤ Q^A over squarefree moduli. Any η > 0 beats Kim–Sarnak. It is a GL(15) problem: Buttcane (Forum Math. 2023) built the GL(3) Kuznetsov formula for hyper-Kloosterman sums; nothing exists for d ≥ 4.

**Cycle 62. Conjecture (joint (∞, p) bound, after Yang arXiv 2011.09054, withdrawn):** for exceptional ρ with parameter t, t + r_p(ρ) ≤ sup over non-exceptional ρ′ of r_p(ρ′). Hecke operators at primes do not exist in weight 1/2, so this would be an input that passes the theta barrier, and with Ramanujan at a single prime it would imply Selberg. **Attack.** The mechanism reads the Petersson geometric side Σ_c S(1,p^n;c)c⁻¹J_{k−1}(4πp^{n/2}/c) (which is O(n) by Deligne) through the Maass Kloosterman zeta Z_{1,p^n}(s). At an exceptional pole s_j = 1/2 + t_j the residue of Z_{1,p^n} carries (p^n)^{1/2−s_j} = p^{−nt_j}, and the J-Bessel Mellin factor carries (p^{n/2})^{2s_j−1} = p^{nt_j}. They cancel exactly, leaving |ρ_j(1)|²λ_j(p^n)M_{J}(−2t_j). This holds for every pair (m,n) at argument 4π√(mn)/c. So holomorphic spectral data (Deligne) cannot see t: exceptional eigenvalues live where J-Bessel test functions vanish (x → 0, i.e. c → ∞). **Verdict: FALSE as a mechanism for the t-part.** It agrees with the author's note "proof of Theorem B is incomplete". Survivor (paper sketch; the convergence of the tempered spectral integral on Re s = 1/2 + ε is not yet checked): **(Y′)** max over exceptional ρ of r_p(ρ) ≤ sup over non-exceptional ρ′ of r_p(ρ′). This is a statement at the finite place only, so it does not move Selberg.

**Correction to cycle 62 (survivor Y′ withdrawn).** In the Kuznetsov formula the Maass transform of J_{k−1} is ϕ̃(t) = (1/sinh πt)·2 sin(πit)cos(π(k−1)/2)/(−4t² − (k−1)²). This follows from ∫₀^∞ J_μJ_ν dx/x = (2/π)sin(π(μ−ν)/2)/(μ²−ν²), and it vanishes identically for even k. Every Maass term of the Kloosterman-zeta expansion therefore integrates to zero form by form. An exceptional residue is cancelled by the same form's own term on the shifted contour, not by the tempered forms. The estimate used for Y′ bounded that shifted term by the tempered sup R, and that step is invalid. The Petersson formula is **Maass-blind**, so it gives no information on exceptional forms at any place. Y′ is withdrawn. Yang's route has the same gap in both its t-part and its r-part.

**Cycle 63. Conjecture:** twisted multiplicativity of Kloosterman sums in the modulus, together with Weil's bound, forces cancellation over moduli. Twisted multiplicativity is the only remaining non-local, non-functorial structure. **Attack.** Build fake data: choose prime-modulus values S′(a,1;p) = 2√p·cos θ′_p(a) with cos θ′_p(a) = (Sato–Tate angle) + p^{2t−1/2}, and extend by twisted multiplicativity. The prime moduli alone then give Σ_{p≤X}S′/p ≍ X^{2t}/log X, a pole of the Kloosterman zeta at 1/2 + t. Weil's bound and vertical Sato–Tate are unchanged, because the bias is o(1) per modulus. **Verdict: FALSE.** Survivor, stated exactly: Selberg for Γ₀(q) ⇔ for all m, n the smoothed sums Σ_{q|c} S(m,n;c)c⁻¹w(c/X) are ≪_{q,m,n,ε} X^ε at fixed level q. The missing input is horizontal equidistribution of Kloosterman angles at a fixed argument with a power-saving rate. That is Katz's horizontal problem, open even for Kl₂ over primes (no sign-change result for prime moduli). Moduli c = q₁q₂ with q₁ fixed turn it into "horizontal Kl_d does not correlate with trace functions of the modulus", which is no easier.

**Cycle 64. Conjecture:** the SL₂(F_p) symmetry of the exceptional eigenspace V of Γ(p) spreads its cusp-strip mass evenly over the unipotent character classes a mod p. Classes with |a| ≍ p have frequency ≍ 1. If true, the modal Hardy law (`SelbergMaassModalHardyLaw`) would fail for every exceptional λ at every prime p. **Attack.** The symmetry that actually holds is local. The GL₂(Z_p) torus preserves the K(p)-fixed space, so the ONB-summed coefficient norm factors as Σ_i|ρ_i(n)|² = |λ_π(n)|²·W(n mod p), with W constant on square classes. The torus element γ_u ∈ SL₂(Z) moves the cusp ∞, so it does **not** preserve the strip mass at ∞. The strip mass of the class-a component is W·Σ_{n≡a}|λ(n)|²B_ν(n/p), and B_ν(x) ≍ x^{−2ν} for x ≪ 1 but decays like e^{−4πY₀x}. So strip mass still sits on |n| ≪ p. With the true B_ν the balance is the negative constant Φ_ν of `3-formalized/selberg-strip-hardy-gap.md`. A naive power-law weight without the exponential decay gives a false "proof of Selberg"; that pitfall is recorded here. **Verdict: FALSE.** The strip no-go stands. Survivor: none new (the factorisation of W is standard).

**Cycle 65. Three remaining global mechanisms, each tested once.**
(a) *Unitarity of lifts.* The residual Speh representation Sp(u,2) on GL₄ has archimedean component u(1,2)|det|^{ν} × u(1,2)|det|^{−ν}. This is a Stein complementary series, unitary for every 0 < ν < 1/2. The Saito–Kurokawa / theta lift of u to PGSp₄ lies in the stable range (Mp₂, O(3,2)), so its archimedean component is unitary for every ν (Li). Lifts to O(p,q) with dim V large likewise preserve unitarity. **FALSE:** local unitarity never excludes ν ∈ (0, 1/2).
(b) *Stark–Odlyzko positivity for L(s, u×ū).* The archimedean term ½ψ((σ−2ν)/2) is very negative only when 2ν is close to σ > 1. This gives only 1/2 − ν ≫ 1/log N (no small eigenvalues near 0). **FALSE** for the quarter bound.
(c) *Level-one sibling.* For SL₂(Z) the quarter bound is elementary (λ₁ > 3π²/2). The corpus's cusp-energy methods work only at bounded level, and the analogous level-one question for SL₃(Z) is already open: Miller (Crelle 2001) proves only that *almost all* cusp forms are tempered at ∞. This is a real open problem the corpus's methods might reach. It is not Selberg's conjecture, but it is the level-one input a Coxeter-cell GL(d) Kuznetsov approach to H_η would need (see cycle 61).

**Cycle 66. Conjecture (Selberg's method one rank up):** Buttcane's GL(3) Kuznetsov formula for hyper-Kloosterman sums (arXiv 2205.14194, Thm 1/3/4), with Deligne's bound |Kl₃(c)| ≤ 3c in place of Weil, excludes complementary SL₃(Z) cusp forms with Re μ > 1/6. By the same token Kl_d with Deligne would give θ_d ≤ 1/(2d). Applied at congruence level to Sym²π (Sym⁴π) of an exceptional GL₂ form, this would give ν ≤ 1/12 (1/40), far past Kim–Sarnak. **Attack (source text of Buttcane §0–1):** "the hyper-Kloosterman zeta function converges on Re(s_i) > 0, but there are poles of the Mellin transform of the Whittaker functions of automorphic forms on Re(s_i) = 0, so we win for the long element, but not for the hyper-Kloosterman sums." For Kl₂ Selberg has room 3/4 − 1/2 = 1/4 between Weil's abscissa and the tempered line; for Kl₃ the room is **zero**. The trivial spectral bound C³X^{1/2+ε} exceeds the Deligne bound C^{3+ε}. The w₅ term has no canonical spectral expansion (the F̂^d(μ) are not unique), so a clean pole argument is unavailable. My heuristic "tempered at d/2, Deligne at (d+1)/2" is wrong for d ≥ 3. **Verdict: FALSE.**
**New insight retained.** Buttcane: the spectral side "concentrates near the self-dual cusp forms, i.e. the symmetric squares", with parameters (a+r, −a+r, −2r), r ≪ X^ε. At congruence level (his text: the analysis "applies nearly verbatim if one changes the particular discrete group, nebentypus, cusp") Sym²π of an exceptional π has μ = (2ν, 0, −2ν). That is exactly his "low-lying complementary" error term C^{3+3θ+ε}X^{ε−1} with σ = 2ν. So **hyper-Kloosterman moduli sums are a direct probe of Sym²(exceptional GL₂)**, with geometric side bounded by Deligne. The open core is precise: the tempered main term (size C³X^{1/2}) must be evaluated asymptotically, to error C^{3−δ}, for m = n with positive weights. If that works, the complementary term C^{3+6ν}X^{−1} (X ≳ C) is detected once 6ν > 1 − δ′. The analogous Kl₅ / GL(5) formula would probe Sym⁴π with exponent 4ν. Deciding whether this beats 7/64 requires the GL(5) hyper-Kloosterman Kuznetsov formula, which does not exist yet.

**Cycle 67. Conjecture (Sym² probe with small X):** In Buttcane's Theorem 3 at congruence level with X < C, the term of Sym²π for an exceptional π exceeds every other term for some range of C and X, which bounds ν. **Attack (source: Buttcane Prop. 14 and §5.5.2):**
- The complementary weight is F̂^d(μ) ≪ C^{3+3x}X^{2x−1}‖μ‖^{1+x}, with B-part C^{3+3x}X^{−1}. For Sym²π, x = 2ν.
- The long-element term has trivial bound C^{9/2}X^{−1}; the tempered spectrum C³X^{1/2}; Deligne on Kl₃ gives C^{3+ε}.
- With trivial bounds everywhere, the complementary term C^{3+3x}X^{−1} is always below C^{9/2}X^{−1}, since x < 1/2. This is the uncertainty principle Buttcane notes.
- **Bootstrap.** The long-element sums are a short c₁-sum (c₁ ≲ C/X) times a long c₂-sum (c₂ ~ C²) of Kl₂-type sums. GL(2) Kuznetsov over c₂ saves (C²)^{1/2−2ν}, giving L_E ≲ C^{7/2+4ν}X^{−1}. Then Sym²-term / L_E = C^{2ν−1/2}, and a contradiction needs ν > 1/4. That is **exactly Selberg's 3/16 again**.
- **Bilinear bootstrap.** Kuznetsov in both c₁ (length C/X) and c₂ gives L_E ≲ C^{3+6ν}X^{−1/2−2ν}, and Sym²-term / L_E = X^{2ν−1/2} ≤ 1. The two terms balance exactly at X = 1.

**Verdict: FALSE.** Buttcane's identity is a precise Sym²–GL₂ reciprocity: Sym²π on the GL₃ side is matched power-for-power by π ⊗ π inside the long-element term. Survivor: the balance is exact at every step, which independently confirms the theta-barrier picture. Any gain has to come from an input that breaks this reciprocity, such as a structure of long-element Kloosterman sums that is not a product of two Kl₂ factors.

**Cycle 68. Conjecture (amplified Sym² probe past the reciprocity):** use Buttcane's Theorem 1 in the range X ≳ C, where the long-element term vanishes. Amplify with α_m = conj λ_{Sym²π}(m) on m ≤ M and bound the rest of the spectrum in absolute value by the GL(3) spectral large sieve. **Attack.** Condition (2) of Buttcane forces X ≳ C·|m₁²m₂n₁n₂²|^{1/3}, i.e. X ≳ CM for arguments of size M. Then the amplified Sym² term is MC^{2+6ν} and the diagonal of the rest is C³X^{1/2}M = C^{7/2}M^{3/2}. A contradiction needs C^{6ν−3/2} > M^{1/2}, impossible for ν < 1/4. Without amplification (M = 1) this is again ν > 1/4. **Verdict: FALSE.** Amplification pushes X up by exactly the amplifier length.
**Survivor (sharpens the H_η bridge of cycle 61).** For d = 2 there is room 1/4 between Weil's convergence line and the tempered spectrum, so Ramanujan at level one implies moduli cancellation for Kl₂. For d = 3 the room is zero (Buttcane): even full temperedness of SL₃(Z) forms does **not** give power saving in Σ_q Kl₃(m;q)q^{−1}w(q/Q). The trivial spectral bound already exceeds Deligne, and cancellation *among tempered forms* is needed. The same heuristic applies to d = 15. So H_η(15), the input needed to beat Kim–Sarnak via moduli-averaged LRS, is a Linnik–Selberg-type conjecture for hyper-Kloosterman sums, strictly stronger than the Ramanujan conjecture for GL(15) at level one. The corpus card `selberg-maass-symmetric-power-attempt.md` §6 had suggested GL(15) Ramanujan bounds might suffice; they do not.

**Cycle 69. Conjecture (non-unitarity of objects built from an exceptional π on exceptional groups):** an exceptional π yields a residual or theta-lifted automorphic form on G₂ whose archimedean component is non-unitary, which is a contradiction. **Attack.** On both GL₂-Levi parabolics of G₂ the Langlands–Shahidi constant terms involve L(s,π), L(s,π,Sym³⊗ω⁻¹) and L(2s,ω). For non-dihedral π, Sym³π is cuspidal (Kim–Shahidi), so these are entire and there is no residual spectrum from π. Continuous-spectrum constituents Ind(π_ν|det|^{it}) are unitary because π_ν is. The Rallis–Schiffmann lift to G₂ is the restriction of the (Mp₂, O(3,4)) theta lift, which is in the stable range (dim V = 7 ≥ 4), so it is unitary for every ν (Li). **Verdict: FALSE.** Survivor: local unitarity on G₂, GL₄ (Speh) and O(p,q) never sees ν ∈ (0, 1/2). The constraint must come from an inequality, not from unitarity.

**Cycle 70. Conjecture (non-product long-element structure breaks the Sym²–GL₂ reciprocity):** the GL(3) long-element Kloosterman sums S(m,n;D₁,D₂) at non-coprime moduli carry arithmetic that is not a product of two Kl₂ sums, and that input is invisible to π ⊗ π on the GL(2) side. **Attack (source: Blomer–Buttcane, Crelle 2019, arXiv:1512.01152, (1.1)–(1.3) and Theorem 5).** Their global decomposition writes every S(m₁,m₂,n₁,n₂;D₁,D₂) as a sum over factorisations D₁ = e₁e₂e₃, D₂ = f₁f₂f₃ of Ramanujan sums S(0,·;eᵢ) times Kl₂ factors, times a C₁-sum Σ_{C₁ mod e₃/E₃} S(·C̄₁; e₃/E₃)·S(·C₁*; f₃/E₃). So the only non-product part is a correlation Σ_C Kl₂(aC̄)Kl₂(bC). At D₁ = D₂ = p it is exactly p+1 for p ∤ m₁m₂n₁n₂ ((1.3)): the trivial summand of Kl₂ ⊗ Kl₂ = Sym²Kl₂ ⊕ 1. The rest is Sym²Kl₂, again GL(2) data. **Verdict: FALSE.** The long-element arithmetic is globally GL(2) (Kl₂ and Kl₂ ⊗ Kl₂), so it cannot break the reciprocity of cycle 67. Survivor: the reciprocity is arithmetic as well as spectral. At every modulus, long-element GL(3) sums are Kl₂ ⊗ Kl₂, and the diagonal constant p+1 is the trivial constituent. A reciprocity-breaking input must therefore come from outside Kloosterman arithmetic entirely: archimedean (Whittaker) or global (functoriality). The w₀ Bruhat decomposition and phase invariance are being formalised as GL(3) infrastructure (`GL3LongElementCell`, card `gl3-automorphic-foundations.md`).

**Cycle 71. Literature correction, then conjecture (Iwaniec's GL₂-only route has a Deligne-free depth form).** *Audit.* Iwaniec, "The lowest eigenvalue for congruence groups" (Topics in Geometry, Birkhäuser 1996, 203–212; Zbl 0884.11024) proves λ₁ ≥ 10/49 (ν ≤ 3/14) **using only GL₂ theory**. The zbMATH review: "Crucial is the fact that the symmetric square L-function for some exceptional eigenvalue and their twists with Dirichlet characters are entire, and have the same factor at infinity. The technical part of the proof requires a careful evaluation of sums of hyper-Kloosterman sums." Risager (arXiv 0707.2332, Remark 1.2) confirm that the proof is "entirely in a GL₂ framework". So the conclusion of cycles 56–61 ("every non-functorial route checked reaches exactly 3/16") is wrong as a statement about GL₂. Shimura's theta integral for L(s, sym²u ⊗ χ) is a GL₂ input that passes 3/16; it is not the Gelbart–Jacquet lift. Iwaniec's 1990 density theorem (Acta Arith. 56; Zbl 0702.11034) is the full density hypothesis Σ V^{4(s_j−1/2)} ≪ V^{1+ε} for Γ₀(N).
*Framework (Blomer–Brumley, Ann. Math. 2011, (1.7), "the idea … is due to Iwaniec").* F(Y) = Σ_{q∈𝒬} Σ_{n²≡1 (q)} λ_{sym²u}(n) g(nY), with g the inverse Mellin transform of L_∞(s, sym²u) = Γ_ℝ(s+2ν)Γ_ℝ(s)Γ_ℝ(s−2ν). The detection 1_{n²≡1 (q)} = φ(q)⁻¹ Σ_χ χ²(n) uses only square twists. Every χ² is even, so all twists share one Γ-factor, and Shimura's integral with θ_χ covers them. As Y → 0 the n = 1 term gives g(Y) ≍ Y^{−2ν}, the pole at s = 2ν.
*Exponent law (computed here).* Take |𝒬| = M moduli of size Q. The main term is M·Y^{−2ν}. The off-diagonal terms (n ≠ 1, q | n²−1, n ≲ 1/Y) contribute M·Y⁻¹/Q. The dual side, with a Deligne-strength bound per modulus, contributes M·Q. **M cancels**, so the threshold is exactly ν > 1/4, i.e. 3/16, and averaging over moduli buys nothing with pointwise bounds. The large sieve over prime moduli (quasi-orthogonality of Kl₃(n̄·;q)/q) gives dual ≪ (Q³ + Q²/Y)^{1/2}; in both regimes, Q ≶ 1/Y, this is again exactly ν > 1/4. To reach 3/14 the dual must be ≪ M·Q^{3/4}: a saving of Q^{1/4} per modulus at the balance point Q = Y^{−4/7}, where the dual length is N = Q³Y = Q^{5/4}. In general, dual ≪ M·Q^{a−1} gives ν > (a−1)/(2a); a < 32/25 would beat Kim–Sarnak.
*Conjecture.* The single-modulus form of the framework with q = p^k (fixed p ∤ 6N, k → ∞) reproves 3/16 **without Deligne**. For k ≥ 2, Kl₃(a;p^k) is evaluated by elementary p-adic stationary phase (|Kl₃| ≤ 3p^k, at most three cube roots). Primitive χ mod p^k have primitive χ² for p odd, and ε(sym²u ⊗ ψ) = ε₀ψ(N)τ(ψ)³/p^{3k/2}. Iwaniec's extra Q^{1/4} survives in the depth aspect.
*Attack.* The first half holds as stated: the exponent law needs only a per-modulus bound, and the three checks above supply it. The second half fails as posed. With one modulus the extra saving must come from GL₃-coefficient sums Σ_{n≤q^{5/4}} λ_{sym²}(n)·e(3(an̄)^{1/3}/p^k) of length q^{5/4}, i.e. conductor^{5/12}. That is below the Pólya–Vinogradov range q^{3/2} of any GL₃ twist technology (Munshi, Kowalski–Lin–Michel–Sawin "periodic twists"). Iwaniec's gain therefore uses the moduli average in a way the large sieve does not capture. His mechanism is not reconstructed here (source paywalled). **Verdict: BRIDGE** (the depth-aspect reproof of 3/16 is a reorganisation) / **OPEN** (the depth-aspect gain).
*Survivor, and the plan change.* (i) Shimura's theorem is on the critical path of **every** known route past 3/16: L(s, sym²u ⊗ χ) entire for non-dihedral u, with functional equation and Γ-factor Γ_ℝ(s+δ)Γ_ℝ(s+2ν+δ)Γ_ℝ(s−2ν+δ). Iwaniec uses it directly, and Gelbart–Jacquet (hence LRS and Kim–Sarnak) feed it to the GL₃ converse theorem. The first formal step past 3/16 does not need GL(3) automorphy. (ii) The exponent law "M cancels; large sieve lands exactly on 1/4" means gains in forced-zero frameworks come only from structure of the dual trace-function sums beyond quasi-orthogonality. (iii) Formal plan: half-integral weight theta series with the abstract multiplier j(γ,z) = θ(γz)/θ(z) (θ has no zeros on ℍ, by the triple product), weight-½ Eisenstein series on Γ₀(4N), Shimura's unfolding Σ λ(n²)χ(n)n^{−s} = ⟨u(4·)θ̄_χ, E(·,s̄)⟩. These precede any GL(3) Whittaker work.

**Cycle 72. Conjecture (Iwaniec's 3/14 is a bootstrap fixed point):** in the framework of cycle 71 the dual cost per modulus is a(θ)−1 = (7/2)θ, where θ is the exceptional exponent fed into a GL₂ Kuznetsov evaluation of the hyper-Kloosterman moduli sums. The exponent law ν > (a−1)/(2a) then gives the map F(θ) = 7θ/(4 + 14θ). Its non-zero fixed point is exactly θ* = 3/14, i.e. 10/49. Iterating from Selberg's θ = 1/4 decreases to 3/14. From any θ < 3/14 (e.g. Kim–Sarnak's 7/64) the map *increases*, since F(θ) > θ ⟺ θ < 3/14. **Consequence if true:** 3/14 is a barrier of the method, not of its input, and GL₂-only sym² methods of this type cannot pass 10/49 even with better exceptional bounds plugged in. **How it fails:** a(θ) is not linear with slope 7/2, or Iwaniec's gain is not spectral at all. This cannot be checked without the source (Topics in Geometry 1996, pp. 203–212; paywalled). **Verdict: OPEN (reconstruction target).** First step: derive a(θ) from the Kuznetsov formula for Σ_q Σ_{x mod q} Kl₂(ax̄;q) e(x/q) w(q/Q), using Kl₃ = Σ_x Kl₂ e(x/q).

**Cycle 73. Three attempts at the moduli saving, tested against the exact per-modulus exponent law.** *Normalisation (recomputed).* In the Duke–Iwaniec family F(Y) = Σ_{q∼Q} Σ_{n²≡1 (q)} λ_{sym²u}(n) g(nY), with g the inverse Mellin transform of L_∞(s, sym²u), the per-modulus sizes are: main term g(Y) ≍ Y^{−2ν}; off-diagonal (n ≡ ±1, 1 < n < 1/Y) ≍ 1/(qY); dual = ε₀ q^{−3/2}(q³N)^{−1/2}Y^{−1} Σ_m λ̄(m) g(m/L)[Kl₃(mN̄;q) + Kl₃(−mN̄;q)] with L = q³NY, from (1/(q−1)) Σ_χ τ(χ²)³ χ̄²(a) = Kl₃(a) + Kl₃(−a). Deligne gives dual ≪ q, and the threshold is ν > 1/4.
(a) *Integral representation instead of the functional equation.* I_χ(w) = ⟨u(4·)θ̄_χ y^{1/4}, E*_χ(·, w̄)⟩ is holomorphic on Re w > 1/4 and bounded directly by the kernel, so the Mellin contour of F can be moved to Re s = ε with no residue: the pole of Γ_ℝ(s − 2ν) is cancelled by the forced zero. Pointwise |L(ε + it, sym²u ⊗ χ²)| ≍ q^{3/2} then gives only ν ≤ 3/10. **FALSE**: the root-number phases (the Kl₃ structure) are indispensable, so the functional equation cannot be bypassed.
(b) *Plancherel in the residue class.* Write Σ_m a_m Kl₃(m;q) = Σ_{c mod q} Kl₃(c;q) A(c;q). Then Σ_c |Kl₃(c;q)|² = (q−1)⁻¹ Σ_ψ |τ(ψ)|⁶ ≍ q³ exactly, from Gauss sums alone. The multiplicative large sieve gives Σ_{q∼Q prime} Σ_c |A(c;q)|² ≪ (L/Q + Q)‖a‖² ≍ QL for L ≤ Q². By Cauchy–Schwarz the dual is ≪ Y^{−1/2} per modulus on average. The threshold is then ν > 1/4 **independently of Q**. **Verdict: BRIDGE.** The survivor is a Deligne-free proof of 3/16 in the sym² family (Plancherel replaces Deligne). It also shows that quasi-orthogonality of Kl₃ in both the residue and the modulus can never pass 3/16, which sharpens cycle 71.
(c) *Depth aspect q = p^k with p-adic stationary phase.* Kl₃(m;p^k) is explicit, so the dual becomes Σ_{m≤L} λ_{sym²}(m) e(3(am̄)^{1/3}/p^k) with L = q^{3−1/(1−2ν)} ∈ (q, q^{5/4}) for ν ∈ (3/14, 1/4). Localising m mod p^j linearises the phase, leaving GL(3) sums over progressions mod p^j twisted by additive characters mod p^{k−j}. Their Voronoi duals are longer than the originals. **OPEN**: this is the same core as cycle 71, a GL(3) coefficient sum below the Pólya–Vinogradov range.
*Survivor.* Passing 3/16 in this family requires correlation between λ_{sym²}(m) and Kl₃(m;q) beyond orthogonality. That means either cancellation of Σ_q Kl₃(m;q) over moduli, or cancellation of Σ_m λ(m)Kl₃(m;q) below the Pólya–Vinogradov range. Neither is supplied by Plancherel, the large sieve, or the integral representation. The formal plan is unchanged: the twisted forced zero for L(s, sym²u ⊗ χ²) (θ_χ on Γ₀(4q²), E(z,w;χ) with the regulariser L(4w−1, χ²)) is a common input to every route in this family.


**Cycle 74. Conjecture (the sign-free second moment of Duke–Iwaniec IV, AJM 1994, passes 3/16 in the archimedean forced-zero family).** *Source read:* Duke–Iwaniec, Estimates for coefficients of L-functions IV, Theorem 1. The functional equation is used only through |ε_χ| = 1, as Σ_χ |A_f(χ)|² = Σ_χ |A_g(χ̄)|², with no Kloosterman sums and no Deligne. *Attack:* take f(n) = g(nY) with g the inverse Mellin transform of L_∞(s, sym²u), and even χ mod p, p ∼ P.
- Left side: main term ≍ (P/log P) Y^{−4ν} (from n = 1); off-diagonal ≲ Y^{−2} (Σ_n |a_n||g(nY)| squared).
- Right side, dual length L = P³Y: diagonal ≍ P/Y per modulus; off-diagonal, via the multiplicative large sieve over moduli, ≍ P³ + P²/Y in total.
- A contradiction needs Y^{4ν−2} ≪ P ≪ min(Y^{−2ν}, Y^{1−4ν}), which is non-empty only for ν > 3/8.
**Verdict: FALSE.** The sign-free method is weaker than the signed one: ν ≤ 3/8 against ν ≤ 1/4. *Survivor:* the full hierarchy for the square-twist family. Sign-free second moment gives 3/8. Signed first moment with Plancherel or large sieve, or with Deligne, gives exactly 1/4. Anything better needs correlation of λ_{sym²} with Kl₃ beyond orthogonality (cycle 73). Iwaniec's 3/14 must therefore use the root-number phases *and* a genuine moduli-averaged Kl₃ evaluation.
*Formal status after cycle 74:* the forced zero L(2τ, sym²u ⊗ χ̄²) = 0 for the whole square-twist family (χ⁴ ≠ 1, odd prime conductor q ∤ N+1) is closed in Lean (`HalfWeightTwistedForcedZero.shimura_forced_zero_tw`). Every family argument in cycles 71–74 additionally needs the functional equation of L(s, sym²u ⊗ χ²) with its root number, i.e. the scattering of E(z,w;χ²) to the other cusps of Γ₀(4(N+1)q²). That is the next formal brick on every GL₂ route.

**Cycle 75. Conjecture (composite depth moduli give an elementary moduli saving).** Take the square-twist family over q = p^a r (p fixed, a even, r ∼ R coprime to p). Twisted multiplicativity gives Kl₃(m; p^a r) = Kl₃(m r̄³; p^a) Kl₃(m p̄^{3a}; r). The p-adic stationary phase gives Kl₃(m r̄³; p^a) = p^a Σ_{y³≡m} e(3y r̄/p^a), which is an additive character of r̄ mod p^a, so the sum over moduli r would see Weil/Postnikov cancellation with no Deligne. *Attack:* the factor Kl₃(m p̄^{3a}; r) also varies with the modulus r. Cancelling e(3y r̄/p^a) against it is the original moduli-cancellation problem for Kl₃(·; r), so the idea is **CIRCULAR** for R > 1. For R = 1 (single modulus p^a), localising m mod p^{a−b} linearises the phase only for b ≤ a/2. The remaining GL(3) additive twists have Pólya–Vinogradov size p^{3a/2}, which beats the trivial bound only when b > 3a/2 − aη, and that is impossible. **FALSE.** *Survivor:* p-adic analyticity of the explicit Kl₃ converts moduli cancellation into GL(3) sums below the square root of the conductor; no GL₂ tool reaches that range.
**Cycle 76. Audit of the exponent law against Luo–Rudnick–Sarnak, then conjecture (Iwaniec's moduli saving is a Salié bootstrap).** *Audit.* Blomer–Brumley (arXiv 1104.1067, §1.4 and §4) and Sarnak's Fields notes (§2, eq. (16)–(17)) state the LRS mechanism exactly. The family is L(β, π ⊗ χ × π̃) over χ of conductor q, and it uses positivity of the Rankin–Selberg coefficients: the off-diagonal is then ≥ 0 and needs no bound. The exponent law of cycle 73 in the form "forced zero at β = kν in a degree-d family with Deligne-size duals ⇒ ν ≤ (d−1)/((d+1)k)" reproduces every known case:
- u × ū ⊗ χ (d = 4, k = 2) gives 3/10;
- sym²u ⊗ χ (d = 3, k = 2) gives 1/4;
- sym²u × sym²ū ⊗ χ (d = 9, k = 4) gives 1/5.

Positivity therefore never helps a GL₂-only family: the only positive GL₂-only families, u × ū ⊗ χ and F × F̄ for the Shimura preimage F (d = 4 with parameter ν/2), sit at 3/10 or worse. A recomputation of cycle 73(b) confirms the Q-independence: at dual length M = Q³Y the large sieve gives D ≍ Q·Y^{−1/2} against the main term Q·Y^{−2ν}, a threshold of exactly ν = 1/4 for every Q. Iwaniec's 3/14 therefore needs cancellation in Σ_{q,χ} ε(χ) Σ_{m≤M} λ_{sym²}(m) χ̄(m) that comes from the root-number phases themselves. *Conjecture (OPEN).* The only GL₂-only source of such cancellation is half-integral weight. On the Shimura side, the q-averaged dual is a sum over c ≡ 0 (4q) of weight-½ Kloosterman sums, i.e. Salié sums. These evaluate explicitly as √c Σ_{x²≡D (c)} e(2x/c), and the equidistribution of roots of quadratic congruences (Duke–Friedlander–Iwaniec) has an error term governed by the exceptional parameter itself. That would give the bootstrap map of cycle 72. *How it fails:* the q-averaged twisted Shimura dual is not a single Poincaré-series object on a fixed group (the levels 4Mq² vary with q). *First step:* describe the twisted theta series at every cusp b/q. This is now closed in Lean: `thetaPeriodic_inversion` gives Σ c(n)e(n²z) = (−2iq²z)^{−1/2} Σ ĉ(n)e(−n²/(4q²z)) for every q-periodic weight, and `thetaTw_inversion` gives the Fricke law τ(χ)θ_χ(z) = τ(χ̄)τ(χ²)(−2iq²z)^{−1/2}θ_χ̄(−1/(4q²z)) (module `HalfWeightTwistedThetaInversion`). At b/q the weight ψ(n)e(bn²/q) has dual Σ_r ψ(r)e((br²+rn)/q), a twisted quadratic Gauss sum that is not ψ̄(n)τ(ψ). This is where the Salié structure enters the functional equation.

**Cycles 77–79. Direct attacks at the forced point, all FAILED (recorded as failed).** For exceptional u (Δu = (1/4 − ν²)u, 0 < ν < 1/2) the completed L-functions force L(ν, u⊗χ) = 0, L(2ν, sym²u⊗χ) = 0 and L(2ν, u×u) = ζ(2ν)L(2ν, sym²u) = 0.
- (a) *Second-moment positivity at the forced zero*: 0 = Σ_χ|L(ν, u⊗χ)|² ≥ (positive Rankin–Selberg diagonal) − (off-diagonal) would contradict any ν < 1/2. **Vacuous**: at s = ν the Gamma factor γ(s) has a pole, so the approximate-FE weights γ(s+w)/γ(s) → 0 and the identity degenerates to 0 = 0. The correct family quantity is the completed Λ(ν) ∝ L'(ν), which has no sign constraint.
- (b) *Positivity of E(z, 2ν)*: φ(s) = ξ̂(2s−1)/ξ̂(2s) < 0 for s ∈ (0,1) (ζ < 0 on (0,1)), so E(z,s) → −∞ in the cusp and positivity fails. Also I(2ν) = ∫|u|²E(z,2ν) is finite and not forced to vanish (a Gamma pole times a forced zero).
- (c) *Katok–Sarnak/Waldspurger sign*: the archimedean factor |Γ(1/4 + ν/2)|² stays positive through the complementary series, so there is no sign flip.
- (d) *Higher-order forced zeros* (e.g. L(s, sym²u)² with a double zero at 2ν): the exponent law for degree 6, k = 2 gives 5/14 > 1/4, worse. The log enhancement of the main term does not change the exponent.

*Survivor:* every GL₂-only positivity or sign mechanism evaluated at the forced point is either vacuous (Gamma-pole degeneration) or sign-blind. The forced zero carries information only through the functional equation and its root-number phases (cycle 73).
*Formal side (classical, built):*
- the theta inversion with Gauss sums;
- the dual weight-½ series Ê (not the FE partner: support q∤n versus q|n);
- the Epstein-with-character FE (entire, root number τ(ψ)/(q²B));
- the Maass twist u_χ;
- Gauss's sign G(p) = √p or i√p (Landsberg–Schaar), and root number 1 for the Legendre symbol.

**Cycle 80. Conjecture (level-by-level GL₂ Kuznetsov gives moduli cancellation for Kl₃).** Write Kl₃(m;q) = Σ*_{x mod q} e(x/q)S(x̄, m; q). Here S(x̄, m; q) is the Kloosterman sum of the cusp pair (∞, 0) of Γ₀(x) at modulus q√x (Deshouillers–Iwaniec). So Σ_{q∼Q} w(q/Q)Kl₃(m;q) = Σ_x Σ_{q>x, (q,x)=1} w(q/Q)e(x/q)S(x̄, m; q), and every inner sum is a GL₂ Kuznetsov sum at level x with a smooth weight: e(x/q) has O(1) oscillation on q ∼ Q. The conjecture is that this gives Σ_q Kl₃(m;q) ≪ Q^{2−η}. By the exponent law ν ≤ (1−η)/(2(2−η)), that passes 3/16; η = 1/4 would give 3/14.
- (a) *Per level.* For newforms ρ_{j0} = ε_jρ_{j∞}, where ε_j is the Atkin–Lehner sign, and ω_j ≍ 1/x. The spectral side Σ_j ε_jω_jλ_j(m)ĥ_x(t_j) is ≍ x^{−1/2} (root numbers of O(x) forms with |t| ≲ 1). So Σ_{q∼Q} S(x̄, m; q) ≍ Q√m, which is square-root cancellation over q at each level. Summing over x ≤ Q gives Q², Deligne's bound |Kl₃| ≤ 3q on average and no better.
- (b) *Across levels (heuristic).* The test functions ĥ_x oscillate like X^{2it} with X = 4π√m/(Q√x), so their Fourier transforms sit at length 2log(1/X) ≈ log(Q³x/m). In the trace formula for T_mW_x the elliptic (class number H(4mx)) term is therefore negligible. What dominates are hyperbolic classes of trace xk and discriminant x(xk² − 4m), i.e. sums Σ_k L(1, χ_{x(xk²−4m)}) at that length. By the Kuznetsov–Selberg dictionary these are again Kloosterman sums over moduli ≍ Q√x. **Verdict: CIRCULAR.**
- (c) *Switching.* The off-diagonal terms n = 1 + kq with k ≤ K = 1/(QY) are sums of λ_{sym²} over n ≡ 1 (k) of length kQ. Expanded in characters mod k, they are the same twisted sym² family at modulus k, with dual length k²/Q. For k < √Q they are negligible (entire L-functions, no main term). For k ≥ √Q the character-averaged dual (Kl₃(·; k)) is ≪ k, so the off-diagonal is ≪ K². With Y = Q^{−a}: off-diagonal Q^{2a−2}, main Q^{1+2aν}, q-dual Q². These are compatible iff ν > 1/4. **The threshold 1/4 is invariant under the switch q ↔ k.**
- (d) *Literature.* The source text of Iwaniec 1996 (Topics in Geometry, 203–212) is not accessible. Risager (arXiv 0707.2332 §1): Iwaniec "used some of the same ideas" as Luo–Rudnick–Sarnak in a proof "entirely in a GL₂ framework". Search snippets saying "Kuznetsov formula and Burgess" refer to Iwaniec's 1984 prime geodesic theorem, not to 10/49. *Numerical question, not a derivation:* if the moduli saving were η = 4δ, with δ the subconvexity saving for L(1/2, χ), then Burgess (δ = 1/16) gives η = 1/4 and ν ≤ 3/14, Iwaniec's exponent. Weyl (δ = 1/12, Petrow–Young) would give ν ≤ 1/5 (LRS's 21/100), and Lindelöf would give ν = 0. This fits one data point.

*Survivor:* level-by-level GL₂ spectral theory reproduces Deligne's bound for Kl₃ on average over moduli without algebraic geometry. This is the moduli analogue of cycle 73(b). Going further needs cancellation across levels of Atkin–Lehner-weighted spectral sums, i.e. a prime-geodesic-type bound for Σ_x e(x/q)Σ_k L(1, χ_{x(xk²−4m)}).
*Formal (built, wired, standard axioms):* `Gamma0MaassHeckeOperator`. For p ∤ M, T_p maps Γ₀(M) Maass cusp forms to Γ₀(M)-invariant C² Laplace eigenfunctions with the same eigenvalue that decay at every integral cusp (`heckeH_maass`). Invariance comes from the permutation of P¹(𝔽_p) by the Möbius action of (D B; C A) with four explicit transfer matrices (`heckeT_invariant`). The Laplacian is additive on C² functions (`laplacian_add`). The axiom check of `LegendreRootNumber` is standard.

**Cycle 81. Conjecture (families with explicitly evaluable duals give moduli cancellation).** Salié sums and Hasse–Davenport products (τ(ψ)τ(ψχ₃)τ(ψχ₃²) = ψ̄(27)τ(ψ³)·const) evaluate explicitly. Look for a forced-zero family whose character-averaged dual is a GL₂ Kloosterman sum, which has spectral cancellation over moduli, instead of Kl₃, which does not.
- (a) The simplest such family is L(s, u ⊗ ψ): degree 2, forced zero at s = ν (pole of Γ_R(s−ν)), root number ∝ τ(ψ)², averaged dual ∝ S(N̄, m; q). With a moduli saving η against Weil the exponent law reads ν* = (1/2 − η)/(3/2 − η), so any η > 1/6 would beat 3/16. But S(N̄, m; q) is the (∞, 0) Kloosterman sum of Γ₀(N), and **u itself is in the level-N spectrum**. Its Kuznetsov term ε_uλ_u(m)(Q√N/√m)^{2ν}, inserted in the dual Σ_m λ̄_u(m)g(m/L)(…), gives Σ_m |λ_u(m)|²m^{−ν}g(m/L) ≍ L^{1−ν}. That is exactly the primal main term Y^{−ν}, so the identity is self-consistent and yields no contradiction. Bounding the other exceptional forms by θ gives the bootstrap map F(θ) = 2θ/(1+2θ) > θ for all θ < 1/2: it cannot even reach 3/16. **Verdict: CIRCULAR.**
- (b) The same resonance holds one rank up. Moduli sums of Kl₃ are GL(3) spectral objects (Bump–Friedberg–Goldfeld, Buttcane), and the GL(3) spectrum contains sym²u with parameter 2ν. Its term in the Kl₃ moduli sum, inserted in the sym² dual, reproduces the main term Y^{−2ν}.

*Survivor (structural):* in a forced-zero family of twists of Π, the moduli sum of the averaged dual is spectrally expanded over a space that contains Π itself, and Π's term reproduces the main term exactly. A spectral proof of moduli cancellation therefore needs an a-priori bound for the exceptional spectrum it contains, so it is a bootstrap, as conjectured in cycle 72. Explicit evaluability of the dual does not remove this; it only moves the family from GL(3) to GL(2), where the bootstrap map F(θ) = 2θ/(1+2θ) has no fixed point in (0, 1/2).

**Cycle 82. Conjecture (the square-twist family law with switching is ν ≤ (1−η)/4, with ceiling 1/8).** Let η be a uniform saving over moduli, Σ_{q∼Q} w(q/Q)Kl₃(±m;q) ≪ Q^{2−η} for m ≤ Q^A. Apply the forced-zero identity over all q ∼ Q with even ψ mod q, and switch the off-diagonal to the k-family (cycle 80(c)), which then enjoys the same saving.
- Sizes with Y = Q^{−a}: main Q^{1+2aν}; q-dual Q^{2−η}; k-dual K^{2−η} with K = Q^{a−1} (zero when K < √Q).
- The constraints are a > (1−η)/(2ν) and (2−η)(a−1) < 1 + 2aν. They are compatible **iff ν > (1−η)/4**. Without switching the law is (1−η)/(2(2−η)). Both give 1/4 at η = 0.
- *Parallel (exact at the level of exponent laws).* For a half-integral weight form the Petersson formula at n gives |a(n)|²n^{−(k−1)/2} ≪ 1 + Σ_{c≲n} |S(n,n;c)|c^{−1}(c/n)^{1/2}. A moduli saving η there gives a(n)n^{−(k−1)/4} ≪ n^{(1−η)/4}: **the same law (1−η)/4.** Weil/Salié (η = 0) gives n^{1/4} and ν ≤ 1/4 (Selberg). Iwaniec's two exponents coincide: a(n) ≪ n^{1/4−1/28} = n^{3/14} (Invent. Math. 87, 1987) and ν ≤ 3/14 (1996). Both are the instance **η = 1/7** of the law, which suggests that the 1996 argument transfers the 1987 moduli saving (averaging over levels) to the sym² family. That is a reading of the exponents, not verified against the source.
- *Attack.*
  - Spectral moduli cancellation is at most square root (tempered Kuznetsov terms are O(C) against the trivial C^{3/2}), so η ≤ 1/2. Hence **the square-twist sym² family is capped at ν ≤ 1/8 (λ ≥ 15/64 ≈ 0.234)**.
  - Reaching Kim–Sarnak (ν ≤ 7/64) would need η ≥ 9/16 > 1/2, so **no moduli-cancellation input lets this family reach Kim–Sarnak**.
  - This also **refutes cycle 72's bootstrap formula F(θ) = 7θ/(4+14θ)**: that formula has F(0) = 0, whereas any method of this type has F(0) ≥ 1/8.
- *Comparison with the positive degree-4 family* (π × π̃ ⊗ χ, zero at 2ν, pole term 1/(qY), dual Kl₄ with Deligne size q^{3/2}). With a saving η its law is ν > (3/2 − η)/(5 − 2η), i.e. 3/10 at η = 0, 1/4 at η = 1/2 and 1/6 at η = 1, worse than the square-twist family at every η. **So the best GL₂ forced-zero family is the square-twist sym² family, with ceiling 1/8.**
- **Verdict: SURVIVES PRELIMINARY ATTACK as a heuristic exponent law.** It is not a theorem: the moduli saving is an input, and the switching step needs smooth weights in both families. **[OPEN CORE]:** a Kl₃ moduli saving η > 0 from GL₂ tools alone, i.e. Iwaniec's mechanism.

**Cycle 83. SOTA read of Deshouillers–Iwaniec (Invent. Math. 70, 1982; GDZ OCR, pp. 219–288), then the exact second moment of Kl₃ over moduli.**
- *Source.*
  - Thm 6 (level-averaged exceptional large sieve): Σ_{q∼Q}Σ_{λ_j exc} X^{2κ_j}|Σ_{n∼N} a_nρ_j(n)|² ≪ (QN)^ε(Q + N + NX)‖a‖².
  - DI's conjecture replaces NX by √(NX), "as powerful as the Selberg eigenvalue conjecture" in all known applications. Thm 7 proves it for a_n ≡ 1.
  - Thms 10–12 are bilinear bounds for S(m r̄, ±n; sc) and for incomplete Kloosterman fractions e(n·\overline{rd}/sc). They save only when the r, d ranges are short (the term (C + DR)² in K²).
- *Consequences.*
  - (i) For one exceptional form, level averaging alone gives nothing beyond a single level (weight 1/level per level against a diagonal of size #levels).
  - (ii) In cycle 80's decomposition the level x runs over a complete period (R ≍ C), so Thms 10 and 12 are weaker than Deligne there. Applying Thm 6 to Σ_x Σ_q e(x/q)S(x̄, m; q) gives LQ^{2+a/4}, worse than Deligne's LQ². Even DI's conjecture gives exactly LQ², i.e. Deligne.
- *Exact reduction (new form, elementary).* With T = Σ_{q∼Q} w_q Σ_m λ̄(m)G(m/L)Kl₃(m;q), Cauchy–Schwarz gives |T|² ≤ ‖λ‖²_L·Σ_m G|Σ_q w_qKl₃(m;q)|². Poisson in m mod qq' uses the Fourier transform of Kl₃, Σ_m Kl₃(m;q)e(βm/q) = qS(1, −β̄; q) − 1, and twisted multiplicativity. The result is
  **Σ_m G(m/L)|Σ_q w_qKl₃(m;q)|² = Diag + L Σ_{h≠0} Σ_{q≠q'} w_q w̄_{q'} Ĝ(hL/(qq')) S(h̄, q³ − q'³; qq') + O(lower)**, where Diag ≍ LQ³.
  - The product S(1, −h̄q'; q)·S(1, h̄q; q') is the single sum mod qq' with argument B = h̄(q³ − q'³), since B ≡ −h̄q'³ (q) and B ≡ h̄q³ (q').
  - The h-range is H = Q²/L.
- *Threshold law.* Let OD ≪ L·HQ^{3−δ} be a saving of Q^δ over Weil. Then dual = Q^{3/2} + Q^{1+(a−δ)/2}, and without switching the family gives **ν* = max(1/(4(1+δ)), 1/6)**. Weil alone (δ = 0) gives exactly 1/4. Iwaniec's 3/14 corresponds to δ = 1/6 at a = 7/6 (H = Q^{1/6}), i.e. to OD ≪ Diag: the whole h-sum costs O(1) at L = Q^{11/6}. In large-sieve language, the vectors (Kl₃(m;q)/q)_{m≤L} would have to be quasi-orthogonal over q ∼ Q already for L ≥ Q^{11/6}. The Schur test with Weil gives (L + Q²)‖c‖², i.e. only L ≥ Q².
- **Verdict: BRIDGE.** The open core is now the concrete Kloosterman bilinear form OD = Σ_{h≤H}Σ_{q≠q'} S(h̄, q³−q'³; qq') (equivalently Σ S(−h̄, q'; q)S(−h̄, q; q')), with a power saving beyond Weil. Heuristically it has square-root size LQ²√H ≪ Diag, which would give η = 1/2. **[OPEN CORE]:** any saving in this reciprocal form, e.g. from Duke–Friedlander–Iwaniec or Bettin–Chandee bounds for Kloosterman fractions, or from Kuznetsov in q at level hq'.

**Cycle 84. Attack on the cubic-difference Kloosterman form (cycle 83's open core).**
- *Formal (built `--old`, wired, standard axioms): `HyperKloostermanSecondMomentKernel`.*
  - `fourier_hyperKloosterman_three`: Σ_m Kl₃(m; n)e(βm/n) = nS(1, −β⁻¹; n) for β a unit. `sum_hyperKloosterman_three`: Σ_m Kl₃ = 0 for n > 1. `star_hyperKloosterman_three`: conj Kl₃(a) = Kl₃(−a).
  - `second_moment_kernel`: Σ_{m mod qr} Kl₃(m; q)Kl₃(−m; r)e(hm/qr) = qr·S(1, h⁻¹(q³ − r³); qr) for a unit h. `second_moment_kernel_of_fst`: it vanishes when q ∣ h. So cycle 83's reduction is exact, with no lower-order terms.
- *Attack (a): expand in q mod q', Kuznetsov in q.* Use S(1, h̄q; q') = Σ*_{t mod q'} e(\overline{ht}/q')e(tq/q'). The q-sum Σ_q w(q)e(tq/q')S(1, −h̄q'; q) is then a Kuznetsov sum at level h; for h = 1 there is no exceptional spectrum at all. But the weight has frequency t/q', so its transform sits at |t_j| ≍ |t| ≤ Q. The spectral large sieve then costs (T² + Q) with T ≍ Q and yields ≍ Q^{7/2}, worse than Weil's Q³. Keeping t small only covers a negligible part of the t-range. **FALSE as a route.**
- *Attack (b): Cauchy–Schwarz in q', then in q.* After factoring, the q-sum becomes a product of two Kloosterman sums modulo the varying modulus q, times a function periodic mod q'q'' ≍ Q² > Q. This is again horizontal, and Poisson in the modulus is not available. **FALSE.**
- *Diagnosis.* OD is a bilinear (Type II) sum of Kloosterman sums over moduli c = qq' whose argument couples the two factors. Only Type I moduli sums (c ≡ 0 mod d, fixed arguments) are within Kuznetsov's reach. Type II bounds for Kloosterman sums over moduli are exactly what blocks sign changes of Kl₂(1; p) over primes (Fouvry–Michel, Annals 2007; Matomäki's refinements handle Type I only).
- *Formal export (built, wired, standard axioms): `SelbergConjectureSmallLevel`.* `restrictMaass` restricts a Maass cusp form to any subgroup Γ' ≤ Γ. `hardy_bound_of_principal_le` gives α(1+α) ≤ 2λ for every Γ ⊇ Γ(N+1). `no_exceptional_of_principal_le` proves **Selberg's conjecture for every subgroup of SL₂(ℤ) containing some Γ(N), 1 ≤ N ≤ 14**, with `gamma0_no_exceptional` and `gamma1_no_exceptional` as corollaries. Literature: Huxley 1985 has level ≤ 18. The 1D Neumann ground state on the strip is μ ≈ κy₀ = α to leading order, so the corpus Hardy bound is sharp there and the only slack left is the strip/cell covering factor 2. Levels 15–18 would need a factor below 1.98–1.58.
- **Verdict: BRIDGE to a known open problem.** The square-twist sym² route past 3/16 needs a Type II moduli estimate for Kloosterman sums. Iwaniec's 1996 argument, if it follows this family, must create Type I structure some other way, e.g. an extra averaging variable or a different family.

**Cycle 85. Conjecture: the strip/cell factor 2 is an artefact, and a floor-1 Hardy bound plus a band trace estimate proves Selberg for Γ(N) for every N ≤ 25.**

*Literature.* Huxley's geometric method gives λ₁(X(N)) > 1/4 for N ≤ 17; the corpus had N ≤ 14. Booker–Strömbergsson cover only squarefree Γ₀(N) (by trace-formula computation).

*Notation (paper proof).* Use the deck-summed densities and slice functions: s(y) = ∫₀¹ D(x+iy) dx, g(y) = sliceGradient, m = s/y². Set a = √3/2, w₀ = 1/a − 1 = 2/√3 − 1, κ = 2π/N and E_F = λM_F. Define
- M_high = ∫₁^∞ m and E_high = ∫₁^∞ g (a full strip inside F);
- M_band = ∫_a^1 m and E_band = ∫_a^1 g.

*Proof.*
1. **Hardy with floor 1.** Take h = α/y − κ with 0 ≤ α ≤ κ, t = κ − α. The corpus ground-state identity g ≥ Qm + (hs)' with Q = α(1−α) + 2ακy holds for every α. Integrated over [1, ∞) it gives E_high ≥ q_α M_high + t·s(1), with q_α = α(1 − α + 2κ) = (κ − t)(1 + κ + t). The boundary term −h(1)s(1) = t·s(1) now helps.
2. **Band trace.** The vertical ground state gives |s'| ≤ c·s + g/c for every c > 0. Then s(y) ≤ s(1) + ∫_a^1(cs + g/c) on [a, 1]. Integrating against dy/y² and using ∫ s ≤ ∫ s/u² gives (1 − w₀c)M_band ≤ w₀s(1) + (w₀/c)E_band.
3. **Covering.** E_band + E_high = E_rect ≤ 2E_F (corpus strip bound), while E_high ≤ E_F because the high strip lies inside F. Also M_F ≤ M_rect = M_band + M_high.
4. **Combination.** With β = t(1/w₀ − c) = t(2√3 + 3 − c):
   - (1 + t/c)E_F ≥ q_α M_high + β M_band ≥ min(q_α, β)M_rect ≥ min(q_α, β)M_F;
   - hence **λ ≥ min(q_α, β)/(1 + t/c)**.
5. **Numerics.** Take c = 11/10 and t = 49/1000. For N ≤ 25, κ ≥ 2π/25 > 0.25132, so q_α ≥ 0.2630 and β ≥ 0.2628, against 1 + t/c = 1.04455. Both ratios exceed 1/4 (0.2518 and 0.2516). **So Γ(N) has no exceptional eigenvalue for N ≤ 25.** Through the conjugation diag(1, N)Γ(N)diag(1, N)⁻¹ ⊆ Γ₀(N²) ∩ Γ₁(N), the same holds for every Γ₀(M) with M ∣ N² (N ≤ 25), including non-squarefree M such as 625, 576 and 529.

*Status: FORMALIZED* (built `--old`, wired, standard axioms, lint clean).
- `SelbergMaassFloorOneGap`: `floor_one_hardy`, `band_trace`, `high_le`, `rect_le`, `cell_le_rect`, `closing_chain`, and **`level_le_twentyfive_no_exceptional`** (Γ(N+1), N+1 ≤ 25).
- `SelbergConjectureLevelTwentyFive`: `no_exceptional_of_principal_le` (every Γ ⊇ Γ(N), N ≤ 25), the Γ₀ and Γ₁ corollaries, `conjMaass` (u(z/N) on Γ(N) from u on Γ₀(N²)), and **`gamma0_sq_no_exceptional`** (Γ₀(M) for M ∣ N², N ≤ 25).

*Literature re-check, verdict REDISCOVERED as a statement.* Booker–Lee–Strömbergsson ("Twist-minimal trace formulas and the Selberg eigenvalue conjecture", JLMS 2020) verify Selberg for Γ(N), N ≤ 226, and Γ₁(N), N ≤ 880, by rigorous trace-formula computation. What is new here:
- a computation-free proof whose geometric range, 25, exceeds Huxley's 18;
- the first machine-checked proof of Selberg's conjecture for these groups.

The floor-one method caps at N ≤ 30 even with a perfect band estimate: q_κ = κ(1+κ) ≥ 1/4 requires κ ≥ 0.2071. With the present band constant it caps at N ≤ 25, and N = 26 fails for every choice of c and t.

**Cycle 86. Two candidate GL₂-only mechanisms for Iwaniec's 10/49, tested.**
- (a) *Cubic structure.* The kernel argument h̄(q³ − q'³) factors over ℤ[ω] as (q − q')(q − ωq')(q − ω²q'), which suggests cubic metaplectic Kloosterman sums over ℚ(ω). Duke–Iwaniec (1993, "A relation between cubic exponential and Kloosterman sums") relate Σ_x e((ax³+bx)/p) to Kloosterman sums with a cubic character, via Hasse–Davenport. Kl₃ is not of that form. The Hasse–Davenport rewriting τ(χ²)³ = χ̄(64)τ(χ)³τ(χη)³/τ(η)³ averages back to Kl₃(±8√a), which is circular. **Verdict: not applicable.**
- (b) *Twist multiplicity plus level density.* The q − 1 twists u ⊗ χ of an exceptional form share its eigenvalue at level Nq². Weil plus Kuznetsov at a single level gives Σ_{exc} M^{4ν_j} ≪ M (harmonic weights ≍ 1/M). If all twists sat in one Kuznetsov family this would force q·(Nq²)^{4ν} ≪ Nq², i.e. ν ≤ 1/8. **FALSE.** u ⊗ χ has nebentypus χ², so each fixed-character space holds O(1) twists. In Γ₁(Nq²), which holds all of them, the volume grows like q⁴ and the density bound becomes trivial.
- *Survivor.* Twist families help only as families of L-functions (LRS), not as multiplicity in a single Kuznetsov space. GL(3) Kuznetsov leaves no room for Kl₃ moduli cancellation (cycle 66), and horizontal Kl₃ over primes is Katz's open problem. **So every route to Kl₃ moduli cancellation checked so far is blocked.** Iwaniec's 3/14 must use a structure not reconstructed here.

**Cycle 87. Conjecture: a bootstrap through Deshouillers–Iwaniec bilinear bounds gives the Type II saving in the cubic-difference form.** Each factor of OD_h = Σ_{q,q'} S(−h̄, q'; q)S(−h̄, q; q') is Kuznetsov-able in its own modulus. S(−h̄, q'; q) is the (∞, 0) sum of Γ₀(h) in the modulus q with argument q', and h ≤ H is small, so the exceptional spectrum involved is that of small levels. That suggests a bootstrap: a saving δ(θ) in OD from DI Theorems 9/10 with exceptional exponent θ gives ν* = 1/(4(1+δ)). The hope is that δ(1/4) > 0, i.e. that Selberg's own 3/16 input already saves.
- *Attack.* DI Theorems 9, 10 and 12 allow arbitrary coefficients in the argument variables (m, n, r, s) but only smooth weights in the modulus variable c.
  - In OD the two variables play symmetric roles. Whichever one is taken as the Kuznetsov modulus, the other factor becomes a rough coefficient in that modulus: S(−h̄, q; q') as a function of q mod q', and vice versa.
  - Expanding the rough factor in additive characters costs √Q and produces weights e(tq/q') of frequency up to 1. The spectral large sieve then runs over |t_j| ≤ Q and loses (cycle 84).
  - Cauchy–Schwarz over q' restores smoothness in q only after squaring. It leaves products of two Kloosterman sums with the same varying modulus q, again horizontal.
- **Verdict: FALSE (structural).** The Type II obstruction is intrinsic to the reciprocal symmetry of OD, and no DI-type bound applies at any θ. This is the same obstruction that blocks sign changes of Kl₂(1; p) over primes, where only Type I information is available (Fouvry–Michel; Matomäki; Drappeau–Maynard use Siegel-zero or Selberg-type inputs, not Type II bounds).
- *State of the formal frontier (unchanged this cycle).* 3/16 for all congruence subgroups; exactly 1/4 for every Γ ⊇ Γ(N) with N ≤ 25 and for every Γ₀(M) with M ∣ N², N ≤ 25.

**Cycle 88. Conjecture: nodal-domain topology is a weight-0-only input that passes the theta barrier.** Take a real exceptional eigenfunction u with λ = λ₁ = s(1−s), s = 1/2 + ν, on a congruence surface X = Γ\H.
- *Structure.* By Courant, u has exactly two nodal domains D₊ and D₋. Each is the Dirichlet ground state of its domain, so λ₀(Γ_D\H) < λ for the image Γ_D of π₁(D) in Γ. By Elstrodt–Patterson–Sullivan (λ₀ = δ(1−δ) when δ > 1/2), **both nodal fundamental groups have critical exponent δ(Γ_D) > 1/2 + ν**.
- *Consequence of the conjecture.* By the minimal-partition characterisation of the first nonzero eigenvalue (Helffer–Hoffmann-Ostenhof–Terracini), Selberg's conjecture would follow if no 2-partition of X had both parts with δ > 1/2.
- *Attack.* The inputs used are real-valuedness, Courant, the Dirichlet ground state and Patterson–Sullivan. **All of them hold equally for non-congruence finite-index subgroups of SL₂(ℤ).** Selberg's own examples, covers of Γ(2)\H through small-Cheeger quotients of the free group, have λ₁ → 0. Hence no argument built only from these inputs can prove λ₁ ≥ 1/4. Large-level congruence surfaces also contain many disjoint subsurfaces with δ > 1/2, so no partition obstruction exists. **Verdict: FALSE (barrier).**
- *Survivor.* A proof must combine an input that fails in weight 1/2 (real-valuedness, Hecke operators at primes) with an input that fails for non-congruence groups (arithmetic: congruence or Hecke structure). Real-valuedness alone fails the second test. Hecke operators at primes pass both, but every known way to couple them to the archimedean parameter goes through families or functoriality (cycles 58–87, and Yang's withdrawn joint bound in cycle 62).

**Cycle 89. The theta barrier is now formal: the weight-1/2 analogue of Selberg's conjecture is FALSE (Lean).**
- `WeightMaassLaplacian` gives:
  - `weightLaplacian_rpowIm_mul`: Δ_k(y^{k/2} f) = (k/2)(1 − k/2) y^{k/2} f for holomorphic f;
  - `norm_jacobiTheta_le`: |θ(τ)| ≤ 1 + 1/√Im τ, by Gaussian sum–integral comparison.
- `HalfWeightThetaExceptionalEigenvalue`, theorem **`weight_half_exceptional`**, proves that for F = y^{1/4}θ on Γ₀(4) with the unitary theta multiplier j:
  - F is nowhere zero;
  - F(γz) = j(γ,z)F(z);
  - Δ_{1/2}F = (3/16)F;
  - |F∘γ|² is integrable on the modular fundamental domain for every γ ∈ SL₂(ℤ), hence F is square-integrable on Γ₀(4)\ℍ;
  - 3/16 < 1/4.
- All built, wired, standard axioms, lint clean.
- *Meaning.* This machine-checks the survivor of cycle 59: every argument whose inputs also hold for the theta multiplier (Weil/Salié-strength Kloosterman bounds, Kuznetsov, positivity, energy methods on the multiplier bundle) is capped at 3/16. Selberg's 3/16 is sharp for such arguments. The classical fact is not new; the formal statement of the barrier is.

**Cycle 90. Source check of the symmetric-square technique, and the GL₂-only ceiling.** Sarnak, *Notes on the generalized Ramanujan conjectures* (Clay Math. Proc. 4, 2005; PDF read), eqs. (21)–(22): for a cusp form Π on GL(n), n ≤ 4, using L(s, Π, sym²) with Duke–Iwaniec at finite places and LRS at ∞ gives |Re μ_j(Π_∞)| ≤ 1/2 − 1/(1 + n(n+1)/2).
- n = 2 (π itself, Shimura's sym²): 1/2 − 1/4 = 1/4, i.e. **ν ≤ 1/4, exactly Selberg's 3/16**. This agrees with cycle 73's per-modulus law and with the formal theta barrier of cycle 89.
- n = 3 (Π = sym²π, Gelbart–Jacquet): 2ν ≤ 5/14, i.e. ν ≤ 5/28, λ ≥ 171/784 (LRS 1995). This needs the GJ lift and the analytic theory of sym² on GL(3).
- n = 5 (sym⁴π, Kim): 4ν ≤ 7/16, i.e. 7/64.
- *Attack on the remaining GL₂-only family:* the Garrett triple product L(s, π × π × π ⊗ χ) = L(s, sym³π ⊗ χ)L(s, π ⊗ χω)². It has degree 8 and a forced zero at 3ν. The exponent law ν ≤ (d−1)/((d+1)k), with d = 8 and k = 3, gives 7/27 > 1/4, which is worse. **FALSE.**
- *Survivor.* Among GL₂-only L-function families (Shimura sym², Rankin–Selberg π × π̃, Garrett triple product), none beats 1/4 under the family method with Deligne-quality duals. Iwaniec's 10/49 is therefore not an instance of this technique, and its mechanism remains unreconstructed. Every bound past 3/16 in the published record uses functoriality (GJ, Kim–Shahidi), with Iwaniec's 1996 paper as the only exception.

**Cycle 91. Conjecture: energy method plus Rankin–Selberg mode distribution beats 3/16 uniformly.**
- *Idea.* The floor-1 Hardy bound (cycle 85) degrades with N only because the Fourier gap is 2π/N. Suppose that at every height y ≥ 1, at most a fraction ε of the deck-summed slice mass sits in modes |n| < δN. Then the effective gap is 2πδ and λ ≳ (1−ε)·2πδ(1 + 2πδ), which is ≥ 1/4 for δ ≈ 0.035 and small ε.
- *Why it looked promising.* The input "Σ_{n≤X}|ρ(n)|² ≫ X at X ≍ δN" fails in weight 1/2, since θ is supported on squares with Σ ≍ √X, so it passes the theta barrier. It is also arithmetic: effective only through Hecke/RS structure at the square-root-of-conductor scale.
- *Attack.* At height y (width-N coordinates) mode n carries |ρ(n)|²·y·K_ν(2π|n|y/N)², and K_ν(x) ≍ x^{−ν} for small x.
  - Even with perfectly equidistributed |ρ(n)|², the fraction of mass in |n| < δN at y ≍ 1 is ≍ (2πδ)^{1−2ν} ≈ 0.3 for δ = 0.035. The Bessel profile itself pushes mass into low modes.
  - The resulting bound, ≈ 0.7·2πδ(1 + 2πδ) + 0.3·κ(1 + κ), is about 0.2 < 1/4. Raising δ raises the low-mode fraction faster.
  - This is exactly cycle 64's negative strip balance Φ_ν.
- **Verdict: REDISCOVERED (cycle 64).** No distribution of |ρ(n)|², however equidistributed, lets the energy method reach 1/4 uniformly. The obstruction is the archimedean Bessel profile of exceptional forms, not arithmetic.

**Cycle 92. SOTA refresh and consolidation.**
- *Literature.* A 2025–2026 search finds no improvement past Kim–Sarnak (arXiv 2505.00489 uses 7/64; arXiv 2608.18236 proves a density theorem for thin groups).
- *Consolidation.* `SelbergConjectureStatus.selberg_status` (built, wired, standard axioms) bundles:
  - 3/16 for every congruence subgroup;
  - exactly 1/4 for every Γ ⊇ Γ(N) with N ≤ 25 and for every Γ₀(M) with M ∣ N²;
  - the formal theta barrier (weight-1/2 eigenvalue 3/16).
- The uniform statement is open in the literature. Every route the loop has examined ends in a named obstruction (cycles 56–91).

**Cycle 93. Falsification side: could some congruence subgroup have an exceptional eigenvalue?**
- *Consequences of a counterexample.* A Hecke–Maass form π with 0 < ν < 1/2 would, under automorphy of every symmetric power (Langlands functoriality; known for n ≤ 4 by Gelbart–Jacquet and Kim–Shahidi, and for all n for holomorphic forms by Newton–Thorne), give sym^nπ an archimedean parameter nν. Once nν ≥ 1/2 the LRS bound on GL(n+1) is violated. So a counterexample contradicts symmetric-power functoriality, a central conjecture of the Langlands programme. It is also excluded computationally for Γ(N), N ≤ 226, and Γ₁(N), N ≤ 880 (Booker–Lee–Strömbergsson), and formally in this corpus for all Γ ⊇ Γ(N), N ≤ 25.
- *What a Lean falsification would need.* An explicit level and an explicit exceptional eigenfunction with a certified eigenvalue. That requires numerical certification, which the no-computation rule forbids, and all evidence says no such form exists.
- **Verdict: falsification route CLOSED** (not a proof of anything; the evidence and the Langlands framework point the other way). With cycles 56–92 the loop has now examined both directions of the goal.

**Cycle 94. Source identification of Iwaniec's family (Blomer–Brumley, arXiv 1003.0559 §1.2, read) and the exact estimate behind 10/49.**
- *Source.* Blomer–Brumley §1.2, eqs. (1.3)–(1.7):
  - the Duke–Iwaniec family F(p^ℓ) = Σ_{Q≤q<2Q prime} Σ_{n²p^{−2ℓ}≡1 (q)} λ_{sym²}(n)g(np^{−ℓ});
  - the bound F ≪ p^ℓ + Q^{(m+1)/2+ε}, obtained by detecting the congruence with characters, applying the FE of L(s, π, sym² × χ²) and Deligne's bound for hyper-Kloosterman sums;
  - the archimedean version (1.7) F(Y) = Σ_q Σ_{n²≡1 (q)} λ_{sym²}(n)g(nY) with g the inverse Mellin transform of L_∞(s, sym²), "due to Iwaniec [9] = Topics in Geometry 1996".
- *Consequence.* For π on GL(2) (m = 3) this gives exactly 1/4, i.e. 3/16. **The family is the one analysed in cycles 73 and 80–84.** Iwaniec's 10/49 therefore comes from improving the Deligne step in the q-sum ("careful evaluation of sums of hyper-Kloosterman sums", zbMATH review), not from a different family.
- *The exact estimate needed.* At the threshold ν = 3/14 of the no-switching law, Y = Q^{−7/4} and the dual length is L = q³Y ≍ Q^{5/4}. Then 10/49 is equivalent to
  **T := Σ_{q∼Q prime} Σ_{m} λ_{sym²}(m)W(m/L)Kl₃(±mN̄; q) ≪ Q^{3+ε} at L = Q^{5/4}.**
  - Deligne gives Q²L = Q^{13/4}.
  - The multiplicative large sieve over characters mod q (cycle 73(b)) gives Q^{25/8}.
  - Full square-root cancellation would give Q^{17/8}.
  - So Iwaniec saves Q^{1/4} over Deligne and Q^{1/8} over the large sieve.
- *Reconstruction path, GL₂-only.* Fourier-expand in m mod q using the formalized identity Σ_m Kl₃(m;q)e(βm/q) = qS(1, −β̄; q) (`HyperKloostermanSecondMomentKernel.fourier_hyperKloosterman_three`). This gives T_q = Σ_{h mod q} S(1, h̄; q)·S_h with S_h = Σ_m λ_{sym²}(m)W(m/L)e(hm/q), additive twists of the sym² series. Via Shimura's integral these are ⟨u·θ_{h/q}, E⟩, with θ at the cusp h/q evaluated through Gauss sums (corpus: `thetaPeriodic_inversion`, `QuadraticGaussSumSign`). The Kl₂ factor then combines with those Gauss sums into Salié-type sums, which evaluate explicitly. This is a plausible reading of the "careful evaluation". **[OPEN CORE]:** carry out this evaluation and extract the Q^{1/4} saving.

**Cycle 95. Conjecture (reconstruction): Iwaniec's 10/49 is a level-of-distribution-4/7 statement for sym² coefficients in the classes ±1 mod q.**
- *Law.* Take F(Y) = Σ_{q∼Q} Σ_{n≡±1 (q)} λ_{sym²}(n)g(nY) with X = 1/Y and Q = X^ϑ.
  - The forced zero (Λ(s, sym²u) entire, and L_∞ poles cancelled) makes the expected main term (1/q)Σ_n λ_{sym²}(n)g(nY) negligible, because its dual has length N²Y ≪ 1.
  - The single term n = 1 contributes g(Y) ≍ X^{2ν} to every class, Q·X^{2ν} in total.
  - A level of distribution ϑ, meaning Σ_{q∼Q}|Σ_{n≡±1 (q)} λ_{sym²}(n)g(nY)| ≪ X(log X)^{−A} for Q ≤ X^ϑ, therefore forces Q·X^{2ν} ≪ X, i.e. **ν ≤ (1 − ϑ)/2**.
- *Consistency checks.*
  - ϑ = 1/2 (Bombieri–Vinogradov quality, from the multiplicative large sieve) gives ν ≤ 1/4: Selberg's 3/16, matching cycle 73(b) and the theta barrier.
  - ϑ = 4/7, the Bombieri–Friedlander–Iwaniec level for a fixed residue class (Acta Math. 1986, via Deshouillers–Iwaniec Kloosterman bounds), gives **ν ≤ 3/14, i.e. λ ≥ 10/49, Iwaniec's exponent exactly**.
  - The dictionary ϑ = 1/(2 − η) reproduces cycle 76's η = 1/4.
  - The threshold Y = Q^{−7/4} of cycle 94 is exactly Q = X^{4/7}.
- *Consequences.*
  - A GL₂-only level ϑ = 3/5 would give ν ≤ 1/5, i.e. LRS's 21/100 without Gelbart–Jacquet. ϑ > 3/5 would beat 21/100 GL₂-only; ϑ = 5/8 would give 55/256.
  - Beating Kim–Sarnak (ν < 7/64) would need ϑ > 25/32, far beyond any known level for any arithmetic sequence.
  - The modern levels for primes (Maynard 3/5; Lichtman ≈ 0.617 for triply well-factorable moduli) rely on the Heath-Brown decomposition of Λ. For λ_{sym²} the analogous structure (λ(k²) = Σ_{d|k} μ(d)λ(k/d)², Rankin–Selberg coefficients) needs shifted-convolution or GL(3)-Voronoi input, which is GL₂-accessible only through Shimura's theta integral.
- **Verdict: SURVIVES as a reconstruction.** It matches Iwaniec's exponent exactly and explains 3/16 as ϑ = 1/2. It is not verified against the source. **[OPEN CORE]:** a level of distribution ϑ > 1/2 for λ_{sym²} in the classes ±1 mod q with suitably factorable moduli, from GL₂ spectral theory; any ϑ > 4/7 improves Iwaniec.

**Cycle 96. Endpoints of the level-of-distribution law ν ≤ (1 − ϑ)/2.**
- *Per-modulus check.* For one prime q, a GL(3) progression sum has Voronoi dual X·q^{−3}Σ_{m≤q³/X}λ̄(m)Kl₃(am;q). With Deligne this is ≤ q, against the trivial X/q, so the level is **1/2** (not 2/3 as for GL(2) coefficients, where the dual error is q^{1/2}). This agrees with ϑ = 1/2 ⟺ 3/16. Going beyond 1/2 needs cancellation in Σ_{m≤q³/X} λ̄(m)Kl₃(am;q) below the Pólya–Vinogradov range. That is exactly T (cycle 94), which Iwaniec overcame by averaging over q.
- *Endpoints.*
  - ϑ → 1, i.e. an Elliott–Halberstam-strength distribution of λ_{sym²} in the classes ±1 mod q averaged over q ≤ X^{1−ε}, gives ν = 0, the full conjecture.
  - Hence **Selberg's conjecture follows from an Elliott–Halberstam-type hypothesis for the Shimura sym² coefficients in the classes ±1**. This is a conditional reduction in the spirit of the Linnik–Selberg implication, not a proof. The hypothesis is open, like EH for primes.
  - Beating Kim–Sarnak needs ϑ > 25/32, beyond every known level for any arithmetic sequence (primes: Maynard 3/5, Lichtman ≈ 0.617 with triply well-factorable weights; d₃ individually: 1/2 + 1/46).
- **Verdict: the level-of-distribution route is CAPPED at the current technology frontier.** It reproduces 3/16 (ϑ = 1/2) and 10/49 (ϑ = 4/7). It would reproduce 21/100 GL₂-only at ϑ = 3/5 and needs EH strength for the conjecture. No uniform proof follows.

**Cycle 97. Consistency of the level-of-distribution law with switching.** Write F_q = Σ_{q∼Q} Σ_{n≡1 (q)} λ_{sym²}(n)g(nY) = Q·g(Y) + F_r, where F_r is the same sum with the complementary divisor r = (n−1)/q ≍ X/Q as modulus.
- *Size of F_r.* Each r-progression is a twisted sym² sum of length X with Voronoi dual length r³/X. It is negligible for r < X^{1/3} and ≲ r (Deligne) otherwise, so F_r ≲ (X/Q)², and F_r is negligible once Q > X^{2/3}.
- *Size of the q-dual.* D ≲ Q^{2−η}.
- *Resulting law.* Q·X^{2ν} must exceed both terms, i.e. ν > max(1 − 3ϑ/2, ϑ(1−η)/2 + ...). With Deligne on both sides (η = 0) the optimum is ϑ = 1/2, ν = 1/4, reproducing cycle 80(c)'s invariance.
- *Agreement.* The LoD law ν ≤ (1−ϑ)/2 corresponds to D ≪ X^{1−δ}, i.e. ϑ(2−η) < 1, the dictionary ϑ = 1/(2−η) of cycle 95. The three formulations (moduli saving η, level ϑ, switching) are consistent and all place Iwaniec at η = 1/4 ⟺ ϑ = 4/7.
- **Verdict: BRIDGE (consistency).** No new saving: the gain must come from moduli cancellation in the q-dual, which is Iwaniec's unpublished-to-us technical step.

**Cycle 98. Source read of Iwaniec 1987, then reconstruction of the moduli saving behind 10/49.**
- *Source (GDZ scans, Invent. Math. 87, 385–401, read in full).* Iwaniec 1987 uses the Petersson formula at (n, n) in half-integral weight.
  - The Kloosterman sums are Salié sums. Lemmas 4–6 evaluate them explicitly as Σ_{ab=q} e(2n(ār/b − b̄r/a + …)), twisted by the Jacobi symbol (±nr/ab).
  - This turns the moduli sum into bilinear forms F(A, B; M) in the factor pair (a, b). In (5.2) and (5.3), Weil for incomplete Kloosterman sums gives F ≪ min(A, B)^{3/2}(nr)^{1/2}.
  - *Averaging over levels* (§6) embeds f into Γ₀(pN) for primes p ∼ P. Then p | ab puts a prime factor into a or b, and Cauchy–Schwarz over the pairs (p₁, p₂) with Weil twice gives (6.3).
  - Theorem 3: Σ_{Q}|K_Q(x)| ≪ xP^{−1/2} + xn^{−1/2} + (x+n)^{5/8}(x^{1/4}P^{3/8} + n^{1/8}x^{1/8}P^{1/4}). With P = n^{1/7} this gives a(n) ≪ n^{1/4−1/28}.
- *Archimedean regime of the 1987 method: FALSE as a route past 3/16.*
  - Take the half-integral Kuznetsov formula at a squarefree n, with the Shimura preimage F of an exceptional u (ν_F = ν/2) and moduli c ∼ y ≫ n².
  - (a) Without averaging, (5.2)/(5.3) give Σ_{c∼y}c^{−1/2}K(n,n;c) ≪ y^{3/4}n^{1/2+ε}, hence 2ν_F ≤ 1/4, i.e. ν ≤ 1/4. This is an arithmetic proof of Selberg's 3/16 through weight 1/2: Weil is needed only at modulus ≍ √c, and the square-root saving comes from the explicit Salié evaluation.
  - (b) Averaging over levels cannot improve (a). The Cauchy diagonal costs y^{1/2}P^{−1/2} and the level diagonal costs P. Beating y^{1/4} needs P > y^{1/2} and P < y^{1/4} at once.
  - (c) In the near-balanced range A ≍ B, Poisson in a followed by Kuznetsov at level n gives exactly ν ≤ ν₀, the exceptional parameter at level n. This is the bootstrap identity of cycle 81.
  - The reading of cycle 82 ("1996 transfers the 1987 saving through the archimedean place") is therefore wrong. The 1987 device works only in a *transition range*, and the forced-zero family creates exactly that range.
- *Reconstruction (paper; exponent check exact).* Restrict the twist moduli of the sym² ⊗ ψ family to **q = p·r**, with p ∼ P prime and r ∼ R coprime to p. This is the family analogue of averaging over levels.
  - Put T = Σ_{r}Σ_{p}Σ_m λ(m)W(m/L)Kl₃(am; pr) with L = Q³/X. Apply Cauchy–Schwarz over (r, m), keeping the p-sum inside.
  - The diagonal is ≪ LQ³ (Parseval, L ≥ Q). The off-diagonal is completed modulo M = p₁p₂r.
  - By the Chinese remainder theorem the complete sum C(h) = C₁C₂C₃ factors as follows.
    - C_i = Σ_x Kl₃(bx; p_i)e(γx/p_i) = p_i S(1, ·; p_i). This is `fourier_hyperKloosterman_three`, so |C_i| ≤ 2p_i^{3/2} by Weil, and C_i = 0 when p_i | h (`sum_hyperKloosterman_three`). In particular C(0) = 0.
    - C₃ = Σ_x Kl₃(β₁x; r)Kl₃(−β₂x; r)e(γx/r) needs square-root cancellation, |C₃| ≪ r^{5/2}.
  - Result: **T ≪ Q²L·P^{−1/2} + L^{1/2}P^{1/4}Q^{9/4}** (up to logarithms). Inserted in the family (main QX^{2ν}, switched off-diagonal ≲ X, dual Q^{−3}X·T), the constraints are 2ν > max(a − b/2, 1/2 − a/4 + b/4, 1 − a) with Q = X^a, P = X^b.
  - The optimum is b = 2/7, a = 4/7, giving **ν ≤ 3/14, Iwaniec's exponent exactly**. At the optimum:
    - L = X^{5/7} = Q^{5/4} and T ≪ Q³, as cycle 94 required;
    - Q = X^{4/7}, the level ϑ = 4/7 of cycle 95;
    - P = √Q, a balanced factorisation.
  - The Type II obstruction of cycle 84 disappears because only one prime factor sits inside the Cauchy–Schwarz. The Poisson modulus drops from Q² to PQ = Q^{3/2}.
- *Deligne-free variant.* Take r = s² with s prime.
  - Stationary phase at even exponent is exact: Kl₃(y; s²) = s²Σ_{z³≡y (s²)} e(3z/s²) for s ∤ 3y. Hence |Kl₃(y; s²)| ≤ 3s², and Kl₃(y; s²) = 0 for s | y.
  - C₃ = s⁴Σ_κΣ_{z unit mod s²} e((3(1+κ)z − γβ̄₁z³)/s²), with κ³ ≡ −β₂β̄₁. Each inner sum equals s·Σ over the stationary points mod s, so it is ≤ 2s when s ∤ γ. It vanishes when s | γ unless p₁³ ≡ p₂³ (s), and then it is ≤ s(s−1).
  - With these bounds the completed off-diagonal is ≤ 36(p₁p₂)^{3/2}s⁵(1 + log M) in every case.
  - The only inputs are Weil's bound for Kl₂ (formal: `EstermannKloostermanSaving.norm_kloostermanSum_le_weil`) and elementary exponential sums. The thinning of the family (count PS instead of Q) cancels out of the exponent law.
- **Verdict: REDISCOVERED (the bound is Iwaniec 1996), with a Deligne-free and Katz-free proof of the exponential-sum core that we have not seen in the literature.** This closes the [OPEN CORE] of cycles 82–97 at paper level.
- *Survivor theorem to formalize (Theorem A, finite and unconditional).* Let a be fixed, 𝒫, 𝒮 disjoint sets of primes > 3 not dividing a, p ≤ 2P, s ≤ 2S, and α supported on [1, L]. Then
  |Σ_{s∈𝒮}Σ_{p∈𝒫}Σ_m α_m Kl₃(am; ps²)|² ≤ |𝒮|²‖α‖²(C₁|𝒫|S⁴P²(L + P) + C₂|𝒫|²P³S⁵ log(PS)).
- *Paper proof of Theorem A (dependency-closed; Lean plan in this order).*
  - **L1 (prime square, first-order shift).** Let ε = s in ℤ/s², so ε² = 0 and (x(1+εt))⁻¹ = x⁻¹(1−εt).
    - For a unit y, Kl₃(y; s²) = Σ_{x₁,x₂ units} e((x₁+x₂+yx̄₁x̄₂)/s²).
    - Averaging over the shifts x_i ↦ x_i(1+εt_i), t_i ∈ ℤ/s², and using Σ_t e(εtc/s²) = s²[s | c], leaves only the pairs with x₁ ≡ x₂ and x₁³ ≡ y (mod s). There are ≤ 3·s·s of them, so |Kl₃(y; s²)| ≤ 3s².
  - **L2 (prime-square correlation).** Apply the same five-variable shift to C₃ = Σ_{x unit}Kl₃(β₁x)Kl₃(β₂x)e(γx/s²), with phase F = x₁+x₂+x₃+x₄ + x(β₁x̄₁x̄₂ + β₂x̄₃x̄₄ + γ).
    - The critical set mod s is u³ = β₁x, v³ = β₂x, u + v + γx = 0. Hence x = β̄₁u³ and v = κu with κ³ = β₂β̄₁ (≤ 3 values), and u² = −(1+κ)β₁γ̄ (≤ 2 values) when s ∤ γ.
    - So there are ≤ 6 critical points, each with s⁵ lifts, and |C₃| ≤ 6s⁵. The trivial bound is |C₃| ≤ 9s⁶.
  - **L3 (prime part).** Σ_{x unit mod p}Kl₃(bx; p)e(γx/p) = pS(1, −(γb̄)⁻¹; p) − Kl₃(0; p), and Kl₃(0; p) = 1. So the sum is ≤ 2p^{3/2}+1 for γ ≠ 0 and has size 1 for γ = 0.
  - **L4 (Parseval at p).** Σ_x |Kl₃(x; p)|² = p⁻¹Σ_β|K̂(β)|² = pΣ_{β≠0}|S(1, β; p)|² ≤ 4p³.
  - **L5 (completion).** For an M-periodic f = M⁻¹Σ_h F(h)e(h·/M): |Σ_{m=1}^{L} f(m)| ≤ (L/M)|F(0)| + M⁻¹Σ_{h≠0}|F(h)|·2/|e(h/M)−1|.
    - Since |e(θ)−1| ≥ 4‖θ‖, Σ_{ζ^M=1, ζ≠1} 2/|ζ−1| ≤ M(1 + log M).
    - For f = A₁(m mod p₁)A₂(m mod p₂)B(m mod s²), the map (h₁, h₂, h₃) ↦ e(h₁/p₁ + h₂/p₂ + h₃/s²) is a bijection onto the M-th roots of unity. The terms with s | h₃ go onto the (M/s)-th roots.
  - **Assembly.** Cauchy–Schwarz over (s, m) with the p-sum inside; the diagonal comes from L1 + L4; the off-diagonal from L5 with L2 (s ∤ h₃), the trivial bound (s | h₃) and L3. This gives
    |T|² ≤ |𝒮|‖α‖²·Σ_s[Σ_p 36s⁴(L/p+1)p³ + Σ_{p₁≠p₂}((L/M)·9s⁶ + (2p₁^{3/2}+1)(2p₂^{3/2}+1)·15s⁵(1+log M))].
- *Next conjecture tested (beyond 3/14 with the same tools).* Iterating the Cauchy–Poisson step needs cancellation in the completed variable h. Its length is H = M/L = X^{1/7}, far below the modulus X^{6/7}, so no further completion applies. The remaining sums over r, p₁, p₂ are horizontal (moduli). **Heuristic ceiling: 3/14 for this method.** Any further gain needs horizontal cancellation, and the family's absolute ceiling is 1/8 (cycle 82).

- *Formal (built `--old`, wired, standard axioms, lint clean). Theorem A is closed in Lean with no hypotheses beyond primality and coprimality.*
  - `HyperKloostermanPrimeSquareStationaryPhase`:
    - `norm_hyperKloosterman_prime_sq_le`: |Kl₃(y; s²)| ≤ 3s².
    - `norm_corr_prime_sq_le`: |Σ_{x unit} Kl₃(β₁x)Kl₃(β₂x)e(γx/s²)| ≤ 6s⁵ for s ∤ γ, by the averaging lemma `sum_eq_sum_ite_of_shift` and `card_condRed_le` (at most six critical points).
  - `RootOfUnityIntervalCompletion`:
    - Jordan bound `norm_exp_sub_one_ge`;
    - harmonic bound `sum_two_div_norm_exp_sub_one_le`;
    - Fourier inversion;
    - CRT injectivity `kFreq_mod_injective`;
    - three-factor completion `norm_sum_Icc_triple_le`.
  - `HyperKloostermanFactoredModuliCompleteSums`:
    - L3 `norm_zmodCoeff_klUnit_le` (≤ 2p√p + 1, via the corpus Weil bound);
    - Parseval `sum_norm_sq_zmodCoeff`;
    - `diag_le`, `offdiag_le`.
  - `HyperKloostermanFactoredModuliBilinear.norm_sq_factored_moduli_le` (Theorem A): |T|² ≤ |𝒮|‖α‖²Σ_s(Σ_p 9s⁴(L/p+1)(2p√p+1)² + Σ_{p₁≠p₂} O). Against the trivial bound P²S³L it saves min(P^{1/2}, (L/PS)^{1/2}), which equals Q^{1/4} at the 10/49 parameters.
  - **Remaining for a formal λ₁ ≥ 10/49:**
    - the forced-zero identity for sym²u ⊗ ψ with ψ primitive mod p s² (Shimura's integral, gamma factor, root number τ(ψ)³). The untwisted and square-twist forced zeros are already in `HalfWeightTwisted*`.
    - the mean square Σ_{m≤L}|λ_{sym²}(m)|² ≪ L^{1+ε};
    - the switched off-diagonal bound (trivial, ≍ X);
    - Hecke/non-dihedral reduction for an exceptional form.
**Cycle 99. Conjecture: a moduli large sieve beats Kim–Sarnak in the degree-15 archimedean family.**
- *Setting (Blomer–Brumley 1003.0559 Thm 2, read).*
  - Kim–Sarnak's 7/64 is the archimedean Duke–Iwaniec family F(Y) = Σ_q Σ_{n²≡1(q)} λ_{sym²Π}(n)g(nY) for Π = sym⁴π on GL(5). This is a degree m = 15 family with forced zero at 8ν.
  - The dual is D_q = Σ_m ã(m)m⁻¹Ṽ(m/L)Kl₁₅(m;q) with L = q¹⁵/X. With Deligne, D_q ≪ q⁷, which gives the law ν ≤ (m−1)/((m+1)·8) = 7/64.
- *Observation.*
  - At the threshold Q ≍ X^{1/8}, so L ≍ Q⁷ ≫ Q².
  - Ṽ(x) ∼ x^{1−kν} as x → 0 (the rightmost pole of L_∞(1−s) is at 1 − kν). Hence the ℓ¹ mass of the dual weights sits at m ≍ L, unlike the finite-place version, where the weights ~1/m spread evenly on a log scale.
  - Split at M₀ = L/Q. The piece m ≤ M₀ saves (M₀/L)^{1−kν} by Deligne. On m > M₀, the Farey large sieve (Q² + L)‖β‖² with Parseval Σ_x|Kl₁₅(x;q)|² ≈ q¹⁵ (no Deligne) saves Q^{−1/2}(L/M₀)^{kν−1/2}.
  - The balanced moduli saving is η = 1 − kν. The law becomes t² − 8t + 1 > 0 with t = 1 − kν, i.e. ν ≤ (√15 − 3)/8 ≈ 0.10912 < 7/64, λ₁ ≥ (3√15 − 4)/32 ≈ 0.23810.
- *Attack.* The large sieve needs the mean square ‖β‖₂, i.e. Σ_{m≤M}|λ_{sym²(sym⁴π)}(m)|² ≪ M^{1+ε}. Since sym²(sym⁴) = sym⁸ ⊕ sym⁴⊗ω² ⊕ ω⁴, this is a mean-square bound for sym⁸π. It needs Rankin–Selberg for L(s, sym⁸π × sym⁸π̃) and is unknown for Maass forms. The pointwise route |λ_{sym⁸}(p)| ≤ 9p^{7/8} loses M^{7/8}. Choosing H(s) to kill the pole at 1 − kν only moves the ℓ² mass to m ≍ L; the hypothesis is still needed. Among GL₂ families whose mean squares are known (degree 2, 3, 6 via sym⁴), the dual is short or the base exponent is worse than 7/64.
- **Verdict: CONDITIONAL (BRIDGE).** MS₈: Σ_{m≤M}|λ_{sym⁸π}(m)|² ≪ M^{1+ε} ⇒ λ₁ ≥ (3√15−4)/32, a gain in the fifth digit.
- *Survivor (structural):* at the archimedean place Kim–Sarnak's 7/64 is a **mean-square barrier, not a Kloosterman barrier**. The dual is long (L ≍ Q⁷), and moduli cancellation is available for free once ℓ² control of the degree-15 coefficients exists. The same arithmetic applied to d = 3 gives L ≍ Q, so no gain: this is why Iwaniec needed factored moduli.
**Cycle 100. Audit of the formal path to λ₁ ≥ 10/49 (what Theorem A still needs).**
- *Inputs of the square-twist family argument* (BB (1.7), cycle 98):
  - (A) Theorem A (done in Lean);
  - (B) the functional equation and root number τ(ψ)³ of L(s, sym²u ⊗ ψ) for ψ primitive mod p s² (the SYM2-FE card, which is at prime q so far);
  - (C) a Hecke eigenform in the exceptional eigenspace;
  - (D) the mean square Σ_{m≤L}|λ_{sym²}(m)|² ≪ L^{1+ε}, which is the ‖α‖² of Theorem A's Cauchy–Schwarz;
  - (E) the Mellin/contour assembly of the family identity with the parity and imprimitive corrections;
  - (F) the trivial switched off-diagonal bound, which needs only ℓ¹ of λ_{sym²} in progressions.
- *ℓ¹ versus ℓ².*
  - Hecke gives λ(k²) = Σ_{e|k}μ(e)λ(k/e)² and λ_{sym²}(m) = Σ_{d²k=m}λ(k²). The ℓ¹ bound Σ_{m≤L}|λ_{sym²}(m)| ≪ L log L therefore follows from Rankin–Selberg for u × ū alone (GL₂). That is all the Deligne-trivial dual needs.
  - The Cauchy–Schwarz step of Theorem A needs **ℓ²**, which is the fourth moment Σ|λ_u(n)|⁴ ≪ x^{1+ε}. The fourth moment requires L(s, sym²u × sym²ū), i.e. Gelbart–Jacquet together with GL(3) × GL(3) Rankin–Selberg.
- *Attempts to avoid ℓ², all FAILED.*
  - Positivity of λ(k)² with Cauchy–Schwarz weighted by λ(k)²: the weights are non-smooth, so Poisson in m is blocked.
  - ‖α‖₂² ≤ ‖α‖₁‖α‖_∞ with the GL₂-only θ_fin ≤ 1/4 loses L^{1/2} and kills the Q^{1/4} saving. With Kim–Sarnak's θ = 7/64 a net saving Q^{0.11} survives, but that is no longer GL₂-only and is weaker than Kim–Sarnak.
  - Moving the Cauchy–Schwarz to (s, p) makes the correlations horizontal.
  - The weight-½ Rankin–Selberg (∫|u|²|θ|²E) produces shifted convolutions, not the fourth moment.
- *The degree-2 family u ⊗ ψ* has a GL₂-available ℓ² (Rankin–Selberg of u). It needs a moduli saving η > 1/6 over Weil for Σ_q Σ_m β_m S(1, m; q) with L = Q^{2/3}. Factored moduli give only η = 1/18 (P = Q^{1/9}). With P = Q, completing the h-sum gives exactly the trivial bound. **FALSE as a GL₂-only route past 3/16.**
- **Verdict (formal frontier):** every known route to a formal λ₁ > 3/16 passes through GL(3) information: the fourth moment for Iwaniec, Gelbart–Jacquet for Luo–Rudnick–Sarnak, Kim's sym⁴ for Kim–Sarnak. Iwaniec's "entirely GL₂" claim must use a device for (D) that the reconstruction does not see. **[OPEN CORE, formal]:** the fourth moment of Hecke eigenvalues of a Maass form without GL(3), or a moduli-saving argument that needs only ℓ¹ of λ_{sym²}.
**Conclusion of cycles 56–61** (corrected by cycle 71: Iwaniec's GL₂-only 10/49 passes 3/16 via Shimura's entire twisted sym²). Every *Kloosterman-sum* route checked reaches exactly 3/16, and Kim–Sarnak's 7/64 is reached only through Sym⁴. What stops each route: Weil's bound is sharp for weight-uniform arguments (theta barrier); the bilinear route needs saving past the Cauchy–Schwarz diagonal; the forced-zero route needs Kl₁₅ cancellation over moduli (GL(15)). No new unconditional theorem survived, so nothing was formalized in Lean this batch. Full Selberg remains open.

### User-directed Einasto discovery — cycle 37 input

The literal corpus query `research Einasto` returned 63 declarations across four modules; both result pages and all four source modules were inspected. EinastoGammaMoments contributes 16 declarations: exact Gamma evaluation of every natural moment, integrability, finite total mass, and the exact identity mass(r)=r^3*core(r), with a continuous unit-interval core. EinastoRadialGravity contributes 21: actual derivatives, exact density/slope curvature decompositions, and central limits. EinastoEnergyConditions contributes 18: logarithmic-coordinate slope/density comparison yields sharp necessary-and-sufficient radius thresholds. DilatonEinastoMoments contributes 8: the constructed quartic Schwartz ground-state squared norm equals einastoDensity 0 (-k/4) (-log 4) pointwise; this identity transfers every radial/absolute moment and its integrability.

The inspected dependency DilatonGroundStates classifies the full zero-energy Schwartz kernel by first-order factorization and a constant undressed amplitude. Candidate mechanisms for the active Selberg loop are exact rescaled integral factorization before a singular/noncompact limit, source-derived moment control before a tail passage, and first-order energy decomposition with every boundary term retained. These are proposed transfers, not proved identifications of the Einasto or dilaton fields with the Maass source. The shape index 1/4 in the Einasto identity supplies no spectral quarter inequality by itself. Earlier Selberg ground-state/cusp factorization work must be checked before repeating that mechanism.

The explicit --any follow-up on ground-state, supercharge, half-density, moment-control, and mass-factorization mechanisms reaches 2070 declarations in 437 modules. This is index coverage; only displayed result metadata and the named source mechanisms above were inspected. Artifacts: /tmp/selberg_einasto_corpus37.json, /tmp/selberg_einasto_corpus37_tail.json, /tmp/selberg_einasto_mechanisms37.json. The wider unfolding/periodization/fundamental-domain/orbit/measure query reaches 56520 declarations in 12321 modules; its displayed results exposed ThetaCuspHawkingBMCompactTestUnfolding's finite translates across the entire closed modular cell. That source proof was inspected for the next actual regulator unfolding step; no cell-integral identity for the new SL(2,Z) functional has yet been claimed.

### User-directed evaporation, then entropy discovery — cycle 38 input

Searches ran in the requested order: `research evaporation` returned 78 declarations in 8 modules; `research entropy` returned 1069 declarations in 218 modules. Evaporation results were expanded without the per-module cap; entropy discovery retained module diversity and exploration hits. These are index coverage counts. Selected proof bodies, not every entropy module, were inspected. Search artifacts: /tmp/selberg_evaporation38_all.json and /tmp/selberg_entropy38.json.

Inspected HawkingMassLossClock constructs the actual cube-root time curve and its derivative/entropy laws. Inspected ThetaCuspHawkingEvaporationSingularityOrderSelectionEndpoint gives exact geometric shell-load summability and finite-cutoff failure. Its proposed physical selector is explicitly falsified: inspected ThetaCuspHawkingMassDilationOrderBlindnessNoGo.thetaCuspHawkingMassDilationDyadicShellLoad_eq shows the actual mass-dilated mirror has a shell load proportional to M_n, summable for every order, rather than the proposed order-dependent singular exponent. Inspected CompleteEvaporationAggregateNoGo proves positive shell integration of a shell-independent phase/energy only multiplies it by total lifetime. Candidate transfer: derive an actual Maass shell law first; finite duration or relabeling a defect cannot establish its decay.

Inspected PartitionDivergenceBounds proves two-cell data processing and the lower bound D(sigma||pi)>=(1-a)log(1/pi(A))-log(2) from target mass at least 1-a. Inspected ThermodynamicAffinityFisherBound proves 2(p-q)^2/(p+q)<=(p-q)log(p/q) for positive populations, with exact zero classification. Inspected DeficitEntropyRate proves the subadditive split of rho*log(C/rho) and exponential-affine decay. These suggest testing source-derived finite-partition entropy for cusp mass and source-derived entropy/current control for congruence directions. No uniform Maass relative-entropy bound or sharp global constant has been established. The existing SelbergMaassTraceRadial source already has the full Fisher decomposition, so merely rephrasing that identity as entropy is not new progress. Nodal contributions remain part of the required source comparison.

An explicit --any follow-up across entropy tails, relative entropy, logarithmic Sobolev, Fisher information, dyadic shells, and uniform integrability reached 292 declarations in 98 modules. Displayed result metadata were inspected; the next mathematical test must discharge an actual source entropy or shell estimate, not assume it as an endpoint premise.

### Refreshed user-directed evaporation, then entropy discovery

The literal searches were repeated in the requested order against the current corpus: `evaporation` has 78 declarations across eight modules; `entropy` has 1076 across 221. All 78 and all 1076 matching declaration records were retrieved with the module cap removed and explicit result limits. These are complete query-result counts, not a claim to have read every proof body. Saved results: `/tmp/selberg_evaporation_latest.json` and `/tmp/selberg_entropy_latest.json`. Each query contains one term, so default AND semantics cannot narrow it accidentally.

Read the endpoint selector's exact geometric-load classification and its explicitly falsified source identification; checked `thetaCuspHawkingMassDilationDyadicShellLoad_eq` and its actual all-order summability proof. Read the complete-evaporation aggregate proof: shell-independent quadratic energy is multiplied by the positive total duration, not erased. This reinforces the next source test: derive an actual scale-dependent Maass cost before asking whether summability forces a restriction; a chosen singular exponent cannot supply that restriction.

Read `ThermodynamicAffinityFisherBound.pseudoEntropyProductionValue_le_entropyProductionValue`, including its logarithm inequality proof: for positive p,q, `2*(p-q)^2/(p+q) <= (p-q)*log(p/q)`. Read `FiniteNoiseMixingApplications`' actual bistochastic construction, exact variance-deficit identity, and Shannon entropy monotonicity under finite mixing. These suggest testing a source-derived finite congruence mixing operator and identifying its variance loss or entropy production with an actual Maass-current quantity. The stochastic weights, source identification, and a uniform quantitative estimate must be proved; the scalar entropy inequality alone provides none of them. The existing radial/Fisher identity and new nodal residual must remain explicit rather than being renamed an entropy estimate. The finite-entropy plateau module's introductory definitions and replica-order-one identities were also inspected; its finite-dimensional entropy floor has not been identified with a Maass spectral bound.

## Verification log

- 2026-09-09, cycle54: complete scratch/source checks passed cleanly; final single-module build rebuilt only `SelbergMaassKernelWronskian` (5.8s). All30 public declarations passed standard-axiom, unchanged-source-hash, complete API/search, and unique-umbrella audits. Index refresh and repository lint passed. Original-source improper endpoint, full complex tail positivity, and quantitative mixed-current bound are proved. Strictly serial foreground Lean; all owned handles terminal and no remaining owned worker. No full/umbrella build, numerical experiment, added axiom, commit, or push. Full Selberg remains active and unproved.

- 2026-09-09, cycle53: complete scratch/source checks passed; final single-module build rebuilt only `SelbergMaassPhaseStress` (10s). All28 public declarations passed standard-axiom, unchanged-source-hash, exact-module API/search, and unique umbrella checks. Index refresh and repository formal lint passed; earlier unrelated concurrent wiring failures are historical. Strictly serial foreground Lean; all task-owned handles terminal. No full/umbrella build, numerical experiment, added axiom, commit, or push. Full Selberg remains active and unproved.

- 2026-09-09, cycle52: complete scratch/source checks, final single-module build (6.9s; only MixedLoss rebuilt), all26 standard-axiom checks, unchanged source SHA256, exact-module API/search coverage, and unique umbrella wiring passed. Repository lint currently reports only unrelated concurrent HTGeometry modules `GomesPolynomialExponentialIntegrability` and `GomesPolynomialExponentialTails` awaiting their own wiring. Strictly serial foreground Lean; all task-owned handles terminal. No full/umbrella build or numerical experiment. Full Selberg remains active and unproved.

- 2026-09-09, cycle51: complete phase-loss scratch/source checks passed; final single-module build rebuilt only `SelbergMaassPhaseRellich` (5.2s). All25 public declarations passed standard-axiom, unchanged-hash, full API/search, and unique-wiring audits. Final global lint reports only two unrelated concurrent HTGeometry modules awaiting their umbrella wiring (`GomesDilatonDensityShape`, `GomesDilatonMeasureReconstruction`). Every task-owned Lean handle is terminal; no remaining worker. Strictly serial cycle51 checks; no full/umbrella builds or numerical experiment. Full Selberg remains active and unproved.

- 2026-09-09, cycle50: three complete scratch/source checks and targeted final builds passed;45 public declarations passed standard-axiom audit with unchanged source hashes. Exact API/search coverage, unique umbrella wiring, index refresh, and formal lint passed. Rellich audit was started before the prior Green handle had been confirmed terminal, causing a duplicate dependency build; both handles subsequently exited and process cleanup found no remaining task-owned worker. No full/umbrella build or numerical experiment. Full Selberg remains active and unproved.

- 2026-09-09, cycle49: complete scratch and exact source checks passed. The final single-module build rebuilt only `SelbergMaassCharacterCuspGlue` (6.8s). All28 public declarations passed post-build axiom auditing with only standard Lean axioms and unchanged source hash. Exact-module API/search coverage, unique umbrella import, index refresh, and repository formal lint passed. All task-owned handles are terminal. No full/umbrella build, build overlap, numerical experiment, commit, or push. [Completed finite assembly and integrated seam estimate](../../selberg-character-core-green.md). Full Selberg remains active and unproved.

- 2026-09-09, cycle48: all three complete scratch and exact source checks passed. Serialized final builds rebuilt only their named target (CharacterDynamics13s, CharacterCoreGreen10s, ReadoutCusp21s). All52 public declarations passed post-build axiom checks using only standard Lean axioms; all three source hashes stayed unchanged. Exact-module search/API coverage, single umbrella imports, index refresh, and repository formal lint passed. Every task-owned handle is terminal; no owned Lean/Lake worker remains. No full/umbrella build, build overlap, numerical experiment, commit, or push. [Actual core and observed cusp identities, with finite assembly still in progress](../../selberg-character-core-green.md). Full Selberg remains unproved and active.

- 2026-09-09, cycle47: both complete scratch files and source checks passed. Final builds were serialized and rebuilt only their named target (ProjectionFlux11s; CharacterSeamFlux4.7s). All29 public declarations passed post-build axiom checks with only standard Lean axioms; both source hashes stayed unchanged. Exact-module search/API coverage, single umbrella imports, index refresh, and repository formal lint passed. All task-owned handles are terminal and no task-owned Lean worker remains. No full/umbrella build, build overlap, numerical experiment, commit, or push. [Actual coherent boundary flux and complete audit](../../../3-formalized/selberg-character-seam-flux.md). Full Selberg remains unproved and active.

- 2026-09-09, cycle46: both complete scratch files and exact source checks passed. Successful final builds were serialized and rebuilt exactly their named target (InversionPhaseEnergy14s; CharacterGradient8.8s). All47 public declarations passed the post-build axiom audit with only standard Lean axioms; both source hashes stayed unchanged. All47 are indexed and present under their exact module in the API catalog; both umbrella imports occur once. Index refresh and final repository lint passed. Initial lint's unrelated `ThetaCuspHawkingBMCausalRiemannKernel` import was resolved externally before the final check. One prematurely started source check briefly overlapped its scratch check; it was interrupted (exit130), both handles were confirmed terminal, and the source check resumed serially. That interrupted attempt is excluded from all passing audits. No full/umbrella build, numerical experiment, commit, or push. [Exact phase/full-gradient law and audit](../../../3-formalized/selberg-inversion-phase-energy.md). The full Selberg goal remains unproved and active.

- 2026-09-09, cycle45: complete scratch/source checks passed. Two serialized final single-module builds rebuilt only their named target (1.9s/6.6s). All39 public declarations passed the post-build scratch axiom audit with only standard Lean axioms; source hashes stayed unchanged. Exact-module API/search coverage and single area-umbrella imports passed. Index refresh and repository formal lint passed with existing large-file warnings. Every task-owned Lean/build handle is terminal. Audit manifest: `/tmp/selberg_gram47_audit.json`. [Complete arithmetic kernel proof and audit](../../../3-formalized/selberg-inversion-gram-fibres.md). No full/umbrella build, computation, commit, or push. The actual Gram probability law is proved; the phase-defect and uniform physical gradient comparison remain next. Selberg remains unproved and active.

- 2026-09-09, cycle44: both complete scratch/source checks passed. Two serialized final single-module builds rebuilt only their named target (8.6s/4.3s). All44 public declarations passed post-build standard-axiom checks with unchanged source hashes, complete API/search coverage, and unique umbrella imports. Repository lint passed with existing large-file warnings; this also clears cycle43's earlier unrelated shared-tree gate. Both positive source cards are formalized. No full/umbrella build, numerical experiment, commit, or push. The actual inversion coupling is proved; the all-level Selberg goal remains active and unproved. [Proof and artifacts](../../../3-formalized/selberg-character-inversion-coupling.md).

- 2026-09-09, cycle 43: complete scratch and exact source checks passed. The final single-module build rebuilt only `SelbergMaassUnipotentFourier` (7.3s). All 20 public declarations passed post-build axiom checks with standard axioms only and unchanged source hash. All 20 public API/search entries are present and the umbrella import is unique. Initial repository lint failed on nine unrelated unreachable `HTGeometry.ConservativeDissipative*` modules. Those were subsequently wired outside this task; cycle44 repository lint passed and the source card is now formalized. No full/umbrella build, numerical experiment, commit, or push. The all-level Selberg goal remains active and unproved. [Exact proof and artifacts](../../../3-formalized/selberg-unipotent-fourier-filter.md).

- 2026-09-09, cycles 41–42: all five complete scratch and needed-source checks passed. Five serialized final single-module builds passed and rebuilt only their named target. All 58 public declarations passed post-build axiom auditing with standard axioms only; all five source hashes stayed unchanged. All 58 public declarations are searchable and appear in the API, all five umbrella imports are unique, and repository formal lint passed with pre-existing large-file warnings. [Exact source proof, module inventory, and audit artifacts](../../../3-formalized/selberg-maass-strip-gap.md). No full/umbrella build, numerical experiment, commit, or push. Both positive subresults are completed; the uniform Selberg goal remains active and unproved.

- 2026-09-09, cycle 40 density/carrier continuation: all three complete scratch and needed-source checks passed without warnings. Final serialized single-module builds rebuilt only their named target (CurrentDensity 4.1s, CurrentDensityMeasure 3.4s, CurrentCarrier 3.5s). All 39 public declarations, including two measure instances, passed post-build axiom checks with standard axioms only; three source hashes stayed unchanged. All 39 are searchable, 37 noninstance API rows are present, and all three imports occur exactly once. Repository formal lint passed with existing large-file warnings (`/tmp/selberg_currentdensity42_lint.log`); the prior external wiring error was resolved outside this task. All task-owned Lean/build handles are terminal. Cycle 40 now has 11 modules and 124 public declarations; cycles 39–40 together have 18 modules and 215 public declarations. No full/umbrella build, computation, commit, or push. [Proof and audit](../../../3-formalized/selberg-current-density-identification.md). The actual density, disjoint carriers, and separate modular invariance are proved; the quarter comparison remains open. Selberg remains unproved and active.

- Cycle 40, actual current/residual measures: all four complete scratch and needed-source checks passed, followed by serialized final single-module builds that rebuilt only their named target (CurrentTests 3.4s, CurrentFunctional 3.1s, CurrentMeasures 3.0s, ResidualSupport 3.2s). All 47 public declarations, including four measure instances, passed post-build axiom checks using only standard axioms; source hashes stayed unchanged. All 47 are searchable, 43 noninstance declarations appear in the API catalog, and every new module is imported exactly once. Repository lint reports one unrelated concurrent unreachable module, `HTGeometry.FokasLenellsRawPhase` (`/tmp/selberg_currentmeasure41_lint.log`); no error concerns these four modules. All task-owned Lean/build handles are terminal. Cycle 40 now has eight source modules and 85 audited public declarations; cycles 39–40 together have 15 modules and 176 public declarations. No full/umbrella build, commit, or push. The positive source-measure split and nodal residual support are proved; current absolute continuity and the quantitative quarter comparison remain open. [Proof and audit](../../../3-formalized/selberg-current-nodal-measures.md). Selberg remains unproved and active.

- Cycle 40, pair/phase/transport/curvature extensions: all three complete scratch and needed-source checks passed without warnings. Final single-module builds rebuilt only their targets (PairPhaseEnergy 4.6s, CurrentTransport 3.5s, CurrentCurvature 3.2s). All 29 public declarations passed the post-build scratch axiom audit with only standard axioms; source hashes stayed unchanged. Index coverage, exact single umbrella imports, source/card whitespace, and card links passed. **Repository lint currently fails four unrelated concurrent umbrella-reachability errors**: `SelbergScatteringNativeResidual`, `FokasLenellsRawBounds`, `FokasLenellsRawEvolution`, and `FokasLenellsRawInteraction` (`/tmp/selberg_pairphase40_lint.log`). No error concerns these three modules. All task-owned Lean/build handles are terminal; other agents' processes were left untouched. No full/umbrella build, commit, or push. Cycle 40 now has four source modules and 38 audited public declarations; cycles 39–40 together have 11 modules and 129 public declarations. The exact curvature split retains both current squares and regulator-gradient energy, including `curvatureWeight=gradientDensity/e` at original nodes. [Proof and audit](../../../3-formalized/selberg-pair-phase-current-curvature.md). The limiting source-measure split and quantitative quarter comparison remain open; Selberg remains unproved and active.

- Cycle 40, first module: complete scratch, needed source olean, and final single-module build passed without new module warnings. The final build rebuilt only `SelbergMaassSourceCurrents` (3.8 seconds; other graph jobs cached). All nine public declarations passed the scratch axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired exactly once, all nine declarations are indexed, source whitespace passed, and repository formal lint passed with existing large-file warnings (`/tmp/selberg_source_currents40_lint.log`). All task-owned Lean/build handles are terminal; other agents' processes were left untouched. No full or umbrella build, commit, or push. Together with cycle 39, eight source modules and 100 public declarations are audited. Cycle 40 and the Selberg goal remain open; phase/current energy reconstruction and the actual quantitative comparison remain outstanding.

- Cycle 39: all seven complete scratch/source checks and serialized final single-module audits passed without new module warnings. PositiveEisenstein rebuilt 104 needed dependencies plus its target; EisensteinPlane rebuilt five plus its target; the remaining five audits rebuilt only their target. No full or umbrella build ran. All 91 public declarations passed initial and post-build axiom checks, using only standard axioms or none. Seven source hashes remained unchanged, all seven imports occur once, and index coverage includes 105 declarations with private helpers. **Final repository lint passed**, with existing large-file warnings (`/tmp/selberg_eisenstein39_lint_final.log`); the earlier nine unrelated wiring errors no longer occur and were not fixed by this task. Every cycle-39 Lean/build handle is terminal. No task commit or push. [Exact positive survivor and audit](../../../3-formalized/selberg-scalar-curvature-flexibility.md). The actual scalar ratio is every positive number; no Maass eigenform was constructed or excluded. Selberg remains unproved and active.

- Cycle 38: all four complete scratch proofs, needed source olean checks, and serialized final single-module builds passed. Each final build rebuilt only its target (secants 1.6s, uniform cusp 32s, uniform tails 14s, quotient mass 12s); the latter three replayed the existing EvenL2LogUnitary informational suggestion without new warnings. All 33 public declarations have only propext, Classical.choice, and Quot.sound dependencies. All four modules are wired exactly once, and index coverage includes all 33 public declarations plus 2 private helpers. Source/card/umbrella whitespace passed. **Repository formal lint passed**, with existing large-file warnings (/tmp/selberg_uniform_mass38_lint.log). All task-owned handles are terminal; final inspection found no Lean or Lake process. No task commit or push. [Exact paper proof and audit](../../../3-formalized/selberg-uniform-regulator-cusp-curvature.md). Uniform tails hold over every positive regulator, the actual compact-orbit total equals lambda*M/2, and the actual limiting curvature measure is nonzero for every original exceptional source. The spectral quarter lower comparison remains unproved; Selberg stays active.

- Cycle 37: both complete scratch proofs, needed source olean checks, and serialized final single-module builds passed. Each build rebuilt only its own target (unfolding 41s, actual cell curvature 4.0s), with the existing EvenL2LogUnitary informational replay and no new module warnings. All 21 public declarations passed the scratch axiom audit with only propext, Classical.choice, and Quot.sound. Both modules are wired; the refreshed corpus audit covers all 21 public declarations plus 3 private helpers. Source/card/umbrella whitespace passed. **Repository formal lint passed**, with existing large-file warnings (/tmp/selberg_cell_curvature37_lint.log), superseding cycle 36's unrelated wiring errors. All task-owned handles are terminal; final inspection observed separate Fokas-time and horizon-domain Lean checks, left untouched. No task commit or push. [Exact paper proof and audit](../../../3-formalized/selberg-full-cell-curvature-unfolding.md). Standard-cell normalization, original regulator convergence, and the uniform signed functional budget are proved; limiting total mass equality and the quarter lower comparison remained open at this stage. Selberg stays active.

- Cycle 36: all three complete scratch proofs, needed source olean checks, and serialized final single-module builds passed. Each final build rebuilt only its target (37s, 15s, 18s), with the existing EvenL2LogUnitary informational replay and no new module warning. All 40 public declarations passed the scratch axiom audit with only propext, Classical.choice, and Quot.sound. All three modules are wired, and the refreshed corpus audit contains all 40 declarations. Source/card/umbrella whitespace checks passed. **Repository formal lint failed only on unrelated, unwired HTGeometry.HawkingMassLossClock and HTGeometry.InformationSurfacePacking** (/tmp/selberg_quotient_curvature36_lint.log). Every task-owned Lean/build handle is terminal; another task's hb-outgoing-domain axiom check was left untouched. No task commit or push. [Exact paper proof and audit](../../../3-formalized/selberg-actual-positive-quotient-curvature.md). The unique positive functional on literal compact orbit fields is proved, including original regulator convergence; standard-cell total mass and the quarter comparison remain open. Selberg stays active.

- Cycle 35: both complete scratch proofs, needed source olean checks, and serialized final single-module builds passed. Each build rebuilt only its target (scaling 28s, atomlessness 10s), with an existing EvenL2LogUnitary informational replay and no new module warnings. All 27 public declarations, including NullSingletonClass, passed the scratch axiom audit with only standard Lean axioms. Both modules are wired/indexed; task-source/card/umbrella whitespace passed. **Repository formal lint passed**, with existing large-file warnings (/tmp/selberg_curvature_noatoms35_lint.log), superseding the prior unrelated wiring failure. Every task-owned handle is terminal; final inspection found no Lean or Lake process. No task commit or push. [Exact paper proof and audit](../../../3-formalized/selberg-actual-curvature-no-atoms.md). The actual curvature measure is atomless, including at common source zeros; quotient curve-boundary weights and the quarter comparison remain open. Selberg stays active.

- Cycle 34: both complete scratch proofs, needed source olean checks, and serialized final single-module builds passed. Each build rebuilt only its target (covariance 10s, transport 5.7s); both replayed an existing EvenL2LogUnitary informational suggestion, with no new module warning. All 16 public declarations passed the scratch axiom audit with only the standard three axioms. Both modules are wired and indexed; task-source/card/umbrella whitespace passed. **Repository lint failed only on unrelated, unwired HTGeometry.DilatonSchwartzTransform** (/tmp/selberg_curvature_transport34_lint.log). All task-owned Lean/build handles are terminal; another agent's DilatonOperator scratch process was left untouched. No task commit or push. [Exact paper proof and audit](../../../3-formalized/selberg-actual-curvature-transport.md). Actual modular curvature transport is proved; quotient boundary/stabilizer control and the quarter comparison remain open. Selberg stays active.

- Cycle 33: all four complete scratch proofs, needed source olean checks, and serialized final single-module builds passed without new warnings; each build rebuilt only its target. All 40 public declarations, including the regularity and compact-finiteness instances, passed the scratch axiom audit with only the standard three axioms. All four modules are wired and indexed; task-source/card/umbrella whitespace passed. **Repository lint failed only on unrelated, unwired RHTower.FokasLenellsHardyOrientation** (/tmp/selberg_curvature_measure_lint.log). All task-owned Lean/build handles are terminal; final inspection found no Lean or Lake process. No task commit or push. [Exact dependency-closed paper proof and audit](../../../3-formalized/selberg-actual-curvature-measure.md). The actual regular curvature measure, continuous-test convergence, uniqueness, C² source identity, and quantitative error are proved. Actual measure transport, quotient boundary control, and the quarter comparison remain open. Selberg stays active.

- Cycle 32: both complete scratch proofs, needed source olean checks, and serialized final single-module builds passed without new warnings; each build rebuilt only its target. All 54 public declarations passed the scratch axiom audit with only the standard three axioms. Both modules are wired and all declarations indexed; task-source/card/umbrella whitespace checks passed. **Repository lint failed only on unrelated HTGeometry.FokasLenellsOrbitDecay, FokasLenellsOrbitEntries, FokasLenellsOscillatoryOrbit, and FokasLenellsScatteringDecay**, recorded in /tmp/selberg_weak_curvature_lint.log. All task-owned Lean/build handles are terminal; final inspection found no Lean or Lake process. No task commit or push. [Exact paper proof and audit](../../../3-formalized/selberg-actual-weak-curvature.md). Actual positive weak curvature and its compact order-zero bound are proved for every real eigenvalue; the representing measure and quarter comparison remain open. Selberg stays active.

- Cycle 31: all three complete scratch checks and serialized final single-module builds passed, each rebuilding only its target. All 36 public declarations, including the regulator-filter instance, passed the scratch axiom audit with only the standard three axioms. All modules are wired/indexed, and task-source/card whitespace checks passed. **Repository lint failed only on unrelated HTGeometry.FokasLenellsScatteringContinuity and HTGeometry.FokasLenellsSpectralContinuity** (/tmp/selberg_regulator_mass_lint.log). All task-owned Lean/build handles are terminal. No task commit or push. [Exact paper proof and audit](../../../3-formalized/selberg-quantitative-regulator-curvature-limit.md). Quantitative regulator removal in the total curvature budget is proved; local weak curvature and the quarter comparison remain open. Selberg stays active.

- Cycle 30: all complete scratch/source checks and four serialized single-module final builds passed. First three rebuilt only their target; the full-budget build rebuilt its needed SelbergMaassTraceMass dependency and target. All 42 public declarations passed the scratch axiom audit with only the standard three axioms. All four modules are wired/indexed; whitespace checks passed. **Repository lint failed only on unrelated untracked, unwired RHTower.MobiusDivisorFibreCoareaVariance and HTGeometry.FokasLenellsContourSymmetry** (/tmp/selberg_full_curvature_lint.log). Final process inspection found no Lean or Lake process; all task handles are terminal. No task commit or push. [Exact paper proof and complete audit](../../../3-formalized/selberg-regularized-cusp-and-full-curvature-budget.md). The full standard-area budget is proved; regulator-uniform passage and the quarter comparison remain open. Selberg stays active.

- Cycle 29: all four complete scratch checks and four serialized single-module final builds passed without new warnings, each rebuilding only its named target. All four modules are wired/indexed. All 57 public declarations passed the scratch axiom audit with only the standard three axioms or none. Whitespace checks passed. **Repository lint failed only on unrelated untracked, unwired `HTGeometry.FokasLenellsUniformizedFrame`** (`/tmp/selberg_augmented_lint.log`). All task-owned handles are terminal; no task commit or push. [Full paper proof and audit](../../../3-formalized/selberg-augmented-chord-capacity-and-nodal-resistance.md). The unqualified uniform-resistance shortcut is retired with exact nodal and actual-source positive survivors. The global quarter estimate and Selberg remain unproved.


- Cycle 28: all complete scratch/source checks and six serialized single-module final builds passed, each rebuilding only its named target. The five new modules are wired and indexed. All 88 public declarations across the six audited modules passed the axiom audit with only the standard three axioms or none. Whitespace checks passed. **Repository lint failed only on unrelated untracked, unwired `HTGeometry.FokasLenellsLeftJost` and `HTGeometry.FokasLenellsScattering`** (`/tmp/selberg_regularized_lint.log`). All task-owned handles are terminal; no task commit or push. [Full paper proof and audit](../../../3-formalized/selberg-regularized-curvature-and-nodal-charge.md). The nodal-limit shortcut is retired with its full positive survivor; the source quarter comparison and Selberg remain unproved.


- Cycle 27: both complete scratch checks and both direct source checks passed without warnings. Both serialized `LEAN_NUM_THREADS=1 lake build <module>` audits passed, each rebuilding only its named target. All 35 public declarations passed the axiom audit with only the standard three axioms or none; modules are wired/indexed. **Latest repository lint failed only on unrelated untracked, unwired `HTGeometry.FokasLenellsSobolevEnergy`** (`/tmp/selberg_direction_nodal_lint.log`). Prior `FokasLenellsUniformization` lint error resolved concurrently. All task-owned handles are terminal; no task commit or push. [Full paper proof and audit](../../../3-formalized/selberg-source-directions-and-nodal-reversal.md). The combined core/Bessel lower bound and Selberg remain unproved.

- Cycle 26: strict physical total mass, cutoff independence, actual radial/angular square completion and zero classification, full source Fisher identity, and a scoped smooth-periodic norm-only reconstruction counterexample are proved in three narrow modules. All scratch/source checks and all three serialized targeted final builds passed; each final build rebuilt only its target. All 46 public declarations passed the axiom audit with only the standard three axioms or none. Sources are wired/indexed; whitespace checks passed. **Latest repository lint failed only on unrelated untracked, unwired `HTGeometry.FokasLenellsUniformization`** (`/tmp/selberg_mass_radial_lint.log`). All task-owned Lean/build handles are terminal; no task commit was made. [Full proof and audit](../../../3-formalized/selberg-positive-mass-and-radial-defect.md). The scalar-norm toy is not claimed to be Maass/cuspidal and does not contradict recovery using the actual eigenvalue equation. The combined core/Bessel lower bound remains unproved; Selberg stays active.

- Cycle 25: actual pointwise trace energy, modular current transport/cancellation, paired Stokes, standard-area Fubini, and the complete physical core-plus-cusp quarter form are proved across five narrow Selberg modules. All five scratch/source checks and serialized targeted final builds passed without new warnings; each final build rebuilt only its named target. All 94 public declarations passed the axiom audit with only the standard three axioms or none. Modules are wired/indexed; whitespace checks passed. **Latest repository lint failed only on five unrelated untracked, unwired HTGeometry modules:** `FokasLenellsJumpGeometry`, `FokasLenellsSingularPhase`, `InwardPlaneDisplacementReturn`, `InwardPlanePrescribedStream`, `PolyatomicSpectralRank` (`/tmp/selberg_core_quarter_lint.log`). All task-owned Lean/build handles are terminal; no task commit was made. [Full paper proof and audit](../../../3-formalized/selberg-maass-core-stokes-and-quarter-form.md). The missing combined core/boundary lower bound and strict total mass positivity are not assumed; Selberg remains unproved.

- Cycle 24: all-cusp transport and the finite congruence trace are proved in `SelbergMaassCuspTransport` and `SelbergMaassCongruenceTrace`. The existing general conformal proof is shared through new `HTGeometry.ComplexC2Laplacian`; its previous specialized statement is preserved and directly checked. All three final targeted builds passed, each building only its target. All 47 public declaration axiom checks passed with only the standard three axioms or none. New modules are wired and indexed; whitespace checks passed. **Latest repository-wide lint failed only on unrelated unwired `HTGeometry.GaussianDisplacedSpectralPole`**, currently untracked (`/tmp/selberg_cusp_trace_lint.log`). The first attempted transport audit spawned parallel dependency workers, violating one-worker discipline; that exact task-owned process tree was stopped and terminal exit 143 verified. Narrowing the shared import removed the cause; the subsequent final audits ran sequentially. All task-owned processes are terminal, and final inspection found no Lean/Lake build process. No task commit was made. [Exact proof, build logs, and full audit](../../../3-formalized/selberg-maass-integral-cusps-and-congruence-trace.md). Selberg and the compact-core Green/quarter estimate remain unproved.

- Cycle 23: complete scratch and direct source checks passed without warnings for `SelbergMaassBesselRemainder` and `SelbergMaassBoundaryForm`. Both serialized targeted final builds passed, each rebuilding only its target (`/tmp/selberg_maass_bessel_remainder_build.log`, `/tmp/selberg_maass_boundary_form_build.log`). All 28 public theorem checks in `/tmp/selberg_maass_bessel_form_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired and indexed; corpus queries return the capstones. Tracked/new task-file whitespace checks passed. **Latest repository-wide lint passed**, with existing large-file warnings (`/tmp/selberg_maass_bessel_form_lint.log`); the prior three unrelated unwired-module errors were resolved outside this task. Every task-owned process finished; a separate `DivisorTwentyTwoAnalyticBounds` Lean process was active during the final audit and was not touched. No commit was made by this task. [Exact result and paper proof](../../../3-formalized/selberg-maass-bessel-boundary-form.md). The global Selberg goal remains unproved.

- Cycle 22: complete scratch and direct source checks passed for `SelbergMaassBoundaryFlux`, `SelbergMaassCuspDecay`, and `SelbergMaassTailEnergy` without warnings. All three targeted final builds passed, serialized; the flux build rebuilt the needed `SelbergExceptionalCuspMean` dependency followed by its target, and the other builds rebuilt one target each. Logs: `/tmp/selberg_maass_flux_build.log`, `/tmp/selberg_maass_cusp_decay_build.log`, `/tmp/selberg_maass_tail_energy_build.log`. All 34 public theorem checks in `/tmp/selberg_maass_flux_decay_tail_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. All three modules are wired and indexed; tracked/new task-file whitespace checks passed. Every task-owned process finished; final process audit found no Lean/Lake process. This task made no commits. [Exact result and paper proof](../../../3-formalized/selberg-maass-mass-flux-tail.md). The full Selberg goal remains unproved.
- **Historical cycle 22 repository-wide lint failed on three unrelated unwired HTGeometry modules:** `BistochasticMixingMajorization`, `FiniteNoiseMixingApplications`, and `VolterraSourceRecovery`. No new Selberg module is named in an error; those concurrent modules were not edited or wired speculatively. Existing large-file warnings remain. Log: `/tmp/selberg_maass_flux_decay_tail_lint.log`. The previous passing lint below is historical.

- Cycles 20–21: complete scratch and direct source checks passed without warnings. Targeted final builds passed for `SelbergMaassBoundaryTrace` and `SelbergMaassParseval`, rebuilding one target each; logs `/tmp/selberg_maass_trace_build.log` and `/tmp/selberg_maass_parseval_build.log`. All task Lean invocations were serialized. Eighteen capstone checks in `/tmp/selberg_trace_parseval_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. Both new modules are wired, and refreshed corpus searches return their capstones. Tracked and new task-file whitespace checks passed. **Latest repository-wide formal lint passed**, with existing large-file warnings (`/tmp/selberg_trace_parseval_lint.log`); the prior seven unwired-module errors were resolved outside this task. Every task-owned Lean/Lake handle finished. Other agents' Coppo/CCM processes were active during the process audit and were not touched. This task made no commits. The full Selberg goal remains unproved.

- Cycles 18–19: complete scratch and final direct source checks passed without warnings. Targeted final builds passed for `SelbergBesselBoundaryOperator` (one target rebuilt) and `SelbergMaassFourierModes` (the changed `SelbergMaassFourierMean` dependency followed by the new target, sequentially). Logs: `/tmp/selberg_boundary_operator_build.log`, `/tmp/selberg_maass_fourier_modes_build.log`. All task Lean invocations were serialized. Twenty-four capstone axiom checks across the two `/tmp` audit files report only `propext`, `Classical.choice`, and `Quot.sound`; the Maass audit also imports the existing `SelbergExceptionalCuspMean` successfully. Both new modules are wired and indexed. Tracked and new task-file whitespace checks passed. All task-owned Lean/Lake handles are terminal; a separate agent's `QNMLorentzAuxiliary` build was active at the process audit and was not touched. No commit was made by this task.
- **Historical cycle 18–19 repository-wide lint failed on seven unrelated unwired modules:** RHTower `MobiusDivisorRemainingFrontTransport`; HTGeometry `CoppoFockRotation`, `CoppoJosephsonPotential`, `CoppoKerrPhaseGeometry`, `CoppoNonlocalNoise`, `CoppoPartnerEigenspaces`, `CoppoSSH`. No new Selberg module is named. Log: `/tmp/selberg_fourier_final_lint.log`. The intermediate cycle 18 audit had 23 unrelated unwired modules; concurrent work resolved those entries or changed the set. The cycle 20–21 passing audit above supersedes these historical failures.

- Cycles 16–17: both complete scratch proofs and final direct source checks passed without warnings. Targeted final builds passed for `SelbergBesselBoundaryTrace` and `SelbergBesselBoundaryEnvelope`, rebuilding one target each; logs `/tmp/selberg_bessel_trace_build.log` and `/tmp/selberg_bessel_envelope_build.log`. All Lean checks/builds in this continuation were serialized. Eighteen capstone checks in `/tmp/selberg_trace_envelope_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into RHTower and present in the refreshed corpus index. Tracked and untracked task-file whitespace checks passed. Final process audit found no Lean or Lake process. This task made no commits.
- **Cycles 16–17 repository-wide lint failed on seven unrelated unwired modules:** RHTower `BoundedPlaneDisplacementBatch`, `MobiusDivisorApproximateTwoReserve`, `MobiusDivisorSquareRootWindowCapacity`; HTGeometry `CPVClassicalDynamics`, `CPVSchwarzschildLimit`, `CPVThermalRadiation`, `CPVTwoModeFock`. These concurrent source modules were not edited by this task, and neither new Selberg module is named in the errors. They were not wired speculatively. Log: `/tmp/selberg_trace_envelope_lint.log`. The preceding continuation's passing lint entry is historical, not the current repository-wide result.

- Cycle 14: all four new modules passed scratch/direct checks and serialized targeted final builds. The energy build rebuilt one target (`/tmp/selberg_bessel_energy_build.log`). Both existing compatibility modules passed direct compilation. Fifteen capstone axiom checks in `/tmp/selberg_bessel_boundary_axioms.lean`, importing both old interfaces alongside the new energy module, report only `propext`, `Classical.choice`, and `Quot.sound`. [Exact survivor](../../../3-formalized/selberg-exact-bessel-boundary-energy.md); [failed all-positive-coefficient conjecture](../../../5-failed/selberg-always-positive-bessel-slope.md). The initial interrupted build is excluded from these passing audits.
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
- Cycle 12 index refresh and repository-wide lint passed. The earlier 11 unreachable-module failures no longer occur; they were resolved outside this task. Existing large-file warnings remain. Lint output: `/tmp/selberg_maass_mean_lint.log` (warnings were emitted on stderr). The process audit found no Lean/Lake process. [Exact result and paper proof](../../../3-formalized/selberg-exceptional-cusp-mean.md).
- Cycle 13 scratch and direct source checks passed without warnings. Targeted `lake build GaloisForLFunctions.RHTower.SelbergCuspRelocation` passed (3547 dependency-graph jobs), rebuilding the target and two needed source dependencies. Six further axiom checks report only the standard three axioms. The module is wired into the umbrella. Final index refresh, repository-wide lint, and whitespace checks passed; lint retains existing large-file warnings. Final lint log: `/tmp/selberg_mean_relocation_final_lint.log`. No Lean/Lake process remained.
