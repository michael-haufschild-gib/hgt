# Selberg quarter bound: constructive conjecturing loop

- **ID:** SELBERG-QUARTER-CONJECTURING
- **Stage:** 1-in-progress
- **Goal:** An unconditional Lean proof of the all-congruence Maass cusp quarter bound.
- **Method:** Corpus-derived ingredients → precise conjecture → attempted proof or explicit failure → stronger surviving statement → pivot. Searches discover ingredients rather than stand in for mathematical work.

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
- [ ] Cycle 20: construct the actual Maass Fourier trace in the sequence-space boundary-form domain, using the proved frequency bound.
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

This target is not yet proved or used. Identifying the resulting boundary series with a physical trace/energy theorem and controlling the quotient-core response remain separate obligations. No inference of global positivity is made from summability.

## Verification log

- Cycles 18–19: complete scratch and final direct source checks passed without warnings. Targeted final builds passed for `SelbergBesselBoundaryOperator` (one target rebuilt) and `SelbergMaassFourierModes` (the changed `SelbergMaassFourierMean` dependency followed by the new target, sequentially). Logs: `/tmp/selberg_boundary_operator_build.log`, `/tmp/selberg_maass_fourier_modes_build.log`. All task Lean invocations were serialized. Twenty-four capstone axiom checks across the two `/tmp` audit files report only `propext`, `Classical.choice`, and `Quot.sound`; the Maass audit also imports the existing `SelbergExceptionalCuspMean` successfully. Both new modules are wired and indexed. Tracked and new task-file whitespace checks passed. All task-owned Lean/Lake handles are terminal; a separate agent's `QNMLorentzAuxiliary` build was active at the process audit and was not touched. No commit was made by this task.
- **Latest repository-wide lint failed on seven unrelated unwired modules:** RHTower `MobiusDivisorRemainingFrontTransport`; HTGeometry `CoppoFockRotation`, `CoppoJosephsonPotential`, `CoppoKerrPhaseGeometry`, `CoppoNonlocalNoise`, `CoppoPartnerEigenspaces`, `CoppoSSH`. No new Selberg module is named. Log: `/tmp/selberg_fourier_final_lint.log`. The intermediate cycle 18 audit had 23 unrelated unwired modules; concurrent work resolved those entries or changed the set. The latest seven-module result supersedes that intermediate count and the older cycle 16–17 result below.

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
