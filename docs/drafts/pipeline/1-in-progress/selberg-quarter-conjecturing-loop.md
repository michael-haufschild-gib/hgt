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

**Current Lean status:** `SelbergBesselBoundarySlope` passes scratch and direct checks. It contains the actual derivative system, Riccati law, exact positive range, unique transition, critical mode differential equation, and full outgoing-sign classification. The exact compact-profile energy identity is in progress in scratch; it is not yet claimed as a theorem.

**Build correction:** an initial targeted slope build expanded through the existing Eisenstein imports and spawned parallel Lean workers. It was stopped, and its child processes were cleaned up. A premature energy scratch check failed because the slope olean did not yet exist. The source argument derivative and strict order comparison are being extracted into small modules, preserving theorem names and existing wrapper imports; subsequent builds are serialized. The interrupted build is not a passing final audit.

## Verification log

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
