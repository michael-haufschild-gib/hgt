# SQB: actual spectral source comparison

Status: the literal horizontal Mellin factorization, the all-complex actual response transform, their one-pole contour transfer, the native scalar Cauchy formula, and exact cancellation of its mean residue are formalized. Complete positive Eisenstein probes separate every finite family of distinct native energies, including real energies: every nonzero coefficient vector has nonzero native packet mass. Upper-half-plane packets also have an exact positive integral norm formula. The decisive remaining arithmetic source cancellation and cofinal residual estimate are open. RH remains unproved.

Full chain: theta source -> normalized full-native residual packets at each Xi target -> occurrence -> critical line -> RH. Hardest target: a source comparison retaining the signed arithmetic contribution, strong enough to orient the native scalar response. The current candidate uses the actual scattering phase rather than replacing the Möbius remainder by its absolute majorant.

## Literal-source calculation

Use `f(y)=sqrt(y) Phi(log(y)/2)`, `J=horizontalWeight`, `g=radialProjection`, and `a=sqrt(y)` from `SelbergThetaHorizontalArithmetic`. Let `Lambda(s)=pi^(-s/2) Gamma(s/2) zeta(s)` and `xi(s)=s(s-1)Lambda(s)/2`.

For `Re z>0`, the proved exact source symbol is

    integral_0^infinity a^(z-1) J(a^2) da
      = xi(z+3/2) * (1 + Lambda(z+1)/Lambda(z+2)).

Derivation: the all-complex bilateral Phi transform is already available from `HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all` and `thetaBilateralLaplace_eq_XiC`, together with Xi reflection: `integral exp(w x) Phi(x) dx = xi(w+1/2)`. Rebuilding that transform from the seed is unnecessary. Reflection gives the radial field `G(r)=r^-1 Phi(log r)`. Polar coordinates then give

    Mellin(g)(s) = sqrt(pi) Gamma(s/2)/Gamma((s+1)/2) * xi(s+1/2).

The complete totient series contributes `zeta(z+1)/zeta(z+2)`. Its angular Gamma factor completes that ratio to `Lambda(z+1)/Lambda(z+2)`. The parabolic row contributes the additional `xi(z+3/2)` term; it must not be dropped.

Lean proof: `SelbergThetaHorizontalTransform.horizontalWeight_log` identifies the literal horizontal mean with its parabolic source and the full reflected kernel. Absolute tilted-source integrability, the Cauchy angular integral, and summability of the complete totient coefficients justify Fubini and the full sum/transform exchange. Logarithmic and square-height substitutions give `horizontalWeight_square_hasMellin`; its `HasMellin` conclusion includes absolute convergence. This proof covers every `Re z > 0`.

Source: [SelbergThetaHorizontalTransform.lean](../../../../formal/GaloisForLFunctions/RHTower/SelbergThetaHorizontalTransform.lean). Scratch source check and final leaf build passed; the module is wired into `RHTower.lean`. Formal lint passed. A separate `/tmp/sqb51_horizontal_audit.lean` checked the final theorem, convergence, literal-source join, and reflected transform: all depend only on `propext`, `Classical.choice`, and `Quot.sound`. The boundary contour argument is not part of this theorem.

## Proved source-response contour

Put `alpha_q = xiSpectralPoint q` and let `p_q` be the literal reflected common-forcing profile. `SelbergThetaCommonForcingTransform` proves, for every actual Xi copy and every complex frequency `w`,

    pHat_q(w) = integral_R p_q(x) exp(-i w x) dx,
    (alpha_q^2-w^2) pHat_q(w) = XiC(w).

The integral converges absolutely throughout the plane. It equals the entire divided-difference expression, including both removed points. The source-ratio bound and the existing all-plane theta transform supply this extension; horizontal Fourier continuity identifies the removed values.

The pole-cleared horizontal source is

    H(z) = xi(z+3/2) * (z+(z+2)*xi(z+1)/xi(z+2)),
    M(z) = H(z)/z,
    C = H(0) = xi(3/2)/xi(2).

`SelbergThetaHorizontalBoundary` proves that `H` is analytic on `Re z >= -1`, that `M` is the literal Mellin transform on `Re z > 0`, and that the Xi ratio is contractive throughout the closed half-plane. The half-shift endpoint follows from the unconditional critical strip. Uniform Gamma and zeta bounds give the required exponential vertical decay for `1/2 <= Re s <= 2`, with absolute integrability of every Xi line in that strip.

Define the complete arithmetic boundary phase and its real coefficient by

    beta(t) = (1+it)/(-1+it) * xi(it)/xi(1+it),
    w(t) = 1+Re beta(t).

The boundary theorem proves

    M(-1+it) = XiC(t)*(1+beta(t)),
    |beta(t)| = 1,
    w(t) = |1+beta(t)|^2/2,
    0 <= w(t) <= 2,    w(-t)=w(t),    w(0)=0.

These are statements about the actual analytic symbol. They do not identify a physical inverse Mellin transform at the boundary by themselves.

`SelbergThetaNativeContour` proves the combined contour transfer. With

    R_q(z) = M(z)*pHat_q(-i*(z+1)),
    V_c(R_q) = (1/(2*pi*i)) integral_(Re z=c) R_q(z) dz,

its exact conclusion is

    V_(1/4)(R_q) = C*xi(3/2)/(1+alpha_q^2)
      + (1/(2*pi)) integral_R XiC(t)*(1+beta(t))*pHat_q(t) dt.

Both vertical sides are absolutely integrable, the horizontal edges vanish, and subtraction of the displayed mean principal part is locally bounded. A single pair of admitted response tilts bounds `pHat_q` uniformly on the whole contour strip. The entire response creates no additional pole to cross. The displayed boundary integral is also formally admitted.

Sources: [SelbergThetaCommonForcingTransform.lean](../../../../formal/GaloisForLFunctions/RHTower/SelbergThetaCommonForcingTransform.lean), [SelbergThetaHorizontalBoundary.lean](../../../../formal/GaloisForLFunctions/RHTower/SelbergThetaHorizontalBoundary.lean), [SelbergThetaNativeContour.lean](../../../../formal/GaloisForLFunctions/RHTower/SelbergThetaNativeContour.lean). Scratch checks and separate final leaf builds pass; all three are wired into `RHTower.lean`. Separate axiom audits of the principal conclusions and their source/decay ingredients use only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint passes.

## Proved native scalar formula

`SelbergThetaNativeScalarBoundary.scalarResponse_eq_contour` proves the exact join

    scalarResponse(q) = 2*V_(1/4)(R_q).

Set `F_q(x)=exp(-5x/4)*p_q(x)` and `G(x)=exp(x/4)*J(exp(2x))`. The native height integral becomes `2*integral F_q G` by the direct substitution `y=exp(2x)`. Both functions are absolutely integrable. `G` is the admitted `logIntegrand` at Eisenstein parameter `s=9/8`, composed with `x -> -2x`. Its Fourier transform is the actual safe source symbol. The actual-response Fourier bridge identifies the transform of `F_q`; its denominator is uniformly separated from zero on this line, and Xi line integrability at `Re s=7/4` admits that Fourier transform. Bilinear Fourier duality gives the contour, with the frequency scale and both factors of two proved explicitly.

The all-plane transform equation and real-line continuity give `pHat_q(-t)=pHat_q(t)`, including the removed points. Reflection conjugates the actual scattering phase. Averaging the absolutely integrable reflected boundary expressions therefore replaces `1+beta(t)` by `w(t)` exactly.

`scalarResponse_cauchy` now proves, at every actual Xi copy,

    S(q) = 2*C*xi(3/2)/(1+alpha_q^2)
      - (1/pi) integral_R Xi(t)^2*w(t)/(t^2-alpha_q^2) dt.

`native_cauchy_integrable` proves absolute convergence for every copy. No off-axis assumption is needed: the quotient agrees almost everywhere with the entire response, so its totalized values at possible real removed points do not change the integral. `sourceMass_eq_xi` proves `M=sourceMass=2*xi(3/2)` from the actual all-plane theta transform.

With `V=inner constantVector constantVector`, `sourcePairing_cauchy` retains the literal native centering:

    m(q) = -(1/4) * (2*C*xi(3/2)/(1+alpha_q^2)
                         - M^2/((1+alpha_q^2)*V))
      + (1/(4*pi)) integral_R Xi(t)^2*w(t)/(t^2-alpha_q^2) dt.

Source: [SelbergThetaNativeScalarBoundary.lean](../../../../formal/GaloisForLFunctions/RHTower/SelbergThetaNativeScalarBoundary.lean). The complete scratch proof and final targeted leaf build pass; the module is wired into `RHTower.lean`. A separate `/tmp/sqb53_native_audit.lean` checks the contour join, parity, real boundary formula, source mass, Cauchy admission, and both scalar/centered formulas: all use only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint passes.

## Exact native mean cancellation

`SelbergThetaNativeMeanCancellation` proves the normalization in the original measure:

    volume(fd) = ofReal(pi/3),
    V = inner constantVector constantVector = pi/3 = 2*xi(2).

The actual modular domain maps to `-1/2 <= x <= 1/2`, `sqrt(1-x^2) <= y`. The existing full-domain inverse-square integrability admits Fubini. Its inner ray integral is `1/sqrt(1-x^2)`; the arcsine primitive gives the outer integral `pi/3`. The measure-preserving complex/real-product chart transports this exact value to native hyperbolic volume. Evaluating `Gamma_R(2)` and the proved `zeta(2)` value identifies it with `2*xi(2)`.

`mean_residue_cancel` now proves equality of the two displayed mean terms, using the already proved `M=2*xi(3/2)` and `C=xi(3/2)/xi(2)`. Consequently, for every actual Xi copy,

    m(q) = (1/(4*pi)) integral_R Xi(t)^2*w(t)/(t^2-alpha_q^2) dt.

This is `sourcePairing_eq_cauchy`, with the actual native pairing and unchanged complete arithmetic weight. It has no extra volume, integrability, zero-location, or source-sign premises. The previous `native_cauchy_integrable` supplies absolute convergence at every copy, including possible real removed points.

Source: [SelbergThetaNativeMeanCancellation.lean](../../../../formal/GaloisForLFunctions/RHTower/SelbergThetaNativeMeanCancellation.lean). Complete scratch proof and final targeted leaf build pass; the module is wired into `RHTower.lean`. The dependency preflight required only the new leaf. `/tmp/sqb54_native_audit.lean` audits all six public conclusions: only `propext`, `Classical.choice`, and `Quot.sound` occur. Formal lint passes.

## Remaining cancellation

The Cauchy density `Xi(t)^2*w(t)` is nonnegative. Its sign agrees with the existing self-adjoint Gram displacement law; the formula does not yet prove reality of the centered scalar. The hardest missing input remains source cancellation strong enough to produce normalized full-native residual packets while retaining mass.

A reproducing-kernel candidate was tested by broad deep and hybrid searches across source cancellation, scattering, de Branges kernels, Hardy orthogonality, and real-frequency reflection. Retrieved `integral_cauchyTransform_eq_zero` needs actual Hardy membership; retrieved Suzuki de Branges expansions explicitly require RH. Neither premise has been supplied for this native source. No additional conditional receiver or no-go theorem was added. Search results were partial, with interrupted retrieval stages and incomplete semantic/compiler coverage; candidate and source-argument views were inspected, while proof-idea and ingredient-set views were empty. This is not a claim that the needed ingredient is absent from the corpus.

## Conjecture checks and search joins

Direct critical Möbius annihilation does not match the literal radial coefficient: the known theta inversion uses critical half-power translation weights, while the full horizontal mean has its own denominator/Jacobian weight. Any use of `XiCTaylorThetaTailMobiusConstraint` must retain this difference.

`ThetaCuspWignerProductFiberNormalForm` supplies complete positive-shell reassembly and divisor-ratio phases, including a fully coupled cone current. Its real-frequency reality theorem cannot be substituted for the native complex-energy orientation. The full coupled integral, rather than one fixed-product sign, is the available survivor.

Broad OR searches used theta/divisor/Mellin/radial, Möbius/theta/Poisson, signed/quadrature, and scattering/Plancherel/contraction. Deep searches remained partial; the second returned source arguments and the newly indexed SQB quadrature theorem but no decisive bound. Search failure is not evidence of corpus absence. No computation or frontier-map edit is part of this construction.

## Verified ingredient matches

The following exact interfaces were checked together by `lake env lean /tmp/sqb41_retrieved_interfaces.lean` (exit 0). The six nontrivial results selected for `#print axioms` use only `propext`, `Classical.choice`, and `Quot.sound`. These earlier checks audit the retrieved interfaces. The literal horizontal-source calculation now has its own module and leaf build as recorded above.

| Source result | Match to this problem | Remaining mathematical join |
| --- | --- | --- |
| `HedenmalmThetaSource.integrable_thetaCuspFourierLaplaceIntegrand_all`, `thetaCuspFourierLaplace_eq_XiC_all`; `thetaBilateralLaplace_eq_XiC` | Literal full theta source; arbitrary complex parameter. The old strip restriction is already removed. | Radial projection and complete horizontal mean are different transforms. |
| `SelbergThetaTotientHankel.transform_kernel` | Complete totient sum, angular integral, and completed-zeta ratio, with absolute admission. | Its input is the dyadic tilted-profile Hankel correlation, not the common-forcing response profile `p_q`. |
| `SelbergThetaTotientHankel.kernel_mean_abel_limit` | Genuine right Abel limit of the full kernel at every Xi copy. | This is a limit at its mean pole; it is not the proposed real-frequency boundary integral for native `m(q)`. |
| `thetaCuspTailSecondDensityAtom_one_eq_tsum_moebius_translate` | Signed critical Möbius inversion of the actual differentiated theta density. | Proved for `x >= 0`; its half-power weights and source must be transported to the full native radial remainder. |
| `DeletionMixedRefinement.norm_unitFullFourierSource_even_le` | Complete complex Bernoulli-source reflection bound, quadratic in horizontal displacement. | Different source and measure; its Hardy-amplitude consequence supplies selected horizontal segments, not all-zero native orientation. |
| `Sieve.eventually_norm_sum_moebiusTwist_div_lt` | Unconditional `o(N)` cancellation, uniform over the explicitly admitted growing twist range. | Supplies neither a critical square-root saving nor the required bound for the signed radial quadrature. |

The all-complex theta identity is an actual retrieval gain: following references outside the initially inspected transform module found its existing producer. Source conclusions, measures, exponents, and quantified domains distinguish usable ingredients from similarly named receivers. The broad deep intertwining query retained 25 candidate lemmas and 25 source arguments, but reported interrupted retrieval stages, pending coverage, and no generated ingredient sets; it is not an exhaustive corpus audit.

The unresolved SQB assertion remains reality of the literal corrected scalar response

    S(q) - M^2 / ((1+z_q^2)*V),

or another source-derived estimate forcing the normalized full-native residual to vanish. None of the verified matches above supplies that assertion by the identities currently proved. The proved native Cauchy formula and mean cancellation supply the exact arithmetic expression for that scalar. The decisive cancellation estimate remains open.


## Source comparison candidates

Broad OR searches across orthogonality, division properties, reproducing kernels, theta likelihood order, and interlacing retrieve `XiPolynomialDensity.ae_eq_zero_of_orthogonal_polynomial_XiC`, actual theta likelihood spectral measures, and the reflected likelihood-interference factorization. The polynomial-density theorem requires all Xi-weighted polynomial pairings to vanish; that source orthogonality is not established. `thetaCuspHigherLikelihoodSpectralMasterLaw` proves positivity of every finite Hankel block in the intrinsic positive Laplace coordinate, while `thetaCuspFullSource_reflected_normalized_eq_singleAtomModel_mul_interference` keeps the complete higher-atom contribution in one explicit likelihood cocycle. Neither retrieved result by itself orients the oscillatory native scalar. The candidate join is control of this complete interference under the native source pairing, with no atomwise sign replacement.

An existing correction mechanism retains the complete source and exactly preserves its integrated signed forms. For `0<a<1/2`, set `F_a(r)=r^2*sinh(a*r)*Phi(r/2)^2`. `ThetaCuspCenterCompensationFlux` proves `integral_(0,infinity) F_a'(r) dr = 0`, with absolute admission. Consequently adding `C*F_a'` to any weighted native signed Hankel form leaves its integral unchanged. `ThetaCuspCenterMixedAllOrderIntegration` identifies the uncorrected integral with the literal center-mixed signed moment form at every order. The positive construction target is a source-derived family of corrections making all required forms nonnegative. The all-order sign, and any resulting cancellation of the SQB native forcing, remain unproved.

The zero-integral correction, its all-order form identity, and the existing all-order sign/RH equivalence were checked by `lake env lean /tmp/sqb58_compensation_interfaces.lean`; all three axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. This verifies retrieved ingredients, not a new sign theorem. The separate next-rank compact-source draft under `clg-ttf-even-compact-incidence/pending-lean/` is still unverified; its own status card retains both source-incidence and middle-interval obligations.

The active all-order construction is a tilt-energy comparison. Write `g_a(x)=exp(a*x)*Phi(x)` and `C_a(t)=integral_R g_a(x+t/2)*g_a(x-t/2) dx`. Differentiating the tilt, pairing `x` with `-x`, and substituting `r=2*x` gives `partial_a C_a(t)=thetaCuspCenterMixedDensity a t`. Thus the Fourier-signed even and odd moment blocks are tilt derivatives of differential-polynomial energies. For a real polynomial `P` of one parity, put `u_a=P(D)g_a`. The analytical calculation is

```text
partial_a u_a = x*u_a + P'(D)g_a,
integral_R u_a*P'(D)g_a = 0,
partial_a integral_R u_a^2 = 2*integral_R x*u_a^2.
```

The middle identity follows by integration by parts: `P(D)^*P'(D)` is skew-adjoint because `P` and `P'` have opposite parity. The positive conjecture is `integral_R x*u_a^2 >= 0` for every such `P` and `0<a<1/2`. This comparison, including its formal identification with every signed block, remains open; the displayed calculation is analytical and is not a new Lean theorem. Ordinary energy positivity does not discharge the signed expectation.

The full-source Ward equation provides a concrete input to this comparison. `ThetaCuspCofinalWardConvexity` identifies the complete Gibbs-shell sum `W` and proves `W'+W/2=-Phi/(2*pi)`, with strictly positive second derivative of `exp(a*x)*W(x)` for `0<=a<=1/4`, `x>0`. Both source identities were checked in `/tmp/sqb59_source_interfaces.lean`, with only `propext`, `Classical.choice`, and `Quot.sound`. The attempted use of this curvature has not oriented the two reflected transform branches. Their Gaussian boundary terms must stay in `thetaCuspShellEvenPhaseValue_eq_gammaRemainders`; the actual pair current is `2*Im(D_n*conj(A_m))`.

For the rank-two theta reassembly, `ThetaWignerEisensteinCrossEnergy` supplies an exact positive completed square with both symbol-weighted energy and reciprocal-symbol dual energy. The missing construction is a bound for the actual arithmetic dual channel that controls the full mixed term. The positive archimedean symbol alone is not that bound. Likewise, the retrieved Hankel terminal-flux method retains its terminal vector, and the shifted Jacobi Toda identities require a frame for different moments. No all-order source-sign or forcing-cancellation theorem is claimed from these matches.

Searches inspected candidate-lemma, source-argument, declaration, prose and source-passage views, with broad OR terms, mechanism descriptions and selected module filters. One all-order request returned a proposed ingredient group combining tilt differentiation with finite rational-gauge reflection; it supplies no native source-sign estimate. Other requests returned empty groups. Retrieval reports incomplete semantic/compiler coverage and, for some deep requests, interrupted stages. These results do not establish absence from the corpus. No computation or frontier-map edit was performed.

## Further source constructions under examination

The lattice-Poisson candidate changes the primitive theta height weight to one quarter: the resulting multiple weight is formally `n^(2k-1/2)`, which disappears at `k=1/4`. A radial Gaussian derivative can then exploit unimodular rank-two Poisson reflection. This is a construction candidate, not an admitted native packet. For the proposed seed `g(r)=(2*pi*r^2-1)*exp(-pi*r^2)` and log profile `h(x)=exp(-x)*sum_{n>=1} g(n*exp(-x))`, the safe-half-plane Mellin calculation gives

    integral exp(w*x)*h(x) dx = xi(w)/(1-w),    Re(w)<0.

The calculation follows by scaling each summand and applying Gamma recurrence. Its continuation and the modular periodization have not been formalized for this seed. The expression cancels at a Xi zero but does not cancel at the reflected exponent `-w`: at `w=1-rho`, the latter value is `xi(2-rho)/(2-rho)`. A two-ended response and nonzero centered native mass must therefore be established together. The retrieved Meyer reflection theorem requires both physical and Fourier zero modes to vanish; it does not directly admit this seed. No lattice occurrence theorem is claimed.

The complete-source oscillation candidate has a stronger existing input than the single-atom inequality: `RHTower.thetaCuspReflectedLogRiccatiMargin_nonneg` in `ThetaCuspGlobalReflectedRiccati.lean` covers every center and nonnegative displacement. `RHTower.thetaCuspCenterMixedThreePointMatrix_posSemidef` in `HedenmalmCenterMixedCorrelationAngle.lean` supplies its integrated three-point consequence. The missing join is a source-specific higher-order sign or comparison that reaches the native Cauchy pairing; neither source statement supplies that join. No new conditional receiver or no-go module was added.

The expanded search uses broad OR/phrase queries, hybrid retrieval, deep requests up to three rounds with a 300-second budget, all retrieval views, module filters and exclusions, and a lexical declaration scan. Generated ingredient groups were inspected. They leave the decisive forcing cancellation as an obligation, or combine kernels in different spaces. Completed requests report a full source inventory but incomplete semantic/compiler coverage; some requests also report interrupted text/source stages. These are candidate-discovery results, not a verified composition or an absence claim. Exact native mean cancellation and retained centered mass are closed; arithmetic forcing cancellation remains open.

## Centered common-forcing mass

**Closed in Lean:** the actual centered common-forcing vector is nonzero at every Xi copy. For a nonidentity primitive row, the transformed height is at most `1/y`. The positive seed's cubic bound therefore supplies an extra factor `1/y` over the already bounded complete quadratic nonidentity row sum. The identity row has its own inverse-height bound. Thus the complete positive forcing satisfies `P(z) ≤ C/z.im` for `z.im ≥ 1/2`. Its strict positivity and the positive measure of every open cusp region exclude an almost-everywhere constant value. Hence the centered forcing is nonzero, and the centered graph equation forces every response vector to be nonzero.

[SelbergThetaCommonForcingMass.lean](../../../../formal/GaloisForLFunctions/RHTower/SelbergThetaCommonForcingMass.lean) constructs `unitDomain q` in the original native energy-operator domain and proves

```text
norm(unitDomain q) = 1
(A - energy(q)) unitDomain(q) = forcing / norm(vector(q)).
```

The complete forcing term is retained. This closes mass and unit normalization for this common-forcing source family; it supplies neither a vanishing normalized occurrence residual nor RH. Core scratch verification, finished-source verification, the targeted leaf build, and formal lint pass. A separate `/tmp/sqb56_mass_audit.lean` audits all eight public theorems: only `propext`, `Classical.choice`, and `Quot.sound` occur. The module is wired into `RHTower.lean` without an umbrella build.

## Source-combination and boundary candidates

For a finite combination of the actual centered responses, the existing graph identities give

```text
(A-z) sum_i c_i v_i = sum_i c_i (energy_i-z) v_i + (sum_i c_i) forcing.
```

Zero-sum coefficients cancel the shared forcing exactly. The positive target is a source-derived coefficient family for which the remaining energy-weighted sum is small relative to the full packet norm. `SelbergThetaCommonForcingGram` supplies both complete quadratic forms; the required cofinal estimate relating them is still missing.

`SelbergThetaCommonForcingPacketMass` proves finite packet mass in the upper spectral half-plane. Write `lambda_i = alpha_i^2`, `N(t)=Xi(t)^2*w(t)`, and `V=sum_i c_i*v_i`. For every finite family with `Im(lambda_i)>0`, its absolutely admitted native norm is

```text
norm(V)^2 = (1/pi) integral_R N(t) * normSq(sum_i c_i/(t^2-lambda_i)) dt.
```

The entrywise formula follows from the exact native source Cauchy transform and Gram displacement, with coefficient `1/pi`. When the `lambda_i` are distinct and `c` is nonzero, clearing denominators produces a nonzero polynomial: evaluating at `alpha_i` isolates `c_i` times the nonzero product of spectral gaps. Its real zero set is finite. A zero packet would force `N=0` almost everywhere, contrary to the native diagonal source flux and the already proved nonzero response. Thus `packet_ne_zero` applies also to nonzero coefficient vectors satisfying `sum_i c_i=0`.

This integral norm formula is quantified over upper-half-plane packets; it does not assert that such Xi copies exist. Its proof does not extend the integral formula across real or reflected energy collisions. Finite nonzero mass at arbitrary distinct energies is proved separately below. A lower bound uniform over a cofinal family and the normalized full residual remain uncontrolled.

`SelbergThetaEisensteinProbes` proves the complete positive Eisenstein pairings for every `r>1`. Put `a=2*r-1`, `E_r=positiveCuspRows r`, and `B_r=(1+cuspReflectionNorm r)*tiltedMass a>0`. On the original native measure, with all primitive rows and both Weyl terms retained,

```text
integral positiveSource * E_r = B_r,
integral source_q * E_r = B_r / (alpha_q^2+a^2).
```

`profile_eisenstein_integrable` and `profile_eisenstein_pairing` establish absolute admission and the two-term Mellin unfolding for every measurable height seed with all-power rapid bounds. `heightProfile_mellin` discharges the actual response moments using the proved all-real mode moments and reflection. The denominator is nonzero for every actual Xi copy because `Re(alpha_q)` is nonzero. No spectral half-plane premise is used.

For the true centered native vectors, the proved identity `image_sub_vector` is

```text
(A-1) v_q = (energy_q-1) nativeSource_q - nativePositive/4.
```

Thus applying `A-1` to a zero packet removes its constant component exactly. Pairing with `E_r` gives the nonzero scalar factor `(1-a^2)*B_r/4` times `sum_i c_i/(alpha_i^2+a^2)`. `packet_zero_probe_identity` proves this rational sum vanishes for every `r>1`. Finitely many distinct negative real probe nodes form a nonsingular Cauchy matrix, so `vector_linearIndependent` and `packet_ne_zero` recover all coefficients for every finite family with distinct squared parameters. This includes real energies and nonzero zero-sum coefficient families cancelling the shared forcing.

Scratch and finished-source checks, the narrow `SelbergThetaEisensteinProbes` leaf build, and formal lint pass. The module is wired into `RHTower.lean`; the generated index is refreshed and `lint --check-generated` passes. The separate `/tmp/sqb61_probes_audit.lean` checks the actual source and packet statements and audits ten results; all depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The quantitative candidate localizes the admitted Eisenstein probes and controls the omitted cusp-tail pairing against the norm of the localized probe. Absolute admission and finite Cauchy invertibility alone give no uniform cost as packet size, probe parameter, and cutoff vary. A source-derived balance between that tail, coefficient recovery cost, and the full residual is still unproved; finite separation does not close cofinal occurrence.

Scratch and source checks, the narrow leaf build, and formal lint pass. The module is wired into `RHTower.lean`. The separate `/tmp/sqb60_packet_mass_audit.lean` verifies the exact statements and audits six results; all use only `propext`, `Classical.choice`, and `Quot.sound`. Broad OR, deep, and proof-method searches supplied the Cauchy denominator-clearing argument used here. Their semantic/compiler coverage remains incomplete; retrieved unrelated Plancherel results are not a substitute for the native periodization join.

A second candidate uses the actual entire divided response in a positive shifted de Branges space. Its two Hardy membership conditions and the boundary relation selecting the unshifted Xi function must be established together. The retrieved `SuzukiDeBrangesRepresentation` and Xi-vector membership results assume RH for the unshifted derivative-based space. The unconditional safe-shift canonical construction uses a different boundary function. No identification supplying the required native orthogonality has been proved.

The fixed theta source's finite signed approximations provide a further exact comparison: `thetaSourceSignedStageMetricDefect + I*pinnedBoundaryCLM = thetaSourceSignedStageGreenRemainder`, and the remainder tends to zero. Thus the remaining quantity to control is the actual pinned boundary form on the source modes. The retrieved positive finite Hardy head Gram and vanishing finite correction do not supply that source-mode bound. These are open positive cancellation targets, not new occurrence theorems.
