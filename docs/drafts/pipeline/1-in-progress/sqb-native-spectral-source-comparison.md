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

A concrete multiplier for this comparison is determined by the complete source score. Set `s=(log Phi)'`, `K=-s'>0`, and

```text
w(x) = 1 / integral_0^1 K(t*x) dt.
```

The source's evenness and strict log-concavity make `w` positive and even, with `w(0)=1/K(0)` and `w(x)*s(x)=-x`. For `u=P(D)g_a`, the full commutator is `C=[P(D),s]g_a`, where `[P(D),s]g_a=P(D)(s*g_a)-s*P(D)g_a`. The product rule gives the finite-interval balance

```text
integral_l^r x*u^2
  = a*integral_l^r w*u^2
    + integral_l^r ((w'/2)*u^2+w*u*C) - [w*u^2]_l^r/2.
```

This retains every derivative of the actual score through `C`; Gaussian replacement would erase these terms. The positive construction target is the lower bound `lim_(R->infinity) integral_(-R)^R ((w'/2)*u^2+w*u*C) >= -a*integral_R w*u^2`, together with its boundary and native signed-block joins. The bound remains unproved for the full theta source at all degrees. The source positivity, the identity `w*s=-x` using the equivalent piecewise quotient, and the local product-rule balance were checked in `/tmp/sqb62_score_balance.lean`; this scratch verification does not establish the all-degree estimate or add a finished corpus module.

The full-source Ward equation provides a concrete input to this comparison. `ThetaCuspCofinalWardConvexity` identifies the complete Gibbs-shell sum `W` and proves `W'+W/2=-Phi/(2*pi)`, with strictly positive second derivative of `exp(a*x)*W(x)` for `0<=a<=1/4`, `x>0`. Both source identities were checked in `/tmp/sqb59_source_interfaces.lean`, with only `propext`, `Classical.choice`, and `Quot.sound`. The attempted use of this curvature has not oriented the two reflected transform branches. Their Gaussian boundary terms must stay in `thetaCuspShellEvenPhaseValue_eq_gammaRemainders`; the actual pair current is `2*Im(D_n*conj(A_m))`.

For the rank-two theta reassembly, `ThetaWignerEisensteinCrossEnergy` supplies an exact positive completed square with both symbol-weighted energy and reciprocal-symbol dual energy. The missing construction is a bound for the actual arithmetic dual channel that controls the full mixed term. The positive archimedean symbol alone is not that bound. Likewise, the retrieved Hankel terminal-flux method retains its terminal vector, and the shifted Jacobi Toda identities require a frame for different moments. No all-order source-sign or forcing-cancellation theorem is claimed from these matches.

Searches inspected candidate-lemma, source-argument, declaration, prose and source-passage views, with broad OR terms, mechanism descriptions and selected module filters. One all-order request returned a proposed ingredient group combining tilt differentiation with finite rational-gauge reflection; it supplies no native source-sign estimate. Other requests returned empty groups. Retrieval reports incomplete semantic/compiler coverage and, for some deep requests, interrupted stages. These results do not establish absence from the corpus. No computation or frontier-map edit was performed.

An analytical operator construction suggested by [the n-potent commutator paper](https://arxiv.org/html/2607.08139v1) uses the actual arithmetic phase. On `L2(R)`, set `Rf(t)=f(-t)`, `Jf(t)=beta(t)*f(-t)`, and `Q=(I+J)/2`. The proved `norm_boundaryPhase` and `boundaryPhase_neg` identities make `J` a unitary involution and `Q` an orthogonal projection. Since Xi is even and real on the real axis, `Q Xi=(1+beta)*Xi/2`, so the complete native density is exactly `Xi^2*w=2*|Q Xi|^2`. These operator statements are analytical deductions, not new Lean theorems. The paper's factorizations can therefore be tested on actual idempotents; applying them to the differential operator or source score would require separate potency identities. The remaining constructive target is a quantitative bound on the native residual. The retrieved `projection_commutator_decomposition` retains both polarized leakage terms, while `norm_sub_intersectionProjection_sq_le` requires a strict angle bound; neither input estimate has been established here.

The differential generator of this actual reflection has a concrete local expression. Write `K0=i*d/dt` and `E(t)=(-1+it)*xi(1+it)`, so `beta=-conj(E)/E`. On smooth compactly supported functions the product rule gives

```text
h(t) = i*beta'(t)/beta(t)
     = 2*(Re(xi'(1+it)/xi(1+it))-1/(1+t^2)),
K0+J*K0*J = multiplication_by_h,
Q*K0*Q = (multiplication_by_h)*Q/2.
```

These are analytical identities, with no new Lean operator-domain construction. Testing whether native mean subtraction removes the rational contribution retains a weighted Cauchy integral with the additional factor `1/(1+t^2)`. The proved mean subtraction instead has its fixed rank-one dependence on `1/(1+alpha_q^2)`. An equality between these pairings has not been established. The positive target is an estimate for the complete compressed generator coupled to the actual source, keeping this rational contribution.

An alternative construction target is convexity of the tilt energies. With the preceding `g_a`, real parity polynomial `P`, and `u=P(D)g_a`, integration by parts gives the analytical second variation

```text
E_P(a) = integral_R u^2,
E_P''(a) = 4*norm(x*u)^2 - 2*norm(P'(D)*g_a)^2
           - 2*inner(P''(D)*g_a, u).
```

Indeed, the cross term is `inner(x*u,P'(D)*g_a) = -(norm(P'(D)*g_a)^2+inner(P''(D)*g_a,u))/2`. Here `P'` and `P''` are polynomial derivatives. Thus the source inequality

```text
2*norm(x*u)^2 >= norm(P'(D)*g_a)^2 + inner(P''(D)*g_a,u)
```

at every degree and `0<a<1/2` would imply `E_P'(a)>=0`, since parity gives `E_P'(0)=0`. This inequality and its formal signed-block join remain unproved. The retrieved one-dimensional Brascamp–Lieb bound controls variance by a derivative energy; it does not supply this signed second variation.

Broad arXiv searches using independently chosen terms `passivity`, `screening`, `fragmentation`, and `synchronization` led to two mechanisms tested against these targets. [Fragmentation and Cluster Prediction](https://arxiv.org/html/2609.07992v1), submitted September 7, 2026, proves cone preservation for ordered velocity differences by a Metzler evolution and gives a positive group-inverse kernel for a fixed path. Its extension from mixed signs requires a positive slow-mode coefficient and enough time before a topology change. For theta, the required cone-preserving evolution and terminal control have not been constructed. [Quantum Synchronization](https://arxiv.org/html/2607.19328v1), submitted July 21, 2026, describes persistent modes through a stationary state and compatibility with both the Hamiltonian and dissipative operators; the actual scattering projection alone does not establish those compatibility conditions. These are possible proof mechanisms, not imported source estimates.

Deep searches with all retrieval views, a broad single-word Laguerre search, and a separate cone-method query outside `RHTower` recovered `finiteTriangularCone_nonnegative`, the finite Hankel boundary extension law, and `OneDimBrascampLieb.variance_le_integral_deriv_sq_div_curvature`. The first requires a nonnegative terminal member of the hierarchy, and the boundary extension law retains its first unseen moment. Their hypotheses have not been discharged for the signed theta source. Candidate and source-argument sections were inspected; these requests returned no proof-idea or ingredient groups and reported incomplete semantic/compiler coverage or interrupted stages. No new Lean theorem or all-degree source bound is claimed from this analytical work.

### First unproved-rank polynomial target

Let `m_a = thetaCuspCenterMixedSignedJet a` and `Q_a = thetaCuspCenterMixedCutoffPolynomial a = HTGeometry.monicOrtho m_a 6`, with `0<a<1/2`. `FiniteGaussCutoff.lean` proves that a positive `N × N` moment section already makes its degree-`N` monic orthogonal polynomial split over the reals with simple roots, at the endpoint where its own signed norm has not been proved positive. The proof uses only lower-degree positivity: a nonreal conjugate quadratic factor would express an orthogonality zero as the sum of strictly positive squared norms; a repeated real factor gives the corresponding single-square contradiction.

For every other monic degree-six polynomial `p`, `ThetaCuspCenterMixedCutoffPolynomial.lean` specializes the exact identity

```text
momentInner m_a p p = momentInner m_a Q_a Q_a
                       + momentInner m_a (p-Q_a) (p-Q_a),
momentInner m_a Q_a Q_a < momentInner m_a p p  when p != Q_a.
```

The source polynomial has exactly six distinct real roots, and its signed norm is exactly `thetaCuspCenterMixedSuccessorSchur a 6`, hence exactly `integral_(r>0) r*sinh(a*r)*thetaCuspNativeSuccessorSource a 6 (r/2)`. The proof identifies Gram–Schmidt's cutoff polynomial with the corpus's canonical inverse-Hankel solve and retains the complete native integral. Nonnegativity of this norm is equivalent to positive semidefiniteness at rank seven; that sign is still unproved. Scratch and finished-source Lean checks pass. The separate `/tmp/sqb65_cutoff_audit.lean`, rerun against the final isolated artifacts, audits all sixteen public results; each uses only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into their umbrellas, and formal lint including generated-index freshness passes. The final isolated Lake builds of both leaves pass in `/tmp/sqb65-leaf-audit`, using the actual source paths and symlinked existing compiled dependency artifacts. A repository Lake preflight first required fifteen sequential dependency/leaf repairs, all completed, then exposed nineteen further dependency records. Those remaining repository records were not rebuilt. The isolated audit checks the new leaves against the compiled corpus and is not a claim that the repository dependency closure is freshly rebuilt.

For the separate all-degree tilt-energy candidate, write `P(i*t)=eta*Q(t)` with `Q` real and `|eta|=1`, and let `F_a` be the Fourier transform of `g_a=exp(a*x)*Phi(x)` in the convention with kernel `exp(-i*t*x)`. Plancherel translates the proposed second-variation bound into

```text
2 * integral |(Q*F_a)'|^2 >= integral (Q'^2-Q*Q'') * |F_a|^2.
```

If `Q` has distinct real roots `r_j`, its right side is `sum_j integral |(Q/(X-r_j))*F_a|^2`. The estimate remains unproved for the actual theta transform. The generic angular Laguerre energy identity has a different domain and weight.

The actual density definition fixes the frequency scaling in the adaptive test. Analytically set `A_a(y)=integral_x g_a(x+y)*g_a(x-y)`. Evenness of `Phi`, followed by `r=2*x`, gives `thetaCuspCenterMixedDensity a y = partial_a A_a(y)`. Thus for a fixed real polynomial `Q`, its signed moment norm is the aperture derivative of `(1/(2*pi))*integral_t Q(2*t)^2*|F_a(t)|^2`. The physical differential polynomial has symbol `P(i*t)=Q(2*t)`; the factor two must be retained. Since the odd source moments vanish, reflection preserves the monic degree-six norm problem. Its strict minimizer is therefore even, now formalized by the Jacobi formula below. Analytically its six simple real roots form three nonzero pairs `+/-r_j`; up to an overall sign, the corresponding physical operator is `product_j (4*D^2+r_j^2)`. The paired-root operator factorization has not been added as a Lean declaration.

For the moving minimizer `Q_a`, differentiating its signed norm cancels the coefficient-motion term: `Q_a` is orthogonal to `partial_a Q_a`, whose degree is below six because the leading coefficient is constantly one. Consequently the derivative of the successor scalar is the second aperture derivative of the preceding energy with `Q_a` held fixed during that derivative. This selects the adaptive frequency polynomial `R_a(t)=Q_a(2*t)`, whose six roots are real and simple, as a sharper target for `2*integral |(R_a*F_a)'|^2 >= integral (R_a'^2-R_a*R_a'')*|F_a|^2`. These differentiated Plancherel identities are analytical deductions, not additional Lean declarations. The adaptive bound and the zero-aperture limit needed to integrate its sign remain to be proved; no native successor positivity is asserted.

The broad corpus queries used real roots, Darboux transformations, compensation, Hardy, orthogonal polynomials, Schur complements, and oscillation, with deep retrieval across all method views. The useful join was `HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal` from `MonicMomentAdmission.lean`, whose lower-moment uniqueness identifies the canonical Hankel solve with the cutoff orthogonal polynomial. Other generated groups retain a missing source-preserving evolution or weighted estimate. Coverage remains partial; the oscillation request completed without errors and reported complete source inventory but incomplete semantic/compiler coverage.

Independently chosen arXiv terms included `polarization`, `coarsening`, and `renewal`. [Discrete time-multidimensional renewal theory and applications](https://arxiv.org/html/2606.31455v1) gives a coefficientwise finite convolution inverse when the nonconstant kernel has zero constant coefficient. A positive inverse additionally needs a nonnegative increment kernel. Constructing such a kernel from the signed theta source remains a conjecture; no numerical results or theorem from the paper is used in the Lean proof.

### Cutoff coefficient cone and mixed-atom retention

The current analytical target retains the actual cutoff coefficients when comparing atom-pair channels. Write `b_j=monicOrthoBeta m_a j`, for `1<=j<=5`. Positivity below degree six makes these five numbers strictly positive. Vanishing odd moments removes the diagonal Jacobi coefficients, so the finite recurrence gives

```text
Q_a(t)=t^6-S*t^4+E*t^2-F,
S=b_1+b_2+b_3+b_4+b_5,
E=b_1*b_3+b_1*b_4+b_2*b_4+b_1*b_5+b_2*b_5+b_3*b_5,
F=b_1*b_3*b_5.
```

In particular `S,E,F>0`. The corresponding signed square norm, in raw even-derivative coordinates `d_j`, is exactly

```text
d_12+2*S*d_10+(S^2+2*E)*d_8+2*(S*E+F)*d_6
  +(E^2+2*S*F)*d_4+2*E*F*d_2+F^2*d_0.
```

For a geometric raw pair jet `d_(2j)=D^(2j)`, this expression is the retained positive square `(D^6+S*D^4+E*D^2+F)^2`, bounded below by `(D^6+F)^2`. The next conjecture is that the actual mixed-atom lower-order terms can be bounded while retaining this square. Their signs, the integrated norm sign, and all-rank propagation are open. [ThetaCuspCutoffJacobiCone.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspCutoffJacobiCone.lean) now formalizes the actual cutoff formula, strict coefficient magnitudes, evenness, imaginary-axis evaluation and square bound, and exact raw-derivative norm. Scratch checking passes; the final isolated leaf build passes in `/tmp/sqb76-cutoff-jacobi-leaf-audit` against the existing compiled dependencies (48 seconds, two Lake jobs). `/tmp/sqb76_final_audit.lean` audits all six public theorems; each uses only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into `RHTower.lean`; global formal lint passes (`/tmp/sqb76_formal_lint.txt`). No mixed-atom remainder estimate is claimed.

The literal atom product gives a scalar differential representation for that next bound. Set `q=pi*n^2*exp(2*x)`, `r=pi*m^2*exp(2*x)`, `c=4*q*r`, and `z(t)=q*exp(2*t)+r*exp(-2*t)`. Direct expansion of the two source seeds gives

```text
Phi_n(x+t)*Phi_m(x-t) = 4*q*r*exp(x)*(c+9-6*z(t))*exp(-z(t)).
z''=4*z,    (z')^2=4*(z^2-c).
R_c P = (z^2-c)*(P''-2*P'+P)+z*(P'-P).
D_t^2 [exp(-z(t))*P(z(t))] = 4*exp(-z(t))*(R_c P)(z(t)).
```

Thus the exact even pair jet of order `2j` is `4*q*r*exp(x-q-r)*4^j*(R_c^j(c+9-6*X))(q+r)`. The cutoff-square pair contribution retains the entire operator `(64*R_c^3+16*S*R_c^2+4*E*R_c+F)^2` applied to `c+9-6*X`. These are analytical identities awaiting formalization, not positivity claims about the operator. The high-order remainder must still be bounded for the actual coefficients and complete atom sum.

All-view deep searches used independently chosen inertia/copositivity, high cumulants, symmetric orthogonal coefficients, and hyperbolic radial diffusion, together with a determinant-correction mechanism query. Statements, source arguments, methods, proof ideas, and ingredient groups were inspected. The applicable finite Jacobi recurrence supplies the displayed cutoff coefficients. Other returned positivity results retain an unmatched source, derivative, or positive-Gram premise. Coverage is partial, with stale compiler metadata and some interrupted retrieval/deadline stages; no corpus-absence conclusion follows.

Recent-paper searches used `screening` and `pinning`. [Exact Cancellation of Horizon Modes in Kerr Ringdown](https://arxiv.org/html/2609.07326v1) retains a complete frequency-dependent zero factor before evaluating a near-horizon source integral. [A dot-product bound from separate growth-minimizing bases](https://arxiv.org/html/2609.06730v1) combines independently chosen minimizing subsets through a product base. Neither paper supplies a theta inequality or a Lean premise. The pair differential identity above follows directly from the theta seed, while the remaining sign estimate still needs proof.

### Unsigned-moment projection candidate

There is an analytical lower bound for the hard derivative energy involving only eight unsigned moments. Use the same non-normalized Fourier transform `F_a` of `g_a=thetaCuspTiltedSource a`, and put

```text
mu_j = (1/(2*pi))*integral t^(2*j)*|F_a(t)|^2 dt,   0 <= j <= 7,
E_ij = mu_(i+j),           O_ij = mu_(i+j+1),      0 <= i,j <= 3,
B = diag(1,3,5,7),         T_ij = 2*j if i+1=j, otherwise 0,
M_a = E*B*O^(-1)*B*E - transpose(T)*O*T.
```

Both `E` and `O` are positive definite: their quadratic forms are ordinary squared-polynomial integrals, and `F_a(0)>0` provides an interval on which the weight is positive. For `R(t)=sum_(k=0)^3 c_k*t^(2*k)`, set `psi=R*F_a`, and normalize all following integrals by `1/(2*pi)`. Integration by parts gives

```text
integral psi' * conj(t^(2*j+1)*F_a) = ell_j,
ell = (O*T-B*E)*c/2.
```

The pairing is real because `F_a(-t)=conj(F_a(t))`. Projection onto the four odd monomials times `F_a` therefore gives `integral |psi'|^2 >= transpose(ell)*O^(-1)*ell`. Meanwhile

```text
J = integral (R'^2-R*R'')*|F_a|^2
  = transpose(c)*(transpose(T)*O*T-E*B*T)*c,
2*integral |psi'|^2-J >= transpose(c)*M_a*c/2.
```

The cancellation uses both cross terms; it does not estimate them separately. Its matrix identity passes `lake env lean /tmp/sqb67_unsigned_moment_check.lean`, with symmetry and inverse relations as the algebraic inputs. The integral/projection argument is a paper derivation, not a new Lean declaration.

**New source conjecture:** `M_a` is positive semidefinite for every `0<a<1/2`. This would supply the derivative inequality for every even degree-six frequency polynomial, including the actual minimizer `R_a(t)=Q_a(2*t)`. Its sign has not been proved. Plancherel gives the independent physical inputs `mu_j=integral |D^j g_a|^2`; thus only source derivatives through seven enter this particular test. `iteratedDeriv_thetaCuspTiltedSource` supplies their exact finite binomial expansion in the full theta derivatives. The retrieved Gaussian-aperture moments instead integrate `x^(2*j)*exp(lambda*x^2)*Phi(x)` and cannot be substituted for these derivative norms. The next source comparison must bound the complete derivative norms sufficiently to orient `M_a`. No rank-seven or all-order positivity follows yet, and this fixed-size candidate supplies no all-order induction by itself.

The Gaussian reference has an exact positive margin. If `mu_(j+1)=(2*j+1)*v*mu_j` for `0<=j<=6` and `v>0`, then `B*E=O*(v^(-1)*I-T)` and `v^(-1)*O=E+transpose(T)*O+O*T`. Substitution gives `M=v^(-1)*E`. This is an analytical toy proof, not an assertion that the theta moments satisfy the Gaussian recurrence.

The comparison error has a direct full-source expression. For any `v>0`, define

```text
Z_ij = mu_(i+j+1)-v*(2*i+2*j+1)*mu_(i+j),
e_(a,v)(x) = g_a'(x)+(2*v*x-a)*g_a(x)
           = exp(a*x)*(Phi'(x)+2*v*x*Phi(x)).
```

The moment definitions give `B*E=E+transpose(T)*O`, `E*B=E+O*T`, and the symmetric error `Z=O-v*(E+transpose(T)*O+O*T)`. Keeping the full quadratic correction yields

```text
M_a = v^(-1)*E - v^(-2)*Z
      + v^(-1)*(transpose(T)*Z+Z*T)
      + v^(-2)*Z*O^(-1)*Z.
```

For `0<=j<=6`, integration by parts and `D^j(x*g)=x*D^j(g)+j*D^(j-1)(g)` give the actual-source identity

```text
mu_(j+1)-v*(2*j+1)*mu_j
  = integral_R D^(j+1)(g_a) * D^j(e_(a,v)).
```

At `j=0`, the term with the negative derivative index is omitted. These are analytical identities, not additional Lean declarations. A sufficient estimate is `transpose(c)*(Z-v*(transpose(T)*Z+Z*T))*c <= v*transpose(c)*E*c` for every coefficient vector `c`; the remaining quadratic term is nonnegative. This estimate has not been proved for the full source. The exact all-order first-atom jet recurrence and complete likelihood-remainder decomposition are available, but their retrieved tail bounds do not establish this global matrix comparison. No Gaussian approximation of the actual source is assumed.

Further broad deep retrieval across recurrence, adjoints, Jensen hyperbolicity, and localization recovered ordinary Favard identities, conditional quartic Jensen bounds, and qualitative Fourier uncertainty. The Jensen bounds concern a different moment family and retain dispersion hypotheses. The uncertainty statements do not provide the quantitative concentration bound for the degree-six native packets. Generated ingredient groups and source arguments were inspected; coverage remained partial, with interrupted stages in the recurrence and localization requests. These searches produced no additional native sign theorem.

For the separate adaptive deletion basis `P_j=R_a/(t-r_j)`, minimizer orthogonality also gives the exact analytical pairing `integral (R_a*F_a)'*conj(P_j*F_a)=integral |P_j*F_a|^2/2`. Its real part is an integration-by-parts identity and its imaginary part vanishes by signed-source orthogonality. This determines the projection onto the six deletion packets in their ordinary Gram metric; the remaining energy comparison is still open.

### Fixed-coefficient middle comparison

The exact zero-integral compensation identity permits every fixed real coefficient; the coefficient need not be the canonical seam coefficient. Set `L=10^12`, `G_2=thetaCuspTwoAtomCompensationSource`, and `e_G=thetaCuspTwoAtomCompensationErrorBound`. Write `A_full(C,x)` for `thetaCuspNativeEvenFourCompensated C x`, `A_2(L,x)` for `thetaCuspTwoAtomEvenFourCompensated L x`, `A_low(x)` for `thetaCuspTwoAtomEvenFourLower x`, and `E_band(x)` for `thetaCuspEvenFourTwoAtomErrorMatrix x`. A sharper error matrix for this single coefficient is

```text
E_L(x) = E_band(x) - 2*L*e_G(x)*e_3*transpose(e_3).
```

Here the reflection-entry errors are unchanged, while the last correction error is `L*e_G` instead of `3*L*e_G`. This follows directly by multiplying `abs_thetaCuspCenterCompensationSource_sub_two_le` by `L`; it does not discard the correction's mixed source terms. On the proved two-atom ray `pi*exp(2*x)>=37/10`, the analytical quadratic comparison is

```text
v^T*A_full(L,x)*v >= v^T*A_2(L,x)*v - sum_ij |v_i|*E_L(x)_ij*|v_j|.
```

Relative to `v^T*A_low*v-sum_ij |v_i|*E_band_ij*|v_j|`, its right side gains exactly

```text
2*L*(max(-G_2(x),0)+e_G(x))*v_3^2.
```

The gain uses `A_2(L,x)-A_low(x)=2*L*max(-G_2(x),0)*e_3*transpose(e_3)`. For each fixed coefficient, the aperture-dependent matrix `thetaCuspCenterCorrectedEvenFour` integrates entrywise to the original native moments. Its correction dominates the weighted source correction, with a nonnegative diagonal remainder, as proved by `thetaCuspCenterCorrectedEvenFour_posDef_of_source`. This makes the coefficient choice admissible; the aperture-independent source matrix itself is not the exact zero-flux matrix. The complete fixed-source theorem covers `L` on `pi*exp(2*x)>=8`, hence throughout `x>=1/2`, and seam positivity for `L` is proved on an unspecified neighborhood of zero. The explicit inner extension through `8/95` still depends on the unfinished compact determinant incidence. **Positivity of the sharper middle lower form remains unproved.** These strengthened comparison formulas are paper deductions from the existing error estimates, not new Lean declarations or a rank-seven sign theorem.

### First-atom central-factorial reserve and full-source comparison

Set `q=pi*exp(2*x)` and `p_n(X)=product_(0<=j<n)(X^2+4*j^2)`. The exact first-atom reflected kernel, divided by its mass squared, is

```text
exp(-2*q*(cosh(2*y)-1)) *
  (1-12*q/(2*q-3)^2*(cosh(2*y)-1)).
```

The normalized signed moment identity
`L_1(p_n)=(2*n-1)!!*(8*q)^n*(1+6*n/(2*q-3)^2)`
is Lean-checked for all seven orders `0<=n<=6`, retaining the original source normalization. The all-order extension is still a conjecture. The implementation directly proves the seven finite transforms of the literal reflection jets, without assuming a Gaussian source.

Set `v=1/(2*q)`, `h=6/(2*q-3)^2`, `Y=X^2/(8*q)`. Use the monic basis

```text
1,
Y-1,
Y^2+(v-6)*Y+3,
Y^3+(5*v-15)*Y^2+(4*v^2-15*v+45)*Y-15.
```

For an actual even polynomial `sum c_i X^(2*i)`, let `y_i` be its coordinates in this basis. The exact normalized source form `N` completes its first square to `(y_0+h*y_1)^2`. The proved parameter relation is `h*(1-3*v)^2=6*v^2`. Explicit polynomial decompositions and three Young inequalities give

```text
q>=4:   N >= (y_0+h*y_1)^2 + (7/8)*y_1^2 + 3*y_2^2 + 282*y_3^2,
q>=7/2: N >= (y_0+h*y_1)^2 + (5/14)*y_1^2 + y_2^2 + 196*y_3^2.
```

`firstAtomEvenEnergy_eq_centralHermite` identifies `f_1^2*N` with the literal source sum over all sixteen Hankel entries. Consequently the first-atom sixth-degree reserves are `282*f_1^2*(8*q)^6*c_3^2` and `196*f_1^2*(8*q)^6*c_3^2` on the respective domains. Both unequal-atom terms and the complete tail error still have to be transferred and bounded; the complete-source middle interval and rank-seven norm sign remain open.

For the retained pair, set `a=5*q`, `b=3*q`, `z=exp(-3*q)`, and let `H_n(a,b)` be the coefficient of `u^n` in

```text
exp(2*a*u)*cos(2*b*sqrt(u*(1-u))).
```

The cosine has an ordinary power series in `u`, so the coefficient is the finite sum

```text
sum_(j=0..n) (-1)^j*(4*b^2)^j/(2*j)! *
  sum_(k=0..min(j,n-j)) (-1)^k*choose(j,k)*(2*a)^(n-j-k)/(n-j-k)!.
```

The seeded mixed coefficient is
`B_n=(a^2-b^2+9-6*a)*H_n+12*a*H_(n-1)+6*b*partial_b(H_n)`, with `H_(-1)=0`.
This follows by writing the pair's even reflected kernel as an exponential times a hyperbolic cosine and its derivative; substitution `u=sin(t)^2` retains both unequal-atom terms. In units `4*q^2*exp(x-2*q)`, the two-atom central-factorial moment is therefore the candidate expression

```text
c_n*q^n*((2*q-3)^2+6*n) + 8*z*(2*n)!*B_n(5*q,3*q)
  + 16*z^2*c_n*(4*q)^n*((8*q-3)^2+6*n),
c_n=(2*n)!*4^n/n!.
```

These mixed-coefficient identities are analytical, not yet Lean-checked. They give a structured target for the retained two-atom correction and its Schur numerator; replacing the mixed terms by zero is not justified. The complete third-and-higher-atom error remains the one already proved through twelve.

A further fixed-coefficient target uses the literal first-atom correction `G_1=3*f_1^2+2*x*f_1*f_1'`. The actual scale obeys `12*q*x<=q^2-9`: multiply `2*x<=sinh(2*x)` by the positive scale and retain `pi>3`. With `P_0=4*q^2-6*q`, `P_1=-8*q^3+30*q^2-15*q`, the adverse first-atom correction is bounded by a single polynomial:

```text
W(q)=629145600*q^7*(2*q-3)
  +10^12*(-8*q^4+30*q^3+129*q^2-378*q+135).
```

For `q>=4`, its proved positive decomposition uses `q-4` on `[4,5]`, `q-5` on `[5,6]`, and `q-6` on `[6,infinity)`. The Lean-checked source identity is

```text
6*q*(10^12*G_1+200*f_1^2*(8*q)^6)
 -2*q^2*(2*q-3)*exp(x-2*q)*W(q)
 =10^12*exp(x-2*q)*P_0*P_1*(12*q*x-q^2+9).
```

The product `P_0*P_1` and the final factor are nonpositive on this domain. The proof of `W>0` therefore gives `10^12*G_1 > -200*f_1^2*(8*q)^6`. Joining this to the literal first-atom form proves

```text
E_1(x,c)+10^12*G_1(x)*c_3^2 >=
 f_1^2*((y_0+h*y_1)^2+(7/8)*y_1^2+3*y_2^2+82*y_3^2)
```

for every real coefficient vector, `x>=0`, and `q>=4`. This is `firstAtomCompensatedEvenEnergy_coordinate_lower` in [ThetaCuspFirstAtomCentralFactorial.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspFirstAtomCentralFactorial.lean). The full scratch check `/tmp/sqb81_all.lean` passes. The module is wired into the RHTower umbrella. Its final narrow build passes in `/tmp/sqb81-central-factorial-leaf-audit`, against the actual source and existing compiled dependencies (`/tmp/sqb81_build.txt`). The compiled-module audit `/tmp/sqb81_final_audit.lean` checks all fourteen public theorems; each uses only `propext`, `Classical.choice`, and `Quot.sound`. Global formal lint passes (`/tmp/sqb81_formal_lint.txt`). All owned Lean/Lake processes for this module completed. The mixed-atom quadratic form and complete remainder must be compared against this full four-coordinate lower form, not merely its last-coordinate scalar reserve.

Broad all-view deep searches through cumulants, Gaussian Schur bounds, Rodrigues/Appell/Touchard, central factorials/Sheffer, and head/cofactor bounds, coherent states, Gaussian product squares, and Poisson finite differences inspected candidate statements, source arguments, methods, and ingredient groups. All requests reported partial coverage; the head-bound request also reached its deadline before judging finished. The recent broad searches `majorization` and `caustics` supplied [Poset-refined majorization relations](https://arxiv.org/html/2607.28061v1), whose refined eigenvalue inequality requires orthonormal spectral bases and an LU approximation of their overlap. That theorem has not been applied to the nonorthogonal source basis here.

### Exact finite-difference square formula for retained pairs

For a real parameter `lambda`, define the polynomial moment functional `T_lambda` by its formal exponential generating series `exp(lambda*(exp(t)-1))`. This definition applies to negative parameters without a probability interpretation. Its polynomial product identity is

```text
T_lambda(A*B) = sum_k lambda^k/k! * T_lambda(Delta^k A)*T_lambda(Delta^k B),
Delta A(J)=A(J+1)-A(J).
```

The sum terminates at the smaller polynomial degree. A finite definition is
`T_lambda(P)=sum_(k=0..degree(P)) lambda^k/k! * (Delta^k P)(0)`.
For the product identity, the forward difference on a product is represented on the tensor product by the sum of three commuting operators `Delta tensor 1`, `1 tensor Delta`, and `Delta tensor Delta`. They are nilpotent on each fixed polynomial-degree space, so their finite exponential factors exactly. Evaluation at `(0,0)` yields the displayed identity. Equivalently, compare coefficients in `F(s+t)=F(s)*F(t)*exp(lambda*(exp(s)-1)*(exp(t)-1))`. Tensoring gives the two-variable identity with weights `lambda^k*mu^l/(k!*l!)`. For `lambda=-p`, `mu=-r`, these weights have sign `(-1)^(k+l)`, so the negative directions are explicit finite-difference squares.

This functional represents the literal atom pair, including its seed. Put `W(J)=4*J*(J-1)+6*J=4*J^2+2*J`, and for physical even coefficients `c_i` put `A(J,K)=sum_(i=0..3) (-1)^i*c_i*(2*(J-K))^(2*i)`. The pair contribution to the even energy is

```text
e^(x-p-r) * (T_(-p) tensor T_(-r))(W(J)*W(K)*A(J,K)^2).
```

Indeed, the weighted generating series is exactly
`P_0(p*exp(2*y))*P_0(r*exp(-2*y))*exp(-p*exp(2*y)-r*exp(-2*y))`, after restoring the factor `exp(x)`, where `P_0(u)=4*u^2-6*u`. For the first and second atoms, `(p,r)=(q,4*q)`; the swapped pair contributes equally. The seed itself has the exact four-square decomposition, with `U=2*J+1/2` and `V=2*K+1/2`,

```text
W(J)*W(K)*A^2 = (U*V*A)^2 - (U*A)^2/4 - (V*A)^2/4 + A^2/16.
```

Thus the proposed comparison retains every lower clock derivative in finitely many signed squares, rather than replacing the pair by its Gaussian approximation. The finite one-variable product and square formulas, and the two-variable square formula for every finite separated polynomial expansion, are now Lean-checked in `HTGeometry/PolynomialSignedPoissonProduct.lean`, namespace `HTGeometry.SignedPoisson`. The construction uses the actual forward-difference operator on degree-bounded polynomials, proves its nilpotence by degree descent, proves the three-term tensor product rule, and factors its finite exponential. `moment_product`, `moment_square`, and `pairSquare_eq_difference_squares` retain every signed coefficient for arbitrary real parameters. The scratch check `/tmp/sqb82_product_final.lean` and narrow leaf build both pass; the five audited capstones use only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into the HTGeometry umbrella. The seeded theta-pair identification displayed above remains an analytical generating-series argument, not a new Lean source-incidence theorem. Domination of the negative squares by the actual coordinate reserve and fixed correction remains unproved.

### Complete order-twelve cooling at physical scale eight

The full higher-likelihood measure has support `t>=3`. Hence `q>=8` gives `q*t>=24`, where the existing exact scalar cooling-score bounds apply through order twelve. Integrating the signed bounds against that complete measure, then applying the spectral moment ceiling, proves

```text
0 <= (-1)^n*R^(n)(x) <= (6*q)^n*epsilon,  0<=n<=12, q>=8,
R = thetaCuspLikelihoodSourceRemainder,
epsilon = regimeOneLikelihoodScale.
```

No atom is omitted. Factoring the full reflection error through the exact first-atom reflected product gives

```text
abs(nativeJet_n-firstAtomJet_n)
 <= sum_(i=0..n) choose(n,i)*abs(firstAtomJet_i)*
      [2*(6*q)^(n-i)*epsilon+(12*q)^(n-i)*epsilon^2].
```

Both inequalities pass the foreground scratch check `/tmp/sqb82_cooling_twelve.lean` and are installed and wired in `RHTower/ThetaCuspSharpFiniteCoolingTwelve.lean`. The final narrow build passes in `/tmp/sqb82-pair-cooling-leaf-audit` against actual source and existing compiled dependencies. The compiled-module audit `/tmp/sqb82_final_audit.lean` checks all five cooling/reflection capstones and five signed-product capstones; all use only `propext`, `Classical.choice`, and `Quot.sound`. The latest global formal lint passes (`/tmp/sqb83_formal_lint.txt`). The cooling bounds feed the complete-source positivity theorem below.

The complete source errors now fit the four central coordinates already carrying reserves `1,7/8,3,82`. With `s=8*q`, the proved normalized entry ceilings for orders `0,...,6` are

```text
[1/200000000, 1/5000000, 1/100000, 1/3000, 1/70, 3/4, 40].
```

Their incidence as bounds for the actual source entries is proved by `abs_native_even_sub_first_le_centralErrorCeiling`. The finite rational comparison and complete central-coordinate error budget pass `/tmp/sqb83_coordinate_error.lean`. The source-entry capstone in `/tmp/sqb83_source_error.lean` uses only `propext`, `Classical.choice`, and `Quot.sound`. Put `d=[1,1,3,15,105,945,10395]`. The checked finite convolution is

```text
sum_(j=0..k) choose(2*k,2*j)*(3/2)*d_j*
  [2*36^(k-j)/800000000+144^(k-j)/800000000^2] <= e_k.
```

For `0<=v<=1/8`, the inverse central-coordinate vector is

```text
z=[y0-y1+3*y2-15*y3,
   y1+(v-6)*y2+(4*v^2-15*v+45)*y3,
   y2+(5*v-15)*y3, y3].
sum_(i,j=0..3) e_(i+j)*abs(z_i)*abs(z_j)
  <= y0^2/8+y1^2/8+2*y2^2+70*y3^2.
```

The proof retains all sixteen entries and uses six Young squares. The actual-entry join uses proved nonnegative first-atom moments with ceiling `(3/2)*d_j` after division by `f1^2*(8*q)^j`, exact vanishing of odd reflection jets, and the analytical exponential bound `q^j*epsilon<=8^j/800000000` for `j<=6` on `q>=8`. The complete compensation also satisfies

```text
10^12*abs(Gfull-G1) <= f1^2*(8*q)^6,   q>=8.
```

Indeed `Gfull-G1=G1*(2*R+R^2)+2*x*f1^2*(1+R)*R'`, the complete cooling bounds give `abs(Gfull-G1)<=11*q^2*epsilon*f1^2`, and the same analytical exponential ceiling pays this cost. Both source capstones pass the scratch axiom audit with only the standard three axioms. The checked error bounds are installed and wired in `HTGeometry/CentralHermiteReflectionErrorBudget.lean` and `RHTower/ThetaCuspScaleEightReflectionError.lean`. Both passed the final narrow build with the source-positivity leaf.

The exact coordinate identity passes `/tmp/sqb83_coordinate_inverse.lean`. Combining it with the two proved physical error bounds and the first-atom lower form proves the complete reserve

```text
f1^2*((3/4)*(y0+h*y1)^2+(47/64)*y1^2+y2^2+11*y3^2),
h=6/(2*q-3)^2.
```

The closed theorem `thetaCuspNativeEvenFourFixed_posDef_of_half_le` in [ThetaCuspEvenFourCentralTail.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspEvenFourCentralTail.lean) proves fixed-coefficient positivity for every `q>=8`, hence every `x>=1/2`, with `L=10^12`. All sixteen entries and the complete likelihood tail are retained. The module is wired once into the RHTower umbrella. The final narrow `lake build GaloisForLFunctions.RHTower.ThetaCuspEvenFourCentralTail` passes in `/tmp/sqb83-central-tail-leaf-audit`, compiling exactly the three new leaves against actual repository source and existing dependencies (`/tmp/sqb83_central_tail_build.txt`). The compiled-module audit `/tmp/sqb83_final_audit.lean` checks all sixteen public theorems; every one uses only `propext`, `Classical.choice`, and `Quot.sound`. Global formal lint passes (`/tmp/sqb83_formal_lint.txt`). All owned Lean/Lake processes for these modules completed. This theorem fixes `L=10^12`; the canonical coefficient and whole rational family retain their separately proved endpoint `x>=4/5`. The lower middle interval and all-rank extension remain open.

For the inner interval, the next concrete conjecture retains the unequal-atom pair's leading positive square, using the signed-Poisson formula above, and charges its remaining signed derivative squares to the existing coordinate reserve. The required seeded theta-pair incidence is still analytical. A broad Pochhammer search recovered the complete polynomial basis and finite coefficient reconstruction in `HTGeometry/GammaShiftConfluentAnnihilator.lean`. Let `U` send the ascending-factorial polynomial `(X)_n` to `X^n`, and set `N(P)=U(P(-X))`. The concrete source-identification conjecture is

```text
N(X*P)=X*((N(P))'-N(P)),
N(4*X^2+2*X)=4*X^2-6*X,
(d/dx)[exp(x/2-q)*N(P)(q)]
 =exp(x/2-q)*N((2*X+1/2)*P)(q),  q'=2*q.
```

This converts literal theta differentiation into multiplication by the same signed clock index used in the pair-square formula. The source transform now agrees exactly with the existing finite-difference moment: `N(P).eval p = moment n (-p) P` on every bounded-degree space. Its unrestricted product and square identities therefore apply to the literal atom frame. The complete scratch `/tmp/sqb84_source_umbral.lean` passes; all eight printed capstones use only `propext`, `Classical.choice`, and `Quot.sound`. The pure results are installed in `HTGeometry/PolynomialSignedPoissonSourceTransform.lean`; its required dependency olean passes a foreground `lake env lean` check. The atom results are installed in `RHTower/ThetaCuspSignedPoissonAtoms.lean`. Both leaves are wired once. The final narrow `lake build GaloisForLFunctions.RHTower.ThetaCuspSignedPoissonAtoms` passes in `/tmp/sqb84-source-pair-leaf-audit`, compiling both actual repository leaves against cached dependencies. The compiled-module audit `/tmp/sqb84_final_audit.lean` checks all 35 public theorems, each using only `propext`, `Classical.choice`, and `Quot.sound`. Global formal lint passes (`/tmp/sqb84_formal_lint.txt`). All owned SQB84 Lean/Lake processes completed.

The paired source identity is installed and audited at every finite rank. With `J=X tensor 1`, `K=1 tensor X`, `D=2*(J-K)`, `W(X)=4*X^2+2*X`, and `A_c(D)=sum_i c_i*(-1)^i*D^(2*i)`, the literal ordered atom-pair even energy is exactly

```text
exp(x-p-r) * (T_-p tensor T_-r)(W(J)*W(K)*A_c(D)^2),
p=pi*a^2*exp(2*x), r=pi*b^2*exp(2*x).
```

`thetaCuspAtomPairReflectionJet_eq_moment`, `thetaCuspAtomPairEvenEnergy_eq_moment`, and `pairedNegativePoissonEvaluation_separated_square` pass `/tmp/sqb84_pair_source.lean` with only the standard three axioms. Thus the signed-square formula now has a literal paired-source identification; no atom-pair positivity follows from that identity alone. The exact seed-shift theorem in the same passing scratch is

```text
T_-p(W*P) = 4*p^2*T_-p(P(X+2)) - 6*p*T_-p(P(X+1)).
```

Tensoring retains four seed terms. Equal shifts leave `A_c(D)` unchanged, giving the installed and audited three-term identity:

```text
(T_-p tensor T_-r)(W(J)*W(K)*A_c(D)^2)
 = (16*p^2*r^2+36*p*r)*M(A_c(D)^2)
   -24*p^2*r*M(A_c(D+2)^2) -24*p*r^2*M(A_c(D-2)^2),
M=T_-p tensor T_-r.
```

The intended estimate groups these signed terms before charging their deficit to the first-atom central reserve and the proved complete deep-tail error. The inner quantitative sign and the all-rank extension remain open. The same module proves `thetaCuspTwoAtomEvenEnergy_eq_four_pair_moments`: the literal two-atom energy is the sum of all four ordered pair energies, including both unequal pairs. These are exact source identifications; their inner lower bound is not asserted.

Broad all-view searches through localization, Riccati, Darboux, and Wronskian mechanisms inspected all candidate and method views; source and semantic coverage remain partial and compiler metadata largely pending. The retrieved Jacobi compression formula retains its terminal square, and the adjacent-trace sign theorem retains its positive-moment and trace premises. Neither has yet supplied the native inner-source estimate. An independently chosen Wronskian arXiv search found [Strict Total Positivity from Spectral Darboux and Toeplitz Smoothing Mechanisms](https://arxiv.org/html/2607.02778v1), dated 2 July 2026. Its spectral induction propagates positive pivots using a shared scalar differential equation and ordered endpoint asymptotics at every stage. The actual theta source has not yet been identified with such a spectral family; no paper theorem is used as a Lean premise.

Broad all-view deep searches using independently chosen queries for discrete product coercivity, Touchard/Charlier moment mechanisms, and cooling inspected declarations, candidate statements, source arguments, methods, proof ideas, and ingredient groups. The cooling search recovered the exact scalar order-eleven/twelve bounds and full-measure support/score identities used above. Coverage remains partial, with stale source/compiler records and an interrupted/deadline stage in the discrete-product request. The exact lexical Touchard/Charlier query returned no hits; this is not a corpus-absence conclusion. Independent recent arXiv searches for hypocoercivity, subordination, and indefinite forms recovered [Weighted L2 bounds for kinetic Fokker–Planck equations and hypocoercivity](https://arxiv.org/html/2608.28120v1) and [Hypocoercivity-preserving space-time Galerkin methods](https://arxiv.org/html/2606.29621v1). Their coupled weighted-energy estimates require identified transport/diffusion operators; no such paper theorem supplies the theta sign here.

Broad all-view deep searches through perturbation/inertia, creation/annihilation, apolarity, and a root-exterior signed-square mechanism inspected declarations, candidate lemmas, source arguments, proof ideas, and ingredient sets. Some requests ended at the judging deadline with pending coverage. The oscillator search recovered exact polynomial-Gaussian derivative bounds; applying them to the negative-parameter theta functional still needs a quantitative source comparison. The apolarity search recovered factorial-weighted polynomial pairings, while the signed-root search returned an angular transport inequality requiring a split polynomial in a cosine coordinate. Neither is yet identified with the required inner pair budget. No absence conclusion follows. Independently chosen umbral searches found [Analytic umbral transmutations and Bessel moments](https://arxiv.org/html/2606.05214v1) and [A Resurgent Analytic Framework for Indicial Umbral Calculus](https://arxiv.org/html/2606.11134v1). The former groups Bessel factors into distinct clocks before a Mellin–Barnes contraction; the latter transfers analytic pairings through Gamma regularisation under admissibility hypotheses. These supply comparison ideas, not a theta sign theorem or Lean premise.

### SQB85: coupled affine inner-source attack

The current conjecture uses the lower-middle interval `37/10<=q<=5`. Write `z=exp(-3*q)` and `U(q)=twoAtomLowerEnvelope q`, so the corpus proves `0<z` and `U(q)*z<=1`. The literal retained energy has the exact form `E11+exp(x-2*q)*z*B+E22`, where `B` contains both ordered unequal-pair clock moments. Transporting the positive first-atom degree-six form by the actual logarithmic dilation should prove `E22>=0`. Hence `E11+exp(x-2*q)*min(0,B/U(q))` is a lower model. The complete compensation already has the direct lower bound `G>=F^2/2`; this avoids replacing it by the two-atom compensation and charging a separate correction-tail error. The remaining raw reflection error must still retain all sixteen entries through derivative twelve. The intended endpoint inequality is an actual source margin above that full error, not positivity of the generic signed Poisson functional. This lower-model construction and its endpoint sign are under proof; no inner interval is yet closed.

The affine-pencil mechanism search (`/tmp/sqb85_affine_pencil_search.json`) returned partial deadline results, including the already used complete two-atom quadratic error. The later broad OR search (`/tmp/sqb85_sheffer_search.json`) inspected all views and returned Gamma–Meixner value frames and unrelated Boolean Sheffer algebra, not an applicable inner-source margin. Its inventory covers 56,804 files and 730,613 declarations; 706,128 method records are ready, 725 stale, while compiler metadata remains mostly pending and semantic retrieval is partial. No absence claim follows.

The all-view deep searches `/tmp/sqb85_translation_energy_search.json`, `/tmp/sqb85_christoffel_search.json`, and `/tmp/sqb85_bernstein_search.json` inspect finite derivative-norm, quadrature, and coefficient mechanisms. The first two return partial judging deadlines; the Bernstein request has full source inventory but incomplete semantic coverage and mostly pending compiler records. Gaussian translation inequalities and Christoffel bounds require their own positive norm; Bernstein basis nonnegativity is available but the actual endpoint coefficients still need a proof. Independently chosen recent searches found [Positive quadrature and mobile sampling](https://arxiv.org/html/2608.11915v1), 12 August 2026, whose sign-localized polynomial tests use exactness and positive weights, and [Local Weyl law and length-minimising loops](https://arxiv.org/html/2607.24060v1), 27 July 2026, which groups paired contributions before controlling an averaged remainder. Neither supplies the required pointwise theta inequality; no numerical experiment or paper assertion enters Lean.

For the next explicit sign attack, put `S(q,c)=M_(q,q)(W tensor W * A_c(D)^2)`, retain `B(q,c)=M_(q,4q)(W tensor W * A_c(D)^2)+M_(4q,q)(W tensor W * A_c(D)^2)`, and clear the positive envelope denominator:

```text
P(q,c) = U(q)*S(q,c) + B(q,c)
         + 500000000000*U(q)*(4*q^2-6*q)^2*c3^2.
```

This is a polynomial in `q`, quadratic in the four test coefficients, using the audited finite transform. The first endpoint is `S+500000000000*(4*q^2-6*q)^2*c3^2`; the second is `P/U`. The first-atom energy already supplies its positive reserve. The new hard assertion is a uniform lower bound for the second endpoint above the complete normalized raw reflection error on `37/10<=q<=5`. Neither a coefficient-sign decomposition of `P` nor this error-dominating margin has been proved. Dropping the pure second pair is only a proved-nonnegative-term strategy; it may have to be restored if this endpoint bound proves too weak.

Further independent word searches found [Umbral calculus over a vector space](https://arxiv.org/html/2609.10030v1), 9 September 2026, and [Charlier and Meixner Sobolev-type generating functions](https://arxiv.org/html/2607.12889v1), 14 July 2026. The former expresses raising and multiplication operators through lowering differentials in symmetric tensor coordinates. The latter retains a rank-one finite-difference correction with its degree-dependent reproducing-kernel denominator and assumes a positive classical discrete measure. These are possible recurrence and finite-completion mechanisms; neither has been identified with the signed theta endpoint form.

### SQB86: proved affine endpoint head margins

The coupled endpoint `z=1/U(q)`, `U(q)=twoAtomLowerEnvelope q`, has strict leading even minor margins throughout the **closed** interval `37/10<=q<=5`. Define `Affine(p,z)=2*p(z)-(p(2*z)+p(0))/2`; for the existing quadratic two-atom numerator polynomials this retains exactly their constant and linear terms. In the common normalization with the Gaussian square and `4*q^2` removed, put

```text
a0 = (2*q-3)^2 + 8*z*(2*q-3)*(8*q-3),
ak = q*Affine(twoAtomOddNumeratork(q,·),z),  k=1,...,4.
```

The formalized conclusions at `z=1/U(q)` are

```text
a0 > 0,
a0*a2-a1^2 > 100000,
a0*(a2*a4-a3^2)-a1*(a1*a4-a2*a3)+a2*(a1*a3-a2^2) > 1000000000000.
```

The proof keeps every mixed term before forming the minors. Its homogeneous variables are `u,t>=0`, `u+t>0`, with `A=37*u+50*t`, `B=10*u+10*t`, `U_h=325*(200*u^2+1180*u*t+2501*t^2)`, and `V=(u+t)^2`. For `q=A/B`, `z=V/U_h`, the polynomial moments satisfy `b_k=U_h*B^(2*k+2)*a_k`. Exact symbolic normalization and positivity prove

```text
b0*b2-b1^2 > 100000*U_h^2*B^8,
det Hankel_3(b) > 1000000000000*U_h^3*B^18.
```

The substitution `u=50-10*q`, `t=10*q-37` covers the full closed interval, including both endpoints, and gives `A=130*q`, `B=130`, `U_h=169*U(q)`, `V=169`. The normalization identities to the existing numerator polynomials are checked in Lean. This is an actual sign-and-margin result for the affine endpoint head. The fourth-coordinate completion, admission of the physical affine form, and the full-source tail margin remain separate obligations; no complete inner interval or all-rank theorem is claimed.

Implemented in `formal/GaloisForLFunctions/HTGeometry/TwoAtomAffineEvenHead.lean`, with capstones `twoAtomAffineEvenMass_pos`, `twoAtomAffineEvenHead_lower`, and `twoAtomAffineEvenThreeDet_lower`. Foreground scratch `/tmp/sqb86_release.lean` passes; the installed source matches it, the module is wired once into the HTGeometry umbrella, and the narrow final `lake build GaloisForLFunctions.HTGeometry.TwoAtomAffineEvenHead` passes in `/tmp/sqb86-affine-head-leaf-audit` (log `/tmp/sqb86_affine_head_build.txt`). Formal lint passes (`/tmp/sqb86_formal_lint.txt`). Per the user's updated instruction, no further `#print axioms` checks are run.

Independent deep searches for a mixed-term absorption mechanism and broad OR `coercivity polarization` inspected declarations, candidate lemmas, methods/source arguments, proof ideas, and ingredient groups. The latter covers 56,810 files and 730,683 declarations, with 706,128 methods ready and 724 stale; compiler metadata is mostly pending and semantic retrieval timed out. Retrieved source-specific coercivity results apply to other forms; the available generic operator bounds assume the positivity needed here.

The independently chosen recent word search also located [additive Maxwell–Stefan diffusion](https://arxiv.org/html/2609.06732v1), 6 September 2026, and [fourth-order skyrmions](https://arxiv.org/html/2609.08255v1), 8 September 2026. The first diagonalizes constrained pair dissipation using its additive pair law; the second uses a forced Helmholtz mean identity and the sphere constraint to retain a positive residual at a degenerate threshold. Their stated structures have not been identified with the theta endpoint form. No paper assertion enters a Lean proof.

### SQB87: fixed-product scalar recurrence for the fourth-coordinate attack

The next analytical construction uses the literal ordered atom pair. Put `p(t)=p*exp(2*t)`, `r(t)=r*exp(-2*t)`, `a=p*r`, and `w(t)=p(t)+r(t)`. Then `a` is constant, `w''=4*w`, and `(w')^2=4*(w^2-4*a)`. The original seeded pair is exactly

```text
4*a*exp(x-w(t))*(4*a+9-6*w(t)).
```

For a polynomial `P` in `w`, define

```text
S_a P = -4*((w^2-4*a)*(P''-2*P'+P) + w*(P'-P)),
P_(a,0)=4*a+9-6*w,     P_(a,k+1)=S_a P_(a,k).
```

The chain and product rules then give the all-order paper identity

```text
(-1)^k * pairReflectionDerivative_(2*k)
  = 4*a*exp(x-w(0))*P_(a,k)(w(0)).
```

Consequently the affine first/two-atom moments, after removing `4*q^2*exp(x-2*q)`, have the one-variable description

```text
a_k(q,z) = P_(q^2,k)(2*q) + 8*z*P_(4*q^2,k)(5*q).
```

For `k=0` this is the exact mass polynomial in SQB86. The intended next proof constructs `k=5,6` with this recurrence and attacks the complete affine four-by-four determinant with its fixed correction. This reduces each even-derivative step to one second-order polynomial operator and keeps both ordered mixed pairs. The scalar-profile second derivative, all-order recurrence, and literal theta-pair identification pass `lake env lean /tmp/sqb87_radial_source.lean`. They are installed in `formal/GaloisForLFunctions/RHTower/ThetaCuspPairRadialRecurrence.lean`, wired once into the RHTower umbrella. The capstones are `thetaPairRadialProfile_second`, `thetaPairRadialProfile_even`, `thetaCuspAtomPair_eq_radialProfile`, and `thetaCuspAtomPairEvenJet_eq_radial`. The last theorem gives every original even atom-pair derivative with its exact Gaussian normalization and actual squared frequencies, for all natural atom indices and derivative orders. The narrow final `lake build GaloisForLFunctions.RHTower.ThetaCuspPairRadialRecurrence` passes in `/tmp/sqb87-radial-leaf-audit` (log `/tmp/sqb87_radial_build.txt`), and updated formal lint passes (`/tmp/sqb87_formal_lint.txt`). No axiom-printing check was run. The fourth determinant margin remains unproved. No numerical experiment or extracted numerical certificate is used.

The broad OR radial/Casimir/Sturm search (`/tmp/sqb87_radial_search.json`) inspected all views. Inventory: 56,825 files, 730,883 declarations, 706,128 ready methods and 724 stale methods; semantic indexing remains partial and compiler records mostly pending. It found Sturm integration-by-parts and amplitude identities, plus Casimir sum-of-squares laws under Hermitian hypotheses. None was imported as a positivity premise for the theta form.

The later broad OR mixed-discriminant search (`/tmp/sqb86_mixed_discriminant_search.json`) inspected all available views. Its inventory covers 56,820 files and 730,859 declarations; semantic reranking timed out, compiler metadata is mostly pending, and 724 method records are stale. It retrieved Gaussian log-determinant concavity and positive-cone determinant monotonicity, with positivity or source-incidence assumptions not yet supplied for the full four-coordinate form.

### Complete compensated outer region through four fifths

Put `q=pi*exp(2*x)`, `f_1=thetaCuspSourceTerm x 1`, and `epsilon=regimeOneLikelihoodScale x`. The cooling recurrence only needs `m+n<=q` and `(m+n)/3<=q-pi`. Combining it with the Gaussian source jets gives the full reflected derivative bound under `6<=q` and `n+3<=q`. In balanced coordinates, for `6<=q` and `2*k+3<=q`,

```text
abs(nativeScaled_k-firstScaled_k)/32^k
  <= 18*8^k*q^k*epsilon + 9*18^k*q^k*epsilon^2.
```

Keep the order `k` throughout the estimate. For `k<=6` and `q>=15`, polynomial-exponential monotonicity and the analytically proved `exp(15)>3200000` give

```text
E = 32/(3200000)^3,
q^k*epsilon <= 15^k*E,   epsilon <= E,
q^k*epsilon^2 <= 15^k*E^2,
abs(nativeScaled_k-firstScaled_k)/32^k
  <= 18*120^k*E + 9*270^k*E^2 <= 120^k*(2/10^17).
```

The exact first-atom reserved determinant has floor `1/10000` on `q>=15`. Its balanced entries leave room for the displayed errors inside the separate ceilings `[2,1/3,1/4,1/3,1,2,5]`. The sixth-profile estimate uses denominator at least `129/10` and numerator absolute value at most `51000000000`. Expanding the determinant into its sixteen product terms and telescoping each product gives error at most `3*10^12*eta` whenever entry `k` has error at most `120^k*eta`. With `eta=2/10^17`, the complete reserved determinant is therefore at least `1/25000`. Its actual native Schur coordinate divided by `f_1^2*q^6` exceeds `100000000`.

The complete mass/slope estimates retain

```text
G = 3*F^2+2*x*F*F' >= -(13/50)*q^2*f_1^2,
G/(f_1^2*q^6) >= -(13/50)/15^4.
```

Consequently every fixed `0<=C<=3*10^12` has compensated normalized Schur coordinate strictly above `80000000` on `q>=15`. A finite Taylor lower bound proves `x>=4/5` implies `q>=15`. The actual complete matrix `thetaCuspNativeEvenFourCompensated C x` is positive definite there, including the canonical coefficient. The literal weighted matrix is positive for every positive aperture and `r>=8/5`. The uniform seam theorem supplies one `delta>0`, `delta<=4/5`, covering every `10^12<=C<=3*10^12` on `0<=x<delta` or `x>=4/5`.

The constructions are formalized in `HTGeometry/FirstAtomEvenTailEntrywiseReserve.lean`, `RHTower/ThetaCuspSupportScaleReflectionApproximation.lean`, and `RHTower/ThetaCuspEvenFourEntrywiseTail.lean`. Verification: foreground scratch checks, three narrow leaf builds against actual repository source and cached dependencies, formal lint, and a separate canonical-source/weighted-source/common-gap axiom audit. The capstones use only `propext`, `Classical.choice`, and `Quot.sound`. Modules are wired into their umbrellas; no umbrella build or numerical experiment is used. **The inner complete-source sign, fixed-barrier compatibility, global degree-six cutoff norm, and all-rank positivity remain open.**

Broad all-view deep searches through Laguerre polynomials, derivative geometry, anisotropic perturbations, reflected pairs, exponential-polynomial positivity, and Toda recurrences inspected declarations, candidate lemmas, source arguments, methods, and proposed ingredient groups. Coverage remains partial and compiler metadata stale. The concrete inner candidate retains both leading atoms using `ThetaCuspTwoAtomScalePolynomials`, with `ThetaCuspDeepTailCoolingTwelve` and `ThetaCuspTwoAtomReflectedTwelve` controlling every required remainder derivative on `q>=37/10`. The actual compensated two-atom lower form still needs its positive margin. `XiShiftedJacobiFrameToda` provides a positive transported boundary-square integral once a differentiable symmetric frame and invertible compression are constructed; constructing that frame from the actual cutoff data remains part of the source problem.

### Actual modular ratio bounds and next determinant target

Write `u=thetaCuspModularMassDrift`, `A=thetaCuspModularGapAmplitude`, and `w=thetaCuspModularTransverseShear`. The actual source ODE and the proved strict energy floor give, on `x>=0`,

```text
t = 9-u^2 > 0,  R = A/t,  k = 3R/4-1/3 > 2/3,
J = u*k-w,     D = t-6/k-4/k^2,
u' = k*t,      t' = -2*u*k*t,
k' = 2*(k+1/3)*J,
J' = k^2*D+2*u*(k+2/3)*J,
D' = -2*u*k*t+2*(k+1/3)*(6/k^2+8/k^3)*J.
```

The formalized global comparison is `J>=0`, hence `R` nondecreasing and
`A(x)>=A(0)*(9-u(x)^2)/9`, with the accompanying shear bound
`w(x)<=u(x)*(3*A(x)/(4*(9-u(x)^2))-1/3)`.

The analytical argument uses the complete actual orbit. If `J` has a negative component `(a,b)`, then `a>=0` and `J(a)=0`, since `J(0)=0`. Its right derivative at `a` is nonpositive, so `D(a)<=0`. Throughout that component `D'<0` and therefore `D<0`; the displayed equation then gives `J'<0`. Continuity excludes a finite right endpoint, so `b=infinity`. Fixing `c>a`, one obtains `J(x)<=J(c)<0` and `k'(x)<=2*J(c)` for every `x>=c`, contradicting the global floor `k>2/3` after integration. The complete argument is formalized in [ThetaCuspModularRatioMonotonicity.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspModularRatioMonotonicity.lean), namespace `RHTower.ThetaCuspModularRatio`. Its public conclusions include `J_nonneg`, `ratio_mono`, `gap_lower`, and `shear_upper`.

The stronger global bound `J<1` is also formalized in [ThetaCuspModularRatioUpperBarrier.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspModularRatioUpperBarrier.lean). The preceding comparison gives `k>=k(0)>5/4`; the last strict inequality uses the proved actual seam bound `A(0)>191/10`. The derivative equation rewrites exactly as

```text
J' = (3-u)*((u+3)*k^2-2*k-4/3)
       +2*u*(k+2/3)*(J-1).
```

The first term is strictly positive: `3-u>0`, and the bracket is at least `41/48` for `u>=0`, `k>=5/4`. If `J(b)>=1`, then `b>0`, the derivative at the level `1` prevents return below it, and `u(x)>=u(b)>0` on the resulting ray. Also `J<=u*k<=3*k`, since `w>=0`. Consequently `J'>(2*u(b)/3)*(J-1)^2` there. Setting `c=2*u(b)/3` and `f=c*(1-J)` gives a nonpositive function on a complete ray with `f'<-f^2`, contradicting the complete-ray Riccati escape theorem. The resulting actual shear interval `u*k-1<w<=u*k` is now proved in Lean, through `J_lt_one` and `shear_lower`. Integration of `k'<=2*(k+1/3)` also gives the paper consequence `k(x)+1/3<=(A(0)/12)*exp(2*x)`; that exponential comparison is not a new Lean theorem.

The actual-source derivative equations and the global comparison pass foreground scratch Lean checks. The final four capstone audits in `/tmp/sqb71_modular_ratio_final_check.lean` use only `propext`, `Classical.choice`, and `Quot.sound`. Installed source bytes match the checked staging source, the module has exactly one RHTower umbrella import, and formal lint passes. The final narrow `lake build GaloisForLFunctions.RHTower.ThetaCuspModularRatioMonotonicity` passes in `/tmp/sqb71-ratio-leaf-audit`, using the actual repository source and existing compiled dependencies. This is a leaf audit against the compiled corpus, not a fresh full dependency rebuild.

The upper barrier passes `lake env lean /tmp/sqb72_modular_ratio_upper.lean`, including capstone axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`. Its installed module is wired once into the RHTower umbrella. The final narrow `lake build GaloisForLFunctions.RHTower.ThetaCuspModularRatioUpperBarrier` passes in `/tmp/sqb72-ratio-upper-leaf-audit` against the actual source and compiled dependency corpus; formal lint passes. No numerical certificate enters either proof.

A sharper actual-orbit barrier is formalized in [ThetaCuspModularRatioSlopeBarrier.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspModularRatioSlopeBarrier.lean): `J<=u/3`. Put `F=J-u/3`. Its exact derivative is

```text
F' = t*(k-4/3)*(k+1/3)+2*u*(k+2/3)*F.
```

If `F(b)>0`, the last zero before `b` has nonnegative right derivative, forcing `k>=4/3` there and on the complete later ray. Derivative fencing keeps `F>=F(b)>0`, so `F'` has a fixed positive lower bound. Linear growth then contradicts `J<1` and `u>=0`. This proves the barrier without an asymptotic assumption. It also proves that `k^2*t` is nonincreasing: substituting `J<=u/3` in its derivative gives an upper bound `-2*u*k*t*(k^2-2*k/3-2/9)<=0`. The actual seam bound `k(0)<19/15` yields the global strict bound `k^2*(9-u^2)<361/25`.

The foreground scratch check `/tmp/sqb73_modular_slope_barrier.lean` passes; `J_le_third_drift` and `kineticGap_lt` depend only on `propext`, `Classical.choice`, and `Quot.sound`. No numerical certificate or additional source premise is used. The installed module is wired once into the RHTower umbrella. Its final narrow `lake build GaloisForLFunctions.RHTower.ThetaCuspModularRatioSlopeBarrier` passes in `/tmp/sqb73-slope-barrier-leaf-audit` against the actual repository source and existing compiled dependencies.

These bounds constrain the same variables in all seven complete-source compact moments. The determinant lower comparison below is proved, but its sign, the rank-seven integral, and all-order propagation remain open. Neither a generic Toda identity nor real-rootedness of an unrelated polynomial family supplies that missing estimate.

A concrete next sign target retains the full source and removes the explicit center from a lower compensation model. The proved bound `w>=4*x+2*u/3`, with the exact identity `w=u*k-J`, gives `4*x<=u*(k-2/3)-J`. Put `v=k-1/6`, `H=Bottcher.completedThetaProfile`, and define polynomials `P_0=v`, `P_(n+1)=V(P_n)+u*(1/6-2*k)*P_n`, where `V` is the polynomial vector field specified by the displayed equations for `u'`, `k'`, and `J'`, with `t=9-u^2`. Analytically, `Phi^(n)=(H*t/12)*P_n` and `P_1=u*(1/6-2*k)*v+2*(k+1/3)*J`. The existing inequality `w>=u` gives `J<=u*(k-1)` and hence `P_1<=-u*(5*k/6+25/36)`. Thus, using the literal source correction `G=3*Phi^2+2*x*Phi*Phi'`,

```text
G >= (H*t/12)^2 * Gsharp,
Gsharp = 3*v^2 + ((u*(k-2/3)-J)/2)*v*P_1.
B_n = (-1)^n * sum_(j=0)^(2*n) (-1)^j * choose(2*n,j)*P_j*P_(2*n-j).
```

Keeping `J` improves the comparison by `-(J/2)*v*P_1>=0` relative to dropping it from the center bound. The upper barrier supplies a further exact positive reserve. For fixed `u,k`, write `g(j)` for the displayed `Gsharp` with `J=j`. Its quadratic term is `-v*(k+1/3)*j^2`, so

```text
g(J) = (1-J)*g(0) + J*g(1) + v*(k+1/3)*J*(1-J).
```

The last summand is nonnegative on the proved actual interval `0<=J<1`. This decomposition and the full-source lower comparison are formalized in [ThetaCuspModularCompensationDeterminant.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspModularCompensationDeterminant.lean), namespace `RHTower.ThetaCuspModularRatio`. They do not yet give a positive decomposition of the full determinant.

For `L=10^12`, the positive candidate is the determinant of the matrix with entries `B_(i+j)` (`i,j=0,...,3`) and last-entry addition `L*Gsharp`, evaluated on the actual orbit. Its head is the already positive actual native head after positive normalization. A positive determinant would imply full compensated source positivity through the preceding lower comparison and then the existing aperture-dependent integration receiver. **This determinant sign is unproved.** The additional actual constraints include `0<=J<=u/3<1`, `J<=u*(k-1)`, `k>151/120`, `k^2*(9-u^2)<361/25`, and `(k-2/3)*(9-u^2)<27/5`; positivity on a larger box of unrelated triples is not being assumed.

The seven required moment identities already have an exact Lean incidence theorem: `thetaCuspNativeEvenJet_eq_compactScalar` in [ThetaCuspEvenCompactSourceCoordinates.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspEvenCompactSourceCoordinates.lean). Thus the sign attack need not first build the displayed recurrence for every order. For `n=0,...,6`, set

```text
C_n(u,k,J) = HTGeometry.evenCompactSignedMoment n
               u ((4/3)*(9-u^2)*(k+1/3)) (u*k-J).
```

On the actual orbit, that theorem gives `(-1)^n*nativeJet(2*n)=H^2*C_n`, and the paper normalization is `C_n=(t/12)^2*B_n`. The equivalent finite target is the determinant with entries `C_(i+j)` and last-entry addition `L*(t/12)^2*Gsharp`. The actual substitution is now formalized as `evenMoment_eq_native` in `ThetaCuspModularCompensationDeterminant`.

In that module, `compensationChord=(1-J)*g(0)+J*g(1)`, `compensationReserve=v*(k+1/3)*J*(1-J)`, and `evenLowerDet` is the determinant with entries `C_(i+j)` and last-entry addition `L*(t/12)^2*compensationChord`. The closed theorem `compensated_det_lower` gives

```text
H^8*evenLowerDet(x)
  + L*(H*t/12)^2*compensationReserve(x)*det(nativeEvenHead(x))
    <= det(nativeEvenFourCompensated(L,x)),       L=10^12.
```

`determinant_reserve_nonneg` proves the second summand nonnegative on the complete actual half-orbit. The exact head cofactor is retained; no source moment is replaced by a Gaussian moment. **The sign of the full left-hand side is still unproved.** The target should retain both summands; positivity of `evenLowerDet` alone would be a stronger sufficient condition.

The five capstone axiom audits in `/tmp/sqb73_modular_compensation.lean` use only `propext`, `Classical.choice`, and `Quot.sound`, and its foreground `lake env lean` check passes. The installed module is wired into the RHTower umbrella. Its final narrow `lake build GaloisForLFunctions.RHTower.ThetaCuspModularCompensationDeterminant` passes in `/tmp/sqb73-compensation-det-leaf-audit`, using actual repository source and existing compiled dependencies. After both new modules were installed and wired, `scripts/formal_tools.py lint` passed; full output is in `/tmp/sqb73_formal_lint.txt`. All owned Lean/Lake processes completed.

### A second correction from the actual slope barrier

Put `B=u/3-J>=0`, `Psi=(H*t/12)^2*B`, and `Q_a(x)=x*sinh(2*a*x)*Psi(x)`. The actual modular equations give the analytical identity

```text
Psi' = (H*t/12)^2 * [t*(k+1/3)*(4/3-k)+u*(5/3-2*k)*B].
```

The retained center inequality gives `k>=4*x/3+2/3` and `u*(2*k-5/3)>=8*x-1`. Consequently `Psi'<=-(8*x-1)*Psi` for `x>=2/3`. On this ray `k>4/3`, so a zero of `B` would be a local minimum with strictly negative derivative; thus `Psi>0`. Combining `y*cosh(y)<=(1+y)*sinh(y)` with `0<a<1/2` gives

```text
-Q_a'(x) >= (2/9)*sinh(2*a*x)*Psi(x) > 0,       x>=2/3.
```

The source inequality `0<=Psi<=Phi^2` bounds `Q_a` by a polynomial multiple of the squared tilted theta source, so `Q_a` tends to zero at infinity and vanishes at zero. Its derivative is continuous on compact intervals and nonpositive on the displayed ray, which gives absolute integrability and `integral_0^infinity Q_a'=0`. These statements pass `lake env lean /tmp/sqb74_barrier_flux.lean` and are installed in [ThetaCuspModularBarrierFlux.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspModularBarrierFlux.lean). The strict flux sign and exact zero-integral capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

For the actual center weight `4*x*sinh(2*a*x)`, subtracting `K*Q_a'` from the last diagonal adds at least `K*Psi/(18*x)` to the source on `x>=2/3`. This is a positive candidate for repairing the upper part of the open middle interval while preserving every integrated moment. On the compact interval `[2/3,6/5]`, the actual positive head cofactor and this positive reserve allow a finite coefficient to dominate a continuous determinant deficit; the existing source tail is already strict beyond `6/5`. The installed theorem `exists_barrierRepairedMatrix_posDef_on_upper_ray` proves existence of one fixed positive coefficient making the revised source matrix positive definite for every `x>=2/3`. Its exact determinant identity and axiom audit pass in the same scratch check. The module is wired once into the RHTower umbrella; the final narrow `lake build GaloisForLFunctions.RHTower.ThetaCuspModularBarrierFlux` passed in `/tmp/sqb74-barrier-flux-leaf-audit` against actual repository source and cached dependencies. The weighted reserve comparison is asserted only on this ray; outside it, this lower source matrix is not identified with the literal zero-flux correction. The coefficient's effect on `0<=x<2/3` still needs a separate sign estimate. The exact cost on that interval is `-K*Q_a(2/3)`, balanced by the same total gain on its complement. A coefficient obtained from compactness alone does not bound this cost. No global rank-seven sign or all-rank propagation follows yet.

A sharper normalization is now proved for controlling that cost. Set `T=t*(k+1/3)` and `V=B-T/12`. Direct differentiation yields

```text
V' = 2*u*(k+2/3)*V
       + (T/6)*[8-2*(3-u)*k+2*u/3-J].
```

The proved kinetic bound gives `(3-u)*k<19/5`; also `J<=u/3`. Thus the bracket is strictly positive on the entire actual half-orbit. If `V` were positive at a center, derivative fencing would keep it positive, and the increasing positive drift would give a fixed positive derivative lower bound on the complete later ray, contradicting `V<=B<=1`. Hence `V<=0`; equality at a positive center would be a local maximum with strictly positive derivative, while `V(0)<0`. This argument is formalized in [ThetaCuspModularGapScaledBarrier.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspModularGapScaledBarrier.lean). The capstones `barrierDefect_lt_gap` and `normalized_barrierDefect_bounds` prove `B<T/12` and `0<=B/T<1/12` on the complete half-orbit. Their foreground scratch check `/tmp/sqb74_gap_scaled_barrier.lean` passes with only `propext`, `Classical.choice`, and `Quot.sound`. The installed module is wired once into the RHTower umbrella. The final narrow `lake build GaloisForLFunctions.RHTower.ThetaCuspModularGapScaledBarrier` passed in `/tmp/sqb74-gap-scaled-barrier-leaf-audit`, using actual repository source and cached dependencies. Formal lint passed after both new modules were installed and wired; output is `/tmp/sqb74_formal_lint.txt`. All owned Lean/Lake and search processes are terminal.

For `U=B/T`, a further analytical differentiation gives

```text
U' = 4/3-k + [4*u*(k+1/3)-2*J]*U,
[(H*t/12)^2*U]' = (H*t/12)^2 * [4/3-k+(5*u/3-2*J)*U].
```

Replacing `Psi` by this normalized profile removes an unnecessary small gap factor from the reserve while keeping the pointwise bound `(H*t/12)^2*U<=(H*t/12)^2/12`. These derivative identities are analytical, not new Lean declarations. The normalized flux sign and the global coefficient compatibility still need proof. The positive upper-ray matrix alone does not settle the actual integrated rank-seven sign.

### An explicit inner budget from the normalized drift

The actual normalized defect now satisfies the closed bounds

```text
0 <= U(x) <= u(x)/36 <= x/3,                 x>=0.
```

For `W=U-u/36`, the actual equations give `W'=c*W+F`, where

```text
c = 4*u*(k+1/3)-2*J >= 0,
F = 4/3-5*k*t/36+u^2/27-u*J/18,
F' = u*t*(36*k^2-1)/162
       +(u/3-J)*[t*(k/3+5/54)+u^2*(k+2/3)/9] >= 0.
```

If `W(b)>0` and `F(b)<0`, monotonicity of `F` makes the derivative strictly negative at every zero of `W` before `b`, contradicting `W(0)=0`. If `F(b)>=0`, a positive `W(b)` persists and gives a fixed positive derivative bound on the later complete ray, contradicting the already proved upper bound on `U`. Thus `W<=0`. The kinetic-gap bound also gives `u'<12`, so `u<=12*x`. This is an actual-source comparison, not an assumption about an arbitrary ODE solution.

For the already admitted flux `Q_a=x*sinh(2*a*x)*Psi`, these bounds give

```text
Psi <= amp^2*T*x/3,
Psi' <= amp^2*T/12,
Q_a' <= (504/169)*(4*x*sinh(2*a*x))*Phi^2,   0<=a<=1/2, x>=0.
```

On `[0,2/3]`, the proof retains `T<=72/5`, `Phi^2>=169*amp^2/144`, and the hyperbolic weight derivative. On the later ray the already proved `Q_a'<=0` gives the same upper bound. Consequently subtracting `K*Q_a'`, for `K>=0`, costs at most `(504/169)*K*Phi^2` after division by the positive center weight. The flux remains the same full-source flux with its proved zero integral; no new endpoint admission is assumed. The four capstones in [ThetaCuspModularBarrierCost.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspModularBarrierCost.lean) pass the foreground scratch check `/tmp/sqb75_normalized_cost.lean` with only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into the RHTower umbrella. The final narrow `lake build GaloisForLFunctions.RHTower.ThetaCuspModularBarrierCost` passes in `/tmp/sqb75-barrier-cost-leaf-audit`, using actual repository source and cached dependencies. This final build includes the signed polynomial comparison below.

The closed theorem `barrierFlux_deriv_polynomial_cost` retains the sign instead of replacing the cost by its constant ceiling:

```text
P = (T/12)*[6-3*k+(u*(k-2/3)-J)/4],
Q_a' <= (4*x*sinh(2*a*x))*amp^2*P.
```

Here `Psi'<=amp^2*T*(4/3-k)` retains the actual negative derivative term, and `4*x<=u*(k-2/3)-J` removes the center from the upper polynomial. This comparison uses exactly the same modular coordinates as the seven native moments. For the fixed original `L=10^12` and one `K>=0`, the resulting sufficient determinant target is

```text
H^8*evenLowerDet
  +amp^2*(L*compensationReserve-K*P)*det(nativeEvenHead) > 0
```

on the complete actual half-orbit. This displayed determinant implication is analytical; no sign for its left side has been proved. It retains both the original concavity reserve and the signed cost of the second flux. The separate inner budget target using the constant ceiling is `nativeEvenFourSchur+L*G>(504/169)*K*Phi^2` on `[0,2/3]`, together with the proved upper-ray repair for that **same** coefficient. Existence of a coefficient meeting both sides remains open. Neither the cost bound nor the upper-ray repair establishes the rank-seven integral sign; all-rank propagation is also open.

The outer gain is now quantitatively stronger as well. With `q=pi*exp(2*x)`, the exact full likelihood decomposition and its nonnegative first spectral moment give

```text
-6*k*Phi <= Phi' <= (5-2*q)*Phi,              q>=15/2,
k >= q/3-5/6.
```

The upper estimate uses the first atom only inside the exact full-source derivative identity: the retained higher likelihood moment has the favorable sign. The polynomial difference in the first-atom slope comparison is `exp(x/2-q)*q*(2*q-15)>=0`. An analytical degree-four Taylor lower bound for `exp(4/3)` gives `q>=23/2` for `x>=2/3`; hence `k>=3` there. No numerical source experiment or computed spectral certificate enters this proof.

Using `u<3` and `J>=0` in the signed polynomial then gives

```text
P <= -(5/48)*T,
R_gap = (5/48)*amp^2*T,
(4*x*sinh(2*a*x))*R_gap <= -Q_a',            x>=2/3,
15*barrierReserve <= R_gap.                  x>=2/3
```

These four capstones pass `/tmp/sqb75_barrier_gain.lean` with only `propext`, `Classical.choice`, and `Quot.sound`, and are installed and wired in [ThetaCuspModularBarrierGain.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspModularBarrierGain.lean). The final narrow `lake build GaloisForLFunctions.RHTower.ThetaCuspModularBarrierGain` passes in `/tmp/sqb75-barrier-gain-leaf-audit`, using actual repository source and cached dependencies. Formal lint passes after both new modules are installed and wired; output is `/tmp/sqb75_formal_lint.txt`. All owned Lean/Lake and search processes completed. The factor fifteen follows from the complete-orbit bound `B<T/12` and `x>=2/3`; it compares actual source profiles pointwise.

Consequently an outer repair previously obtained with coefficient `K0` against `barrierReserve` is supplied by the same literal flux with coefficient `K0/15` against its improved lower reserve. This is an analytical consequence of the proved comparisons, not a numerical estimate of `K0`. The remaining task is to prove the native determinant margin pays the inner cost for that same coefficient, or to prove the retained signed-polynomial determinant target directly. A compactness-selected `K0` still has no proved numerical ceiling. The complete rank-seven sign and all-order extension remain unproved.

Broad all-view deep searches through transport/redistribution, majorization, successor, confinement/Riccati, multiplier budgets, star-shaped concavity, and full-source logarithmic slopes inspected declarations, candidate lemmas, source arguments, and proposed ingredient groups. The retrieved Riccati identities retain derivative identifications; the radial-phase concavity result concerns a different actual equation; generic derivative budgets retain the estimate to be supplied. These results do not establish the displayed native determinant sign. Search coverage is partial, with stale source/compiler records; some earlier requests also had interrupted, malformed-judging, or deadline stages. No corpus-absence conclusion follows.

An independently chosen broad arXiv search for pinning recovered [Networked Admissibility-Preserving Control for Directed Safe Coordination](https://arxiv.org/html/2609.09384v1), submitted September 8, 2026. Its exact cascade retains the initial realization mismatch and prices its positive and negative demands separately before applying a boundary-invariance argument. The mechanism suggests preserving the sign of the source correction when testing a compatible coefficient. Its graph and actuator assumptions have not been identified with theta data; it supplies no Lean premise or determinant sign. The elasticity search also recovered a September 2026 upload of a paper published in 2022, which is not treated as new 2026 research.

### Integrating before taking the Schur complement

There is an analytical alternative to pointwise compensated positivity. Put `H_x=nativeEvenHead(x)`, let `b_x` be the first three entries of the last column of the uncorrected native even-four matrix, and put `c_x=nativeJet(12,x)`. The actual head is positive definite. Define `r_x=H_x^(-1)*b_x` and `s_x=c_x-b_x^T*H_x^(-1)*b_x`. For aperture `0<a<1/2`, use the complete center measure `dmu_a(x)=4*x*sinh(2*a*x) dx` on `x>0`. Write `Hbar=integral H_x dmu_a`, `bbar=integral b_x dmu_a`, and `rbar=Hbar^(-1)*bbar`. Completion of squares gives

```text
Schur(integral nativeEvenFour(0,x) dmu_a)
  = integral [s_x+(r_x-rbar)^T*H_x*(r_x-rbar)] dmu_a.
```

The bracket equals `c_x-2*rbar^T*b_x+rbar^T*H_x*rbar`, so it is integrable by the existing raw-entry estimates. This argument does not require separately splitting an integral of `s_x` and an integral of the nonnegative variance. The linear native successor source in `ThetaCuspCenterMixedSuccessorSource` has the same integral; it is not pointwise equal to this squared-polynomial source. A quantitative bound showing the variance offsets the negative part of `s_x` is still missing. The scalar finite-sum identity `schurComplement_sum_eq` in `HTGeometry/QuotientFusionProjectionGenesis.lean` and mathlib's matrix square-completion identities support the algebra; no theta variance domination is claimed.

Broad deep searches through discriminants/interlacing, Hardy/uncertainty/coercivity, heterogeneity/variance/mixtures, and mechanism queries for continued fractions and averaged Schur complements inspected all retrieval views. Current all-view searches through factorization/dissipation, zero-derivative multipliers, Schwartz/polynomial constructions, and virial identities inspected statements, source arguments, proof ideas, and ingredient groups. Returned virial/Stein receivers retain their own energy or moment hypotheses; none supplies the needed inner correction budget. The actual flux admission instead follows from the proved source-square domination and monotone tail derivative. Some searches were partial with interrupted stages, malformed local judging, or reranking deadlines; source/compiler coverage remains stale. Further all-view deep searches through Halphen/Chazy and subresultants/Bezoutians recovered modular differential identities and equivalent Xi kernel forms, without a sign-producing join to the seven native moments. A disconjugacy query returned unrelated disjointness results and does not establish absence of an oscillation method in the corpus. Returned recurrence theorems retain positive Jacobi data or unmatched evolution equations. Variance identities expose a positive gain without bounding the native deficit. Coverage remains partial, with source/compiler staleness and retrieval deadlines on some requests. No absence conclusion follows.

An independent recent-paper search for metastability recovered [An Eyring–Kramers Law for the Hypoelliptic Third-Order Langevin Diffusion](https://arxiv.org/html/2607.20882v1). Its saddle reduction chooses a dual coordinate aligned with the single unstable eigenvalue, while its capacity argument keeps the full weak current until localization errors are controlled. The theta correction above is derived from the actual modular ODE; no Langevin small-noise asymptotic, stochastic premise, or Gaussian replacement is used. The paper supplies a comparison mechanism to examine, not a theta determinant theorem.

Recent-paper searches used independently chosen rigidity, fragmentation, and capillarity terms. The direct arXiv search page sorted by announcement date recovered [Rigidity for capillary liquid drops of nearly circular section with constant vorticity](https://arxiv.org/html/2607.17844v1), submitted July 20, 2026. Its argument controls missing low Fourier modes quadratically using the area and barycenter constraints, then absorbs a cubic remainder through interpolation and regularity. This suggests retaining source constraints before estimating a degenerate quadratic form. Its smallness and elliptic estimates have not been identified with the theta determinant problem; the paper contributes no Lean premise.

The analytical loop has closed both the constant upper barrier and the one-third drift barrier. Two determinant attacks remain unresolved: a first-singular-boundary derivative retaining the full source ODE, and a Bell/Wick decomposition retaining non-Gaussian cumulants through order twelve. Broad deep searches through Appell/Sheffer/Rodrigues, Darboux/Christoffel, cumulants/Turan/Bell, Wick/chaos, positive polynomial decompositions, and matrix-cone boundary mechanisms inspected all retrieval views, source arguments, and proposed ingredient sets. Retrieved cone theorems identify the singular boundary but do not give its actual theta derivative sign; Gaussian Wick laws require a source identification not established here. Coverage is partial, with stale source/compiler metadata and interrupted or malformed-response stages on some requests. No corpus-absence conclusion follows.

Independently chosen recent-paper terms included hysteresis, soliton, and polarization. [Hysteresis-Driven Radiative Mpemba Effect in Phase-Change Nanostructures](https://arxiv.org/html/2606.22552v1) retains a separate memory-variable mismatch when comparing crossing rates. Its local Taylor calculation does not establish the global theta boundary inequality. No paper result is imported as a Lean premise.

The unsigned-moment matrix conjecture above also remains open. Attempts to supply its source estimate from reciprocal-score positivity, coupled derivative energies, and Toda evolution have not produced the needed inequality. The retrieved Toda law requires coefficient equations not identified with these signed moments; positive reciprocal-moment measures use a different variable from `-x/(log Phi)'`. Broad deep searches through anharmonicity, score, compensation, Lee--Yang, reciprocity, moment flow, and lattice harmonics inspected statement, proof, method, source-argument, and proposed ingredient-group results. Coverage remains partial; some requests had interrupted or timed-out stages. No corpus-absence conclusion follows.

Independently chosen recent-paper searches included hypocoercivity, orthogonality, and roughening. [Weighted L2 bounds for kinetic Fokker--Planck equations and hypocoercivity](https://arxiv.org/html/2608.28120v1) uses a joint power of entropy and a weighted norm whose differential cross terms cancel. [Sharp hypocoercive convergence estimates for underdamped Langevin dynamics with specular reflection](https://arxiv.org/html/2608.17022v1) retains Hessian and boundary terms in a weighted Reilly identity. Neither calculation has yet supplied a source-preserving evolution or the required theta derivative-energy bound; neither is used as a Lean premise.

### Adaptive deletion basis and modular Sturm coordinates

At a fixed aperture, put `R(t)=Q_a(2*t)` and `P_j(t)=R(t)/(t-r_j)` for its six simple real roots. Orthogonality of the monic minimizer gives the analytical identities `integral P_i*P_j*partial_a(|F_a|^2)=0` for `i != j`, since `P_i*P_j` is `R` times a degree-four polynomial. Each diagonal integral is strictly positive by positivity below degree six. This diagonalizes the deletion basis for the signed aperture-derivative weight. The kinetic inequality above instead contains the ordinary weight `|F_a|^2`; controlling its deletion Gram form by `2*integral |(R*F_a)'|^2` is still the target. These integral identities have not been formalized.

The actual modular source field supplies a second analytical construction with an explicit retained residual. In the real coordinates of `modularThetaSourcePositiveVectorField_coordinates`, set `r=U+3*B`, `b=B`, and `k=Q+3/8-3*B^2/8`. Its equations are

```text
r_x = 2*b*r+16*k,   b_x = b^2+4*k-1,   k_x = 4*b*k-2*k*r.
K = r^2+16*k > 0,   K_x = 4*b*K.
d = sqrt(K),       T = r/d,           T_x = d*(1-T^2).
```

The actual theta curve has `k>0`, so `|T|<1`. Locally take `y=artanh(T)` and `h=sqrt(d)`. Then `y_x=d=h^2` and `h_yy=(1-T^2)*h/4-h^(-3)`. Thus, with `V=(1-T^2)/4=sech(y)^2/4`, the change `psi(y)=h(y)*f(x(y))` has the exact forcing identity

```text
[-D_y^2+V-(1+z^2)*h^(-4)] psi = h^(-3)*[-D_x^2-z^2] f.
```

The Casimir derivative, normalized-ratio derivative algebra, amplitude equation algebra, and forced Sturm substitution pass `lake env lean /tmp/sqb66_modular_coordinate_check.lean`. This scratch check verifies algebraic identities under their displayed differential relations; it does not construct the clock, prove its endpoint behavior, or admit an operator domain. In particular, the forcing pairing still needs a sign. The energy potential cancels to `b^2+4*k-b_x=1`, so this substitution alone is a coordinate expression of the original forced equation. No source-positivity theorem or new finished Lean module is claimed.

Broad and mechanism-oriented deep searches used all retrieval views, including methods, with queries through coercivity, Pearson identities, variation, Rodrigues formulas, unfolding, virial estimates, and the modular differential field. Candidate lemmas, source arguments, and generated ingredient groups were inspected. Returned compact-incidence determinant identities are pending research candidates, not checked declarations; even their completion would leave the separate middle-interval estimate open. Requests reported partial semantic/compiler coverage, and several had interrupted retrieval stages. No absence claim follows.

Independently chosen arXiv terms included `nodal`, `screening`, `spectral flow`, `balayage`, and `buckling`. [A dimension-free weak-type (1,1) bound for the vector Riesz transform on R^n](https://arxiv.org/html/2608.18068v1) constructs an obstacle decomposition of a nonnegative density into a bounded nonnegative part and a fractional Laplacian of a nonnegative potential. Its useful mechanism is positivity from the variational inequality and the sign of the disjoint-support Dirichlet cross term. Applying that decomposition separately to the positive and negative parts of the native current retains their difference; a theta-specific variational inequality orienting that difference has not been obtained. No theorem or numerical result from the paper enters Lean.

### Actual source-weighted differential factorization

For an actual Xi copy, write `z=b+i*c`, `u=SelbergThetaSourcePhase.mode q`, `Phi=thetaCuspFullSource`, and `s=(log Phi)'`. The existing source-ratio equation in `SelbergThetaSourceVariance` gives the following analytical, pointwise construction:

```text
R = u/Phi,                 R' = (-i*z-s)*R-i,
v = exp(i*z*x/2)*u/sqrt(Phi),
Omega_z = sqrt(Phi)*exp(i*z*x/2),
A_z = D+s/2+i*z/2,         B_z = -D+s/2+i*z/2,
A_z v = -i*Omega_z,        B_z Omega_z = 0,
B_z A_z v = 0.
```

Thus `-v''+(s^2/4-s'/2)*v+(i*z*s/2)*v=(z^2/4)*v`. The finite-interval Green identity retains the endpoint term `[conj(v)*v']`. If that term vanishes at both ends and the derivative energy is admitted, its imaginary part gives `integral s*|v|^2=c*integral |v|^2`, while its real part gives `integral (|v'|^2+(s^2/4-s'/2)*|v|^2)=|z|^2*integral |v|^2/4`. The first equality is the existing gauge source balance. These calculations supply no new bound on `c`; no additional derivative-energy admission or operator-domain theorem is claimed.

The forcing is essential when testing the adjoint. The formal adjoint `A_z^*` kills `Omega_(-conj(z))`. Pairing the inhomogeneous equation with this vector yields exactly `integral Phi(x)*exp(i*z*x) dx=0` when the endpoint vanishes: its integrand is `conj(Omega_(-conj(z)))*Omega_z`. This is the original Xi zero condition. The factorization and this compatibility equation therefore leave the signed tilt-energy inequality above unproved, including the rank-seven native successor integral. They are analytical identities, not a new source estimate or finished Lean module.

Broad searches through covariance, transport, Bessel, weighted operators and intertwining inspected declarations, candidate lemmas, source arguments, and generated groups. The proposed groups retain unmatched density/reflection or intertwining obligations. The single-word intertwining request completed its retrieval stages and returned a full source inventory, but semantic coverage remained incomplete and most compiler metadata remained pending. None of these results establishes corpus absence.

Independently chosen arXiv terms included `hypocoercivity`, `majorization`, `repulsion`, and `entanglement`. [Conditional hypocoercivity](https://arxiv.org/html/2607.26616v1), submitted July 29, 2026, suggests an inverse-Poisson corrector whose derivative supplies missing macroscopic dissipation; a native SQB evolution with the required dissipation and bounds has not been constructed. [From Majorization to Horn and Unitary-Orbit Inequalities](https://arxiv.org/html/2609.05854v1), submitted September 5, 2026, requires inequalities for every compressed scalarizer in its lifting theorem. A determinant or trace comparison of the theta Gram matrices does not supply those hypotheses. No source estimate is imported from either paper.

### SQB88: corrected affine fourth determinant

The finite sign uses the scale-dependent complete-source correction `10^12*(11/2-q)*(2*q-3)^2`, on `37/10 ≤ q ≤ 5`, at `z=1/U(q)`. All entries use the common normalization removing `4*q^2*exp(x-2*q)`. SQB87 supplies the exact moments `a_k=P_k(q^2,2*q)+8*z*P_k(4*q^2,5*q)`; SQB86 supplies strict leading minors. The sixth moment follows by normalizing each radial recurrence step before the next differentiation. Its symbolic derivation passes `lake env lean /tmp/sqb88_sixth_moment_derive.lean`.

The sharper correction has an analytical source: `pi ≥ 25/8` and the quadratic exponential lower bound give `q ≥ 10*x+5/2` for `x≥0`. Indeed the remaining quadratic is `(25/4)*(x-3/10)^2+1/16`. The existing complete-source slope `F'≥-5F` then gives `G=3F^2+2xFF' ≥ (11/2-q)*F^2`. Both inequalities pass the minimal scratch `/tmp/sqb88_affine_compensation_clock.lean`. This preserves a larger reserve at the lower end of the scale interval without changing the fixed coefficient `10^12`.

The corrected affine fourth determinant exceeds `10^20`: its degree-forty homogeneous difference has strictly positive coefficients on the nonnegative quadrant. `HTGeometry/TwoAtomAffineEvenFour.lean` proves the normalized determinant bound. `RHTower/ThetaCuspTwoAtomAffineEvenFour.lean` proves the complete-source correction and identifies all seven affine moments with the literal radial recurrence. Both modules pass scratch checks with actual corpus imports, are wired into their respective umbrellas, and pass their narrow leaf builds. Formal lint passes. The uniform `F^2/2` replacement did not meet this determinant-margin target at the lower endpoint; the positive survivor is the scale-dependent correction above. SQB93 below completes the sixteen-entry absorption on this interval. Global degree-six positivity and the all-rank extension remain open.

The broad determinant deep search retrieved the corpus's exact two-border Schur identity in `ProjectiveHorizonCausticQSystem.lean`; it requires an invertible central block and preserves the off-diagonal minor product. Its generated ingredient group mixed continued-fraction and Jacobian statements without identifying their matrices, so that group is not used. Coverage reported a complete 56,835-file inventory, with incomplete semantic retrieval and predominantly pending compiler metadata. Earlier broad polynomial and Bernstein requests returned partial lexical hits with interrupted source/semantic stages. No absence claim follows.

Independent recent-paper terms included `inertia`, `coalescence`, and `condensation`. [Luo–Liu, September 1, 2026](https://arxiv.org/html/2609.01436v1) combine one-scale positive collision estimates in a bounded weighted sum; Cauchy–Schwarz makes persistent mass in unresolved shells force growth beyond that bound. A theta analogue would require a source-derived rank-to-rank inequality and summable weights; these have not been established. [Kim–Lee, September 3, 2026](https://arxiv.org/html/2609.03821v1) compare a nonreversible process with its symmetrization using a uniform sector estimate and a positive stationary Dirichlet form. Those positivity and stationarity structures have not been identified for the signed theta-pair functional. Neither paper supplies a premise to the Lean argument.

### SQB89: diagonal reserves for complete-tail absorption

`HTGeometry/TwoAtomAffineEvenFourReserve.lean` strengthens SQB88 from a determinant margin to a usable quadratic reserve. Put `d=(2*q-3)^2` and `s=8*q`. The corrected affine quadratic form dominates `d*(c0^2/10^6+s^2*c1^2/10^4+s^4*c2^2/10+(500*(5-q)^2+1)*s^6*c3^2)` throughout `37/10 ≤ q ≤ 5`, `0≤z`, `U(q)*z≤1`. All four leading principal minors remain positive after subtracting these diagonal reserves at both endpoints `z=0` and `z=1/U(q)`. An exact division-free four-square identity gives nonnegativity of the remainder, and affine interpolation covers every intermediate weight, including the physical exponential weight. Scratch verification with actual imports and the narrow leaf build pass; the module is wired into `HTGeometry.lean`. SQB93 uses these reserves to prove complete-source inner positivity.

The full error formula retains all sixteen entries and both linear and quadratic deep-tail terms. `HTGeometry/LogarithmicLaplaceMiddleAbsoluteTwelve.lean` proves `|laplaceCoolingJet n 0 z|≤(2*z)^n` through twelve from `z≥111/10`; its scratch check and narrow build pass. `RHTower/ThetaCuspTwoAtomMiddleCoolingTwelve.lean` proves the exact twelfth second-moment ceiling at tilt `11/5`, transfers it to every lower moment, and separates the second-atom spectral measure before taking absolute values. It proves `|Z^(n)|≤0^n+(6*q)^n/100` through twelve without the artificial `2*D_n` term of the older estimate. Its actual-import scratch check and narrow build pass. Both modules are wired into their umbrellas, and formal lint passes. SQB93 completes the weighted square comparison against the four reserves.

The broad OR/deep/method search for quadratic Schur squares retrieved the exact division-free rank-three square decomposition. The proposed complex quadratic-form classification cannot imply real nonnegativity and is not used. Search inventory covered 56,861 files and 731,423 declarations; semantic coverage remained incomplete and compiler metadata predominantly pending. The scalar four-coordinate square identity is checked directly rather than assuming any positive representation of the source.

New independent paper terms were `subordination`, `screening`, and `persistence`. [Aurzada–Helmer, August 2026](https://arxiv.org/html/2608.17463v1), Section 4.2, combine geometric distance comparison with Slepian comparison of existing Gaussian fields having equal variances. This transfers persistence bounds once both covariance kernels are admitted; it does not construct a positive theta covariance. [Bagchi–Majhi–Mitra–Virk, September 2026](https://arxiv.org/html/2609.07691v1), Proposition 7.1, retain a squared separation margin after subtracting a uniform squared orthogonal-tail bound. A theta use would require a positive Hilbert representation and a rank-dependent tail estimate, still open here.

### SQB90: retain score cancellation inside the deep-tail transport

`HTGeometry/LogarithmicLaplaceInnerTransport.lean` proves `(-1)^n*laplaceCoolingJet n 0 (q*t) ≤ (3/4)*(16*q)^n*exp((q-49/20)*(t-8))` for `6≤n≤12`, `37/10≤q≤5`, and `8≤t`. The proof retains the full alternating score, bounds the exponential below by its degree-`n` Taylor polynomial, and homogenizes the compact `q` interval. All seven three-variable polynomial certificates, normalization identities, and exponential comparisons pass the actual-import scratch check `/tmp/sqb90_transport_release.lean`. The module is installed and wired; its narrow build passes. `RHTower/ThetaCuspInnerSourceReserves.lean` integrates the estimate against the complete calibrated deep measure, proving `|D^(n)|≤(3/4)*(16*q)^n*epsilon` for all seven orders. Its actual-import scratch, narrow build, and formal lint pass; it is wired into `RHTower.lean`. Complete-tail absorption on this interval is proved in SQB93 below.

A second positive reserve is exposed by the already proved full-source affine slope `F'≥(4-2*q)*F`. Combining it with the SQB88 clock bound gives `G≥(1+9*q/5-2*q^2/5)*F^2`. On `37/10≤q≤9/2`, this improves the existing coefficient by `(2/5)*(q-5/2)*(9/2-q)≥0`, precisely where the deep tail is largest. Both the full-source bound and its transfer to the first-atom normalization are proved in `ThetaCuspInnerSourceReserves.lean`. The fixed correction multiplier remains `10^12`.

For the remaining quadratic comparison, let `e_k` be bounds on the signed even-jet errors divided by `f1^2*(8*q)^k`, and let `delta=(10^-6,10^-4,1/10,500*(5-q)^2+1)`. Weighted Young inequalities allocate the six off-diagonal errors to the four coordinates if
`e0≤delta0/2`,
`e2+8*e1^2/delta0≤delta1/4`,
`e4+8*e2^2/delta0+4*e3^2/delta1≤delta2/2`, and
`e6+4*e3^2/delta0+2*e4^2/delta1+2*e5^2/delta2≤delta3`.
The extra complete-source correction can augment the last right-hand side on the lower subinterval. SQB92 proves these four source-specific inequalities strictly; SQB93 completes the allocation with all sixteen entries retained.

The existing `thetaCuspFirstAtomScaledEvenJet_bounds_middle` already bounds the first five first-atom moments, normalized by `f1^2*q^k`, by `11,310,14000,800000,55000000` on `37/10≤q≤7`. Thus their bounds in the `8*q` coordinates are these constants divided by `8^k`; no new proof of those five bounds is needed. The sixth polynomial bound `|a6(q,0)|≤2*10^10*(2*q-3)^2*q^6` and its exact literal-source normalization are now proved in `ThetaCuspInnerReflectionError.lean`.

### SQB92: complete seven-moment absorption budget

Put `c_n=1` for `n≤5` and `c_n=3/4` for `6≤n≤12`, `alpha_n=0^n+6^n/100`, `beta_n=c_n*16^n`, and
`K_n=sum_i choose(n,i)*(alpha_i*beta_(n-i)+beta_i*alpha_(n-i)+beta_i*beta_(n-i)/(22*10^9))`.
For the seven first-atom ceilings `M=(1,11,310,14000,800000,55000000,2*10^10)`, the candidate errors are
`e_k=P_k(q)/D(q)`, where
`P_k=sum_r choose(2*k,2*r)*M_r*q^(k-r)*K_(2*(k-r))/8^k`
and `D=22*10^9*T10(8*(q-37/10))`.
This retains both mixed products and the quadratic deep product, using only one factor of the calibrated exponential to linearize the latter.

All four denominator-cleared inequalities pass Lean: the first three for every `q≥37/10`, the last on `37/10≤q≤9/2` with the extra correction and on `9/2≤q≤5` without it. The last two proofs homogenize their full closed intervals. Their strict versions and all fraction-normalization steps pass the combined `/tmp/sqb92_full_budget_release.lean`. The finished module `HTGeometry/TwoAtomInnerErrorBudget.lean` is installed and wired; its narrow build and formal lint pass. Its public theorems give the four strict normalized inequalities, a positive denominator, and the explicit complete convolution coefficients.

`RHTower/ThetaCuspInnerReflectionError.lean` proves `|J_full(2k)-J_two(2k)|≤f1^2*(8q)^k*e_k` for all `k≤6`, `37/10≤q≤5`. The exact full partition decomposition supplies both mixed derivative products and the quadratic deep product; the proved odd first-atom vanishing only removes genuinely zero convolution terms. The exponential denominator is justified analytically by `exp(10)≥22000` and the Taylor lower bound. Its actual-import scratch `/tmp/sqb92_source_error_release.lean`, narrow module build, and formal lint pass; the module is installed and wired. Source error admission is closed. The sixteen-entry Young comparison and literal two-atom affine energy join are proved in SQB93, including the resulting inner positive definiteness.

Broad OR/deep/method absorption and single-word `majorant` searches cover 56,891 inventoried files and 731,829 declarations. Semantic coverage is incomplete and compiler metadata mostly pending; all candidate, source-argument, and ingredient views were inspected. Existing decay and summability methods do not replace the four quantitative inequalities. Own paper terms `entrainment`, `localization`, and `hypocoercivity` retrieved [Dong–Georgoulis, June 2026](https://arxiv.org/html/2606.29621v1): Lemma 3.2 assigns separate Young parameters to individual indefinite couplings before proving four positive reserves. This supports the coordinate-wise allocation being tested here. [Bouin–Dolbeault–Ziviani, August 2026](https://arxiv.org/html/2608.28120v1), Proposition 13, derives all-order moment control from a source-specific adjoint Lyapunov inequality; identifying and proving such an inequality for the signed theta-pair functional remains an all-rank construction target. Neither paper is used as an unproved Lean premise.


### SQB93: strict quadratic absorption and literal retained energy

`HTGeometry/TwoAtomInnerQuadraticAbsorption.lean` proves that the full sixteen-entry error quadratic is strictly below `innerEvenCoordinateReserve` for every nonzero coefficient vector and `37/10≤q≤5`. The six Young parameters are `8*10^6,8*10^6,4*10^6,40000,20000,20`. Its actual-import scratch and narrow module build pass; it is installed and wired. The extra lower-interval compensation appears only in the fourth coordinate.

`RHTower/ThetaCuspTwoAtomAffineEnergy.lean` identifies the first pair and both ordered unequal pairs with the affine radial moment at every even order. Exact atom dilation gives `f2(x)=2^(-1/2)*f1(x+log 2)`, hence the full pure second-atom degree-six energy is nonnegative by the proved shifted first-atom bound. The corrected literal two-atom energy dominates the corrected affine quadratic after multiplication by `4*q^2*exp(x-2*q)`; its seed-square normalization is exactly `f1^2`. The complete scratch, narrow module build, and formal lint pass; the module is installed and wired. `RHTower/ThetaCuspEvenFourInner.lean` proves `(thetaCuspNativeEvenFourCompensated 10^12 x).PosDef` for `37/10≤q≤5`, using all sixteen native error entries and the full compensation. Its clean actual-import scratch `/tmp/sqb93_native_inner.lean`, final narrow module build, and formal lint pass; the module is installed and wired. The inner tail-absorption gap is closed. Global degree-six positivity and the all-rank extension remain open.

Broad OR/deep/all-method queries through absorption and moment symmetrizers, plus the single-word `symmetrization` query, inspected declarations, candidate statements, source arguments, and ingredient views. Inventory covers 56,921 files and 732,156 declarations; semantic retrieval is incomplete and compiler metadata mostly pending. The independently chosen recent-paper term `coercivity` retrieved [Bothe, September 6, 2026](https://arxiv.org/html/2609.06732v1). Proposition 2.7 reduces additive pair friction to a diagonal form on a constrained subspace; Theorem 8.1 pulls a positive constrained inverse back through an affine moment map. A native all-rank use would require an exact theta source map and a positive constrained operator; neither is supplied by the current finite proof or admitted as a premise.


### SQB94: full compensation reserve on the middle interval

`RHTower/ThetaCuspMiddleCompensationReserve.lean` proves `10^12*G > -240*f1^2*(8*q)^6` for `5≤q≤8`. Complete first-moment transport loses only `q/250` from the first-atom affine slope, proving `F'≥(4-2*q)*F` through scale eight. The SQB88 clock bound gives `G≥(1+9*q/5-2*q^2/5)*F^2`. On `q≥5` this coefficient is nonpositive, so the one-percent full-mass ceiling gives the lower estimate in first-atom units.

The scalar inequality
`240*(8*q)^6+10^12*(101/100)^2*(1+9*q/5-2*q^2/5)>0`
is proved for every `q≥5`. Homogeneous coordinates handle `[5,6]`; on `[6,infinity)` the polynomial remaining after subtraction of `7*10^11*(q-6-1/10)^2` has strictly positive coefficients. The complete actual-import scratch `/tmp/sqb94_middle_compensation_budget.lean` passes. The module is installed and wired; its narrow build and formal lint pass.

The theorem `firstAtomEnergy_fullCompensation_middle_reserve` proves the usable full quadratic bound
`f1^2*((y0+h*y1)^2+(7/8)*y1^2+3*y2^2+42*y3^2) ≤ E_first+10^12*G*c3^2`,
where `h=6/(2*q-3)^2` and `y=firstAtomCentralCoordinates ((2*q)^(-1)) (8*q) c`. The complete compensation is admitted. The remaining `[5,8]` obstacle is the mixed-pair and deep-tail entry comparison against these four reserves. An exact affine-pencil comparison can retain the large positive part of both ordered mixed pairs before bounding the deep tail; applying absolute derivative bounds to the whole second atom would discard that reserve.


### SQB95: admitted affine reserve on scales five through eight

`HTGeometry/TwoAtomMiddleEvenFourReserve.lean` subtracts `240*(8*q)^6*(2*q-3)^2` from the last diagonal of the full affine first-plus-mixed-pair matrix. On `5≤q≤8`, its quadratic form still dominates
`(2*q-3)^2*(c0^2/10^6+(8*q)^2*c1^2/10^4+(8*q)^4*c2^2/10+(8*q)^6*c3^2)`.
All four leading principal minors after subtracting these reserves are strictly positive at both affine endpoints `z=0` and `z=1/U(q)`, where `U=3*10^6*(1+3*(q-5)+(9/2)*(q-5)^2)`. The division-free four-square identity and affine interpolation prove the full interval bound. The physical admission `U(q)*exp(-3*q)≤1` follows from `exp(15)≥3*10^6` and the quadratic exponential lower bound. Both certificate and full scratch checks pass, as do the installed module's narrow build and formal lint; it is wired into `HTGeometry.lean`.

The remaining middle source comparison uses the existing complete derivative coefficients `b_n=1` through ten and `b_n=5/4` at eleven and twelve. Compared with the inner coefficients `c_n=1` through five and `c_n=3/4` thereafter, total order `i+j≤12` gives `b_i*b_j≤2*c_i*c_j`; also `b_n≤2*c_n`. Thus the complete convolution, including its quadratic deep product, is bounded by twice the inner error polynomial. The first-five absolute ceilings extend past scale seven using `thetaCuspFirstAtomScaledEvenJet_bounds_of_seven_le`; the sixth ceiling already holds on the entire scale ray. `HTGeometry/TwoAtomMiddleErrorBudget.lean` proves the strict four-coordinate bounds for `e_k=2*innerEvenErrorBound k q` on every `q≥5`, this coefficient comparison, and strict sixteen-entry Young absorption into `y0^2/10^6+y1^2/10^4+y2^2/10+y3^2`. Its actual-import scratch and narrow module build pass; it is installed and wired. `RHTower/ThetaCuspMiddleReflectionError.lean` proves `|J_full(2k)-J_two(2k)|≤f1^2*(8q)^k*middleEvenErrorBound k q` for all seven moments and every `q≥37/10`, without an upper scale bound. The complete source scratch and narrow module build pass; the module is installed and wired. `/tmp/sqb96_native_middle.lean` passes: all sixteen error entries, the full compensated reserve, and middle positive definiteness are closed in scratch. Its join with SQB93 and SQB83 proves `(thetaCuspNativeEvenFourCompensated 10^12 x).PosDef` for every `q≥37/10`. The final narrow build and the elementary physical endpoint `x≥1/12` both pass; the latter follows from the quadratic exponential bound and overlaps the separate compact target ending at `8/95`.

SQB96 is installed and wired in `RHTower/ThetaCuspEvenFourMiddle.lean`; its final narrow module build and formal lint pass. `thetaCuspNativeEvenFourFixed_posDef_of_thirtySevenTenths_le` closes the complete fixed compensated matrix on every `q≥37/10`. `thirtySevenTenths_le_firstAtomScale_of_twelfth_le` and `thetaCuspNativeEvenFourFixed_posDef_of_twelfth_le` close the physical endpoint `x≥1/12` using the quadratic exponential lower bound. This overlaps the compact target ending at `8/95`; compact positivity and the separate all-rank extension remain open.

The broad single-word all-view `pencil` search inspected candidate and method statements, source arguments, and empty idea/ingredient groups. Inventory covers 56,936 files and 732,288 declarations; semantic and compiler coverage remain partial. The retrieved complex Gram congruence requires an existing self-adjoint square root. The current reserve instead follows from the literal affine moments and the eight checked endpoint certificates.

### SQB97: compact positivity by a fixed polynomial basis

The next analytical conjecture uses the already identified complete compact moments `m_k=evenCompactUnitMoment k r t v` and adds `evenCompactUnitCorrection r t` to `m_6`. In the monic basis `1`, `T-3/8`, `T^2-2*T+3/8`, `T^3-2*T^2+1/8`, conjecture that the transformed matrix is strictly diagonally dominant on the complete admitted unit cube. Every transformed entry is linear in these seven literal moments. Each row inequality can be checked through its eight signed off-diagonal sums, retaining the full correction. Positive homogeneous coefficient proofs on the cube would supply a direct compact source proof without the unfinished degree-twenty determinant identity. The signed row inequalities are unproved; no compact positivity or all-rank propagation follows yet. The first last-row expression reduces exactly to `m6-3*m5-m4+8*m3-(31/8)*m2-(3/8)*m1+(15/64)*m0+correction-1/100`. Both the initial whole-expression simplification and the revised scratch that first combines repeated moments reach the heartbeat limit during unfolding, before a sign result. The displayed linear identity passes in the revised scratch. The next certificate must split the literal moment polynomials into smaller coefficient blocks before the homogeneous substitution; neither timeout disproves the row inequality.

The broad OR/deep/all-method compact-reserve search recovered the literal nonlinear eighth-jet reserve and a smaller-chart rank-three determinant reserve; their exact matrices must be retained. Single-word `oscillation` and `Bernstein` searches inspected all candidate and method views. Inventory covers 56,943 files and 732,430 declarations, with mostly pending compiler metadata and incomplete semantic coverage; deep requests reported interrupted stages. No corpus absence is inferred. The independently chosen arXiv term `transmutation` retrieved [Kuznetsova, June 8, 2026](https://arxiv.org/pdf/2606.09405). Theorem 5 bounds differences of transformation kernels by a factorially convergent iteration in the integrated potential. Such a native source transport could help an all-rank argument only after its exact kernel and positive form are constructed; no result from this paper is assumed in Lean.

The expanded page-two searches use `--offset 20`, `--per-module 0`, exclusions of dominant modules, and all retrieval views. `GramFormPositivity.gramForm_pos_of_bounds` supplies a verified source-level combination argument once uniform diagonal and off-diagonal bounds are established; it does not establish the compact source bounds. The three-round mechanism request generated further basis-change and diagonal-control queries, but several retrieval stages were interrupted by the request budget. Its proposed ingredient groups still require positive-definiteness premises. Inventory covers 56,948 files and 732,517 declarations; semantic coverage is not measured and most compiler metadata remains pending. No corpus-exhaustiveness claim is warranted.

### SQB98: coefficient blocks for the compact row

The seven existing `PolynomialODEEvenCompactMoment*Integer` modules identify the complete moments with integer numerators over fixed positive denominators. `clg-ttf-even-compact-incidence/pending-lean/SQB98CompactMomentBlocks.lean` splits each literal numerator into nine powers of the drift-square coordinate; all seven equality proofs pass `lake env lean` in `/tmp/sqb98_blocks.lean`. Every source coefficient is copied unchanged, and all algebra is checked in Lean. No row sign follows from these decompositions alone.

The first homogeneous coefficient target is the last-row expression at drift square one, with the full correction. The source-zero factor there is `(341+35*t)/480`. Multiplication by `(T+U)^8*(V+W)^12`, with `t=T/(T+U)` and `v=V/(V+W)`, gives the literal candidate in `clg-ttf-even-compact-incidence/pending-lean/SQB98CompactLastRowEndpointCandidate.lean`. Its unannotated expanded definitions hit type-inference heartbeat limits before the sign proof. The typed four-variable scratch was stopped at the user's request after reported memory usage reached 6 GB; it produced no checked sign theorem and must not be restarted unchanged. Remaining homogeneous drift coefficients, all other signed rows, complete source admission and all-rank propagation remain open.

Broad OR/deep/all-view searches through homogenization and reflection, together with page-three single-word domination retrieval, inspect candidate statements, source arguments and generated groups. The homogenization coefficient theorem applies to an explicit polynomial with matched degree bounds; generic reflection-square identities do not supply a positive source representation. Semantic and compiler coverage remain incomplete. Independent recent-paper searches for `dilation` and `balayage` retrieved [Deng–Yang, September 6, 2026](https://arxiv.org/html/2609.06661v1) and [Chlebicka–Kim–Li–Zhang, June 29, 2026](https://arxiv.org/html/2606.29912v1). The former constructs Hankel structure from a normalized operator product; its finite Mellin nodes and weights are not the native signed source. The latter develops measure representation from a proved superharmonic comparison property. A native all-rank use would require constructing that operator or comparison law, which remains open; neither paper is a Lean premise.

### SQB99: bounded scalar certificates and reconstruction

The replacement for the stopped four-variable expansion keeps each homogeneous coefficient scalar. At drift square one, the candidate coefficients `C(a,b)`, `0≤a≤8`, `0≤b≤12`, correspond to the last-row expression displayed in SQB97 after subtracting `1/100`. Integer coefficient sums are copied from the literal moment numerators and normalized inside Lean once; `IntegerCoefficientCertificate` retains each exact equality. `SQB99CoefficientCore.lean` is checked and compiled in scratch. No externally evaluated coefficient is used.

`SQB99BernsteinReconstruction.lean` proves the univariate monomial reconstruction and its tensor product for arbitrary degrees. Thus the positive basis is explicitly `t^a*(1-t)^(8-a)*v^b*(1-v)^(12-b)`. The exact join from the seven original moment numerators to this coefficient family is still pending; separate source-incidence drafts retain the original numerator on the left. These components remain in `clg-ttf-even-compact-incidence/pending-lean/` and are not installed or umbrella-wired. The other drift coefficients, signed rows, native compact positivity and all-rank propagation remain open.

The initial corrected scalar proof passes in 26 seconds with sampled physical footprint 490 MiB. The uncached endpoint column passes at 962 MiB. A shared coefficient core, one Lean worker, and bounded checks replace that form. All 117 scalar coefficient cases now pass, covering columns zero through eight. Columns six and seven pass in 70 and 54 seconds at sampled physical footprints of 394 and 392 MiB. These are the coefficients of one signed row expression at drift square one, not all row inequalities. Splitting alone did not resolve the fifth-column timeout: a native process sample located the delay in imported compiler-specialization metadata, before theorem elaboration. `SQB99CoefficientPublicCore.lean` uses the module system to separate public proof data from private compiler metadata. Its compilation passes at 373 MiB. With that core, the complete fifth column passes in 72 seconds at 389 MiB; its profiled import takes 5.95 seconds, compared with 44 seconds in the preceding legacy-core profile. The proved falling-factorial identity replaces recursive binomial unfolding in this proof form. The current guard samples physical footprint, stops above 1 GiB, and records exit status and remaining owned processes; Lean also receives a 768 MB heap limit. The reconstruction check passes at 257 MiB. Timed-out owned compilers have exited. These are resource measurements, not mathematical experiments or an RH result.

Broad/deep/all-view searches through dissipativity, intertwining and covariance, and a second-page lexical Bernstein search, inspected statements, source arguments and proposed ingredient groups. Inventory reaches 56,964 files and 732,762 declarations; semantic retrieval remains incomplete and compiler records mostly pending. The recurrence query also retrieved algebraic-integrality results whose meaning of “integral” differs from the requested measure representation; those are not treated as applicable lemmas.

The independently chosen arXiv term `intertwining`, sorted by newest announcement on arXiv itself, retrieves [Caputo–Quattropani–Sau, September 9, 2026](https://arxiv.org/html/2609.10450v1). Its all-degree reduction uses a positive hidden-model semigroup, quadratic vanishing of higher-degree components, and one nonnegative quadratic Lyapunov form. The native construction candidate starts from the already proved radial operator. With `h(w)=w²−4a`, its exact algebraic decomposition is `S_a P = -D_a P + 4*(w-h(w))*P`, where `D_a P=4*h(w)*P''+4*(w-2*h(w))*P'`. Constructing a positive evolution and the original theta pairing while retaining this potential is the open all-rank attack. The paper supplies no assumed Lean premise. [Karlin, September 8, 2026](https://arxiv.org/html/2609.09548v1) provides a second concrete model: a positive collision form is represented by coherent-state kernel coefficients after its full integral identity is established. The corresponding theta integral identity is still to be constructed.

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
