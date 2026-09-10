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

The actual density definition fixes the frequency scaling in the adaptive test. Analytically set `A_a(y)=integral_x g_a(x+y)*g_a(x-y)`. Evenness of `Phi`, followed by `r=2*x`, gives `thetaCuspCenterMixedDensity a y = partial_a A_a(y)`. Thus for a fixed real polynomial `Q`, its signed moment norm is the aperture derivative of `(1/(2*pi))*integral_t Q(2*t)^2*|F_a(t)|^2`. The physical differential polynomial has symbol `P(i*t)=Q(2*t)`; the factor two must be retained. Since the odd source moments vanish, reflection preserves the monic degree-six norm problem. Its strict minimizer is therefore even. Analytically its six simple real roots form three nonzero pairs `+/-r_j`; up to an overall sign, the corresponding physical operator is `product_j (4*D^2+r_j^2)`. This evenness and factorization have not been added as Lean declarations.

For the moving minimizer `Q_a`, differentiating its signed norm cancels the coefficient-motion term: `Q_a` is orthogonal to `partial_a Q_a`, whose degree is below six because the leading coefficient is constantly one. Consequently the derivative of the successor scalar is the second aperture derivative of the preceding energy with `Q_a` held fixed during that derivative. This selects the adaptive frequency polynomial `R_a(t)=Q_a(2*t)`, whose six roots are real and simple, as a sharper target for `2*integral |(R_a*F_a)'|^2 >= integral (R_a'^2-R_a*R_a'')*|F_a|^2`. These differentiated Plancherel identities are analytical deductions, not additional Lean declarations. The adaptive bound and the zero-aperture limit needed to integrate its sign remain to be proved; no native successor positivity is asserted.

The broad corpus queries used real roots, Darboux transformations, compensation, Hardy, orthogonal polynomials, Schur complements, and oscillation, with deep retrieval across all method views. The useful join was `HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal` from `MonicMomentAdmission.lean`, whose lower-moment uniqueness identifies the canonical Hankel solve with the cutoff orthogonal polynomial. Other generated groups retain a missing source-preserving evolution or weighted estimate. Coverage remains partial; the oscillation request completed without errors and reported complete source inventory but incomplete semantic/compiler coverage.

Independently chosen arXiv terms included `polarization`, `coarsening`, and `renewal`. [Discrete time-multidimensional renewal theory and applications](https://arxiv.org/html/2606.31455v1) gives a coefficientwise finite convolution inverse when the nonconstant kernel has zero constant coefficient. A positive inverse additionally needs a nonnegative increment kernel. Constructing such a kernel from the signed theta source remains a conjecture; no numerical results or theorem from the paper is used in the Lean proof.

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

The gain uses `A_2(L,x)-A_low(x)=2*L*max(-G_2(x),0)*e_3*transpose(e_3)`. For each fixed coefficient, the aperture-dependent matrix `thetaCuspCenterCorrectedEvenFour` integrates entrywise to the original native moments. Its correction dominates the weighted source correction, with a nonnegative diagonal remainder, as proved by `thetaCuspCenterCorrectedEvenFour_posDef_of_source`. This makes the coefficient choice admissible; the aperture-independent source matrix itself is not the exact zero-flux matrix. The complete-source tail theorem already covers `L` on `pi*exp(2*x)>=30`, and seam positivity for `L` is already proved on an unspecified neighborhood of zero. The explicit inner extension through `8/95` still depends on the unfinished compact determinant incidence. **Positivity of the sharper middle lower form remains unproved.** These strengthened comparison formulas are paper deductions from the existing error estimates, not new Lean declarations or a rank-seven sign theorem.

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

On `[0,2/3]`, the proof retains `T<=72/5`, `Phi^2>=169*amp^2/144`, and the hyperbolic weight derivative. On the later ray the already proved `Q_a'<=0` gives the same upper bound. Consequently subtracting `K*Q_a'`, for `K>=0`, costs at most `(504/169)*K*Phi^2` after division by the positive center weight. The flux remains the same full-source flux with its proved zero integral; no new endpoint admission is assumed. The three capstones in [ThetaCuspModularBarrierCost.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspModularBarrierCost.lean) pass the foreground scratch check `/tmp/sqb75_normalized_cost.lean` with only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into the RHTower umbrella. Its initial narrow leaf build passes in `/tmp/sqb75-barrier-cost-leaf-audit`; the sharper comparison below is undergoing its own scratch check before the final module audit.

Retaining the sign instead of replacing the cost by its constant ceiling gives the analytical full-orbit candidate

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

Broad all-view deep searches through transport/redistribution, majorization, successor, confinement/Riccati, multiplier budgets, and star-shaped concavity inspected declarations, candidate lemmas, source arguments, and proposed ingredient groups. The retrieved Riccati identities retain derivative identifications; the radial-phase concavity result concerns a different actual equation; generic derivative budgets retain the estimate to be supplied. These results do not establish the displayed native determinant sign. Search coverage is partial, with stale source/compiler records; some earlier requests also had interrupted, malformed-judging, or deadline stages. No corpus-absence conclusion follows.

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
