# HB: native radial form admission

Stage: 1-in-progress. Global native gradient energy and its exact identity are [formalized](../3-formalized/hb-native-global-energy.md). Native membership in the original joint form domain remains unproved. The actual angular energy family is now installed and audited: continuity, compact radial support, zero trace, and C¹ regularity of its original value embedding with the literal radial derivative. The endpoint cutoff error, angular-energy value convergence and complete projected radial derivative convergence are also [formalized and audited](../3-formalized/hb-native-radial-form-approximation.md). Convolution and full native form admission remain open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains cancellation of the complete physical current with independent SS/SV/VV amplitudes. This card attacks native form-domain admission, which is needed to identify the complete native and physical causal inverses. RH and complete current cancellation remain open.

## Actual family and original graph

For each cusp cutoff n, H_n(x) is the angular energy-domain element supplied by `nativeTimePrimitiveCutoff`. Its value is eta_n W and its two angular derivatives are the actual product-rule derivatives. The angular value embedding is J = `D4BMModularCore.embedding`. The audited family theorems supply H_n continuous and compactly supported in the angular energy norm, H_n(0)=0, and J H_n continuously differentiable in the original angular L² norm with derivative eta_n W_x. No angular derivative of W_x or other mixed derivative is assumed.

The target joint graph has four slots: value, radial derivative, sech(x) times horizontal derivative, and sech(x) times vertical derivative. `RadialEnergyFamily.graph_mem` admits smooth compact radial families taking values in the angular energy domain. Its supporting `familyPacketLift_apply` shows that only the original value projection of the radial derivative enters the joint graph. When approximants vary, prove convergence of those four actual slots; convergence of their full angular-energy-valued radial derivatives is unnecessary and is not asserted.

## Constructive approximation

Fix a continuous compactly supported angular-energy-valued family H with H(0)=0 and JH in C¹. The following construction is the current analytical target. Family regularity and endpoint convergence are formalized; convolution and closed-graph admission remain to be formalized.

1. For positive epsilon define beta_epsilon(x) = 1 - baseCuspCutoff(-x/epsilon). The existing profile is one below 2 and zero above 3. Thus beta is zero for x >= -2 epsilon and one for x <= -3 epsilon. Multiply H by beta. This preserves angular core data and gives support strictly inside the negative half-line.
2. Differentiate after J: (J(beta H))' = beta (JH)' + beta' JH. Compact support and continuity bound (JH)' by a constant D. The zero trace and the mean-value estimate give norm(JH(x)) <= D abs(x). The already formalized weighted derivative bound gives abs(x beta'(x)) <= C uniformly in epsilon. Consequently norm(beta' JH) <= CD. The derivative vanishes below -3 epsilon and above -2 epsilon. For epsilon <= 1 this is an L² majorant on [-3,0], while the term is eventually zero at each fixed negative radius. Dominated convergence removes this endpoint error. The remaining beta factors converge directly in their original L² graph slots. Both these limits, including convergence of the complete product-rule radial derivative, are now formalized and audited.
3. For each fixed epsilon, convolve beta H radially with the existing normalized smooth bump of width delta < epsilon. The convolution is smooth in the angular energy space. The sum-of-supports bound retains support below -epsilon. The original value embedding commutes with the Bochner integral. The existing classical convolution derivative theorem applies to J(beta H), which is C¹ and compactly supported, giving the convolution of its actual radial derivative.
4. As delta tends to zero, continuity of beta H and of (J(beta H))' gives pointwise convergence. Uniform bounds and a common compact support give convergence in the required original L² spaces. Thus the smooth families' four joint graph slots converge to the beta-cutoff graph. Closedness of `jointDomain` admits that graph.
5. Let epsilon tend to zero. Step 2 gives convergence to the fixed cusp-cutoff graph, so closedness admits it. Finally remove the cusp cutoff: global energy controls (eta_n-1) grad(W), and the already proved cutoff-error integral controls W grad(eta_n). The resulting value and actual gradients form an element of the original `jointDomain`.

The convolution step can be made with width `epsilon_m/(k+2)`. The kernel support is inside that radius and the cutoff family has support at or below `-2 epsilon_m`, so convolution has support below `-epsilon_m`. For each fixed endpoint cutoff, use the same shrinking kernels on H in the angular energy space and on `(JH)'` in the original angular L² space. The normalized-bump convolution theorem gives pointwise convergence in both spaces. A compact support bound enlarged by one and the compact functions' uniform norm bounds give square-integrable majorants on the radial half-line. The continuous linear map J passes through each Bochner integral. Classical convolution differentiation then identifies the projected radial derivative before taking any limit.

This uses classical convolution differentiation after an interior cutoff. It does not require a new distributional zero-extension theorem. The original source, measure, angular action and radial weight are preserved.

## Corpus evidence

`L2DominatedContinuity.continuous_toLp_two_of_dominated` supplies actual quotient continuity. `L2DominatedDerivative.hasDerivAt_toLp_two_of_dominated` supplies norm differentiation from the admitted literal derivative and a common square-integrable majorant. Finite native propagation and compact angular cutoff support supply these majorants from jointly continuous pure jets. `BumpMollifierFamily` supplies a nonnegative normalized smooth bump at every positive width. Mathlib's compact-support convolution smoothness and classical derivative statements have been checked against this toolchain in scratch. `SuzukiHlogMollifiedFormCore` supplies a source pattern for retaining an interior support margin under convolution; its aperture-form hypotheses are not native assumptions.

The older `radialDirichlet_zeroExtension_derivative` presupposes domain membership and is not used to infer native admission. No search ingredient group is accepted as a proof. Some deep searches returned partial results or service deadlines; no launcher or search implementation was invoked.


## Current smoothing proof target

The current scratch construction is in `/tmp/hb-native-smoothing.15b3vexe`. It defines the actual interior family and normalized-bump smoothing, constructs smooth compact radial energy families with support below `-epsilon_m`, and attempts the exact original-value embedding and derivative identities. The library names have passed a scratch check. The construction itself is being checked; no new smoothing theorem is installed or audited yet.

The next limit argument fixes n,m, bounds the compact family and its projected derivative, and dominates both smoothing errors on one enlarged compact interval. The normalized-bump theorem gives pointwise limits. This must yield original graph convergence before invoking closedness. The existing endpoint limit then removes m; global native energy and the existing cusp error remove n.
