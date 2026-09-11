# HB: actual angular cusp jets

Stage: 3-formalized. Unconditional Lean theorems prove derivative-weighted bounds for the literal squared source, its retained spin-two image, and the six quartic contact expressions. The quartic extension also admits the original regulated periods, proves decay of the integrated principal-subtracted Green flux, and constructs modular core cutoffs with exact Green transposition against the physical QNM angular test. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes and every physical current retained. Source-time/radial interchange is formalized in [its card](hb-source-time-radial-interchange.md). Angular cusp currents require derivative estimates, not only value decay.

## Formalized statement

For every finite word of horizontal/height coordinate derivatives, every complex height weight, and every positive lower height, the differentiated literal squared-source remainder is uniformly bounded over the complete horizontal line and height half-strip. Both Weyl powers, their cross terms with the full infinite signed Fourier tail, and the tail-square term are retained.

## Proof mechanism

The corpus supplies `value_hasFDerivAt`, `valueGradient`, and `weighted_value_bounded`. Horizontal differentiation increments the Fourier index degree. Height differentiation shifts the real height exponent and Bessel order by one. Finite sums, complex scalar multiples, products, and complex height powers times these full families therefore form a class closed under actual coordinate differentiation. Every member has all complex weighted bounds. Express `squareRemainder = 2 principal * tail + tail^2` inside that class and induct on the derivative word.

This is an estimate on actual derivatives of the infinite source, not a finite Fourier truncation or an admitted packet. [Native mean cusp-jet transport](hb-native-cusp-jet-transport.md) is also formalized. The principal angular current, full modular Green integration and final cancellation still need their own proofs.

## Searches and applicability

Broad automorphic/cusp searches and deep Green-current search found exact modular edge cancellation for absolute-convergence Eisenstein pairs, and full native circle-mean modular invariance. Their source types do not directly give the current full-source/native-kernel pairing. The existing cusp exponential jet packet has an unconstructed source-specific admission; the derivative-stable infinite Bessel family supplies a direct route around that missing admission.

The full native mean has three principal powers `2q`, `1`, `2-2q`; rapid remainder estimates alone do not remove those principal angular fluxes.

## Dependency-closed analytical proof

Let `V(u,nu,a,d,sign)` denote the corpus's complete signed Fourier–Bessel family. Its actual derivatives satisfy

```
partial_X V = horizontalRate(sign) V(u,nu,a,d+1,sign),
partial_Y V = a V(u,nu,a-1,d,sign)
              - pi [V(u,nu+1,a,d+1,sign)+V(u,nu-1,a,d+1,sign)].
```

Every family on the right has a uniform bound after multiplication by `Y^w`, for every complex `w` and every fixed positive lower height. Define the generated class using zero, these full families, sums, constant multiples, multiplication by `Y^w`, products, and equality on the open positive-height chart. The product rule and `partial_Y Y^w = w Y^(w-1)` prove closure under actual coordinate differentiation. Equality on the chart transfers derivatives through equality of germs, including at every higher order.

Weighted bounds are preserved by each constructor. For a product, give the first factor weight `w` and the second weight zero. For multiplication by `Y^v`, use the already available bound at weight `w+v`. This proves a bound for every derivative word by induction, without truncating the infinite Fourier series.

The original signed scalar tail is twice the sum of the two `a=1/2,d=0,nu=u` families. Multiplication by either Weyl principal term stays in the class. Hence the literal identity `squareRemainder = 2 principal * tail + tail^2` admits the full squared-source remainder. Closure under `Delta = Y^2(partial_XX+partial_YY)` admits its retained fourth-order image `-Delta(Delta-2) squareRemainder` and every further derivative.

For any such derivative `f`, the bound at weight `w+1` gives `|Y^w f(X,Y)| <= C/Y` for `Y>=1`. Thus `Y^w f(X(Y),Y)` tends to zero for every horizontal path `X`, with no regularity assumption on that path.

## Exact remaining bridge

[Transport through the literal circle average](hb-native-cusp-jet-transport.md) is now formalized for every radius/base-coordinate derivative, uniformly on compact radius ranges. The three principal powers remain explicit. Their angular Green flux and invariant-coordinate characteristic admission still require proof.

## Literature and search limits

The broad recent-paper search examined Kanigowski–Loyd, [Visible Measures along Omega(n) and Distribution of Horocycle Orbits](https://arxiv.org/abs/2608.11382), submitted August 2026. No theorem from that paper is used in this proof. The formal argument uses the installed corpus's exact Bessel derivative formulas and weighted estimates.

The corpus searches were partial: broad retrieval reported incomplete source/semantic indexing; two deep derivative searches reached their time budgets. Candidate source statements and actual Lean checks, rather than search coverage or generated method descriptions, determine applicability here.

## Lean certificate

Module: [ThetaCuspHawkingBMSquareCuspJets.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSquareCuspJets.lean), namespace `RHTower.D4BMSquareCuspJets`.

- `squareRemainder_jet_weighted_bound`
- `spinTwoRemainder_jet_weighted_bound`
- `squareRemainder_jet_tendsto_zero`
- `spinTwoRemainder_jet_tendsto_zero`

The theorems quantify over the original complex source parameter, every complex weight and every finite derivative word. No source decay, smoothness, summability or radiation premise is supplied by the caller. For the physical half-square at an actual Xi copy, specialize the source parameter to `center q` and retain the factor `1/2`.

Scratch `lake env lean` passed. The final exact-module `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareCuspJets` passed without warnings in 24 seconds (three jobs). The 3,466 cached own-module imports were frozen; no dependency or umbrella build ran. A separate scratch axiom audit of only these four new theorems reported exactly `propext`, `Classical.choice`, and `Quot.sound` for each. The verified source and five artifacts were copied byte-identically into the corpus, and the module was wired into `RHTower.lean`.

Source indexing completed (three changed files, no removals). Whole static `scripts/formal_tools.py lint` passed with existing large-file warnings. Fifteen local documentation links, edited-file whitespace and the single umbrella import were checked. Every owned Lean/Lake/search process completed, and scratch sources, cached-import links and search outputs were removed.

Complete physical-current cancellation, fixed Hawking-clock extinction and RH remain unproved.


## Quartic contact extension, 11 September 2026

The [retained contact balance](../1-in-progress/hb-source-contact-spin-two-balance.md) uses the six actual differential expressions

```
Q², J², Delta(J²)/2-J Delta J, J[-Delta(Delta-2)Q], H, Delta H,
Q=f²/2, J=(cQ-2Delta Q)/8, c=7rho(rho-1)-2,
H=2J²+c(c-4)Q²/96.
```

`quarticContactField` evaluates these products and actual angular derivatives on the full literal scalar. `quarticContactPrincipal` evaluates the same expressions on both original Weyl powers. No Fourier mode or principal cross term is deleted. The gradient expression is retained in its displayed differential form; attachment to the separately named physical gradient/contact fields belongs to the ensuing Green-transport proof.

The private proof first closes the finite principal algebra under coordinate differentiation and multiplication by rapid remainders. Structural induction then proves that evaluating any of the six differential expressions on the full source differs rapidly from its principal evaluation. In the product step the complete difference is `f0*(g-g0)+g0*(f-f0)+(f-f0)*(g-g0)`. In the Laplacian step actual Fréchet derivative linearity transfers the existing rapid bound. This proves every coordinate-word bound and cusp limit.

For every full scalar test psi, the function `psi*(P-chi*P0)` belongs to both L² and L¹ of the original modular measure, with the unchanged cutoff `chi(y)=smoothTransition(y-2)`. Above height three it is a rapid remainder times the full scalar; below height three continuity and compactness control it. The quotient has finite volume.

Define the actual Green flux and its full principal counterpart by

```
B(psi,P)=psi partial_y P-P partial_y psi,
B0(psi0,P0)=psi0 partial_y P0-P0 partial_y psi0.
```

Each flux has an ordinary interval integral at every positive height. Their difference is a sum of products with at least one rapid differentiated remainder. Its bound at weight `w+1` gives the uniform estimate `|y^w(B-B0)| <= C/y`. The horizontal interval has length one, so

```
lim_(Y -> infinity) integral_(-1/2)^(1/2) Y^w(B-B0)(x,Y) dx=0.
```

This is an actual integrated boundary theorem. It does not set B0, a cutoff commutator, or the physical cusp contribution to zero.

New public theorems in the existing leaf:

- `quarticContact_remainder_jet_bound`
- `quarticContact_remainder_jet_tendsto_zero`
- `quarticContactResidual_scalar_memLp`
- `quarticContactResidual_scalar_integrable`
- `quarticContactGreenFlux_remainder_integral_tendsto_zero`
- `quarticContactField_smooth`
- `quarticContactGreenFlux_intervalIntegrable`

The complete extension passed `lake env lean /tmp/hb-quartic-contact.lean` without diagnostics. The final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareCuspJets` passed without warnings in 178 seconds against twelve cached import roots. The verified source and leaf artifacts were copied byte-identically to the corpus. The existing umbrella import remains in place; no umbrella build or numerical evaluation was used. Source SHA-256: `922f4996faa598b52121805e3ad2ec122d5f5d6852fb549796ed82b84c614ace`.

The next mathematical obligation is the finite modular Green identity with its explicit principal-power and native Mellin corrections. Transport to the complete causal/left-QNM action, all independent channels and changing metric weights, and fixed-clock extinction remain open.

The extension's twelve public declarations are present in the regenerated API. Whole static `scripts/formal_tools.py lint` passed with existing large-file warnings. The single existing umbrella import, documentation file links and scoped whitespace checks passed. All owned scratch, leaf-build and search processes completed; temporary sources and isolated cached-import audit files were removed.


## Modular compact-core physical Green extension, 11 September 2026

For each of the six full quartic differential expressions P, the original theta modularity and invariant angular Laplacian prove modularity of P by structural induction. The actual field `gamma_N P`, with N=n+1, is then a constructed `CoreField`: its smoothness, modular invariance and compact quotient support are proved from the source and the existing modular cusp cutoff.

For arbitrary source and target Xi occurrences q,r, the target's physical test psi_r satisfies

```
integral_F psi_r Delta(gamma_N P_q) dmu
 =mu_r integral_F psi_r gamma_N P_q dmu,
mu_r=physicalAngularParameter(r)^2-1/4.
```

Both integrands are absolutely admitted. Use the existing conjugated physical core test at index 3n+2. Its cutoff equals one as a germ on the support of the source core and its Laplacian. Outside that support, both source expressions vanish as germs. Applying the original completed core Green identity therefore gives the displayed pairing with the actual full physical test, including the modular seams. This proof does not require the full physical test to be an L² eigenvector.

On the original closed cell the source cutoff Laplacian is exactly

```
Delta(gamma_N P)=gamma_N Delta P
                +2y² gamma_N' partial_y P+y² gamma_N''P.
```

Both cutoff derivatives remain. The new public declarations are `quarticContactField_modular`, `quarticContactCoreCutoff`, `quarticContactCoreCutoff_physical_green`, and `quarticContactCoreCutoff_laplacian` in the same existing leaf. No source regularity, test-domain, Green identity or extinction premise is supplied by their callers.

`lake env lean /tmp/hb-quartic-green.lean` passed without diagnostics. The exact cached `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareCuspJets` passed without warnings in 7.3 seconds, using twelve cached import roots. Source and five leaf artifacts were copied byte-identically to the corpus; the existing single umbrella import remains. Source SHA-256: `04bf62862b8754bf3f1a01ad6e4832c7a59c66567171c4cd31a2a3cf8ab08110`.

The [active contact-balance card](../1-in-progress/hb-source-contact-spin-two-balance.md#constructed-compact-core-physical-green-identity) derives the next finite-transition Mellin cancellation on paper, retaining all five principal powers. That native finite-part transport is not yet a Lean theorem. Attachment to the complete causal/left-QNM action, independent SS/SV/VV channels, solved corrections, changing metric weights and remaining spacetime faces is still required. Fixed Hawking-clock extinction and RH remain unproved.


The compact Green extension's four public declarations are present once each in the regenerated API. The single existing umbrella import, eight local documentation links and scoped whitespace checks pass. Whole `scripts/formal_tools.py lint` returned exit 1 because the concurrently appearing, untracked `ThetaCuspHawkingBMOnsetPulseTransform` and `XiAffineCollisionControl` modules are not reachable from the RHTower umbrella; the gate reported no error for the quartic leaf. These two modules are outside this extension's write scope and were not modified.


## Five-exponent finite Mellin boundary extension, 11 September 2026

New module: [ThetaCuspHawkingBMQuarticCutoffMellin.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticCutoffMellin.lean), namespace `RHTower.D4BMQuarticCutoffMellin`.

With rho the original Xi occurrence, define `k_j=4-j+(2j-4)rho` and `w_j=k_j-rho/2`, for j=0,...,4. All five w_j are nonzero: their imaginary parts are `(2j-9/2) Im(rho)`, and both factors are nonzero. For every natural n put N=n+2, keep the original cutoff chi(y)=smoothTransition(y-2), gamma_N(y)=1-chi(y/N), and the existing native M(w)=3^w/w-integral_2^3 chi(y)y^(w-1). Lean proves

```
integral_2^(3N) gamma_N(y)chi(y)y^(w_j-1)dy=(N^w_j-1)M(w_j),
-integral_N^(4N) gamma_N'(y)y^w_j dy=w_j N^w_j M(w_j).
```

These are finite-interval identities with directly established smoothness, integrability and endpoint values. They require no condition on Re(w_j), no zero cutoff contact, and no changed physical frequency. The first proof separates the two transition intervals and rescales the outer one; the second integrates by parts on [1,4] before rescaling. Thus the two scale terms match exactly. The excluded w=0 case would have a logarithmic bulk term and is not silently included.

Public declarations: `quarticPrincipalExponent`, `quarticPhysicalMellinExponent`, `quarticPhysicalMellinExponent_ne_zero`, `quarticCutoff_bulk_moment`, and `quarticCutoff_flux_moment`.

The complete scratch `lake env lean /tmp/hb-quartic-cutoff-mellin.lean` passed without diagnostics. The exact cached `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticCutoffMellin` passed without warnings in 23 seconds (two jobs, twelve cached import roots). Source and five leaf artifacts were copied byte-identically to the corpus, and the module was wired once into the RHTower umbrella. Source SHA-256: `c05f47bf4838608b5cb497bee03bcfbd71d15477ce87bed5aa4f3cf1531fbd75`.

This closes the finite cutoff moments at the exponents used by the paper principal expansion. Equality of each actual quartic principal field with that explicit five-power expansion and the full renormalized Green limit still require Lean proofs. The result does not assert complete physical-action cancellation or fixed Hawking-clock extinction.


Final verification after the Mellin leaf: the regenerated API contains all five new declarations once; both owned modules have one umbrella import, nine local documentation links pass, and scoped whitespace checks pass. The subsequent whole `scripts/formal_tools.py lint` returned exit 0 with existing large-file warnings. The two earlier concurrent umbrella-reachability errors were resolved elsewhere in the shared worktree; this extension did not edit those modules. All owned Lean/Lake/search processes completed.


## Pointwise contact balance and actual principal attachment, 12 September 2026

New leaves:

- [ThetaCuspHawkingBMQuarticContactBalance.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticContactBalance.lean), namespace `RHTower.D4BMQuarticContactBalance`.
- [ThetaCuspHawkingBMQuarticPrincipalExpansion.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticPrincipalExpansion.lean), namespace `RHTower.D4BMQuarticPrincipalExpansion`.

With lambda=rho(rho-1), c=7lambda-2, Q=f²/2, J=(cQ-2Delta Q)/8, RQ=-Delta(Delta-2)Q and H=2J²+c(c-4)Q²/96, the first leaf proves

```
J RQ = Delta H+2(c-4)J²-4Gamma(J,J)-c(c-4)(13lambda-6)Q²/96.
```

The statement uses the original six contact fields. Actual scalar smoothness, its eigen-equation and the two-jet product rule discharge every differential input. The proof first eliminates RQ pointwise, then cancels matching derivatives without unfolding J inside nested Laplacians. Its single public theorem is `quarticContactField_balance`.

The second leaf attaches all six original principal fields to the five powers k_j=4-j+(2j-4)rho. J and RQ coefficients are obtained by applying actual Laplacians to the existing original three-power Q expansion. A small finite convolution proof retains every ordered product and keeps complex powers opaque during ring cancellation. Actual height differentiation and a second Laplacian are proved by local field equality and differentiated finite sums.

For each slot, the physical principal Green flux is

```
D sum_j p_j (k_j-1+rho/2) y^(k_j-rho/2),
D=reflectedCompletedLambda(rho-1).
```

For H and Delta H, the actual coefficients satisfy

```
p_(Delta H),j - rho(rho-2)p_H,j/4
 = (k_j-rho/2)(k_j-1+rho/2)p_H,j.
```

Its six public declarations are `quarticPrincipalCoefficient`, `quarticContactPrincipal_eq_power_sum`, `quarticContactPrincipal_heightDeriv_eq_power_sum`, `quarticContactPrincipal_laplacian_eq_power_sum`, `quarticContactPrincipalGreenFlux_physical_eq`, and `quarticContactPrincipal_physical_bulk_flux_coefficient`.

Both complete scratch checks passed without diagnostics. Exact cached leaf audits passed without warnings: the contact balance in 65 seconds, principal expansion in 38 seconds. Both are wired once into the umbrella; no umbrella build was run and no heartbeat setting was added or increased. The existing cusp-jet source is unchanged.

This closes the principal-attachment gap recorded on 11 September. The [active contact-balance card](../1-in-progress/hb-source-contact-spin-two-balance.md#exact-next-limit-to-prove) specifies the remaining native Green limit. Independent SS/SV/VV amplitudes, solved quadratic corrections, metric variations and all remaining spacetime boundary contributions still need assembly and a source-derived sign or cancellation law. Neither fixed-clock extinction nor RH is proved.


Final verification for the two 12 September leaves: all seven new public declarations occur once in the regenerated API; both leaves have exactly one RHTower umbrella import; scoped whitespace and thirteen local documentation links pass. Whole `scripts/formal_tools.py lint` returned exit 1 because the concurrently present `HTGeometry.SecondEndpointMellinLaurentInterchange` and `HTGeometry.UniformSecondOrderJet` modules are not reachable from the HTGeometry umbrella. No error was reported for either new quartic leaf. These unrelated modules were not modified. All owned Lean, Lake and corpus-search processes completed; both leaf audit directories were removed after byte-identical artifact publication.


## Original quartic cutoff contact and native residual Green transport, 12 September 2026

New leaves:

- [ThetaCuspHawkingBMQuarticCutoffContact.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticCutoffContact.lean), namespace `RHTower.D4BMQuarticCutoffContact`.
- [ThetaCuspHawkingBMQuarticResidualCore.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticResidualCore.lean), namespace `RHTower.D4BMQuarticResidualCore`.
- [ThetaCuspHawkingBMQuarticResidualGreen.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticResidualGreen.lean), namespace `RHTower.D4BMQuarticResidualGreen`.

For every actual principal slot, the contact leaf proves

```
K = Delta(chi P0)-chi Delta P0 = sum_j p_j cutoffCommutator(k_j),
integral psi_q K dmu = D sum_j p_j [k_j(k_j-1)-mu_q] M(k_j-rho/2).
```

Both original cutoff derivatives are retained. The actual residual H satisfies `Delta R_H=R_(Delta H)-K_H`, and its complete scalar Laplacian pairing is absolutely admitted.

The core leaf constructs a smooth modular extension of the entire residual. Its principal height subtraction vanishes below two, so every nonparabolic closed-cell overlap gives the same zero germ, while parabolic translations preserve height. The full cell-germ extension therefore preserves the original source through the seams and elliptic corners. Original scaled cutoffs produce actual native cores with full physical Green transposition and both differentiated-cutoff terms.

The Green leaf proves native L2 admission of every weighted actual residual jet, then bounds the full physical cutoff Laplacian by

```
|psi Delta R|+2 C |psi y partial_y R|+C |psi R|.
```

The first derivative pairs integrably because `psi/y` and `y^2 partial_y R` belong to the original L2 space. Dominated convergence and stabilization of full germs prove `integral psi_r Delta R_H=mu_r integral psi_r R_H` for independent source/target Xi occurrences. The same-occurrence original Mellin correction then gives

```
quarticNativePhysicalPeriod q 5
  = (physicalAngularParameter q^2-1/4)*quarticNativePhysicalPeriod q 4.
```

This closes the native angular H/Delta-H Green limit left open in the earlier checkpoints. It does not identify or annul the complete nonlinear left-QNM action; independent SS/SV/VV amplitudes, both solved quadratic correction grades, varying metric weights, and the remaining spacetime faces still require attachment and a source-derived cancellation or sign law.

All three full scratch checks passed without diagnostics. The cutoff-contact and residual-core exact cached leaf builds passed without warnings in 66 and 92 seconds. The final Green leaf build passed without warnings in 25 seconds; its source SHA-256 is `275d33f0f1f664da5b65e6972148fd1a9d9a9f8360dabfdd9da5cbd65522719b`, and all five artifacts were published byte-identically. Each source has one umbrella import, and none adds a heartbeat setting or transparency override. No full or umbrella build was run.


Final audit for the cutoff-contact, residual-core and native-Green leaves: all 21 public declarations occur once in the regenerated API; all three umbrella imports occur once; nineteen local documentation links and scoped whitespace checks pass. Whole `scripts/formal_tools.py lint --check-generated` returned exit 1 with seven unrelated unreachable modules (`DeningerOriginalGreenXiResolventBound`, `RealPrincipalSeriesDerivedDirections`, `ThetaCuspHawkingBMHorizonCoordinateJets`, `ThetaCuspHawkingBMSelfChannelHorizonJet`, `ElementaryHorizonJets`, `SecondEndpointMellinLaurentInterchange`, `UniformSecondOrderJet`) and stale global `LEAN_API.md`/`LEAN_OVERVIEW.md` after concurrent source changes. No error was reported for the three new quartic leaves. The unrelated modules were not modified. All owned Lean/Lake/search processes completed, and all three owned audit directories were removed after artifact publication. Fixed-Hawking-clock extinction and RH remain open.


## Native spin-two contact period, 12 September 2026

[ThetaCuspHawkingBMQuarticNativeBalance.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuarticNativeBalance.lean)
now transports the literal six-field contact identity through the actual native
physical finite part. With lambda=(center q)^2-1/4, c=7lambda-2,
a=c(c-4)/96 and the unchanged physical mu, its final theorem is

```
N(J RQ) = (2mu+2c-8) N(J²) - 4 N(Gamma(J,J))
          - a(13lambda-6-mu) N(Q²).
```

All five original Mellin terms and the original cutoff residual are retained.
Six exported theorems have closed source-specific proofs. Factoring the spin-two
coefficient before convolution avoids large simultaneous expansions; no
heartbeat, recursion-depth or transparency override was added. The scratch check
passed without diagnostics, and the exact cached leaf audit passed in 121 seconds
without warnings. SHA-256:
`d12f4dc95999a9e834e4eaef091bb77069d46f8d33080fe21e9c86a41a652de8`.
The umbrella imports the leaf once; no full or umbrella build was run.
Complete corrected left-QNM action identification and original-clock extinction
remain open, including response-dependent mixed-channel work.
