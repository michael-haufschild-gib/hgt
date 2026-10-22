# HB: original lift current, horizon transport and source contact

Stage: 3-formalized for the specified original lift contribution. RH and complete physical-current cancellation remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target is `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes and all physical currents. The [original delay horizon theorem](hb-original-delay-horizon.md) supplies the finite native source action. This result identifies the lift–lift Einstein current, its original master-source contact, and their finite onset integrals. It makes the square and gradient source terms explicit for the remaining lift/response current comparison.

## Exact source and current

Write `s=physicalRate(q,branch)`, `t=-s-3`, `lambda=(s+1)(s+2)`, `delta=2s+3`. Let `J` be the actual full-square covector, `G` the actual full-gradient covector, and `chi=Real.smoothTransition`. In original ingoing time and positive radius,

```
c_s(r,v)=-s(s-1)/4 * a_s^2 r^-2 (1+r^-1)^(2s) chi(v) exp(2sv),
H_s=c_s J.
```

The radial coefficient times the original onset equals `timeRadialLift/u` at `r=tortoiseRadius(x)`, `u=radialUnit(x)`. Its first two radial derivatives are actual derivatives. With `f=r^2-1`, conversion to static derivatives retains `partial_r_static=partial_r_ingoing+f^-1 partial_v`, including the second derivative of the tortoise change. Both ordered angular second derivatives come from `ScalarTwoJet.ofField` of the original full-square covector.

For coefficients `c,d`, put `O(c)=r^2 f c_rr+2r^2 c_rv+2r c_r-2r c_v`. The full original stream master is `O(c)J+c A J`, where `A=roughLaplacian-1`. Substitution into the proved four-component Einstein action gives

```
omega^v=(d_r O(c)-c_r O(d)) (J dot J)/r^2,
omega^r=[(f d_r+d_v)O(c)-(f c_r+c_v)O(d)] (J dot J)/r^2,
omega^X=omega^Y=0.
```

These are complex bilinear contractions. The angular cancellation is proved for this common-covector lift pair; it asserts nothing about response or mixed angular fluxes. The formal action identity evaluates `actionSymplectic` on the explicitly reconstructed stream jets; it does not assert that the complete causal response is this lift.

The source contact `C` is formed from the actual unseparated stream master before taking the horizon limit. Its time and radial entries use respectively `c_r M(d)-d_r M(c)` and `(f c_r+c_v)M(d)-(f d_r+d_v)M(c)`, paired with `J` and divided by `r^2`. Their sum with the physical current is proved to be

```
(omega+C)^v=(c_r d-d_r c) (J dot A J)/r^2,
(omega+C)^r=[(f c_r+c_v)d-(f d_r+d_v)c] (J dot A J)/r^2.
```

No angular eigenvalue is substituted. On the actual upper-half-plane source, the already proved covector equation gives

```
A J=(2lambda-2)J+2G,
J dot A J=(2lambda-2)(J dot J)+2(J dot G).
```

## Horizon and finite-clock transfer

At `r=1`, `c_r=-(s+2)c`. The complementary powers multiply to `2^-6`, giving

```
K=delta(lambda-2)(lambda-6)a_s^2 a_t^2/512,
omega_h^r=K exp(-6v)[-(chi')^2+5chi chi'+4(lambda-1)chi^2](J dot J),
omega_h^v=K exp(-6v)[-chi chi'+2(2-lambda)chi^2](J dot J),
(omega+C)_h^r=K exp(-6v)chi^2(J dot A J),
(omega+C)_h^v=-K/2 exp(-6v)chi^2(J dot A J).
```

The exterior physical current tends to the displayed horizon value. Joint continuity on positive radius and finite real time follows from actual original profile and onset derivatives. The parametric integral theorem then transports the limit through each fixed finite time interval; this is a limit of the original exterior current integral, not merely an integral of a proposed limiting expression.

For a finite cutoff `V`, define

```
M(V)=integral_0^V exp(-6v)chi(v)^2 dv,
E(V)=integral_0^V exp(-6v)chi'(v)^2 dv,
B(V)=exp(-6V)chi(V)^2.
```

The actual product derivative proves `integral_0^V exp(-6v)chi chi'=3M+B/2`. Consequently,

```
lim_(r->1+) integral_0^V omega^r(r,v) dv
  =K[-E+(4lambda+11)M+(5/2)B](J dot J),
lim_(r->1+) integral_0^V omega^v(r,v) dv
  =K[(1-2lambda)M-B/2](J dot J).
```

The exact original horizon source-contact integrals are

```
integral_0^V C_h^r dv
  =K[2M(J dot G)+(E-(2lambda+13)M-(5/2)B)(J dot J)],
integral_0^V C_h^v dv
  =K[-M(J dot G)+(lambda M+B/2)(J dot J)].
```

The terminal term is retained. These formulas hold for oriented finite intervals; the physical use is `V>=0`. They do not take an infinite-time limit or replace a static-time boundary with a constant ingoing-time boundary.

## Conjecture loop and search applicability

The initial target was an original source/current intertwining law. Deep corpus searches for transmutation and full Green divergence exposed the actual master/Einstein current identity, but no producer closing the full causal response pairing. Expanding that identity for the fixed lift gave a concrete positive target: both ingoing components and the exact source contact. The complementary exponents fix the weight `exp(-6v)`. Retaining the original onset derivatives produces the energy and mixed-clock insertions. The finite product-derivative transfer closes their integrals. Applying the actual square-covector equation then resolves the remaining angular insertion into `J dot J` and `J dot G`.

Own broad and mechanism searches used the documented deep tool, including OR searches for pullback, jets, chain rule, and real coordinates. Declaration candidates, source arguments/methods, proof ideas, ingredient groups, and freshness were inspected. Results were partial, with 401 pending/stale source files in the first three searches and predominantly source-only compiler metadata. The final pullback query also reported interrupted text/source stages and local semantic deadlines; available hits were used without inspecting or restarting search services. The affine entire-function jet pullback and formal differential-field chain-rule candidates do not identify the nonlinear real tortoise/source field. The existing actual tortoise derivative, source onset jets, full-square covector equation, and complete action current are the applicable ingredients, verified in the new Lean leaf.

Broad arXiv queries used transgression, reciprocity, intertwiner, conservation and sewing with recent-date filters. No relevant June–September 2026 result was verified. Primary abstracts inspected were [Deák–Fülöp, Reciprocity in quantum, electromagnetic and other wave scattering](https://arxiv.org/abs/1108.5743) and [Green et al., Conserved currents for Kerr and orthogonality of quasinormal modes](https://arxiv.org/abs/2210.15935). They motivate testing an actual source/detector or current intertwiner with its precise domains; neither supplies an HB current identity or a Lean premise.

## Certificate and remaining target

Owner: [ThetaCuspHawkingBMPhysicalLiftHorizonCurrent](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPhysicalLiftHorizonCurrent.lean), namespace `RHTower.D4BMPhysicalLiftCurrent`.

The eighteen new public theorems cover the literal profile dictionary and derivatives; all four action components; the original master/contact dictionary and decomposition; both horizon values and finite-clock integrals; the finite exterior-current integral limit; and the actual square/gradient source resolution.

The new public statements impose no extra source-equation, regularity, integrability, boundary-vanishing or cancellation premises. Positive-radius, exterior-chart, and upper-half-plane restrictions are intrinsic domains. The full physical cancellation remains open: the causal response, lift/response cross-currents, response/response current, original oriented temporal/radial/cusp faces, complete physical integration, independent SS/VV coefficients, and fixed-clock extinction still require identification and proof. The next attack must match those currents to the explicit source-contact coefficients above and the native signed delay action on the same original finite domain.

The exact isolated leaf build passed in 76 seconds (three jobs), with no warnings or errors and no dependency or umbrella rebuild. Only these eighteen new public theorems were axiom-audited, in a separate scratch file; every report contains only `propext`, `Classical.choice`, and `Quot.sound`. Audited source and five artifacts were installed byte-identically. The new umbrella import is unique.

Indexing completed (two changed sources in the shared workspace), and the generated API contains all eighteen new public theorem entries. All seven local links across the three affected cards passed. Global formal lint passed; existing large-file warnings remain elsewhere. All owned process handles reached terminal status, the owned Lean/Lake process check was clear, and this task’s scratch, audit and search files were removed. The frontier map and universal ledger were not edited. No mathematical computation ran.
