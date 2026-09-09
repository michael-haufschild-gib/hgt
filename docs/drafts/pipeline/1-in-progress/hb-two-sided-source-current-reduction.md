# HB: two-sided reduction of the complete source current

- **ID:** HB-TWO-SIDED-SOURCE-CURRENT
- **Stage:** 1-in-progress
- **Type:** analytical current reduction; physical causal boundary evaluation in progress
- **Source:** `ThetaCuspHawkingBMJointSourceTimeField.timeOriginalForcing_gradient_absorption`, the [complete physical current](hb-mixed-complete-current.md), and the [finite optical source identity](hb-optical-source-boundary-matching.md).
- **Statement:** Use the existing actual source lift in both slots of the complete current; retain its fixed physical boundary terms and reduce the remaining forcing to scalar multiples of the full angular half-square.

The chain is literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. The hard target remains the complete physical pairing, with independent SS/SV/VV amplitudes. Neither its cancellation nor RH is proved here. The frontier map is read only.

## Source-specific conjecture

The four optical radial rows arise from the two original source polynomials. Their angular-gradient factors are already absorbed by an explicit wave image in the corpus. Applying that absorption in both slots, with every physical boundary retained, should replace the four-row bulk by the single `h11` row and explicit onset terms. This is a reduction of the actual source, with no angular spectral replacement.

## Existing source identity in the original master normalization

Put `u=1/r=-tanh(x)`, `v=tau+x`, `s=rho-2`, `t=-s-3`, `delta=2s+3`, and `lambda=(s+1)(s+2)`. Let `Q` be the literal full half-square, `J=coexact(Q)`, and write

```
k_s=s(s-1)/4, eta_s=(2s+1)(2s+2),
F_s^0=a_s² exp(2s v)(1+u)^(2s),
F_s=chi(v) F_s^0,
H_s=-k_s u² F_s J.                                      (1)
```

Here `H_s` is a stream covector. Its scalar wave potential is `u H_s`, whose coefficient is exactly the already formalized `timeRadialLift`. The original stream master, in ingoing coordinates, is

```
M=(1-u²)partial_uu+(2/u-4u)partial_u
       -2 partial_uv-(2/u)partial_v+A,
A=roughLaplacian-1, A(coexact Q)=coexact((Delta-2)Q).
```

The scalar version replaces `A` by `Delta-2`. Direct differentiation, or the existing wave-image identity and `M(r phi)=-(r³/f)L(phi)`, gives

```
S_s=M H_s+T_s,
T_s=F_s^0 [eta_s chi(v)
       -2k_s u(3+delta u)/(1+u) chi'(v)] J.              (2)
```

Thus `T_s` contains the complete `J`, with no angular derivative of `J`. To check all coefficients, without differentiating or dividing the clock, first compute

```
M((1+u)^(2s) exp(2s v) Q)=(Delta-eta_s)F_s^0 Q,
M(u² F_s^0 Q)=6F_s^0 Q+u²F_s^0(Delta-2(s+2)delta)Q.
```

The source's constant coefficient satisfies `2A0+6k_s=eta_s`, where `A0=(5lambda-6)/4`. Finally, the ingoing master obeys
`M(chi H)=chi M H-2chi'(H_u+H/u)`, which fixes the sign and coefficient of the onset term in (2). These calculations use arbitrary angular `Q`; the actual source identification uses the corpus's full half-square Laplacian identity.

## Complete current transport, with no omitted faces

Let `U_s` and `U_t` denote the actual response candidates and put `V_s=U_s-H_s`, `V_t=U_t-H_t`. Their remaining equations are `M V_s=T_s`, `M V_t=T_t` wherever the original forcing equations hold.

Write `B(X,Y)=omega(X,Y)+C(X,Y)` for the complete four-component master current of the linked physical-current card. Both the physical current and its source-contact correction are evaluated using the actual master of their arguments. They are bilinear and alternating. Their exact decomposition is

```
B(U_s,U_t)=B(V_s,V_t)+B(H_s,U_t)+B(V_s,H_t).             (3)
```

Using the already derived full divergence, including the angular component, gives

```
(S_s dot A U_t-S_t dot A U_s)/r⁴
 =(T_s dot A V_t-T_t dot A V_s)/r⁴
       +div[B(H_s,U_t)+B(V_s,H_t)].                    (4)
```

Proof: apply `div B(X,Y)=[M X dot A Y-M Y dot A X]/r⁴` to the three terms in (3), substitute (2), and distribute. This keeps the exact temporal, radial and angular components. Integrating (4) over a finite physical domain gives its entire oriented boundary. The contacts must subsequently be subtracted to return from `B` to `omega`; (3) does not declare the physical pairing invariant under lift subtraction.

## Exact lift traces and its explicit self-pairing

At the ingoing horizon, define `h_s(v)=a_s² 2^(2s)chi(v)exp(2s v)`. The fixed lift and normal derivative are

```
H_s|horizon=-k_s h_s J,
partial_r H_s|horizon=k_s(s+2)h_s J.                    (5)
```

For the current convention in the physical-current card,
`B_h(X,Y)=X_v dot A Y-Y_v dot A X`. Consequently

```
B_h(H_s,H_t)=2delta k_s k_t h_s h_t (J dot A J).         (6)
```

The `chi chi'` terms cancel in (6) by their actual equal coefficients. No term from `B(H_s,V_t)` or `B(V_s,H_t)` is dropped. More generally the exact lift-lift current in ingoing `(v,r)` coordinates is

```
B^r(H_s,H_t)=2delta k_s k_t a_s²a_t²
       u^7/(1+u)^6 chi²exp(-6v) (J dot A J),
B^v(H_s,H_t)=-2delta k_s k_t a_s²a_t²
       u^8/(1+u)^7 chi²exp(-6v) (J dot A J),
B^angular(H_s,H_t)=0.                                 (7)
```

For the last identity, both angular arguments are scalar multiples of the same `J`, and the angular Green current is alternating. The coordinate transformation is `B^v=B^tau+B^r/f`, with unchanged radial component. Formula (7) follows by differentiating (1) at fixed static time before transforming. It is regular at the horizon and vanishes at the AdS endpoint. The time integral of (6) is

```
delta (lambda-2)(lambda-6) a_s²a_t² J0/512
       times the actual angular pairing of J with A J, (8)
J0=integral_0^infinity chi(v)² exp(-6v)dv.
```

This uses `k_s k_t=(lambda-2)(lambda-6)/16`. It does not assign a sign or zero to the angular pairing, and its finite angular boundary remains explicit if that pairing is transferred to `Q R Q`.

## The reduced long-delay kernel to evaluate

After the physical causal Green identification and boundary transport, use the same optical change of variables as in the optical source card. On the long-delay region, the `chi chi` part of (2) has source constants `eta_s,eta_t`. The master Green normalization `-1/(2uw)`, with both `u²du` measures, gives the reduced source-source bulk

```
-eta_s eta_t/2 * a_s²a_t² J0
  integral Q R[(L^delta-L^(-delta)) h11(L,z) M_Z Q] dz dL,
eta_s eta_t=4lambda(4lambda-3).                         (9)
```

The time factors involving `chi'` in (2) remain separate, explicit source terms. On the long-delay domain a target derivative of the original onset is zero; a source derivative need not be zero. Its actual integral must be evaluated before reducing (9) to a final kernel. The compact optical transition and finite-terminal-time remainder also remain attached. Equation (9) names only the `chi chi` summand, not their complete sum.

The remaining direct test is to combine these fixed onset contributions and the physical lift currents in (3) with the single-row kernel. This can be compared with the earlier four-row `G_st` and corrected optical cross-section functional, using identical finite domains. Full causal admission, infinite-time/cusp transport and the independent SS/VV coefficients remain open.

## Search and formal scope

Broad searches used `Lagrange`, `Darboux`, `transmutation`, `Green`, `intertwiner`, and `commutator`, followed by source/absorption searches in the actual BM family. The existing `timeOriginalForcing_gradient_absorption` and actual lift jets provide (2); no new source decomposition is postulated. The deep search returned partial, source-only results with no proof ideas or ingredient sets for the requested Green mechanism, so none was treated as a checked producer.

Equations (3)–(9) are analytical consequences and calculations, not new Lean theorems. No mathematical computations, new axioms, existing-module rebuilds or axiom rechecks were used.
