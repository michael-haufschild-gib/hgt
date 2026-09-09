# HB: exact radial evaluation of the zero-delay current

Status: twelve closed Lean source and radial-contact theorems; [exact scope and validation](../3-formalized/hb-zero-delay-source-current.md). The finite-clock transfer, angular/current identification and complete physical cancellation remain analytical or open as specified below. Complete extinction and RH remain unproved. The frontier map is read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest obstacle is the complete physical source/current cancellation. This calculation evaluates the full zero-delay radial contact from [finite-clock transfer](hb-reduced-source-clock-transfer.md), rather than assigning that contact to zero.

## The source primitive

Use `t=-s-3`, `delta=2s+3`, `k_s=s(s-1)/4`, `alpha_s=(2s+1)(2s+2)`, and define, for `0<=u<=1`,

```
f_s(u)=(1+u)^(2s),
p_s(u)=u f_s(u),
b_s(u)=2 k_s u(3+delta u)/(1+u),
B_s(u)=p_s(u)b_s(u),
H_s(u)=2 k_s u³ f_s(u).
```

All positive-base powers use the real logarithm. Direct differentiation gives `H_s'=B_s` and `H_s(0)=0`. This is the actual reduced source's onset coefficient, with the original radial measure included. It is also the primitive selected by the original null-time master coefficient `-2(partial_u+1/u)`.

Write its endpoint moments

```
I_s=integral_0^1 p_s(u)du,
J_s=integral_0^1 B_s(u)du=2 k_s 2^(2s),
K_s=integral_0^1 u B_s(u)du.
```

Integration by parts additionally gives
`K_s=J_s-2 k_s integral_0^1 u³ f_s(u)du`.

## Antisymmetrization evaluates the whole triangle

The zero-delay direct cone is the complete radial triangle `0<=w<=u<=1`. Set `R=-Delta(Delta-2)` and retain the outer original `Q` pairing. The corrected characteristic bracket from equation (6) of the clock-transfer card is

```
Gamma_st(0)-b_s(u)b_t(w)E0 K(0)
 =J2_V[(alpha_s b_t(w)-b_s(u)alpha_t
          +delta b_s(u)b_t(w))RQ
        +b_s(u)b_t(w)(u-w)R Delta Q/2]
   -b_s(u)b_t(w)E0 RQ/2,

J2_V=integral_0^V exp(-6v)chi(v)^2 dv,
E0=exp(-6V)chi(V)^2.
```

Multiply by `p_s(u)p_t(w)`, subtract the opposite ordered branch, and integrate over the triangle. The exact two angular coefficients are

```
A_Q=alpha_s I_s J_t-alpha_t J_s I_t+delta J_s J_t,
A_D=(K_s J_t-J_s K_t)/2.                              (1)
```

Proof for `A_Q`: its antisymmetrized integrand is symmetric under `u↔w`. Its two `alpha_s` terms combine into the product `I_s J_t`, the two `alpha_t` terms into `J_s I_t`, and the two `delta` terms into `J_s J_t`. Equivalently, after taking the inner integral, it is the derivative of
`alpha_s I_s(u)H_t(u)-alpha_t H_s(u)I_t(u)+delta H_s(u)H_t(u)`, where `I_s(u)=integral_0^u p_s`.

The remaining zeroth source moments also evaluate without dividing by a frequency polynomial:

```
alpha_s I_s=1+4s 2^(2s),
A_Q=2 k_t 2^(2t)-2 k_s 2^(2s)
      +delta(lambda-2)(lambda+2)/256,
lambda=(s+1)(s+2).                                    (1a)
```

For the first identity, differentiate
`(1+u)f_s(u)((2s+1)u-1)+1`. Its derivative is `alpha_s p_s(u)`, and its value at zero is zero. Substitution into (1), followed by `f_s(1)f_t(1)=1/64`, gives the second identity. Both identities include all exceptional frequencies; neither uses division by `alpha_s` or an eigenvalue polynomial.

For `A_D`, the single outer integrand is exactly half the derivative of
`K_s(u)H_t(u)-H_s(u)K_t(u)`, where `K_s(u)=integral_0^u x B_s(x)dx`. These proofs use finite integrals of the actual source functions, with no spectral or decay premise.

The remaining terminal coefficient is also explicit:

```
integral_0^1 integral_0^u
 [B_s(u)B_t(w)-B_t(u)B_s(w)] dw du
 =8 delta k_s k_t N,

N=integral_0^1 u^6/(1+u)^7 du
 =log(2)-1327/1920.                                   (2)
```

Indeed, taking the inner integral leaves
`4 k_s k_t[(u³ f_s)'u³ f_t-(u³ f_t)'u³ f_s]`, equal to
`8 delta k_s k_t u^6/(1+u)^7`. The last integral follows by substituting `x=1+u` and integrating `(x-1)^6/x^7` term by term.

Restoring the source normalization, the entire corrected zero-delay contribution is therefore

```
a_s²a_t² J2_V/2 * [A_Q RQ+A_D R Delta Q]
 -2 a_s²a_t² delta k_s k_t E0 N RQ.                    (3)
```

The outer angular source, its geometric measure and Green boundary have not been integrated away.

## Match with the fixed physical lift coefficients

The complementary exponents give `J_s J_t=k_s k_t/16`. The `delta J_s J_t` part of (3) consequently has coefficient

```
a_s²a_t² J2_V delta k_s k_t/32
 =a_s²a_t² J2_V delta(lambda-2)(lambda-6)/512,
lambda=(s+1)(s+2).                                    (4)
```

This is exactly the scalar coefficient of the already derived lift–lift horizon current. The terminal term in (3) has exactly the scalar coefficient of that lift's finite `v=V` null-slice flux:

```
integral_(r=1)^infinity B^v(H_s,H_t)(V,r)dr
 =-2 a_s²a_t² delta k_s k_t E0 N * pairing(J,A J),
J=coexact(Q), A=roughLaplacian-1.                      (5)
```

The comparison of angular bulk expressions retains

```
pairing(J,A J)=integral Q RQ
               +integral_boundary Q partial_n((Delta-2)Q).
```

Equations (4)–(5) identify coefficients of specified current components. They do not silently change the orientation of a physical boundary face or prove cancellation of the complete current. The remaining `alpha_s I_s J_t-alpha_t J_s I_t` and `A_D` terms are explicit endpoint moments for comparison with the lift/response cross-currents. The positive-delay bulk, positive characteristic delays, terminal integral and all other physical faces remain attached.

## Formal scope

`RHTower.D4BMZeroDelayCurrent` identifies the profile and onset coefficient with the existing original radial amplitude and full reduced time forcing. It proves the onset primitive at every nonnegative radius, both complete triangle identities in (1), the division-free endpoint and zeroth-jet formulas in (1a), the terminal density and closed integral in (2), and the horizon scalar coefficient in (4). All interval integrability and differentiation facts used by those identities are discharged for the actual functions.

The finite-clock/native-kernel transfer used to obtain the input contact, restoration of the full physical angular pairing, orientation of the faces, comparison with lift/response cross-currents, and the positive-delay terms are not asserted as new Lean theorems. The new closed radial identities specify the exact quantities in that remaining comparison.
