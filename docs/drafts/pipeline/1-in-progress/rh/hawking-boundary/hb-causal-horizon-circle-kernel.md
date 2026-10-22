# HB: source-only causal horizon kernel

Status: analytical source-only kernel construction; formal Green/admission work remains. The [actual scalar Riemann kernel](../../../3-formalized/hb-causal-riemann-kernel.md) now has Lean proofs of its actual derivatives, original BM wave equation, characteristic normalization, causal support, and AdS cancellation. The full angular circle-mean realization, forced integral, horizon admission, and physical extinction are not proved by that leaf.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The immediate target is the unknown causal pulse horizon value in equations (6)–(7) of [hb-causal-onset-contact-cancellation.md](../../hb-causal-onset-contact-cancellation.md). The candidate here constructs that value from the original full angular source, without an angular eigenprojection or an assigned horizon value.

## Kernel derived from the original wave equation

Use static time `tau`, tortoise coordinate `x<0`, and the actual scalar horizon Laplacian `Delta`. The corpus wave is

```
L = partial_tau²-partial_x²-sech(x)² Delta.
```

For time separation `h` and source tortoise point `y`, define

```
Z(h,x,y) = [cosh(h)+sinh(x)sinh(y)]/[cosh(x)cosh(y)].
```

Direct differentiation gives

```
Z_h²-Z_x² = sech(x)²(Z²-1),
Z_hh-Z_xx = 2 sech(x)² Z.
```

On the characteristic `h=|x-y|`, `Z=1`; inside the forward cone, `Z>=1`. Thus the required operator-valued Riemann function is a family `M_Z` satisfying

```
(Z²-1)partial_Z² M_Z+2Z partial_Z M_Z = Delta M_Z,
M_1 = identity.
```

It has a concrete geometric construction on the actual hyperbolic horizon.

## Actual hyperbolic circle average

For an angular base point `(X0,Y0)`, `Y0>0`, and `d>=0`, set `C=cosh(d)`, `S=sinh(d)` and

```
Dtheta = C-S cos(theta),
Xtheta = X0+Y0 S sin(theta)/Dtheta,
Ytheta = Y0/Dtheta.
```

`Dtheta>0`. Define `M_(cosh d) Q` as the average of the actual field `Q(Xtheta,Ytheta)` over `0<=theta<=2pi`. The pulled-back hyperbolic metric is `dd²+sinh(d)² dtheta²`; integrating its angular second derivative gives the displayed Darboux equation. Smoothness of the actual source handles `d=0`, where the average equals `Q`.

Commutation with the Laplacian of the base point can also be checked directly, without a spectral theorem. Write `Xtheta=X0+Y0 A(theta)`, `Ytheta=Y0 B(theta)`. Then

```
1+A²-B² = -2 A',
2 A B = -2 B'.
```

Consequently the difference between the base-point Laplacian of the integrand and the pulled-back Laplacian of `Q` is exactly

```
-2 Y0 partial_theta [Q_X(Xtheta,Ytheta)].
```

Its circle integral vanishes by periodicity. This is the needed source-level operator commutation, not a prescribed eigenvalue relation. The intrinsic circle description also preserves modular invariance; all finite circle averages are well-defined for the actual smooth theta-square field, including its cusp growth.

The proposed Dirichlet retarded Green action is therefore the difference of two characteristic kernels,

```
(1/2) 1_(h>=|x-y|) M_(Z(h,x,y))
 - (1/2) 1_(h>=|x+y|) M_(Z(h,x,-y)).
```

The two terms agree at the AdS boundary `x=0`. The characteristic value `M_1=identity` fixes the source normalization. Admission and identification with the corpus's constructed causal response must be proved, including the differentiated forcing and original finite-part conventions.

## Candidate full-source horizon value

The horizon limit can be taken from a finite-interval formula in the original ingoing chart. Put `eta=exp(2x)=(r-1)/(r+1)`, so `0<eta<1` in the exterior. At delay `q>=0`, set

```
E=exp(q),
a_eta=(E-eta)/(E+eta),
b=(E-1)/(E+1),
Zdirect_eta(u)=[E(1-u)+eta E^(-1)(1+u)+(1-eta)u]/(1+eta),
Zimage_eta(u) =[E(1-u)+eta E^(-1)(1+u)-(1-eta)u]/(1+eta).
```

The direct radial interval is `0<=u<=a_eta`; the image interval is `0<=u<=b`. Both kernel arguments equal one at their respective upper endpoints. The finite exterior response has precisely the two radial integrals below with these arguments and endpoints. At `eta=0` they become the displayed horizon formula; at `eta=1` the two arguments and endpoints agree, so the AdS value is exactly zero. For finite time, these are compact integrals with smooth coefficients reaching `eta=0`, not an exchange of an uncontrolled infinite-time limit with a spectral integral. Smooth extension of the circle-mean family through `Z=1` and the actual forcing identity remain required for a complete formal admission theorem.

Let `q>=0` denote time delay, `E=exp(q)`, `b=(E-1)/(E+1)`. The future-horizon limit of the direct kernel has

```
Zdirect = E-(E-1)u,                 0<=u<=1,
```

where `u=-tanh(y)`. The image kernel survives only for `0<=u<=b`, with

```
Zimage = E-(E+1)u.
```

For source rate `s`, put

```
w=2s,
k=s(s-1)/4,
A=(5s²+15s+4)/4,
B=(s+2)(2s+3),
Q=fullSquarePotential qXi.
```

The exact original source has angular factor

```
[A+k u²(B-Delta/2)] Q.
```

This follows from the already proved `Delta Q=2(s+1)(s+2)Q+fullGradientEnergy`: both original angular source terms remain. Define the source-only delay kernel

```
K_s(q)Q = -a² integral_0^1 u(1+u)^w
                    M_(E-(E-1)u)([A+k u²(B-Delta/2)]Q) du
           +a² integral_0^b u(1+u)^w
                    M_(E-(E+1)u)([A+k u²(B-Delta/2)]Q) du.
```

The candidate full scalar-master horizon value is

```
U_s(v) = integral_0^v chi(t)exp(wt) K_s(v-t)Q dt.
```

The stream covector horizon value is `coexact U_s`. Both radial integration ranges and the image term are fixed by the original causal domain. For finite `v`, the circle radii are bounded, the radial source weight is integrable, and the formula uses the literal full angular field. There is no angular resolvent denominator in this expression. Infinite-time and global cusp pairing limits remain separate obligations.

## Pulse comparison and the next cancellation test

For a separated angular component with `Delta` value `lambda`, let `P_lambda(Z)` solve
`(Z²-1)P''+2ZP'-lambda P=0`, `P(1)=1`. This is a diagnostic representation of the circle mean, not a replacement of the full angular source. If `f_s(u)=a²(1+u)^w u[c_s-k u²]` is the known particular scalar radial profile, `c_s=alpha_s/(lambda-alpha_s)`, the pulse horizon kernel is

```
I_s(q) = f_s(b)-f_s(1)
   + integral_1^E [f_s((E-z)/(E+1))-f_s((E-z)/(E-1))] P_lambda'(z) dz.
```

The value at zero delay is `I_s(0)=-f_s(1)`, interpreted through the original radial-integral expression. Hence integration by parts in the original `chi'` pulse convolution cancels the complete switched particular horizon value:

```
P_s,h(v)+Z_s,h(v)
 = integral_0^v chi(t)exp(wt)[I_s'(v-t)-w I_s(v-t)]dt.
```

The bridge `I_s'-w I_s=K_s` has the following direct radial proof. It retains the moving image endpoint and does not require evaluating an unknown source moment.

For the direct branch put `c=E-1`, `d=E+1`; for the image branch put `c=E+1`, `d=E-1`. In both cases let

```
Z=E-c u,
Q_c(u)=(1-u)(c u-d)/2,
J(u)=w f'(u)P(Z)-E(1-u)f'(u)P'(Z),
k(u)=-(1-u²)f''(u)/2+(u+w)f'(u)-lambda f(u)/2,
F_c(u)=(1-u²)f'(u)P(Z)/2+Q_c(u)f(u)P'(Z).
```

The characteristic geometry gives `Q_c'=Z` and `-c Q_c=(Z²-1)/2`. The Legendre equation therefore yields exactly

```
J(u)-k(u)P(Z) = partial_u F_c(u).
```

For the literal particular profile, the already derived original stream equation gives

```
k(u)=-a² u(1+u)^w [A+k_s u²(B-lambda/2)].
```

The direct boundary term at `u=1` vanishes. Since `f(0)=0`, the two lower boundary terms are identical and cancel. At the moving image endpoint `u=b`, `Q_c(b)=0`, `Z=1`, and

```
F_(E+1)(b)=(1-b²)f'(b)/2=b'(q)f'(b).
```

This cancels exactly the moving-endpoint term from differentiating the image integral. Thus `I_s'-w I_s=K_s`, with every radial boundary term accounted for. In the full angular calculation the same proof uses the circle-mean Darboux equation and commutation with `Delta`; `lambda f` is replaced by the actual `Delta f`. No angular spectral substitution is needed.

This identifies the proposed source-only kernel with the onset-pulse construction at the analytical level. The subsequent hard test is substitution of this explicit `U_s` into the actual Einstein horizon current and evaluation of its pairing, with all time, AdS, and cusp terms retained. Extinction is not a consequence of the kernel construction alone.

The denominator-free radial flux identity for both direct and reflected kernels, and the identity `(1-b²)/2=2E/(E+1)²` for the moving image endpoint, passed `lake env lean` scratch checks. Their axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Those algebra checks do not formalize the differentiated integrals or the full angular circle-mean Green theorem.

## Evaluation of the fixed clock in the remaining horizon pairing

The next conjecture tested is cancellation by exchanging the two source branches in the explicit causal kernel. The exact time reduction below supplies the clock factor for that test. It does not establish the needed identity between the two radial/angular source kernels.

Keep the actual branch relation `t=-s-3`, and write

```
w=2s=-3+delta, z=2t=-3-delta, delta=2s+3,
g(v)=exp(-3v)chi(v),
h_s(v)=exp(delta v)g(v), h_t(v)=exp(-delta v)g(v).
```

All three functions vanish for `v<=0`. For a finite terminal time `V`, define the explicit clock correlation

```
T_V(q,r)=integral_0^V h_s(v-q)h_t(v-r) dv
         =exp(delta(r-q)) C_V(q,r),
C_V(q,r)=integral_0^V g(v-q)g(v-r) dv.
```

For `0<=q,r<=V`, put `d=r-q` and `m=max(q,r)`. Then

```
C_V(q,r)=integral_0^(V-m) g(u+|d|)g(u) du.
```

This is a finite integral of the original fixed transition. Differentiation gives

```
E_V(q,r)=h_s(V-q)h_t(V-r),
(partial_q+partial_r)T_V=-E_V,
B_V=(partial_r-partial_q)T_V/2.
```

The first identity follows by integrating the time derivative of the product; its lower endpoint vanishes. No terminal term has been dropped.

Let `k_s(q)=coexact(K_s(q)Q)` and `k_t(q)=coexact(K_t(q)Q)` be the constructed source-only covector kernels. Let `S_s,S_t` be the literal horizon-source coefficients from equation (2) of [the source contact reduction](../../hb-causal-onset-contact-cancellation.md), so the original sources are `h_s S_s` and `h_t S_t`. On a finite angular region `Omega`, use its actual bilinear covector pairing `inner_Omega`, set `A=D-2`, and define

```
B_st(q,r)=inner_Omega(k_s(q),A k_t(r)),
B_ts(q,r)=inner_Omega(k_t(r),A k_s(q)),
b_Omega(k_s(q),k_t(r))=B_st(q,r)-B_ts(q,r).
```

The last expression is the actual angular Green boundary integral. With these definitions, direct substitution into the Einstein horizon current (1) gives the following **finite-time identity for the constructed candidate response**:

```
integral_0^V integral_Omega omega_h
 = integral_0^V integral_0^V
       [B_V(q,r)(B_st(q,r)+B_ts(q,r))
        + E_V(q,r)b_Omega(k_s(q),k_t(r))/2] dq dr
   + integral_0^V
       [(partial_q T_V)(q,0) inner_Omega(k_s(q),S_t)
        -(partial_r T_V)(0,q) inner_Omega(k_t(q),S_s)] dq.     (8)
```

Proof: `U_s=integral h_s(v-q)k_s(q)dq`, and similarly for the second branch. Since `h_s(0)=h_t(0)=0`, differentiating this convolution introduces no moving-endpoint contact. Fubini on the finite domains turns the two time-derivative pairings into `-partial_q T_V` and `-partial_r T_V`. Splitting their symmetric and antisymmetric parts gives `B_V` and `E_V/2`; the antisymmetric angular pairing is exactly the displayed Green boundary integral. The two original-source contacts give the final single integral with the stated signs. Smoothness on the finite causal/angular domains suffices for these operations. Identifying this candidate response with the admitted physical field is still required.

For the clock alone the infinite-terminal-time limit is explicit. Define

```
C(d)=integral_0^infinity g(u+|d|)g(u) du,
T_delta(d)=exp(delta d)C(d),
beta_delta(d)=T_delta'(d).
```

`C` is even, `C(0)=C_chi`, and `C'(0)=0`; the derivative equality follows by integrating `(g²)'/2`. Thus `beta_delta(0)=delta C_chi`, recovering the balanced local clock coefficient from the actual delayed pairing. Since the literal transition equals one after time one, put `J_chi=integral_0^infinity exp(-6u)chi(u)du`. Then the entire lag tail is

```
C(d)=J_chi exp(-3|d|)                      for |d|>=1,
beta_delta(d)=w J_chi exp(wd)              for d>=1,
beta_delta(d)=-z J_chi exp(-zd)            for d<=-1.
```

For `0<=d<=1`, the remaining clock value is a compact transition integral:

```
C(d)=exp(-3d)[
  integral_0^(1-d) exp(-6u)chi(u)chi(u+d)du
  +integral_(1-d)^1 exp(-6u)chi(u)du+exp(-6)/6].
```

Thus no unknown time-response function remains in (8): it uses the explicit circle/source kernels, the fixed clock, and the original local source contacts. If the required infinite-time and cusp transport is established, its infinite-time version has `B_V=beta_delta(r-q)` and source contacts

```
-integral_0^infinity [
  beta_delta(-q) inner(k_s(q),S_t)
  +beta_delta(q) inner(k_t(q),S_s)] dq,
```

with the double-kernel term from (8). This limiting interchange has not been proved; the finite formula retains the `E_V` boundary term. The unresolved cancellation is now an explicit radial/angular identity in those terms. No cancellation of SS/VV sectors, AdS flux, or the cusp completion is asserted, and the complex `delta` is not substituted for the real RH displacement. The clock reduction is analytical; no additional Lean module is installed for this integral calculation.

## Source-specific radial adjoint evaluation

The next cancellation test moves the actual angular operator in (8) onto the radial weights. For `E>1`, use `(c,d)=(E-1,E+1)` in the direct branch and `(E+1,E-1)` in the image branch. Put

```
D=d/c, Z=E-cu, p_D(u)=(1-u)(D-u),
L_D f=partial_u(p_D partial_u f).
```

The circle-mean Darboux equation is exactly `Delta M_Z=L_D M_Z`, because `c²p_D=Z²-1` and `-c p_D'=2Z`. In the original source the weight of `Delta` is `h(u)=u³(1+u)^(2s)`. Its adjoint flux is

```
h p_D partial_u M_Z-h' p_D M_Z.
```

This vanishes at both endpoints: `h(0)=h'(0)=0`, and `p_D` vanishes at the direct upper endpoint one and the image upper endpoint `D`. Consequently the original radial source integral equals the integral of `g_(s,D)(u) M_Z Q`, where

```
g_(s,D)(u)=u(1+u)^(2s-2) C_(s,D)(u),
C_(s,D)(u)=c0+c1 u+c2 u²+c3 u³,
c0=A-3kD,
c1=2A+9k/2-3kD(4s+1)/2,
c2=A+k[2s²+14s+9-D(2s²-2s-6)],
c3=k(2s+3)[6s+3+D(2s+3)]/2.
```

Here `A,k,B` remain the original coefficients defined above. The fourth radial power cancels because `B=(s+2)(2s+3)`. The equivalent form `u(1+u)^(2s) C/(1+u)²` avoids a power-branch rewrite. Thus the constructed horizon kernel can be evaluated using the full `Q` itself, with its original `Delta Q` contribution carried by explicit radial coefficients. The [actual Legendre-kernel integral version](../../../3-formalized/hb-causal-source-adjoint-kernel.md) is formalized, including its identification with the original source remainder; full angular transport still uses the analytical circle-mean construction.

The second adjoint transfer, needed for `A=D_covector-2` in the Einstein current, has a nonzero endpoint. Since `g(0)=0` and `g'(0)=c0`, its lower-end contribution is `D c0 M_E Q`. Writing `D_d=(E+1)/(E-1)` and `D_i=(E-1)/(E+1)`, the complete direct/image result is

```
(Delta-2)K_s(q)Q
 = -a² integral_0^1 [(L_(D_d)-2)g_(s,D_d)] M_(E-(E-1)u)Q du
   +a² integral_0^b [(L_(D_i)-2)g_(s,D_i)] M_(E-(E+1)u)Q du
   +Gamma_s(E) M_E Q,

Gamma_s(E)=-4a²E/(E²-1) [A-6k(E²+1)/(E²-1)].                (9)
```

The coefficient follows by evaluating `a²[D_i(A-3kD_i)-D_d(A-3kD_d)]`. `D4BMCausalSourceKernel.sourceKernel_action` proves the entire actual Legendre-kernel version of (9), including both integrals and this coefficient. This is the boundary term created by moving the angular operator in the actual horizon expression. It is not an identification with the complete four-dimensional Einstein AdS flux. The terms in (9) must remain assembled near zero delay; their separate formulas contain singular factors there although the original finite-source expression supplies the combined value.

The original horizon-source contact itself has the explicit local form

```
S_s=2a² 2^(2s)[A+kB-(k/2)D_covector]J,
J=coexact Q.
```

This follows by setting `r=1` in `M Psi=2 current`, retaining `fullGradientEnergy` through the proved square-source Laplacian identity. For a finite angular region the resulting contact pairing is

```
inner(k_s(q),S_t)
 = 2b² 2^(2t) [
     (A_t+k_t B_t-k_t)inner(k_s(q),J)
     -(k_t/2)inner((D_covector-2)k_s(q),J)
     -(k_t/2)b_Omega(k_s(q),J)].                            (10)
```

Equations (9) and (10) evaluate the operator and contact factors in (8) using the source-only kernels and explicit circle terms. The first adjoint transfer closes positively; the complete cancellation test now includes the forced `Gamma_s(E) M_E Q` term, the remaining radial integrals, and the original angular boundary terms. Their assembled vanishing, the other tensor sectors, and physical Green/limit admission remain open.
