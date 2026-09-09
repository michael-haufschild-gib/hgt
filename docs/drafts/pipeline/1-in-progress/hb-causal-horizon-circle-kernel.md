# HB: source-only causal horizon kernel

Status: active analytical construction. The circle-mean Riemann kernel and the resulting source-only horizon formula below are being checked against the actual wave equation. No complete Lean Green/admission theorem or extinction result is claimed.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The immediate target is the unknown causal pulse horizon value in equations (6)–(7) of [hb-causal-onset-contact-cancellation.md](hb-causal-onset-contact-cancellation.md). The candidate here constructs that value from the original full angular source, without an angular eigenprojection or an assigned horizon value.

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
