# HB: source-polynomial optical boundary matching

- **ID:** HB-OPTICAL-SOURCE-BOUNDARY
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, finite optical reduction); [four exact scalar cap theorems formalized](../../../3-formalized/hb-optical-source-boundary-caps.md)
- **Source:** [actual optical primitives](../../hb-optical-source-tail.md), [corpus Green ingredients](../../hb-corpus-ingredient-search.md), [complete mixed current](../../hb-mixed-complete-current.md).
- **Statement:** Transferring only the two original source polynomials cancels the internal optical interface and the source edge; the moving characteristic contributes an explicit corner primitive.

The chain remains literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. The complete physical pairing, the independent SS/VV coefficients and RH remain unproved. This calculation concerns the SV–SV long-delay bulk on finite optical domains. The original compact onset, finite-time correction, angular Green and physical current terms remain attached to it. The frontier map is read only.

## Source-specific conjecture and construction

The quartic transfer current is exact, but transferring the spin-two weight as well as the source polynomials needlessly differentiates the piecewise radial coefficients past their matching order. Keep the physical weight `R=-Delta(Delta-2)` angular. Transfer only `P_s P_t`, whose degree is at most two.

Use `d=L-z`, `D_star=∂L²(L²·)-∂z²(L²·)` and the original source coefficients

```
s=rho-2, t=-s-3, delta=2s+3, lambda=rho(rho-1),
A0=(5lambda-6)/4,
k_s=s(s-1)/4, B_s=(s+2)(2s+3),
A_s(X)=alpha_s+beta_s X,
alpha_s=k_s B_s, beta_s=-k_s/2,
A_t(X)=alpha_t+beta_t X.
```

Define real radial moments on their actual interval

```
h_mn(L,z)=integral_(max(0,-1-z))^(1-z)
               y^m(y+z)^n/(L+y)^6 dy,
(m,n)=(1,1),(1,3),(3,1),(3,3).
```

The four scalar coefficients of one ordered branch are

```
f11=L^delta h11,   f13=L^delta h13,
f31=L^(delta-2) h31, f33=L^(delta-2) h33.
```

Positive-real-base powers use the real logarithm. The opposite ordering replaces `delta` by `-delta` and exchanges `s,t` throughout. These moments are exactly the four primitive differences already evaluated in the optical source card, including the `L^-2` factors.

Let `N=R M_Z Q`, with the actual native circle operator. On the optical interior,
`L²(N_LL-N_zz)=Delta N`; the angular derivatives commute with optical derivatives. At the characteristic `z=1-L`,

```
N(L,1-L)=R Q,  Delta N(L,1-L)=Delta R Q.                (1)
```

These are actual source values, constant in `L`, rather than angular eigenvalue assignments. The native mean of every smooth angular jet has the required one-sided characteristic regularity: its even radial expansion gives a finite first right `Z` derivative. Finite optical and angular domains suffice here; no infinite-time or cusp estimate is inferred.

The complete ordered source integrand, before the outer angular `Q` pairing, is

```
I_st=A0² f11 N + A0 f13 A_s(Delta)N
        +A0 f31 A_t(Delta)N + f33 A_s(Delta)A_t(Delta)N.
```

Its transferred density has no angular polynomial beyond the retained `N`:

```
G_st=A0² f11 + A0 alpha_s f13 + A0 beta_s D_star f13
       +A0 alpha_t f31 + A0 beta_t D_star f31
       +alpha_s alpha_t f33
       +(alpha_s beta_t+beta_s alpha_t)D_star f33
       +beta_s beta_t D_star² f33.                      (2)
```

For the Lagrange current `J(F,N)` of the ingredient card, define the fixed five-term source current

```
J_st=A0 beta_s J(f13,N)+A0 beta_t J(f31,N)
       +(alpha_s beta_t+beta_s alpha_t)J(f33,N)
       +beta_s beta_t[J(D_star f33,N)+J(f33,Delta N)].   (3)
```

The finite polynomial identity gives, separately on both smooth cells,

```
I_st = G_st N - div J_st.                              (4)
```

## Exact orders at the interface and source edge

Here is the source calculation that discharges the boundary matching conditions in (3). No endpoint trace is supplied as a premise.

Near `z=-1`, put `epsilon=z+1`. The difference between the two analytic continuations of the radial moment is the short interval

```
g_mn(L,epsilon)
 =integral_0^(-epsilon) y^m(y-1+epsilon)^n/(L+y)^6 dy
 =(-epsilon)^(m+1) integral_0^1
       t^m[-1+epsilon(1-t)]^n/(L-epsilon t)^6 dt.       (5)
```

For every fixed positive `L`, the integral on the second line is jointly smooth in `L,epsilon` near `epsilon=0`: its denominator stays positive uniformly on the fixed compact interval. Thus both cell formulas have equal mixed jets of total order at most `m` at the interface. In particular `h11,h13` match through order one, and `h31,h33` match through order three.

Near `z=1`, put `epsilon=1-z`. The actual moment has the corresponding factorization

```
h_mn(L,1-epsilon)
 =epsilon^(m+1) integral_0^1
       t^m[1-epsilon(1-t)]^n/(L+epsilon t)^6 dt.        (6)
```

Consequently its mixed jets of total order at most `m` vanish on this edge. Multiplication by the smooth original Mellin factor and `L^-2` preserves these orders.

The scalar integral identities underlying (5)–(6), their unmixed vanishing jets, reflected interface jets, and joint smoothness for `L>2` are now proved in `RHTower.D4BMOpticalBoundaryCaps`. The explicit primitive equals `∫_0^x y^m(y+c-x)^n/(L+y)^6 dy` for either sign of `x`; set `(c,x)=(-1,-epsilon)` or `(1,epsilon)`. Mixed-jet transport, multiplication by the Mellin coefficients and the assembled current cancellation below remain paper deductions from these facts.

The source current needs exactly these jets:

| Scalar coefficient | Source-polynomial degree | Largest coefficient-jet order in its current | Available matching/zero order |
|---|---:|---:|---:|
| `f11` | 0 | no current | 1 |
| `f13` | 1 | 1 | 1 |
| `f31` | 1 | 1 | 3 |
| `f33` | 2 | 3 | 3 |

Therefore the two interface traces of `J_st` agree, and their oppositely oriented fluxes cancel. At `z=1`, every term of `J_st` vanishes. This proves both cancellations for the complete original source polynomial. It also explains why splitting the rational and logarithmic pieces before comparing their jets loses the useful matching order.

The interface has a physical corner interpretation. Its lower radial endpoint has `y=0,u=-1`; undoing the image reflection gives source AdS radius `w=0` and target horizon radius `u=1`. The original delay is `h=log(L/2)`, and the native kernel argument is `Z=L/2=exp(h)`, exactly the circle argument of the original horizon formulas. On the long-delay domain `L>=2 exp(1)`, this corner lies after the original onset transition. This identification does not assign its individual higher transferred currents to zero.

## Moving characteristic: an exact corner primitive

Write `a=L²F`. Along `z=1-L`, the sum of current components is

```
J_L(F,N)+J_z(F,N)
 =(∂L-∂z)a N-a(∂L-∂z)N
 =d/dL [L²F(L,1-L) R Q].                              (7)
```

The second equality uses (1). It uses the tangential derivative of the actual constant trace, so it introduces no independent characteristic normal jet. The same identity for `Delta N` has constant trace `Delta R Q`.

Define the fully fixed characteristic primitive

```
C_st(L)=L²[A0 beta_s f13+A0 beta_t f31
              +(alpha_s beta_t+beta_s alpha_t)f33
              +beta_s beta_t D_star f33]_(z=1-L) R Q
           +L² beta_s beta_t f33(L,1-L) Delta R Q.     (8)
```

Then the lower-face flux of (3) is `-C_st'(L)`. The sign follows from the oriented boundary form `J_L dz-J_z dL` and `dz=-dL` on that face.

## Complete finite optical identity

For `2<a<b`, put

```
B_st(L)=integral_(1-L)^1 (J_st)_L(L,z) dz-C_st(L).
```

Integrate (4) over the two cells of `a<=L<=b, 1-L<=z<=1`. Equations (5)–(6) cancel the internal interface and source edge. Equation (7) integrates the moving characteristic. The remaining exact formula is

```
integral_a^b integral_(1-L)^1 I_st dz dL
 =integral_a^b integral_(1-L)^1 G_st N dz dL
      -B_st(b)+B_st(a).                               (9)
```

An independent sign check uses differentiation of the moving-interval integral:
`∫∂L J_L dz = d/dL ∫J_L dz - J_L(L,1-L)`.
Adding the `z` divergence gives `d/dL ∫J_L dz-(J_L+J_z)(L,1-L)`, hence the sign in (9).

The opposite branch has the same identity with the original exchanged coefficients. Subtract the two and restore `-2 a_s² a_t² J0` and the outer angular `Q` pairing to obtain the exact finite long-delay contribution. The spin-two weight remains the actual angular operator throughout.

## Remaining hard cancellation

The source-polynomial interface, source edge and moving characteristic have now been reduced on paper. The remaining optical object is the explicit bulk (2) together with the two cross-section values `B_st`. Extinction requires cancellation of their ordered difference with the retained compact onset, finite-terminal-time correction, angular Green faces and physical action/source-contact terms. The finite identity does not supply that final cancellation or an infinite-limit bound.

Next proof target: identify this fixed cross-section functional with the corresponding original physical flux, then evaluate their complete source-specific balance. The corpus identities are used with the actual source flatness (5)–(6), rather than assuming boundary matching.
