# HB: spin-two kernel transfer with the full onset retained

Stage: 1-in-progress for the source-delay and physical-current transfer. The original scalar-kernel identities are [formalized](../../../3-formalized/hb-spin-two-kernel-primitive.md); the [full native-source primitive and characteristic data](../../../3-formalized/hb-native-spin-two-primitive.md) are also formalized. Complete physical extinction and RH remain unproved. Frontier map read only.

The [direct coincident-radius finite-clock transfer](../../../3-formalized/hb-spin-two-delay-characteristic.md) is now formalized, including its actual source clock, zero characteristic current, retained finite bulk contact and radius-independent geometric coefficients. The [full off-diagonal/image finite transfer and signed assembly](../../../3-formalized/hb-full-spin-two-delay-transfer.md) are now formalized with their original causal lower limits. A [derived finite-delay bulk bound](../../../3-formalized/hb-uniform-spin-two-delay.md) now controls both entire radial domains, retaining the original source and both clock derivatives. Boundary-limit and global angular transport, and the full physical-current comparison, remain open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes and the full physical boundary. This construction attacks the reduced SV–SV source integral from [the two-sided reduction](../../hb-two-sided-source-current-reduction.md). It uses the spin-two angular weight before transferring the onset derivatives. It does not change the original clock or project the angular half-square onto an eigenfunction.

## Conjecture and exact differential mechanism

The conjecture is that the spin-two weight admits a primitive with enough vanishing at the characteristic to transfer the complete finite source density without separate lower-endpoint jets. Write `M(Z)=M_Z Q` for the native circle mean of the full half-square and

```
p=Z^2-1, L=p partial_Z^2+2Z partial_Z,
R=-Delta(Delta-2), F(Z)=p^2 partial_Z^2 M(Z).
```

The native Darboux equation and angular commutation give `L M=Delta M`. Product differentiation gives the operator identity

```
L(L-2)M = partial_Z^2(p^2 partial_Z^2 M).
```

Thus the actual retained angular weight satisfies

```
R M=-F'',
F=p Delta M-2Zp M',
F'=p(Delta-2)M',
F''=Delta(Delta-2)M.                                  (1)
```

These identities hold on `Z>1`. Smoothness of the original circle mean from the right gives `F(1)=F'(1)=0`. An alternative description, retaining the full source, is

```
F(Z)=integral_1^Z (Z-r) Delta(Delta-2)M(r) dr.
```

For each compact angular region and bounded `Z>=1`, this implies `F=O((Z-1)^2)` and `F'=O(Z-1)`. The derivatives in (1) are argument derivatives, not time derivatives. No factor involving an angular eigenvalue is divided out.

The [native-source proof](../../../3-formalized/hb-native-spin-two-primitive.md) establishes (1), both characteristic limits, the full double-integral identity and the two displayed vanishing orders at each fixed original angular base point, uniformly over compact invariant intervals. It also proves equality with the original radius-frozen physical spin-two trace. Uniform compact-angular bounds and the delay-coordinate quotient estimates below remain analytical obligations.

## Apply (1) to the original finite clock density

Keep exactly the notation and source normalization of [the finite-clock transfer](../../hb-reduced-source-clock-transfer.md). At fixed `0<u,w<1`, set `t=-s-3`,

```
alpha=(2s+1)(2s+2), gamma=(2t+1)(2t+2),
b=2 k_s u(3+(2s+3)u)/(1+u),
d=2 k_t w(3-(2s+3)w)/(1+w),
D_V(h)=integral_0^(V-h) exp(-6v)
  [alpha chi(v+h)-b chi'(v+h)]
  [gamma chi(v)-d chi'(v)] dv,
W(h)=exp(2s h)D_V(h).                                 (2)
```

Here `chi=Real.smoothTransition`, and `V>0` is a common finite **ingoing** cutoff. Both onset factors and both onset derivatives remain in (2). The fixed smooth transition is flat at zero. Finite-interval differentiation therefore gives a smooth `W` on `[0,V]` and

```
W(V)=W'(V)=0.                                        (3)
```

For example, the moving endpoint in `D_V'(V)` contains the earlier source factor `gamma chi(0)-d chi'(0)=0`; the remaining interval has length zero. This is an evaluation of that endpoint, not deletion of the terminal factors appearing in other integrations by parts.

For either native branch put

```
Z= (1-uw)cosh h+(u-w)sinh h+epsilon uw,
A=partial_h Z, B=partial_h^2 Z=Z-epsilon uw,
epsilon=1 (direct), epsilon=-1 (image).
```

The lower limits are respectively
`a_+=2 max(atanh w-atanh u,0)` and `a_-=2 atanh w`.
On a nonempty interval `a<h<V`, one has `Z>1`, `A>0`, `A'=B`, `B'=A`.

Define the explicit transpose on the complete scalar time density,

```
T W = W''/A^2-3B W'/A^3+(3B^2-A^2)W/A^4,
C(W,F)=-W partial_h F/A^2+(W'/A^2-WB/A^3)F.           (4)
```

Twice integrating by parts on any closed interior interval gives

```
integral W R M = [C(W,F)] - integral F T W.             (5)
```

This can also be checked directly: `F''` in (1) equals
`partial_h^2 F/A^2-B partial_h F/A^3`. Differentiating (4) cancels the two first-derivative cross terms in (5).

## Characteristic limit, including coincident radii

For a direct characteristic with `u!=w`, `A(a)=|u-w|>0`; for the image, `A(a)=u+w>0`. The two vanishing orders of `F` immediately imply `C(W,F)->0` at the lower limit.

The direct diagonal `u=w` requires a separate check. Write `k=1-u^2>0`. There

```
a=0, Z=1+k(cosh h-1), A=k sinh h, B=k cosh h.
```

Consequently `Z-1=O(h^2)`, `F=O(h^4)`, and `partial_h F=O(h^3)`. Both terms of the boundary expression in (4) tend to zero, although its displayed denominators vanish. The bulk `F T W` is bounded: its three contributions have orders `O(h^2)`, `O(h)`, and `O(1)`. This is an improper-integral limit; it does not multiply distributions by `1/A` at the diagonal.

The [original diagonal proof](../../../3-formalized/hb-spin-two-delay-characteristic.md) sharpens this to the exact bulk contact `F T W -> -3 (R Q) W(0)/8`, while the boundary current tends to zero. It derives both facts from the literal source moments and retains both onset derivatives in `W`. It also proves (7) on this entire diagonal interval. The raw bulk's assigned value at zero need not equal its limit; integrability is proved by agreement with the continuous expression away from zero.

The control also holds uniformly on a compact radial square `0<=u,w<=r<1`. At either characteristic, write `B0=1-epsilon uw`, and let `d0=|u-w|` on the direct branch or `d0=u+w` on the image. The exact identity

```
A^2=d0^2+2B0(Z-1)+(Z-1)^2
   >=2(1-r^2)(Z-1)                                  (6)
```

controls every quotient in (4). Since `p=(Z-1)(Z+1)`, the boundary is uniformly `O(sqrt(Z-1))`, while the bulk is uniformly bounded. Native-source derivatives are bounded on the corresponding compact angular and circle domains. Finite radial and angular integration therefore preserves the lower-limit cancellation. The constants depend on `r`; no horizon limit is inferred from this compact estimate.

At the upper endpoint, (3) gives `C(W,F)(V)=0` whenever `a<V`. Thus (5) becomes

```
integral_a^V exp(2s h)D_V(h) R M_Z Q dh
  =-integral_a^V F(Z(h)) T[exp(2s h)D_V(h)] dh.         (7)
```

Intervals with `a>=V` contribute zero. Formula (7) contains the entire source-clock density. In particular, it does not discard the zero-delay characteristic term computed when onset derivatives are transferred first; that contribution is included in the integral on the right.

## Explicit surviving source coefficient and physical scope

The coefficient to evaluate next is entirely fixed:

```
T[exp(2s h)D_V]
 =exp(2s h)/A^4 * {
   A^2[D_V''+4s D_V'+(4s^2-1)D_V]
   -3BA[D_V'+2s D_V]+3B^2D_V
 } .                                                 (8)
```

No onset derivative is set to zero on its transition interval. Expanding the derivatives in (8) differentiates the actual integral (2), including its moving endpoint.

Those retained terminal terms have a useful exact form. Absorb the physical rates into the original source profiles,

```
g_s(v)=exp(2s v)[alpha chi(v)-b chi'(v)],
g_t(v)=exp(2t v)[gamma chi(v)-d chi'(v)],
c=V-h, I_j(h)=integral_0^c g_s^(j)(v+h)g_t(v) dv.
```

Then `W=I_0`, and direct differentiation of this same finite interval gives

```
W'=I_1-g_s(V)g_t(c),
W''=I_2-g_s'(V)g_t(c)+g_s(V)g_t'(c).
```

Substitution into (4) identifies the surviving coefficient completely:

```
T W = I_2/A^2-3B I_1/A^3+(3B^2-A^2)I_0/A^4
    +[g_s(V)g_t'(c)-g_s'(V)g_t(c)]/A^2
    +3B g_s(V)g_t(c)/A^3.                            (9)
```

Thus the physical source's terminal Wronskian and its geometry-dependent product correction remain inside the finite transformed bulk. Their presence is compatible with the zero upper boundary in (5). The [full-source terminal estimate](../../hb-full-source-terminal-decay.md) controls both terms after multiplication by `F`: their integrated contribution tends to zero at rate `exp(-4(1-beta)V)` on every fixed compact radial square and angular region, where `beta=max(Re rho,1-Re rho)<1`. The estimate retains the complete angular source. It concerns the source integral; the physical lift/response and source-contact temporal currents still require their own comparison.

Restore the original factor `-a_s^2 a_t^2 uw(1+u)^(2s)(1+w)^(2t)/2`, the outer `Q` pairing, direct minus image, and subtraction of the reversed ordered branch. Formula (7) changes this reduced source bulk into the corresponding **positive** prefactor times `F T W`. It replaces the separate characteristic-period comparison with a single weighted spin-two-kernel integral.

The physical lift/response cross-currents from the two-sided reduction, the source-contact correction taking its master current back to the Einstein current, and the finite angular Green boundary remain attached. Their temporal faces have not been set to zero by (3): (3) concerns the source-delay integration only. A static-time cutoff has radius-dependent ingoing bounds and needs its own transported domain. The source integral's infinite-ingoing-time limit is controlled on fixed compact radial and angular regions by the linked estimate. Horizon and cusp limits, the physical temporal-current limit, the independent SS/VV coefficients, and cancellation of the remaining integral against the complete physical current remain open.

## Corpus evidence and verification scope

The original native-circle wave and Darboux identities supply the angular input. The bounded `bispectral`, squared-eigenfunction and Rodrigues/Gegenbauer searches were checked in statement and proof-method views; results were partial and did not supply a complete source-current cancellation. `ProlateCommutationKernel` supplies the concrete method of deriving a kernel operator identity before doing the boundary integral. Its band endpoints are not substituted for the HB endpoints.

The original positive-chart Legendre kernel provides a closed scalar check of (1): with `ell=nu(nu+1)`, its primitive is `p[ell P_nu-2Z P_nu']`. Its first derivative is `p(ell-2)P_nu'`, and its second is `ell(ell-2)P_nu`. Five Lean theorems prove these actual derivatives, the weighted-second-derivative identity, both zero characteristic jets, and the two finite integral formulas. The separate full native-source proof establishes these mechanisms on the literal angular mean, including its original physical trace; it uses no spectral replacement. Equation (7) is formalized on both complete causal branches with the actual finite clock, including degenerate characteristics; see the [full finite transfer](../../../3-formalized/hb-full-spin-two-delay-transfer.md). The [original source horizon transport](../../../3-formalized/hb-original-delay-horizon.md) now proves the target-horizon limit of its signed native source action on finite delay intervals at fixed source radius and angular point. Integration under the full physical radial/angular measure, joint corner limits and complete physical-current comparison remain open.
