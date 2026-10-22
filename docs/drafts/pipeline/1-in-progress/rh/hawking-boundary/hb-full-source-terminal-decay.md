# HB: full-source growth and terminal decay

Stage: 1-in-progress. Analytical terminal-decay proof below; the full source's value and native mean growth are [formalized](../../../3-formalized/hb-full-source-circle-growth.md). Complete physical extinction and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target is the complete physical cancellation `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes. This attack resolves the terminal source coefficients in [the spin-two transfer](../../hb-spin-two-kernel-transfer.md). All statements below keep the actual full half-square `Q`, the original smooth transition, a fixed Xi occurrence, a compact angular region, and `0<=u,w<=r<1`.

## Conjecture, proof and scope

Set `sigma=Re rho`, `beta=max(sigma,1-sigma)`, `kappa=2 beta`, `s=rho-2`, `t=-rho-1`. The unconditional Xi strip gives `1/2<=beta<1`. The conjectured sufficient estimate is growth `exp(kappa h)` for the full native circle source and its invariant Laplacians. It gives decay `exp(-4(1-beta)V)` when paired with a terminal original source.

The full scalar is `a y^rho+b y^(1-rho)+tail`, with the actual completed coefficients and both infinite signed Fourier tails. Every fixed coordinate derivative of the tail is a finite combination of the derivative-stable families in `ThetaCuspHawkingBMAngularSeriesSmooth`; their arbitrary height weights are bounded by `ThetaCuspHawkingBMAngularCuspBounds.weighted_value_bounded`. Thus, on the closed modular cell, every fixed `Delta^j Q` is bounded by `C_j(1+y^kappa)`: its three principal powers are `y^(2rho)`, `y`, `y^(2-2rho)`, and applying `Delta=y^2(partial_x^2+partial_y^2)` preserves their exponents. Derivatives of the remainder retain rapid cusp decay. The compact lower cell is controlled by actual smoothness.

The original scalar is modular by `ThetaCuspHawkingBMFullSourceOverlap.xi_scalar_modular`; invariant Laplacians preserve this invariance. For every modular matrix, its transformed height is at most `max(y,1/y)`: zero lower-left entry preserves height, and a nonzero integer lower-left entry gives height at most `1/y`. Therefore, globally,

```
|Delta^j Q(x+iy)| <= C_j max(1,y,1/y)^kappa.             (1)
```

The native radius-`d` circle has height `y/(cosh d-sinh d cos theta)`, between `y exp(-d)` and `y exp(d)`. For a compact set of basepoints, (1) consequently gives

```
|M_(cosh d)(Delta^j Q)| <= C_j,K exp(kappa d).           (2)
```

No angular spectral projection occurs in (1)–(2). For the scalar value itself the bound is uniform in the base horizontal coordinate, with base-height factor `exp(kappa |log y|)`.

## Uniform control of the transferred primitive

Use `F,A,B,Z` from the spin-two transfer and write `H=B/A`, `J=F/A^2` on the open cone. Its exact equation and adjoint are

```
J''+3H J'+2J=-R M,
F T W=J[W''-3H W'+(3H^2-1)W].                         (3)
```

Here `H'=1-H^2`. Equivalently the operator on `J` is `(partial_h+H)(partial_h+2H)`. This is a representation of the actual source-circle primitive; identifying it with a physical response current is a separate task.

For bounded delay, the Volterra formula gives `F=O((Z-1)^2)`. The previously derived identity `A^2>=2(1-r^2)(Z-1)` controls all three quantities `J`, `HJ`, `H^2J`, including the direct coincident-radius corner. For large delay, uniformly on the fixed radial square, `Z` and `A` are bounded above and below by positive constants times `exp(h)`, and `H` is bounded. The native identity

```
(Z^2-1) M_Z = integral_1^Z M_(zeta)(Delta Q) d zeta
```

and (2) give `M_Z=O(Z^(kappa-1))`. Since `F=(Z^2-1)Delta M-2Z(Z^2-1)M_Z`, it follows that

```
|J|+|HJ|+|H^2J| <= C exp(kappa h)                      (4)
```

on both cones. The constants depend on `r`, the Xi occurrence and the angular compact set. Values of the quotients at an exactly degenerate endpoint are interpreted through the integrals, not by dividing distributions.

## Terminal source terms vanish with a strict rate

Keep the exact original factors

```
g_s(v)=exp(2s v)[alpha chi(v)-b chi'(v)],
g_t(v)=exp(2t v)[gamma chi(v)-d chi'(v)].
```

For each fixed derivative order `j`, smoothness and constant tails of the actual transition give `|g_s^(j)(v)|<=C_j exp(2 Re(s) v)` for `v>=0`, uniformly on the fixed radial square; similarly for `t`. Put `c=V-h`. The terminal part of `F T W_V`, with its signs retained, is exactly

```
E_V(h)=J[h][g_s(V)g_t'(c)-g_s'(V)g_t(c)]
       +3H[h]J[h]g_s(V)g_t(c).                        (5)
```

By (4), changing variables to `c` gives

```
integral_a^V |E_V(h)| dh
 <= C exp((2 Re(s)+kappa)V)
        integral_0^V exp((2 Re(t)-kappa)c) dc
 <= C' exp(-4(1-beta)V).                              (6)
```

The first integral is zero when `a>=V`. The reverse orientation has the same estimate with `s,t` exchanged. The coefficient `3H` in (5) is essential and is included in (6).

For the bulk coefficients, let

```
W_infty^(j)(h)=integral_0^infty g_s^(j)(v+h)g_t(v) dv.
```

These are the actual derivatives for `j<=2`, by the integrable bound `C exp(2 Re(s)h-6v)`. They satisfy `|W_infty^(j)(h)|<=C exp(2 Re(s)h)`. Their finite-`V` integral versions have error at most `C exp(2 Re(s)h-6(V-h))` for `h<=V`. Equations (3)–(4), followed by integration in `h`, control this error and the omitted `h>V` tail at the same rate as (6). Hence the entire finite transferred reduced-source integral converges, uniformly on the fixed radial square and angular compact set, to

```
-integral_a^infty F T W_infty dh,                       (7)
```

with truncation error `O(exp(-4(1-beta)V))`. The finite radial and angular measures and original bounded outer source factors preserve this convergence. The lower characteristic cancellation remains the one already established in the finite transfer.

## Remaining physical target

Equation (7) removes the finite terminal source coefficients inside this reduced SV–SV bulk. The value of (7) remains to be evaluated in the full physical pairing. The response–response current, source-contact current, cross-currents, angular Green boundary, horizon and cusp limits, and independent tensor amplitudes still require their actual assembly. In particular, scalar circle bounds alone do not give the basepoint derivatives of a physical response. No temporal Einstein-current limit, uniform horizon limit, uniform cusp limit, or exchange of those limits is claimed here.

The original native-circle kernel has an absolutely convergent delay Laplace integral for `Re w>kappa`, since `Z=O(exp h)` and (2) applies. Because `kappa<2`, this leaves the nonempty overlap `max(kappa,3/2)<Re w<2`, with nonzero imaginary part, inside the chamber of `ThetaCuspHawkingBMPhysicalResponseGreenIdentification.physicalCuspProfile_eq_completePhysicalGreenProfile`. [Native/physical causal time-class equality](../../../3-formalized/hb-native-causal-equality.md) is now proved independently of a native global growth bound. The remaining task is transferring that equality into the projected Green/current formulas in this smaller chamber, with their actual derivatives, cusp/AdS data and boundary limits. The existing shifted Hilbert-space Laplace theorem has a different threshold; the time-class equality alone does not establish every required current limit.

## Corpus search evidence

Broad `moderate`, `Starobinsky`, `bitensor`, OR `symplectic propagator`, OR `growth bound decay` within Eisenstein, and mechanism-directed deep circle-growth, wave-transposition and interior-estimate searches were inspected through candidate declarations and source arguments. The useful verified sources are the literal angular derivative families, their weighted bounds, modularity, and native-circle identities cited above. Generated ingredient groups did not establish the physical current identification. Coverage is partial: source inventory is complete, semantic coverage incomplete; the Eisenstein search reached its request deadline. No absence claim follows from these searches.
