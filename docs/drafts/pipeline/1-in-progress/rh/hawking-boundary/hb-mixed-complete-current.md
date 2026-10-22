# HB: complete mixed-current cancellation test

Status: analytical conjecture/proof loop in progress. Complete physical pairing and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The target is the complete SV–SV coefficient of `2 Omega(B(p,p)/2,B(m,m)/2)`. Its source is the same literal angular half-square on both physical branches; the source rates are `s` and `-s-3`. The scalar/vector amplitudes remain independent. The [circle cancellation and fixed-clock expression](../../hb-causal-circle-taylor-cancellation.md) supplies the exact horizon bulk and derived contacts.

## Conjecture under test

The complete mixed Einstein action current, with temporal and angular components included, has a source-contact transgression to the original stream master's Green current. This would combine the horizon expression with its physical AdS, temporal and cusp edges before testing extinction.

Use static coordinates, `f=r²-1`, `D=roughLaplacian+1`, `A=D-2`, and actual stream fields `Psi,Phi`. Their mixed metric entries are `h_tA=f partial_r Psi_A`, `h_rA=partial_t Psi_A/f`. The original master is

```
M Psi = r² f Psi_rr+2r Psi_r-r² Psi_tt/f+A Psi.
```

The already proved actual radial action current is

```
omega_r=(f/r²)[Psi_r dot(A Phi-M Phi)-Phi_r dot(A Psi-M Psi)].
```

The current test derives the temporal component from the actual Einstein action variation, rather than supplying it from a scalar analogy. After both components are fixed, differentiate them and retain the full angular Green contribution. Then apply the resulting identity to the original fixed-clock sources. No source or boundary term may be assigned to zero.

## Complete current: successful derivation

Write `T=f Psi_r`, `R=Psi_t/f`, `U=f Phi_r`, `V=Phi_t/f`, and `curl(T)=partial_X T_Y-partial_Y T_X`. The actual volume-weighted Einstein variation gives

```
omega_t=sum[-R(partial_t V-partial_r U)
            +V(partial_t R-partial_r T)+2(TV-UR)/r],
omega_r=sum[T(partial_t V-partial_r U)-U(partial_t R-partial_r T)],

omega_X=y²/r²[-(T_Y curl(U)-U_Y curl(T))/f
               +f(R_Y curl(V)-V_Y curl(R))],
omega_Y=y²/r²[ (T_X curl(U)-U_X curl(T))/f
               -f(R_X curl(V)-V_X curl(R))].
```

All four components were checked by expanding the actual action's mixed first variation, including the volume and inverse-metric derivatives. The temporal curvature term is essential. Its stream substitution yields

```
omega_t=-[Psi_t dot(A Phi-S_Phi)-Phi_t dot(A Psi-S_Psi)]/(f r²),
omega_r= f[Psi_r dot(A Phi-S_Phi)-Phi_r dot(A Psi-S_Psi)]/r²,
S_Psi=M Psi, S_Phi=M Phi.
```

For coexact covectors, define the actual angular Green density

```
G_X(P,Q)=y²[P_Y curl(Q)-Q_Y curl(P)],
G_Y(P,Q)=y²[-P_X curl(Q)+Q_X curl(P)].
```

Direct product differentiation and zero divergence give `div G(P,Q)=P dot A Q-Q dot A P`. In particular, for actual scalar potentials `p,q`,

```
G(coexact p,coexact q)=grad p Delta q-grad q Delta p.
```

The products of the two scalar Laplacians cancel in this divergence. The complete stream's angular current is

```
omega_angular=-(f/r²)G(Psi_r,Phi_r)+(1/(f r²))G(Psi_t,Phi_t).
```

Consequently the entire four-divergence, with angular terms included, is

```
div omega =-f/r²[Psi_r dot partial_r S_Phi-Phi_r dot partial_r S_Psi]
           +1/(f r²)[Psi_t dot partial_t S_Phi-Phi_t dot partial_t S_Psi].
```

Define the source-contact current, with zero angular components,

```
C_t=-[Psi_t dot S_Phi-Phi_t dot S_Psi]/(f r²),
C_r= f[Psi_r dot S_Phi-Phi_r dot S_Psi]/r².
```

Differentiating it cancels both differentiated-source terms. The products `S_Psi dot S_Phi` cancel by symmetry, leaving the source-weighted Green identity

```
div(omega+C)=[S_Psi dot A Phi-S_Phi dot A Psi]/r⁴.          (1)
```

This proves the conjectured transgression analytically. It is an equality with the full boundary of a finite domain. In ingoing coordinates, `C_r` has horizon limit `Psi_v dot S_Phi-Phi_v dot S_Psi`, which is exactly the original contact in the horizon formula. Temporal, AdS and angular boundary terms remain on the same boundary integral. This does not justify an infinite-time or cusp limit.

If the physical retarded/advanced adjoint identification and all boundary transport are established, (1) reduces the response-response bulk to the source pairing with one causal Green difference and angular weight `A`. For scalar potentials, angular integration transfers this weight to `-Delta(Delta-2)`, with the original angular boundary current retained. That is the spin-two factor; no angular spectral substitution is required.

## Shared source operator: successful second conjecture

The literal branches have `s` and `-s-3`, common scalar eigenvalue `lambda=(s+1)(s+2)=rho(rho-1)`, and centered weights `delta=2s+3` and `-delta`. At fixed ingoing time `v`, let

```
u=-tanh x,
F_s(v,u,z)=a² chi(v)exp(2sv)(1+u)^(2s)Q(z),
Q=fullSquarePotential q,
D_u=(1+u)partial_u+3=partial_x/(u-1)+3.
```

Actual radial differentiation gives `D_u F_s=(2s+3)F_s`; it never differentiates or divides the fixed onset. Both complete original scalar forcing branches are exactly

```
timeOriginalForcing_s=-2(1-u²)u P_lambda F_s,

P_lambda F=(5lambda-6)F/4
 +u²/8[(4lambda+1)(lambda+2)F-(lambda+4)Delta F
       -(7lambda-2)D_u F+2D_u Delta F].                    (2)
```

Equivalently,

```
P_lambda=(5lambda-6)/4
 +u²/8[(lambda-2)(4lambda-4-Delta)
       -(1+u)(7lambda-2-2Delta)partial_u].                 (3)
```

The two original source polynomials are evaluations of this single differential operator. This identifies the full `timeOriginalForcing` on each actual Xi copy, either physical branch, every exterior tortoise coordinate and original angular point; the full gradient-energy term is discharged using the already proved actual half-square Laplacian. No angular inverse, fitted coefficient, adjusted polarization, or onset premise is introduced.

The normalization linking (2) to the current is fixed, too. With `Psi=r coexact(phi)`, direct substitution and `partial_x=f partial_r` give

```
M Psi=-(r³/f)coexact(timeFieldWave phi).
```

Since `(1-u²)u=f/r³`, the actual wave source in (2) therefore gives `S_Psi=2 coexact(P_lambda F_s)`. Thus the Green inverse in the next pairing is the inverse of the original master `M`. Replacing it by the scalar wave inverse requires these radial conjugating factors; they cannot be suppressed.

## Exact adjoint test and next pivot

A shared producer alone does not establish adjoint symmetry. Compute its formal radial adjoint with the *actual* master measure `r^(-4)dr=u²(-du)`. Put

```
A0=(5lambda-6)/4,
C=[(4lambda+1)(lambda+2)-(lambda+4)Delta]/8,
K=(7lambda-2-2Delta)/8.
```

Then `P=A0+u²C-u²K D_u`, whereas

```
P_dagger=A0+u²C+(4u-u²)K+u²K D_u.                         (4)
```

This is a formal transpose for the complex bilinear pairing; no coefficient is conjugated. The extra multiplication term is fixed by the radial measure. In the tortoise coordinate the measure is `mu=u²(1-u²)`, and the radial Green boundary density for its scalar coefficient is exactly `u^4(1+u)K F G`. The [formal source-kernel Green transfer](../../../3-formalized/hb-common-source-green-transfer.md) supplies its two angular currents and proves their complete local divergence identity on the literal theta seed and both native kernel terms, retaining the full spin-two weight. Radial differentiation holds ingoing delay fixed, so both the kernel's time separation and source radius vary. The [improper radial transfer](../../../3-formalized/hb-source-characteristic-radial-flux.md) retains both angular divergences, admits the full characteristic spin-two traces, and evaluates the signed direct-minus-image radial face. Its [actual source-time integral](../../../3-formalized/hb-source-time-radial-flux.md) is formally bounded by `C exp(-T)`, uniformly in exterior target radius, and decays along every exterior radius path. The [source-time/radial interchange](../../../3-formalized/hb-source-time-radial-interchange.md) now identifies this face integral with the admitted original radial source transfer, including both angular divergences. Angular integration, the actual transposed kernel action and the remaining physical currents still require proof.

The next direct extinction test is the source-specific action of `P_dagger A(G_ret-G_adv)P` on the two actual common seeds, with `G_ret,G_adv` the original master's causal inverses and with the boundary densities in (1) and (4), followed by the independent SS/VV coefficients. On scalar potentials, replace `A` by the derived angular weight `-Delta(Delta-2)` and retain its cusp Green boundary. No vanishing of this operator pairing has been established.

## Formal scope

The complete four-component Einstein current and its stream-master representation are formalized. Equation (2), for the actual original theta source and fixed onset on both branches, and its differential form (3), are formalized. See the [four exact theorem statements and targeted validation](../../../3-formalized/hb-complete-mixed-current-common-source.md). The separate [source-producer transfer](../../../3-formalized/hb-common-source-green-transfer.md) formalizes the three-current local Green identity, both affine causal invariants and its literal forcing dictionary; its radial characteristic integration and signed-face decay are also formalized. The differentiated Einstein four-divergence, angular and full spacetime integration, remaining transverse boundary admission and physical-current transport remain analytical. RH remains unproved.

The [actual source cusp-jet admission](../../../3-formalized/hb-angular-cusp-jet-admission.md) proves every complex-weighted coordinate-derivative bound and arbitrary-horizontal-path cusp limit for the literal square remainder and its retained `-Delta(Delta-2)` image. These estimates supply the differentiated source side of the angular boundary argument.

The [native cusp-jet transport](../../../3-formalized/hb-native-cusp-jet-transport.md) identifies every radius/base-coordinate derivative with the original differentiated angle integral and proves arbitrary-order decay uniformly in horizontal position and compact radius. The [native angular current evaluation](../../../3-formalized/hb-native-angular-current-cusp.md) retains all three principal interactions, evaluates their exact coefficients and exponents, and proves every complex-weighted full-current remainder limit in the original height coordinate. The [original causal cusp transport](../../../3-formalized/hb-causal-response-cusp-current.md) now proves exact integral formulas and arbitrary-order compact-causal cusp bounds for every actual angular remainder jet, together with its original Goursat equation and both first-null derivative identities. Higher angular null-trace bounds, reconstruction, invariant-coordinate characteristic admission, and complete physical boundary cancellation remain open. The existing [full onset source decomposition](../../../3-formalized/hb-full-source-onset-reduction.md) supplies the explicit incoming profile `H-s(s-1)Q/4` and fixed onset pulse that this comparison must retain. The [complete incoming wave-image current](../../../3-formalized/hb-full-incoming-current.md) now identifies all four original Einstein-current components, their actual horizon limits, and finite fixed-clock integrals with both constructed angular responses and their cross currents retained. The pulse-response, wave-image/pulse cross terms and remaining physical faces still require their signed comparison.
