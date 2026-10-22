# HB: finite-clock transfer for the two reduced sources

- **Stage:** 1-in-progress.
- **Status:** analytical finite-domain identity. No new Lean theorem is claimed. Complete physical extinction and RH remain unproved.
- **Inputs:** [two-sided source reduction](../../hb-two-sided-source-current-reduction.md), [original optical coordinates and clock](../../hb-optical-source-tail.md), [native characteristic contacts](../../hb-causal-horizon-circle-kernel.md).

The chain is literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. The hard target is the complete `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes and all physical faces retained. This calculation attacks the previously unevaluated compact-onset portion of its reduced SV–SV source bulk.

## Source-specific conjecture and result

Both derivatives of the fixed onset can be transferred from the two reduced sources onto the native kernel, on the original finite time domain. The transfer produces two explicit first-order kernel operators, a characteristic contact and a finite-terminal-time term. The formula below proves that conjecture analytically. It does not assert that the resulting bulk or complete physical pairing vanishes.

Fix target/source inverse radii `0<u,w<1`, and write

```
t=-s-3, delta=2s+3,
k_s=s(s-1)/4, k_t=t(t-1)/4,
alpha=(2s+1)(2s+2), gamma=(2t+1)(2t+2),
b=2 k_s u(3+delta u)/(1+u),
d=2 k_t w(3-delta w)/(1+w).
```

The actual reduced stream source from the existing absorption identity is

```
T_s(v,u)=a_s² exp(2sv)(1+u)^(2s)
          [alpha chi(v)-b chi'(v)] coexact(Q),
```

with `Q=fullSquarePotential q` and `chi=Real.smoothTransition`; the other source uses `t,w,gamma,d`. Powers of positive real bases use their real logarithms. In this card `h=v_target-v_source` is **ingoing** time difference, as in the optical-source card. It is not static time difference.

## Exact finite clock

For fixed later ingoing cutoff `V>0` and `0<=h<=V`, define

```
J_V(h)=integral_0^(V-h) exp(-6v)chi(v+h)chi(v) dv,
E_V(h)=exp(-6(V-h))chi(V)chi(V-h),
F_V(h)=exp(-6(V-h))chi(V)chi'(V-h).
```

Here `E_V` and `F_V` are actual terminal values. All differentiations below are on finite intervals with the original smooth functions. Let `I_ij` be the same integral as `J_V`, with `i` derivatives on `chi(v+h)` and `j` on `chi(v)`. Leibniz differentiation and integration by parts in `v` give

```
I_10=J_V'+E_V,
I_01=6 J_V-J_V',
I_11=6 J_V'-J_V''+F_V.                              (1)
```

For the second equality, the upper endpoint in
`I_10+I_01-6J_V=E_V` cancels the moving endpoint in `J_V'`. For the third, differentiate the second equality: `I_01'=I_11-F_V`. The lower endpoint vanishes because `chi(0)=chi'(0)=0`. Thus no terminal value has been silently discarded.

The entire ordered reduced-source clock factor is exactly

```
D_V(h)=integral_0^(V-h) exp(-6v)
        [alpha chi(v+h)-b chi'(v+h)]
        [gamma chi(v)-d chi'(v)] dv

      =A0 J_V+A1 J_V'-A2 J_V''-b gamma E_V+b d F_V,

A0=alpha(gamma-6d),
A1=alpha d-b gamma+6bd,
A2=bd.                                                (2)
```

This follows by expanding the original product and substituting (1). The radial coefficients and both branch rates are unchanged.

## Transfer onto the actual native kernel

On either smooth interior cone, put

```
Z_+(h)=(1-uw)cosh(h)+(u-w)sinh(h)+uw,
Z_-(h)=(1-uw)cosh(h)+(u-w)sinh(h)-uw,
R=-Delta(Delta-2),
K(h)=exp(2sh) R M_(Z_+(h))Q
```

or the corresponding `Z_-` expression. Angular evaluation is held fixed. The outer angular source pairing and its angular Green boundary remain outside this one-variable identity.

For a smooth closed subinterval `[a,H]` of the cone, two integrations by parts give

```
integral_a^H K D_V
 =integral_a^H J_V P_K + Gamma_V(H)-Gamma_V(a)
   +integral_a^H K(-b gamma E_V+bd F_V),                 (3)

P_K=A0 K-A1 K'-A2 K''
   =(alpha+b partial_h)(gamma-d(partial_h+6))K,

Gamma_V=(A1 K+A2 K')J_V-A2 K J_V'.                     (4)
```

The factorization is an identity of constant-coefficient operators at the fixed radii. Since `2s+2t=-6`, it also gives the symmetric source-rate form

```
P_K=exp(2sh)
  [alpha+b(partial_h+2s)]
  [gamma-d(partial_h-2t)] R M_Z Q.                      (5)
```

One can verify (3) directly: differentiating `Gamma_V` cancels both terms containing `K' J_V'`, and leaves
`(A1 K'+A2 K'')J_V+A1 K J_V'-A2 K J_V''`.

At `H=V`, the actual values are `J_V(V)=J_V'(V)=0`, so the upper `Gamma_V` vanishes. The remaining terminal integral in (3) is still present. Equivalently, since `E_V'=6E_V-F_V`, one may rewrite the whole formula as

```
integral_a^V K D_V
 =integral_a^V J_V P_K
  +integral_a^V E_V b[(-gamma+6d)K+d K']
  -[Gamma_V(a)-bd E_V(a)K(a)].                         (6)
```

This alternative exhibits one terminal function and its exact accompanying lower contact. It does not delete the terminal contribution.

## Characteristic contacts from existing native jets

The physical lower delays are

```
a_+=2 max(atanh(w)-atanh(u),0),
a_-=2 atanh(w).
```

Substitution in the displayed `Z_+` and `Z_-` gives

```
Z_+(a_+)=Z_-(a_-)=1,
Z_+'(a_+)=|u-w|,   Z_-'(a_-)=u+w.                     (7)
```

The already constructed native mean has right jets
`M_1 Q=Q` and `(partial_Z M_Z Q)|_(1+)=Delta Q/2`. Consequently the lower values in (4) are completely specified:

```
K(a)=exp(2sa) RQ,
K'(a)=exp(2sa)[2s RQ+Z'(a) R Delta Q/2].               (8)
```

Apply (3) separately inside each cone and take the smooth one-sided characteristic limit. Its explicit lower contact accounts for the retarded step; differentiating a Heaviside factor and omitting its distributions is not part of the argument. The image contribution is then subtracted with its original sign.

There is a useful direct-cone simplification on the entire radial triangle `u>=w`, where `a_+=0`. Define

```
J2_V=integral_0^V exp(-6v)chi(v)^2 dv,
E0=exp(-6V)chi(V)^2.
```

The product derivative of `exp(-6v)chi(v)^2` gives
`J_V(0)=J2_V` and `J_V'(0)=3 J2_V-E0/2`. Hence

```
Gamma_V(0)
 =J2_V[(alpha d-b gamma+delta bd)RQ
         +bd(u-w)R Delta Q/2]
   +bd E0 RQ/2.                                      (9)
```

If (6) is used instead of (3), its corrected lower bracket subtracts `bd E0 RQ`; its terminal half therefore has the opposite sign. These are two forms of the same finite identity.

## Connection to the rational long-delay expression

For the clock alone, the limit `V→infinity` is explicit. For `h>=1`, the later transition is already one, so

```
J(h)=J0=integral_0^infinity exp(-6v)chi(v)dv,
J'(h)=J''(h)=0,
D(h)=alpha(gamma-6d)J0.                               (10)
```

Since `6d=12 k_t w(3-delta w)/(1+w)`, this is exactly the coefficient in the existing three-row rational reduced optical tail. At `h=0`, the same clock instead has `J(0)=J2` and `J'(0)=3J2`, yielding the squared-onset local contact in (9). Thus `J0` and `J2` enter one finite-clock formula with fixed roles.

These are limits of the scalar clock functions, not a justification for taking the limit of (3) after radial/angular integration. For finite `V`, even when `h>=1`, the moving upper endpoint remains and `J_V` need not be constant.

## Remaining direct proof obligation

Restore the actual common factor
`-a_s² a_t² uw (1+u)^(2s)(1+w)^(2t)/2`, the outer angular `Q` pairing, the direct-minus-image sign, and subtract the reversed ordered branch. Equations (3)–(9) then give a source-specific replacement for the complete compact-onset plus tail integrand. Retain the physical lift/response currents from the two-sided reduction, the angular Green faces and the independent tensor sectors.

The immediate cancellation conjecture is that this explicit `P_K` bulk, its characteristic contacts and its terminal integral combine with those fixed physical currents to extinguish the complete action coefficient. That cancellation is not established here. For a static-time truncation, substitute the actual radius-dependent ingoing cutoff before radial integration and keep the resulting geometry of the temporal face.

The [spin-two primitive transfer](../../hb-spin-two-kernel-transfer.md) gives another exact analytical representation of the same finite reduced-source bulk: transfer the spin-two angular weight first, retaining both onset factors in `D_V`. Its characteristic boundary vanishes even on the direct coincident-radius diagonal; the original terminal source Wronskian remains explicitly inside the resulting coefficient. The primitive is checked for the actual complex-degree scalar Riemann kernel in Lean. Full native-circle formalization and comparison with the physical boundary currents remain open.

This is an analytical result only. No numerical experiment, Lean build, axiom audit, or frontier-map edit was performed for this card.
