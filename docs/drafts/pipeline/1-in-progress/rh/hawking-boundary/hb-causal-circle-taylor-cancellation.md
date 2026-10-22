# HB: cancellation of the forced circle term

Status: the actual Legendre-kernel cancellation, Taylor integral remainder, explicit regular source numerator, and its joint continuity are [formalized in Lean](../../../3-formalized/hb-causal-circle-cancellation.md). Full-angular fixed-clock substitution is analytical. The complete physical pairing and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target is the assembled physical pairing. This calculation attacks the explicit circle term in equations (8)–(10) of [the source-only horizon construction](../../hb-causal-horizon-circle-kernel.md), using the [proved source adjoint identity](../../../3-formalized/hb-causal-source-adjoint-kernel.md).

## Exact cancellation

Retain the original coefficients `A=(5s²+15s+4)/4`, `k=s(s-1)/4`, `B=(s+2)(2s+3)`. At positive delay, `E=exp(q)>1`. Direct geometry is `(c,d,U)=(E-1,E+1,1)`; image geometry is `(E+1,E-1,(E-1)/(E+1))`. Put `D=d/c`, `Z=E-cu`, `p_D=(1-u)(D-u)`, `L_D f=(p_D f')'`, and let `g_(s,D)` be the already evaluated cubic source weight.

Write `a_(s,D)=(L_D-2)g_(s,D)`. The proved source action has the form

```
(lambda-2)K_nu(E)
 = -a² integral_direct a_(s,D) P_nu(Z)du
   +a² integral_image a_(s,D) P_nu(Z)du
   +Gamma_s,a(E)P_nu(E),
lambda=nu(nu+1).
```

**Conjecture tested:** the forced circle term cancels against the constant and linear radial moments, leaving the second Taylor remainder of the actual kernel.

**Result:** the constant and linear Legendre solutions, `P_0(Z)=1` and `P_1(Z)=Z`, give exactly the two moment identities needed. Let `K_0(E)` denote the same original source kernel at angular degree zero. Then

```
-a² integral_direct a_(s,D)du+a² integral_image a_(s,D)du
  =-2K_0(E)-Gamma_s,a(E),

-a² integral_direct a_(s,D)Zdu+a² integral_image a_(s,D)Zdu
  =-E Gamma_s,a(E).
```

These follow from the original source action, whose left factor is respectively `-2` and zero. Subtract the actual first Taylor jet

```
R_nu(E,Z)=P_nu(Z)-P_nu(E)-(Z-E)P_nu'(E).
```

The three explicit `Gamma` contributions cancel. The complete identity becomes

```
(lambda-2)K_nu(E)
 =2K_0(E)[E P_nu'(E)-P_nu(E)]
   -a² integral_direct a_(s,D)R_nu(E,Z)du
   +a² integral_image a_(s,D)R_nu(E,Z)du.                    (11)
```

No circle contribution is set to zero separately. Its cancellation uses the retained radial moments. The coefficient left in front of the circle jet is an elementary original-source tail:

```
K_0(E)=-a² integral_b^1 u(1+u)^(2s)[A+kB u²]du,
b=(E-1)/(E+1).
```

## Regular form at zero delay

The cubic `C_(s,D)` is affine in `D`; write it `C_const(s,u)+D C_linear(s,u)`. The coefficient

```
G_s(E,c,d,u)=c g_(s,D)(u)
 =u(1+u)^(2s-2)[c C_const(s,u)+d C_linear(s,u)]
```

has no division by `c`. Define

```
H_s(E,c,d,u)=partial_u[(1-u)(d-cu)partial_u G_s]-2c G_s.
```

Direct differentiation gives `H_s=c² a_(s,D)`. Taylor's theorem for the actual kernel gives

```
R_nu(E,Z)=(Z-E)² J_nu(E,Z),
J_nu(E,Z)=integral_0^1 (1-theta)P_nu''(E+theta(Z-E))dtheta.
```

Since `Z-E=-cu`, the radial integrand in (11) is exactly

```
a_(s,D)R_nu(E,Z)=u² H_s(E,c,d,u)J_nu(E,Z).                  (12)
```

Every coefficient in (12) reaches the direct zero-delay endpoint `E=1,c=0,d=2` without a radial denominator. The image interval shrinks to zero. On finite time and angular regions, the actual source is smooth and the circle radii are bounded; the analogous full-angular expression uses the first and second `Z` derivatives of the intrinsic circle mean. A formal joint-continuity/admission proof must use these combined expressions, not integrate the earlier singular `Gamma` formula separately.

The original scalar source kernel's zero-delay value is fixed directly by the characteristic value `P_nu(1)=1`:

```
K_nu(1)=-a²[A I_1+k(B-lambda/2)I_3],
I_j=integral_0^1 u^j(1+u)^(2s)du.
```

For the full angular source, (11) replaces `P_nu(Z)` by `M_Z Q`. Its circle-jet factor is `(partial_q-1)M_(exp q)Q`, because `E partial_E=partial_q`. Thus the remaining circle contribution is a regular, explicitly weighted time derivative, available for integration against the already evaluated fixed clock. Its boundary and source-contact terms must be assembled with the remainder in (12), the cusp Green terms, and the other tensor sectors. Equation (11) cancels the forced circle coefficient; it does not establish extinction of that complete pairing.

## Substitution into the fixed-clock pairing

**Next conjecture under test:** the regular circle-jet term is a time divergence in the complete physical current. Its exact finite-domain integration is now available; whether its remaining bulk and contact terms cancel with the regular remainder and other tensor sectors is unresolved.

Use the actual finite clock `T_V,B_V,E_V` from equation (8) of the source-only horizon construction. Write

```
kappa_s(q)=K_(s,0,a)(exp q),
J_s(q)=coexact(M_(exp q)Q_s),
R_s(q)=coexact(the signed regular radial remainder in (11)).
```

Thus the full-angular version of (11) is

```
A k_s(q)=2 kappa_s(q)(J_s'(q)-J_s(q))+R_s(q),  A=D-2.
```

For the circle-jet contribution to the symmetric double integral in (8), integration by parts in the corresponding delay variable gives

```
W_t(q,r)=-2[kappa_t(r) partial_r B_V(q,r)
             +(kappa_t'(r)+kappa_t(r))B_V(q,r)],
W_s(q,r)=-2[kappa_s(q) partial_q B_V(q,r)
             +(kappa_s'(q)+kappa_s(q))B_V(q,r)].
```

The upper-delay edge terms vanish: the literal clock and its derivatives are zero at and before time zero, hence `B_V(q,V)=B_V(V,r)=0`. The lower edges combine with the original source contacts. Define the effective contact fixed by that combination,

```
S_hat_s=S_s+2 kappa_s(0)J_s(0),
kappa_s(0)=-a²[A I_1+kB I_3].
```

The original finite horizon expression becomes exactly

```
integral_0^V integral_0^V
  [ W_t(q,r) inner(k_s(q),J_t(r))
   +W_s(q,r) inner(k_t(r),J_s(q))
   +B_V(q,r){inner(k_s(q),R_t(r))+inner(k_t(r),R_s(q))}
   +E_V(q,r)b_Omega(k_s(q),k_t(r))/2 ] dq dr

 -integral_0^V
   [ B_V(q,0)inner(k_s(q),S_hat_t)
    +B_V(0,q)inner(k_t(q),S_hat_s) ] dq

 +integral_0^V
   [ -E_V(q,0)inner(k_s(q),S_t)/2
     +E_V(0,q)inner(k_t(q),S_s)/2 ] dq.                    (13)
```

The edge signs use `partial_q T_V=-B_V-E_V/2` and `partial_r T_V=B_V-E_V/2`. Thus the source contact is changed by the *derived* lower-edge term; it is not freely adjustable. The same effective contact appears on both branches, and all finite-terminal-time and angular Green terms remain explicit.

The radial coefficient in `W_s` is elementary. With `b=(exp q-1)/(exp q+1)`, differentiation of the exact original-source tail gives

```
kappa_s'(q)=(a²/2)b(1-b)(1+b)^(2s+1)[A+kB b²].           (14)
```

Equations (13)–(14) remove derivatives of the circle mean from the double integral and put them on the known clock and source tail. They are analytical identities for the constructed full-angular candidate on finite domains. They do not assert physical admission, the infinite-time/cusp interchange, or vanishing of (13). The remaining direct cancellation test is now the bulk combination containing `W_s,W_t,R_s,R_t`, the two derived effective contacts, and the independent SS/SV/VV action contributions.
