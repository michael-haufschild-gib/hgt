# HB: native angular kernel in the complete source pairing

Status: native full-source circle average, interior Riemann kernel, first right characteristic jet and original-coordinate source-normal contacts formalized. Higher characteristic jets, complete two-leg distribution contacts and the retained AdS master trace are proved on paper. Complete physical pairing and RH remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Direct cancellation target

The [common source and complete current](hb-mixed-complete-current.md) reduce the next calculation to the common producer on both legs of the causal Green kernel, with all derived contacts and boundary terms retained. The scalar Legendre kernel alone does not identify its action on the full theta half-square. The present target is the actual angular averaging identity needed in that pairing.

For the actual source `Q=fullSquarePotential q` and original upper-half-plane point `(X,Y)`, define

```
C=cosh d, S=sinh d, D=C-S cos theta,
A=S sin theta/D, B=1/D,
circle(d,theta;X,Y)=(X+Y A,Y B),
m(d;X,Y)=(1/(2pi)) integral_0^(2pi) Q(circle(d,theta;X,Y)) dtheta.
```

`D>0` at every real radius and angle. The actual field is smooth on every such circle, including radius zero; no cusp cutoff is needed to define this finite average.

## Conjecture and paper derivation

The original half-square average satisfies the full hyperbolic Darboux equation and commutes with the original scalar Laplacian. For `F(d,theta)=Q(circle(d,theta))`, the denominator-cleared polar identity is

```
S² F_dd+S C F_d+F_theta_theta=S² (Delta Q)(circle).       (1)
```

The base-point Laplacian has an equally explicit correction:

```
Delta_(X,Y) F-(Delta Q)(circle)
  =-2Y partial_theta[Q_X(circle)].                         (2)
```

Equation (2) follows from `1+A²-B²=-2 A_theta` and `2AB=-2 B_theta`. Both angular derivatives in (1) and (2) have zero period integral by actual endpoint equality. Differentiation under the compact circle integral then gives

```
S² m_dd+S C m_d=S² Delta_(X,Y) m,
m(0;X,Y)=Q(X,Y).
```

This is a source-level identity with the complete `Delta Q`; the square is not assigned an angular eigenvalue. Transfer to `Z=cosh d` gives the required Legendre-form angular kernel in the interior `Z>1`. The interior equation, characteristic value and first right derivative are formalized and audited. The all-orders characteristic regularity proof below is analytical; full causal forcing admission and the complete pairing remain open.

## Constructive characteristic regularity and exact contact jets

Apply the same circle derivation to each actual smooth field `Delta^j Q`. Every such field is smooth on the upper half-plane: the original theta half-square has every finite derivative there, and the scalar Laplacian has smooth coefficients. On a compact radius interval, all circles stay in a compact subset of the upper half-plane. Their averages and radial derivatives therefore exist and are continuous at radius zero. These statements concern finite circles; they assert no uniform estimate as the base point approaches the cusp.

Write `m_F(d)` for the mean of such a field, and `M_F(Z)=m_F(arcosh Z)` for `Z>=1`. In divergence form, the Darboux equation is

```
(sinh(d) m_F'(d))'=sinh(d) m_(Delta F)(d),  d>0.
```

Integrate from a positive lower radius and let it tend to zero. Smoothness of `m_F` makes the lower flux tend to zero. Substituting `Z=cosh d` gives the exact formula

```
(Z²-1) M_F'(Z)=integral_1^Z M_(Delta F)(a) da,  Z>1,
M_F'(1+h)=1/(2+h) integral_0^1 M_(Delta F)(1+t h) dt, h>0.    (4)
```

The second expression has a continuous limit at `h=0`. Integrating it back to the continuous value `M_F(1)=F` proves the right derivative there; it does not assume differentiability of `arcosh` at one. Applying (4) simultaneously to every `Delta^j Q` proves right smoothness by induction: continuous means give continuous first derivatives, and `C^n` means give `C^n` right sides in (4), hence `C^(n+1)` means. The same compact argument permits arbitrary base-point derivatives throughout.

Thus the original operator equation can be differentiated up to the characteristic. With `J_n(F)=partial_Z^n M_F(1)`, its exact recurrence is

```
J_0(F)=F,
J_(n+1)(F)=[Delta-n(n+1)]J_n(F)/[2(n+1)],
J_1(Q)=Delta Q/2,
J_2(Q)=Delta(Delta-2)Q/8.                                 (5)
```

For the recurrence, differentiate `(Z²-1)M_F''+2Z M_F'=Delta M_F` exactly `n` times and evaluate at one. The surviving coefficients are `2(n+1)` and `n(n+1)`. No convergent Taylor series is claimed. The finite second Taylor remainder, for `h>=0`, is

```
M_Q(1+h)=Q+h Delta Q/2
 +h² integral_0^1 (1-t) partial_Z² M_Q(1+t h) dt.           (6)
```

Equation (5) identifies the second characteristic jet with one eighth of the angular operator `Delta(Delta-2)` occurring, with its orientation sign, in the coexact mixed symplectic pairing. This fixes a contact coefficient in the two-leg transfer. It does not prove cancellation of the remaining interior integral or the complete physical pairing. The full statements (4)–(6), including all-orders regularity, remain paper proofs. The first-jet case `J_1(Q)=Delta Q/2` is formalized by the shorter argument below.

### Formal first-jet proof and original-coordinate contacts

The actual Laplacian circle mean is continuous at radius zero by compact domination. Divide the already proved radial Darboux identity by `sinh d` for `d!=0` and take the limit at zero: radial smoothness gives `m'(0)=0`. Consequently `m'(d)/sinh d` tends to `m''(0)`. Dividing the Darboux identity by `sinh(d)^2` and taking the limit then gives `2m''(0)=Delta Q`. Composition with `arcosh` from the right and extension of the derivative from the open interval prove the actual first right characteristic jet.

For positive ingoing delay `h`, write `R(h_static,x,y)=nativeRiemannKernel q h_static x y X k`. The exact source-normal traces in the original causal coordinates are

```
partial_y^+ R(h-x+y,x,y) at y=x-h/2
 =sinh(h/2)/(cosh x cosh(x-h/2)) Delta Q,

partial_y^+ R(h-x+y,x,-y) at y=-h/2
 =sinh(h/2-x)/(cosh x cosh(h/2)) Delta Q,  x<=0.
```

The proof establishes the actual invariant's maps into `Z>=1`; it does not impose these derivatives as boundary assumptions. These are traces of the Riemann kernel, before the master factor `-1/(2uw)` and source measure are applied. All five new identities are documented in the [formal characteristic-contact scope](../3-formalized/hb-native-characteristic-contacts.md).

## Two-point transfer exposed by the common producer

At fixed ingoing times, write `u=-tanh x`, `w=-tanh y`, `h=v-v'`, `C_h=cosh h`, `S_h=sinh h`. The direct/reflected invariant is

```
Z_epsilon=C_h+S_h(u-w)+(epsilon-C_h)uw, epsilon=1 or -1.
Z_u Z_w=(epsilon-C_h)(Z+epsilon).
```

The original master Green kernel has radial factor `-1/(uw)` times the scalar wave kernel. Conjugating the actual common-source transpose by `1/u` yields

```
P_dagger(R/u)=[a(u)R+b(u)R_u]/u,
a(u)=A0+3Ku+(C+K)u², b(u)=Ku²(1+u),
A0=(5lambda-6)/4,
C=((4lambda+1)(lambda+2)-(lambda+4)Delta)/8,
K=(7lambda-2-2Delta)/8.
```

On each smooth kernel region its two-leg action is therefore

```
a(u)a(w) M_Z
+[a(u)b(w)Z_w+b(u)a(w)Z_u+b(u)b(w)Z_uw] partial_Z M_Z
+b(u)b(w)Z_u Z_w partial_Z² M_Z.                          (3)
```

The characteristic indicators also differentiate. For positive ingoing delay, put `b=tanh(h/2)`: the direct source interval is `0<=w<=(u+b)/(1+ub)`, the image interval `0<=w<=b`. Both upper endpoints have `Z=1`. Moving-endpoint terms and the previously derived action contacts must be combined explicitly; (3) describes the smooth interior only and is not a vanishing theorem.

## Two-leg characteristic contacts: conjecture and direct differentiation

To keep the endpoint and operator coefficients distinct, write `eta=tanh(h/2)`, `T(u)=(u+eta)/(1+eta*u)`, and retain `a,b` for the operator in (3). At positive delay and interior target radius, the direct causal factor is `H(T(u)-w)M_Q(Z_+)`; the image factor is `H(eta-w)M_Q(Z_-)`. Here `H` denotes the characteristic step. All formulas below are local distribution identities in the open radial square; exterior radial endpoints still contribute separately when integrating the complete physical domain.

Apply `(a(u)+b(u)partial_u)(a(w)+b(w)partial_w)` and put every delta coefficient at `w=T`. With `J_1(Q)=Delta Q/2`, the direct result is the step times the smooth expression (3), plus

```
delta(T-w) * {
  [b(u)T'(u)a(T)-a(u)b(T)-b(u)T'(u)b'(T)]Q
  +b(u)b(T)T'(u)Z_w(u,T) J_1(Q)
}
-delta'(T-w) * b(u)b(T)T'(u)Q.                           (7)
```

The prime on delta differentiates its displayed argument, so `b(w)delta'(T-w)=b(T)delta'(T-w)+b'(T)delta(T-w)`. This fixes the sign of the third term in braces. Tangency gives `Z_u(u,T)+T'(u)Z_w(u,T)=0`; the full first-jet boundary contribution reduces to the single term displayed in (7).

For the image, its endpoint is independent of `u`, and its entire local characteristic contact is

```
-delta(eta-w) a(u)b(eta)Q.                               (8)
```

Thus the direct-minus-image kernel has (7) minus (8). At the AdS target `u=0`, `b(0)=0`, `a(0)=A0`, and `T(0)=eta`: these contact distributions cancel for the conjugated scalar kernel, together with its already proved value. The original master inverse also carries `-1/(2uw)`. Its boundary value therefore requires the first coefficient in `u`, not just the scalar value at zero. The next calculation retains that coefficient.

The calculation shows that the two-leg contact coefficients require only the original value `Q` and first right jet `Delta Q/2`; the second right jet controls regularity of the smooth interior expression. The actual first right jet and original-coordinate source-normal traces are formalized. Distribution identities (7)–(8) and their use with the original source and measure factors remain analytical.

## Retained AdS master trace and its complete producer action

Keep positive delay `h`, `eta=tanh(h/2)`, `S_h=sinh h`, `Z_0=cosh h-S_h w`, and `H=H(eta-w)`. In the open source interval `0<w<1`, the original master kernel is

```
G(u,w)=-[H(T(u)-w)M_Q(Z_+)-H(eta-w)M_Q(Z_-)]/(2uw).
```

The two smooth arguments differ by `2uw`, and `T'(0)=1-eta²`. Differentiate their numerator at zero as a distribution in `w`; the smooth difference contributes `2w H partial_Z M_Q(Z_0)`, and the moving step contributes `(1-eta²)delta(eta-w)Q`. Since `(1-eta²)/(2eta)=1/S_h`, the full trace is

```
G_AdS(w)=-H partial_Z M_Q(Z_0)-delta(eta-w)Q/S_h
        =(1/S_h)partial_w[H M_Q(Z_0)].                    (9)
```

This is the master boundary value after the original radial conjugation, with the causal factor `1/2` retained. It is an exact local distributional limit; no source radial endpoint or cusp integration has been performed.

The original radial transpose, before conjugation by `1/w`, is

```
P_dagger=tilde_a(w)+b(w)partial_w,
tilde_a(w)=A0+4Kw+(C+2K)w²=a(w)+b(w)/w.
```

At the target boundary its action reduces to `A0`, because the master kernel has a smooth distribution-valued extension in `u`, and its derivative coefficient is `O(u²)`. Applying the source transpose to (9) gives the complete two-producer trace

```
A0 * {
 H [b(w)S_h partial_Z² M_Q(Z_0)-tilde_a(w)partial_Z M_Q(Z_0)]
 +delta(eta-w)[b(eta) Delta Q/2
               +(b'(eta)-tilde_a(eta))Q/S_h]
 +delta'(eta-w)b(eta)Q/S_h
}.                                                       (10)
```

The delta coefficient includes the first characteristic jet, the derivative of `b`, and the shifted endpoint of the smooth part. Taking only the limit of (7) misses that last contribution. Equation (10) is the two-producer trace before the derived scalar angular-current weight `-Delta(Delta-2)` is applied; transferring that weight still retains its cusp Green boundary. Equations (9)–(10) are constructive boundary data for the complete pairing; they are not a claim that its AdS Einstein flux is nonzero or that the other boundaries cancel.

For finite ingoing time and a compact angular region, the candidate causal scalar response is smooth in `u>=0` and vanishes at `u=0`: use the paper-proved right smoothness of the native mean and smooth moving endpoints in its finite causal integral. Dividing this response by `u` and taking its original coexact angular derivative gives a smooth master `Psi`. In ingoing coordinates the actual mixed radial current is

```
omega_r=u²[(Psi_v-(1-u²)Psi_u) dot(A Phi-S_Phi)
           -(Phi_v-(1-u²)Phi_u) dot(A Psi-S_Psi)].         (11)
```

The temporal terms in (11) follow from `partial_r|t=-u² partial_u|v+(1/f)partial_v` and are retained. All bracketed terms of these finite-time candidate fields have finite AdS limits, including the original source. Thus this constructed current tends to zero at AdS. This finite-time conclusion does not exchange the AdS, infinite-time or cusp limits, and it does not identify the candidate with the original admitted physical response. The master trace (9) remains part of that identification and of any subsequent source integration. The distributional limits, smooth causal integral, divided master regularity and current limit in this section are paper proofs, not yet formalized.

## Formal scope

Four installed modules, `ThetaCuspHawkingBMNativeCircleChart`, `ThetaCuspHawkingBMNativeCircleSource`, `ThetaCuspHawkingBMNativeCircleMean`, and `ThetaCuspHawkingBMNativeCircleRiemannKernel`, prove the native circle geometry, actual source derivatives, compact-average Darboux and Laplacian-commutation identities, actual interior wave equation, original-source characteristic value and reflected AdS cancellation. See the [formalized scope](../3-formalized/hb-native-circle-riemann-kernel.md).

The two further modules `ThetaCuspHawkingBMNativeCharacteristicContact` and `ThetaCuspHawkingBMNativeCausalSourceContacts` prove the actual first right jet, its interior derivative limit and the two original-coordinate source-normal traces. Every module received only an exact leaf build with existing dependencies frozen. All 26 public theorems across these six modules report exactly `propext`, `Classical.choice`, and `Quot.sound`; only the five new theorems were axiom-checked in the contact audit. All imports are wired without building the umbrella.

The two-leg interior expression (3), full Volterra and higher-jet statements (4)–(6), distributional contacts (7)–(8), retained master trace (9)–(10), candidate AdS current limit (11), physical inverse identification, full-domain integration, cusp limits and complete polarization pairing remain outside these Lean results. In (4)–(6), boundary derivatives are right derivatives on `Z>=1`; no ordinary derivative of the totalized `Real.arcosh` composition at one is asserted.
