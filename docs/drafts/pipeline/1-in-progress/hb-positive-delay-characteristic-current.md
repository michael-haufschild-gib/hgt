# HB: positive-delay characteristic source/current balance

Status: analytical conjecture/proof loop. Complete physical extinction and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains the complete physical current cancellation. The [zero-delay radial contact](hb-zero-delay-current-match.md) is now explicit. This card attacks the remaining positive-delay direct and image contacts and their comparison with the physical cross-currents in the [finite-clock transfer](hb-reduced-source-clock-transfer.md).

## Conjecture: joint characteristic transport assembles the remaining contacts

For a positive delay `h`, put `beta=tanh(h/2)` and `W_h(u)=(u+beta)/(1+beta*u)`. The direct characteristic is `w=W_h(u)`, with `0<=u<=1`; the image characteristic is `w=beta`. Both use `dw/dh=(1-w²)/2`. Their original native-kernel normal derivatives are respectively `w-u` and `u+w`.

Use the actual source weights `p_s=u(1+u)^(2s)`, `B_s=p_s b_s`, `b_s=2k_s u(3+delta*u)/(1+u)`, with `t=-s-3`. Their primitives `I_s(u)=integral_0^u p_s`, `J_s(u)=2k_s u³(1+u)^(2s)`, and `K_s(u)=integral_0^u xB_s(x)` are the original functions in `RHTower.D4BMZeroDelayCurrent`.

At a characteristic, the corrected source bracket has zeroth-jet density

```
exp(2s h)*[(alpha_s p_s(u)B_t(w)-alpha_t B_s(u)p_t(w))*J_V(h)
 +B_s(u)B_t(w)*((2s+6)*J_V(h)-J_V'(h)-E_V(h))]
```

and first-jet density

```
exp(2s h)*B_s(u)B_t(w)*Z_h*J_V(h)/2.
```

Each is multiplied by `(1-w²)/2` when the original `w` integral is written in `h`. Take direct minus image, then subtract the reversed ordered branch. The actual outer angular `RQ` and `R Delta Q`, the physical source normalization and all other current faces remain attached.

The candidate mechanism is a bilinear identity for the transported source primitives on this complete direct-minus-image domain. It must produce the physical cross-current traces, not an independently assigned zero.

## One-coordinate primitive test

The earlier candidate of a primitive `r0(q)J_V(h(q))+r1(q)J_V'(h(q))` along one optical radial coordinate does not close by itself. On the direct sheet, `u=q-d`, `w=(q-L)/L`, `a=d-1`, and `h'= -a/(q(q-a))`. If the density coefficients of `J,J',J''` are `D0,D1,-D2`, the highest two jets force `r1=-D2/h'` and `r0=(D1-r1')/h'`. A residual `D0-r0'` remains. At the actual `u=0` edge its first-jet compatibility involves `alpha_s-12k_s*d/(d-1)`, so dropping that residual would lose boundary data. No no-go theorem or route retirement is claimed: the joint characteristic/physical-current problem is the retained target.

## Verification scope

The displayed characteristic transport and source bracket are analytical identities under inspection. No new Lean result is claimed by this card. Existing zero-delay theorems are reused without rebuilding or re-auditing them.

## Common period of the direct characteristic contacts

The next constructive conjecture is that the five radial contact moments have a common scalar period, so their cancellation can be compared by coefficients and explicit endpoints. The following analytical reduction establishes that statement; its use in the complete physical current remains open.

Fix `h>0`, put `c=exp(-h)`, `a=1-c`, `delta=2s+3`, `t=-s-3`, and use

`r=(1+c+a*u)/2`, with `(1+c)/2 <= r <= 1`.

In particular `0<c<r`. Define the affine polynomials

```
A = 2r-1-c
B = (1+c)r-2c
Cs = 2delta*r+3-delta-(3+delta)c
Ct = (3-delta-(3+delta)c)r+2delta*c.
```

On the direct characteristic, `u=A/a`, `w=B/(a*r)`, and

```
1+u = 2(r-c)/a
1+w = (1+u)/r
dw/dh = 2c(1-r)(r-c)/(a^2 r^2)
(w-u)/2 = (1-r)(r-c)/(a*r).
```

All complex powers here mean `exp(exponent * log(positive real base))`; no branch crossing occurs. Since `2s=delta-3` and `2t=-delta-3`,

`exp(2s*h) fs(u) ft(w) = c^(3-delta) (1+u)^(-6) r^(delta+3)`.

Multiplication by `u*w*(dw/dh)*du` gives the base measure

`c^(4-delta) * a/16 * r^delta * (1-r) A B /(r-c)^5 dr`.

The actual onset multipliers become

`bs(u)=ks*A*Cs/(a*(r-c))`, `bt(w)=kt*B*Ct/(a*r*(r-c))`.

Consequently, the moments obtained by inserting `1`, `bs`, `bt`, `bs*bt`, and `bs*bt*(w-u)/2` into the base measure share the factor

`c^(4-delta)/(16a^2) * r^(delta-2)/(r-c)^7 dr`,

with respective polynomial numerators

```
P00  = a^3 r^2 (1-r) A B (r-c)^2
P10  = a^2 ks r^2 (1-r) A^2 B Cs (r-c)
P01  = a^2 kt r   (1-r) A B^2 Ct (r-c)
P11  = a ks*kt r (1-r) A^2 B^2 Cs Ct
Pjet = ks*kt (1-r)^2 A^2 B^2 Cs Ct (r-c).
```

Their degrees are at most nine. This is a change of variables in the original contact densities, with both onset factors retained.

Write `nu=delta-2`, `r0=(1+c)/2`, and

`Ij(nu,c) = integral[r0,1] r^nu/(r-c)^j dr`.

Polynomial division at `r=c` expresses each `P/(r-c)^7` as a polynomial of degree at most two plus `sum[j=1..7] aj/(r-c)^j`. For `j>=2`, direct differentiation gives

```
d/dr [r^(nu+1)/(r-c)^(j-1)]
 = (nu-j+2) r^nu/(r-c)^(j-1)
   -(j-1)c r^nu/(r-c)^j.
```

Integration therefore proves the terminating recurrence

```
Ij = (nu-j+2)/((j-1)c) * I(j-1)
     - [r^(nu+1)/(r-c)^(j-1)](r0,1)/((j-1)c).
```

Only nonzero `c` and positive integers are divided out. The coefficient of the single remaining period `I1` is

`a1 + sum[j=2..7] aj * product[k=1..j-1] (nu-k+1)/(k*c)`.

The polynomial part integrates to endpoint powers. At exponent `-1` its primitive is `log r`; elsewhere it is `r^(exponent+1)/(exponent+1)`. Thus the reduction covers every complex frequency without imposing a spectral nonresonance assumption.

If these five original moments are named `I00,I10,I01,I11,Ijet`, the direct zeroth contact is exactly

`[alpha_s*I01-alpha_t*I10+(2s+6)*I11] J_V - I11*(J_V'+E_V)`;

the first circle-mean jet contributes `Ijet*J_V`. The physical normalization and angular operators from the contact formula above remain to be applied. The reversed ordered branch has `delta` replaced by `-delta`.

## Frequency-independent clock equation for that period

There is a further useful reduction. Differentiating the moving-endpoint integral gives

`dI1/dc = I2 - r0^nu/(2*(r0-c))`.

This differentiation is valid locally at every `0<c<1`: the integration interval stays uniformly away from both zero and the pole, so the integrand and parameter derivative are bounded on a surrounding compact rectangle. Using the `j=2` recurrence and `r0-c=(1-c)/2` yields

`c*dI1/dc = nu*I1 + (r0^nu-1)/(1-c)`.

Define the period with its actual source prefactor,

`F_delta(h) = c^(4-delta) I1(delta-2,c)`.

Since `dc/dh=-c`, the frequency terms cancel and give the exact analytical identity

`(d/dh+2) F_delta(h) = c^(4-delta) * (1-r0^(delta-2))/(1-c)`.

For formalization, the substitution `r=c*z` removes the parameter from the integrand:

`F_delta(h) = exp(-2h) * integral[(exp(h)+1)/2, exp(h)] z^(delta-2)/(z-1) dz`.

Both endpoints are strictly greater than one. The interval-integral fundamental theorem at the two endpoints, followed by the product rule, proves the same clock equation without differentiating a parameter-dependent density.

The remaining period therefore has universal homogeneous clock rate `-2`; its forcing contains only endpoint powers. This does **not** prove that its coefficient in the complete current vanishes. The next cancellation test is to compare this coefficient, its clock derivative, and the endpoint forcing against the physical cross-currents, with the image contact, terminal face and angular cusp face retained.

## Regular clock realization and the retained lower endpoint

The fixed-interval realization is

`R_delta(h)=exp(-2h) integral[1/2,1] (1+(exp(h)-1)y)^(delta-2)/y dy`.

Its power base is positive for every real `h` and every `1/2<=y<=1`. For `h>0`, the affine substitution `z=1+(exp(h)-1)y` proves `R_delta=F_delta`. It also makes the lower clock contact explicit:

```
R_delta(0) = log 2
R_delta'(0) = (delta-2)/2 - 2 log 2
(d/dh+2)R_delta(h)
 = (delta-2) exp(-h) integral[1/2,1] (1+(exp(h)-1)y)^(delta-3) dy.
```

The integral on the right is regular at zero. The unextended moving-endpoint integral has identical endpoints at `h=0` and hence value zero there; that assigned value must not replace its positive-delay limit in integration by parts. The regular realization retains the original limit `log 2` and its frequency-dependent first derivative.

## Explicit finite coefficient test for the original contact

The coefficients can be written without the apparent `1/(1-c)^2` singularity of the common-denominator representation. Set `x=1+u`,

```
D(x)=c+(1-c)x/2
b=(1-c)/(2c)
L(x)=delta*x+3-delta
T(x)=(3+delta)D(x)-delta*x.
```

For a polynomial `P`, define the finite coefficient functional

`H(alpha,n,P)=[x^n](P(x)*(1+b*x)^alpha)`.

This notation involves only the first `n+1` Taylor coefficients: explicitly it is `sum[k=0..n] P_k * binomial(alpha,n-k) * b^(n-k)`, where the generalized binomial coefficient is the falling product divided by the integer factorial. No evaluation or numerical experiment is needed.

The coefficients of `F_delta` in the five original moments are analytically

```
C00  = c^2/2 * H(delta,4,(x-1)(x-D)(2-x))
C10  = ks*c^2 * H(delta,5,(x-1)^2(x-D)(2-x)L)
C01  = kt*c * H(delta-1,5,(x-1)(x-D)^2(2-x)T)
C11  = 2ks*kt*c * H(delta-1,6,(x-1)^2(x-D)^2(2-x)L*T)
Cjet = ks*kt * H(delta-2,5,(x-1)^2(x-D)^2(2-x)L*T*(1-D)).
```

To derive them, write the original base density in `x` as

`c^4/2 * (x-1)(x-D)(2-x) * x^(-5) * (1+b*x)^delta dx`.

The two onset multipliers are `2ks(x-1)L/x` and `2kt(x-D)T/(D*x)`; the first-jet multiplier is `x(1-D)/(2D)`. Multiplying these factors gives the five displayed coefficient formulas. The coefficient of `x^(-1)` in each density is its residue at this auxiliary pole. The normalized period has residue `c^2`, whereas derivatives of the endpoint primitives have zero residue there. Dividing by `c^2` therefore gives precisely its period coefficient. This is a local analytic residue, not an integration contour through the physical domain.

All five coefficient functions are finite expressions regular at `c=1`. Let

`C_Q=alpha_s*C01-alpha_t*C10+(2s+6)*C11`,

and let `D_delta=(d/dh+2)R_delta` be the regular forcing above. On any compact positive-delay interval, the zeroth-jet period contribution satisfies

```
integral [C_Q*R_delta*J_V-C11*R_delta*J_V']
 = -[C11*R_delta*J_V] at the endpoints
   + integral [(C_Q+C11'-2C11)*R_delta+C11*D_delta]*J_V.
```

The original additional term `-C11*R_delta*E_V` and first circle-mean jet `Cjet*R_delta*J_V` remain. The lower-endpoint limit uses `R_delta(0)=log 2`. Thus the next signed comparison has explicit finite coefficient functions, a regular clock forcing and a fixed lower contact. Cancellation of these expressions against the physical bulk and cross-currents has not been established. The five coefficient formulas and this full-current comparison are analytical, not Lean-verified.

## Corpus ingredients inspected for this attack

- `HTGeometry/EulerPolePartCalculus.lean` supplies the triangular Euler action on successive pole parts. The displayed finite-interval recurrence is its analytic counterpart; the existing pole-part theorem alone does not establish the integral identity.
- `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`, `integral2_divergence_prod_of_hasFDerivAt_off_countable`, retains all four oriented rectangle faces. Application still requires the actual current's regularity, integrability and characteristic coordinate transport.
- `RHTower/SelbergModularCurrentGreen.lean`, `current_green_identity`, proves the full Green formula on the compact modular domain for arbitrary C1 real planar currents, including the side jump, top face and both circular normal densities. The proof uses the two domain-slice descriptions and one-dimensional FTC; it assumes no Maass eigenvalue or vanishing boundary flux. Complex physical currents require applying it to their real and imaginary parts and proving the physical smoothness conditions.
- The broad Darboux/transmutation search found `ThetaCuspHawkingBMPeierlsDarbouxOrbitOpticalTransgression`. Its documented result identifies optical power with a helicity-mixing invariant; it supplies no vanishing theorem for the forced current. No extra stationarity premise is introduced here.

These ingredients were retrieved with hybrid and deep corpus searches, broad OR queries, quoted phrases, module-filtered follow-ups and an uncapped module result count. The returned source arguments were inspected alongside candidate lemmas. The optical follow-up returned an unverified ingredient set proposing susceptibility scaling and nonnegative mixing energy; that set does not derive a signed current cancellation. Search inventory covered 55,915 files, but semantic coverage and source/compiler freshness were partial. Empty proof-idea sections are not evidence that an ingredient is absent from the corpus.

The new period and clock reductions are analytical work, not Lean-verified results. No mathematical computation, frontier-map edit, launcher invocation, Git command or old-module axiom audit was used for these reductions.
