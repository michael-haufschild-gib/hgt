# HB: source reduction of the complete finite QNM action

Scope: evaluate the original complete temporal/metric/QNM action, then compare
it with the physical source receiver. The frontier map remains read-only.

**Status.** The compact two-frequency identity and its diagonal limit are
Lean-verified in `ThetaCuspHawkingBMOriginalSourceResolvent.lean`, including
separate admission of both integrals. The actual two-frequency endpoint brackets pass Lean scratch and isolated
exact module audit in `OriginalSourceResolventEndpoints`. Both whole-domain integral admissions and the full-exterior source-resolvent
identity are Lean-verified in `OriginalWholeSourceResolvent` (scratch and
isolated exact audit passed). The source-derived reader remainder, diagonal continuity, and exact opposite-
branch logarithmic normalization are verified in `OriginalReaderRegularization`.
The complete horizon diagonal equals the original metric finite part in
`OriginalReaderDiagonalMatch` (scratch and isolated exact audit passed). The
whole-domain combined source-difference identity (2a) is Lean-verified in
`OriginalRegularizedSourceResolvent`, including the actual horizon amplitude
and diagonal source admission (scratch and isolated exact audit passed).
`OriginalMetricTemporalDiagonal` identifies its complete metric/temporal
diagonal with the original finite part and corner (scratch and isolated exact
audit passed). `OriginalSourceActionReduction` proves the actual-source Cauchy bound,
admits the source derivative integral, and establishes (2b) and its exact
tortoise-weighted form (scratch and isolated exact audit passed).
`OriginalPhysicalSourceAction` identifies the physical Green/corner
coefficients, the exact native forcing pullback, and the combined elementary
source-action density at either QNM (scratch and isolated exact audit passed).
Continuation of the resulting source formula to the QNM remains to be
formalized; the argument below records its analytical derivation. It does
not establish equality with the unit left-channel extinction receiver or RH.

## Fixed original data

Fix an actual Xi occurrence, source branch and amplitude. Write

```
s = physicalRate q br,
chi = physicalRadialFrequency q,
K = reducedGreenGradient chi s 1,
C = physicalSelfSourceCoefficient q,
mu = physicalAngularParameter q^2 - 1/4,
T(w) = continuedOnset s w,
c(w) = connection w chi,
beta(w) = c(w)/(2*w),
y_w(z) = continuedResponse s chi amp 1 K z w,
n_v(z) = normalizable v chi z,
S_w(z) = continuedSourceProfile s amp 1 K w z,
E(w) = greenHorizonAmplitude s chi amp 1 K w.
```

All source differentiation holds `s,chi,K,C,amp` fixed. Reader differentiation
changes only `v`. In particular, differentiation does not move along the
fundamental-frequency curve while changing the angular parameter.

Put `x(z)=tortoiseOf(z)`, `p=z*sqrt(1-z)`, `rho=1/(2*p)`. The actual source is

```
S_w(z) = exp(w*x(z))*A(z)*T(w),
A(z) = (1+sqrt(1-z))^(2*s)*amp^2 *
       ((5*s^2+15*s+4)/4
        +(1-z)*s*(s-1)*((s+2)^2-K)/4).
```

This follows by expanding the two original powers in `sourceProfile`, using
`x(z)=log(z)/2-log(1+sqrt(1-z))`. Hence

```
partial_w S_w = exp(w*x)*A*(x*T(w)+T'(w)).
```

## Exact source identity before endpoint removal

For the actual jets set `W(w,v,z)=p*(y_w*n_v'-y_w'*n_v)`. The original forced
ODE and homogeneous reader ODE give

```
2*d_z W = (v^2-w^2)*rho*y_w*n_v - n_v*S_w.
```

For every `0<e<=b<1`, Lean proves both integral admissions and

```
(v^2-w^2)*int_e^b rho*y_w*n_v
  = 2*(W(w,v,b)-W(w,v,e)) + int_e^b n_v*S_w.
```

Continuity of the first integral in `v`, proved by dominated convergence,
and holomorphy of both actual reader jets imply the diagonal identity. No
frequency derivative of the evolved response is used.

## Removing the horizon: a regularized two-frequency pairing

Start in a nonreal right convergence chamber with `Re(w)>0` and `c(w)!=0`.
Choose a reader disk about `w` of radius smaller than
`min(Re(w),1,abs(Im(w)))/4`. The actual horizon representation is

```
y_w(z) = z^(w/2)*R(z),          R(0)=E(w),
n_v(z) = a(v)*z^(v/2)*F_v(z) + beta(v)*z^(-v/2)*F_-v(z),
F_v(0)=1.
```

Here `a` is the original `horizonRegularCoefficient`, not an adjustable
normalization. The corpus's `incomingSourcePrimitive_common_data` and
`incomingSourceTransport_uniform_first_bound`, together with the horizon
Gauss series, give `R-E=O(z)` and bounded `R'`. On the closed reader disk,
the Gauss series and its spatial derivative converge uniformly on a smaller
complex spatial disk: the coefficients have bounded parameters, denominators
stay separated from the nonpositive integers, and their ratio tends to the
spatial argument uniformly. Thus `F_v-1=O(z)` and `d_z F_v=O(1)` uniformly.

Let `d=(w-v)/2`, and fix a small positive interface `b`. Define

```
Ireg(v) = int_0^b [rho*y_w*n_v - E(w)*beta(v)*z^(d-1)/2]
        + E(w)*beta(v)*(b^d-1)/(2*d)
        + int_b^1 rho*y_w*n_v,
```

where `(b^d-1)/d` has its removable value `log(b)` at `d=0`.
The incoming integrand is bounded by a constant times `z^(Re(w)-r-1)`;
the subtracted opposite integrand is bounded by a constant times `z^(-r)`
for a sufficiently small `r>0`. Both are integrable. These bounds also give
local continuity, and holomorphy by the corpus's Cauchy dominated integral
argument. At the outer endpoint use `t=sqrt(1-z)`: `n_v=O(t)` and the actual
Dirichlet response is `y_w=O(t)`, uniformly for the reader. Thus the outer
density is `O(t)` and is separately admitted.

At `v=w`, the displayed definition is exactly

```
Ireg(w) = lim_e->0+ [int_e^1 rho*y_w*n_w
                      + E(w)*beta(w)*log(e)/2] = GreenFP(w).
```

The original additional incoming power counterterms vanish in this chamber;
there is no finite constant change. The coefficient of the logarithm agrees
with `normalizableHorizonPairingCutoff` exactly.

For `Re(v)<Re(w)` in the reader disk, the unsubtracted mixed integral is
admitted and

```
int_0^1 rho*y_w*n_v = Ireg(v)+E(w)*beta(v)/(w-v).
```

The actual bracket tends to zero at both endpoints in this region. At the
horizon, its two leading powers are `z^((w+v)/2)` and `z^((w-v)/2)` with
positive real exponents; the remainders gain another power. At the outer
endpoint, the Green representation gives `y_w=t*H+O(t^3)` and
`n_v=t*N_v+O(t^3)`, with the corresponding first jets. Their leading
Wronskian terms cancel and `W=O(t^3)`. These statements use the original
source and both actual endpoint modes.

Writing `J(w,v)=int_0^1 n_v*S_w`, the compact identity therefore yields

```
(v^2-w^2)*Ireg(v) = J(w,v)+(v+w)*E(w)*beta(v).       (1)
```

Both sides are holomorphic on the reader disk, so (1) extends across its
diagonal. Equivalently one can take a real one-sided difference quotient,
using continuity of `Ireg` and holomorphy of the right-hand side. Evaluation
and differentiation at `v=w` give

```
J(w,w) = -2*w*E(w)*beta(w) = -c(w)*E(w),
2*w*GreenFP(w) = partial_v J(w,v)|v=w
                 + E(w)*(beta(w)+2*w*beta'(w)).     (2)
```

This proves the required finite-part identity analytically without exchanging
a derivative with an unsubtracted divergent integral. The first identity
also agrees with `greenHorizonAmplitude_eq_original` and `outerMoment`.

## Direct source difference before the diagonal limit

The global proof can avoid the reader derivative in (2). For nearby chamber
frequencies `w,v`, keep `s,chi,K,amp` fixed and use the literal diagonal
source identity `J(v,v)=-c(v)*E(v)`. Subtract it in (1) before dividing:

```
(v+w)*Ireg(w,v)
 + c(v)*(E(v)-(v+w)*E(w)/(2*v))/(v-w)
 = -int_0^1 n_v*(S_v-S_w)/(v-w).                 (2a)
```

The left quotient has limit `E'(w)+E(w)/(2*w)`. On the right, only the
source varies in the divided difference; `n_v` tends to `n_w`. Uniform
Gauss bounds and the source's complex exponential give an integrable
majorant consisting of a horizon power times `1+abs(log z)`. The outer
endpoint is regular. Thus dominated convergence gives

```
2*w*GreenFP(w)+c(w)*(E'(w)+E(w)/(2*w))
 = -int_0^1 n_w*partial_w S_w.                    (2b)
```

This is the Green action plus its prescribed temporal corner before either
is evaluated separately. It requires continuity of the regularized pairing,
the literal diagonal endpoint integral, differentiability of `E` in the
right chamber, and source divided-difference domination. It does not require
a separate theorem differentiating `J` in the reader or differentiating
`c`. The remaining Lean attack uses (2a)–(2b); (2) remains a consistent
analytical consequence, rather than an extra formal prerequisite.

## Cancellation with the actual temporal corner

### Source divided differences from Cauchy bounds

**Lean verified in `OriginalSourceActionReduction`.** For fixed
`s,chi,K,J,amp` and nonreal `w` with `Re(w)>0` and `w-2*s!=0`, there are
`R,C>0` such that

```
u,v in ball(w,R), 0<z<1  ==>  |n_v(z)*S_u(z)| <= C*z^(-1/2).
```

Choose `R<=1/4` small enough to avoid the source pole and real reader axis.
The existing horizon representation expresses `n_v` as its original
`a(v)*h_v+beta(v)*h_-v`. Both coefficients are continuous and locally
bounded; `horizonGauss_uniform_first_bound` controls both Gauss factors.
The source remainder is jointly continuous on the compact frequency/radius
rectangle, and the unchanged onset factor is locally bounded. The two
products have powers `z^((u+v)/2)` and `z^((u-v)/2)`. Their real exponents
are greater than `-1/2` on the chosen ball, giving the displayed bound on
`0<z<=1/2`. On `1/2<=z<1`, `outerGauss_uniform_bound`, the compact bounds
for the two powers, and the source remainder give a constant bound. Since
`z^(-1/2)>=1`, this extends the same majorant over the full interval.

For fixed reader `v` and radius `z`, the function
`u |-> n_v(z)*S_u(z)` is holomorphic on the source ball. Applying
`Bottcher.norm_sub_le_of_bounded_on_ball` to this actual function gives

```
v in ball(w,R/2), v!=w, 0<z<1  ==>
|n_v(z)*(S_v(z)-S_w(z))/(v-w)| <= (2*C/R)*z^(-1/2).
```

The majorant is integrable. Pointwise, the source divided difference tends
to `partial_w S_w`, and the entire normalizable reader tends to `n_w`.
Dominated convergence therefore gives the source side of (2b), with
`chi,K,J,s,amp` fixed throughout. This route avoids a separate logarithmic
majorant calculation in the convergence chamber. It does not admit the raw
integral at the physical QNM; continuation there still requires the actual
incoming endpoint subtraction described below.

The exact `original_density_native` identity cancels the reduced-response
lift against its retained contact. Consequently the *complete* radial metric
action can be expressed using the full native response and native forcing;
the outer reduced pairing must not be substituted for the full native
`GreenFP` alone.

Its Green coefficient is `2*mu*w*(mu-2)*C`. The Green part of the prescribed
`physicalCornerCandidate` is

```
mu*(mu-2)*C*(c*E/(2*w)+c*E').
```

Since `beta+2*w*beta'=c'-c/(2*w)`, (2) makes their sum

```
mu*(mu-2)*C*(partial_v J+(c*E)')
 = -mu*(mu-2)*C*partial_source_w J(w,v)|v=w.        (3)
```

The chain rule here differentiates both arguments of the diagonal `J(w,w)`.
The remaining partial derivative differentiates only the source. Both are
admitted in the right chamber: the horizon bounds above remain integrable
after a factor `abs(log z)`, and the source is bounded at the outer endpoint.

Changing variables in the *native* forcing gives exactly

```
T(w)*forcingKernel(x(z))*dx = -n_w(z)*S_w(z)*dz/z.
```

Therefore, with `Z(w)=FP int_0^1 n_w*S_w/z` using its actual two power and
logarithmic subtractions, the full action is

```
canonicalAction(w)
 = -mu*C*((mu-2)*partial_source_w J(w,v)|v=w+w*Z(w))
   + mu*c(w)*C*Fforcing'(w)/2.                    (4)
```

The last term is the original forcing temporal corner. It is retained even
in the convergence chamber: the native forcing can have an opposite-mode
logarithmic divergence there.

## Cauchy bound after the actual incoming subtraction

**[BRIDGE] Subtraction and Cauchy derivative bound Lean verified in
`OriginalSourceIncomingSubtraction`; integrated finite-part construction in progress.** Fix a
nonreal centre `w` with `Re(w)>-2` and `w-2*s!=0`, and let `a(v)` be the
actual incoming coefficient of the normalizable reader. For independent
source and reader frequencies define

```
P(u,v,z) = n_v(z)*S_u(z)
           -a(v)*z^((u+v)/2)*R_s(u,0)*T(u).
```

The literal horizon decomposition gives

```
P = a(v)*z^((u+v)/2)*(G_v(z)*R_s(u,z)-R_s(u,0))*T(u)
    +beta(v)*z^((u-v)/2)*G_-v(z)*R_s(u,z)*T(u).
```

Uniform first Gauss and source-remainder bounds control the incoming
parenthesis by `C*z`. A sufficiently small source/reader ball therefore
gives `|P|<=C*(z^(beta+1)+z^(-1/2))` for some `beta>-2` on `0<z<=1/2`.
Both powers are integrable. The source-variable Cauchy derivative bound
preserves this majorant on the half ball, now for `partial_u P(u,v,z)`.
The diagonal derivative is analytic in `w`: factor the incoming term as
`a(v)*z^(v/2)` times its source-only leading profile before differentiating.
Thus Cauchy-dominated holomorphy applies to the actual subtracted source
action throughout the physical strip, without requiring raw-integral
admission there or separate logarithmic majorants.

The differentiated leading coefficient restores the original primitive
with `log(z)/2-log(2)`. Its finite value must be retained when equating this
source continuation with the canonical metric/corner action. This is the
remaining continuation proof mechanism, not an assumed matching identity.

## Continuation and the actual fundamental QNM

The two-frequency source overlap near its diagonal has incoming exponent
`(u+v)/2` and opposite exponent `(u-v)/2`. Subtracting the incoming constant
extends it holomorphically near each nonreal diagonal point with `Re(w)>-2`.
The incoming remainder, including its source derivative, is bounded by
`z^(Re(w)+1)*(1+abs(log z))`. The opposite branch remains locally integrable.
For `Z`, subtract two incoming coefficients and the opposite logarithmic
coefficient. Its remainder has the same integrable power without the source
derivative. Coefficients come from the actual Gauss/source products.

These subtractions agree with (4) in the right chamber and with the original
canonical counterterms: coefficients of the same actual density expansion
are equal, and both prescriptions add the primitive at the lower cutoff
without an additional constant. The source pole lies at `2*s`, whose real
part is below `-2`. The resulting expression is meromorphic on each connected
nonreal half of `Re(w)>-2`. Equality with the original canonical action
extends there by the meromorphic identity theorem.

At `w0=physicalFundamentalFrequency q side`, the source expression is analytic.
The forcing transform is analytic and `c(w0)=0`, so its corner term tends to
zero. Interpret (4) by its limit: raw values of `E` or `c*E` at a connection
zero need not equal their meromorphic extensions.

The exact fundamental identities give `a(w0)=1`, `beta(w0)=0`,
`n_w0=z^(w0/2)*sqrt(1-z)` and `mu=(w0+1)*(w0+2)`. Put
`F(z)=fundamentalSourceCore w0 s amp z`. Equation (4) then gives the proposed
Lean target

```
canonicalQNMValue q br side amp
 = -mu*C*((mu-2)*(T'(w0)*M+T(w0)*X)+w0*T(w0)*Z0),

M  = FP int_0^1 z^w0*F(z),
X  = FP int_0^1 z^w0*F(z)*tortoiseOf(z),
Z0 = FP int_0^1 z^(w0-1)*F(z).
```

Here `M` is the existing `fundamentalSourceMoment`. For `F0=F(0)` and
`F1=d_z F(0)`, the exact counterterms added to integrals from `e` to `1` are

```
M:  F0*e^(w0+1)/(w0+1),
X:  F0*e^(w0+1)*((log(e)/2-log(2))/(w0+1)
                  -1/(2*(w0+1)^2)),
Z0: F0*e^w0/w0+F1*e^(w0+1)/(w0+1).
```

The `log(2)` term is fixed by the original tortoise coordinate. Omitting it
changes the action. Varying `w` in `fundamentalSourceMoment(w,s,amp)` also
varies its substituted gradient; that derivative cannot replace the fixed
source derivative in (3).

## QNM forcing moment by exact integration by parts

**Analytical reduction; Lean proof pending.** At a physical QNM write
`F=fundamentalSourceCore(w,s,amp)`, `F0=F(0)`, `F1=F'(0)`.
The explicit source gives `F(1)=0`, a quadratic Taylor remainder at zero,
and an integrable square-root derivative at the outer endpoint. For
`-2<Re(w)` and `w!=0`, let

```
D = FP int_0^1 z^w*F'(z),
```

with counterterm `F1*e^(w+1)/(w+1)`. At every positive cutoff, integration
by parts gives the exact identity

```
w*(int_e^1 z^(w-1)*F(z)
     +F0*e^w/w+F1*e^(w+1)/(w+1))
 = -(int_e^1 z^w*F'(z)+F1*e^(w+1)/(w+1))
   -e^w*(F(e)-F0-F1*e).
```

The last term tends to zero because the actual source remainder is
`O(e^2)` and `Re(w)>-2`. Thus `w*Z0=-D`, with no constant shift.
The proposed QNM formula is equivalently

```
canonicalQNMValue = mu*C*(T*D-(mu-2)*(T'*M+T*X)).
```

**Whole-route effect:** the shifted-exponent forcing moment can be replaced
by a first-subtracted derivative period. This reduces the source-value
problem to one common Mellin exponent and preserves all original finite
constants. It does not establish the continuation of (4) or extinction.

## Remaining decisive work

Formalize the complete native forcing combination and the same-counterterm
continuation yielding (4). The actual-source Cauchy bound, source derivative
admission, identity (2b), and original tortoise-weighted source formula are
verified in Lean. Then prove or disprove
equality of the resulting explicit three-period value with the physical
unit left-channel source receiver. The current derivation eliminates the
unknown evolved-response derivative; it supplies no extinction implication
by itself.
