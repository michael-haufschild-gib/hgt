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
`OriginalSourceIncomingSubtraction`, `OriginalSourceHorizonFinitePart` and
`OriginalSourceFinitePart` prove the full source derivative continuation for
nonreal `Re(w)>-2`, with the literal cutoff limit and its original power/log
finite constant. It agrees with the ordinary integral in the convergence
chamber (scratch and isolated exact audits passed).
`OriginalNativeSourceFinitePart` proves the native forcing continuation with
all three original counterterms. `OriginalCanonicalSourceAction` proves the
full canonical metric/temporal action equals these source finite parts,
including its unique value at both physical QNMs (scratch and isolated exact
audits passed). The unit left-channel extinction comparison and RH remain open.
`OriginalElementaryQNMAction` also evaluates both incoming forcing
coefficients and proves the complete elementary QNM cutoff limit (scratch
and isolated exact audit passed). The contour/counting obstruction below
remains under development.

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

## Complete source comparison: cutoff and meromorphic uniqueness

**Lean verified in `OriginalCanonicalSourceAction`.** Let `D(w)`
be the full differentiated-source finite part from DN18, and let `N(w)` be
DN19's full native forcing finite part. Both are analytic on each component
of `{Re(w)>-2, Im(w)!=0}`; the physical source pole lies to its left. Define

```
A_source(w) = -mu*(mu-2)*C*D(w) + mu*w*C*T(w)*N(w)
              +mu*c(w)*C*Fforcing'(w)/2.
```

The original monotone radial substitution extends to the outer endpoint
`z=1`. In the genuine chamber the native Green density is admitted on every
`[e,1]`: its outer limit is zero by the proved response boundary and
normalizable boundary ratio. The forcing density has the uniform outer bound
from the actual source profile. Therefore the original complete metric
cutoff splits into its native Green cutoff and its native forcing cutoff.
Use the same small interface for the Green restoration, the original horizon
amplitude and DN15's metric/corner identity. The two cutoff limits give
`canonicalAction(w)=A_source(w)` throughout the chamber, with every original
finite term retained.

Their difference is meromorphic on each nonreal strip component. Its germ
vanishes at a chamber point. Connectedness and the meromorphic identity
principle imply a zero germ at every point of that component, including its
fundamental QNM. Since `A_source` is analytic there, uniqueness of the already
proved canonical QNM limit identifies that value with `A_source(w0)`.
The forcing temporal corner vanishes because `c(w0)=0`. This yields (4)
with `T*N=-FP int n_w*S_w/z`. It leaves evaluation of the source periods and
the extinction comparison as the decisive remaining problem.

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

**DN22, Lean verified.** The canonical value is the limit of the single
integral of `z^w*F(z)*((mu-2)*(tortoiseOf(z)*T+T')+w*T/z)` with the displayed
combined counterterms, multiplied by `-mu*C`. The actual incoming value and
slope equal
`F0=2^(2*s-w)*amp^2*(A+B)` and
`F1=-2^(2*s-w)*amp^2*((2*s-w+2)*(A+B)/4+B)`;
the opposite logarithmic coefficient is zero. This is
`elementaryQNMActionCutoff_tendsto`, not a statement about a raw unsubtracted
integral at the horizon.

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
constants. DN20 establishes continuation of (4); this integration-by-parts
reduction does not establish extinction.

## Remaining decisive work

Evaluate the combined source finite parts in DN20 and prove or disprove their
extinction/nonextinction relation to the physical unit left-channel source
clock. The canonical metric/temporal action and its QNM source continuation
are now identified in Lean. The remaining value retains both the source
derivative (including the original tortoise moment) and the native forcing.
Nonvanishing of the scalar source moment alone cannot settle their possible
cancellation. Angular source collisions remain a separate factor in the
same original action; no RH implication follows from DN20 alone.

## Candidate impossibility test: compact contours and zero counts

**Conjecture under analytical development; not a proved matching obstruction.**
Test the proposed extinction equivalence on critical copies. The corpus proves
`eventually_superlinear_xiSimpleCriticalZeroCount` in
`Zeta23SimpleCriticalDensity`: simple critical zeros have a positive
`T*log(T)` lower bound. `exponentialType_zeroCount_linear` in
`HTGeometry/ExponentialTypeZeroDensity` bounds zeros of a nonzero entire
finite-exponential-type function by `O(T)`. These statements were inspected
in source; their application to the complete action is still unproved.

For the actual `br=side=true` source, `s=-2*w-4`. Set `E(w)=exp(2*pi*i*w)-1`
and `lambda=w-2*s=5*w+8`. The polynomial coordinate `z=x*(2-x)` gives

```
J_n(w,s) = FP int_0^1 x^w*(2-x)^(2*s)*(1-x)^n dx,
M = 2*amp^2*(A*J_2+B*J_4),
Z = 2*amp^2*(A*J_2(w-1,s-1/2)+B*J_4(w-1,s-1/2)).
```

Here `A=fundamentalMomentConstant(s)` and
`B=fundamentalMomentQuadratic(w,s)`. For the tortoise moment, differentiate
only the Jacobi periods, holding these coefficients fixed:
`X=2*amp^2*(A*delta J_2+B*delta J_4)`,
`delta=(1/2)*partial_w-(1/4)*partial_s`.

The candidate contour identity uses the unit circle with the lifted logarithm
`log(x)=i*t`, `0<=t<=2*pi`, and the single analytic branch of `log(2-x)`:

```
H_n(w,s) = int_0^(2*pi) i*exp(i*t)*exp(i*w*t)
              *exp(2*s*Log(2-exp(i*t)))*(1-exp(i*t))^n dt,
E(w)*J_n(w,s) = H_n(w,s).
```

A direct Taylor-series proof below identifies this with the original
subtracted Mellin periods, including their finite constants. Let `H_M`
and `H_Z` be the displayed polynomial combinations of `H_n`; let `H_X`
insert the bounded contour weight `(i*t-Log(2-exp(i*t)))/2`, still holding
`A,B` fixed. Differentiating the monodromy factor retains the essential term

```
E^2*X = E*H_X-pi*i*exp(2*pi*i*w)*H_M.
```

With `Theta0=lambda*T` and `Theta1=lambda^2*T'`, the proposed entire
numerator of the complete radial action is

```
G = (mu-2)*(Theta1*E*H_M
      +lambda*Theta0*(E*H_X-pi*i*exp(2*pi*i*w)*H_M))
      +w*lambda*Theta0*E*H_Z,
G = E^2*lambda^2*((mu-2)*(T'*M+T*X)+w*T*Z).
```

Every contour is compact and avoids `x=0,2`; the cleared onset and its
fixed-source derivative are compact transition transforms plus polynomials.
This supplies a concrete route to global finite exponential type after
substituting `s=-2*w-4`. Nontriviality should follow from the removable
`w=0` value of the radial expression: `mu=2`, `w*Z -> F(0)`,
`F(0)=51/256` for unit amplitude, and `T(-4,0)>0` from the fixed positive
onset. DN24 closes the scalar contour identity and its affine entirety/growth in Lean. DN25 closes the logarithmic contour identity, the complete candidate numerator, its nonzero pole anchor and linear zero count. Attachment to the original cutoff remains open.

Angular cancellation cannot be discarded. **DN23, Lean verified:**
`physicalSelfSourceCoefficient_fourLambda_closedHalfPlane` extends the actual
four-Lambda formula to `Re(rho)>=1/2`. Thus critical angular
collisions lie on the `Re=1/4` or `Re=3/4` Xi lines at heights scaled by
`1/2,3/2,5/2`. The corpus's
`Sieve.exists_eventually_zetaLittlewoodZeroCountAbove_le_linearExponent`
has exponent `(16/5)*(1-sigma)` and fixed polylogarithmic loss for
`7/10<=sigma<1`; at `sigma=3/4` this is `4/5`. A precise reflected affine
counting injection would make those collisions sublinear. The resulting
`O(T)+o(T)` exceptional set could not cover the critical census.

**Whole-route test:** if all these obligations close, some actual critical
copy has nonzero complete canonical action, disproving the proposed
critical-wall extinction equivalence. This is an attack on the full action,
including its source amplitude, rather than on a selected scalar term.
No such impossibility theorem is currently claimed.

The inspected strict-right restriction has a precise arithmetic origin:
`NativeFourierDirichletValue.nativeRamanujanChamber` packages
`a=b=-2*center(q)` in `D4BMNegativeDivisorShift`. The earlier Bessel/Fourier
integral identity and the three-moment modular assembly already allow every
actual Xi copy. At a critical copy, keep `q` and the testing parameter fixed
and approach its purely imaginary divisor shift by `a_epsilon=a-epsilon`.
The negative-shift four-zeta theorem then applies for every `epsilon>0`.
The divisor-square majorant is independent of epsilon because
`Re(a_epsilon)<=0`; with `Re(w)>2`, dominated convergence of the absolutely
convergent Dirichlet series should give the critical-shift identity. All four
zeta arguments and the denominator stay in their zero-free convergence
chamber. This would extend the angular formula using the existing
test-parameter meromorphic argument, without varying the discrete Xi copy.
**DN23 closes this boundary-shift limit and the complete physical angular
formula in Lean.** It uses `Re(w)>1`, the full range of the divisor-square
majorant; no nonvanishing assumption on individual local Euler factors is
introduced.


## Monodromy proof and nontriviality test

**Analytical derivation; Lean implementation in progress.** Let
`g_n(s,x)=(2-x)^(2*s)*(1-x)^n`. On `|x|<=3/2`, the chosen logarithm is
analytic because `Re(2-x)>=1/2`. If `c_k(s)` are its Taylor coefficients,
Cauchy's estimate gives

```
|c_k(s)| <= (5/2)^n * exp(2*L*|s|) * (2/3)^k,
L = max_{|x|<=3/2} |Log(2-x)| < infinity.
```

For `Re(w)>-2`, `w!=-1`, the *existing first-subtraction* integral is exactly
`sum_{k>=0} c_k(s)/(w+k+1)`. Subtract `c_0` before integrating; the remaining
series is dominated by a constant times `x^(Re(w)+1)`, so termwise integration
is justified. The second-subtraction version has the same series for
`Re(w)>-3`, away from `w=-1,-2`. This identifies finite constants as well as
poles; it is not an arbitrary continuation.

Uniform convergence on the unit circle gives

```
H_n(w,s) = sum_k c_k(s) * int_0^(2*pi) i*exp(i*(w+k+1)*t) dt
         = E(w) * sum_k c_k(s)/(w+k+1).
```

Each integral is entire, including its value `2*pi*i` at `w=-k-1`, and its
norm is at most `2*pi*exp(2*pi*abs(Im(w)))`, independently of `k`. The
geometric coefficient estimate therefore proves normal convergence and
finite exponential type after every affine substitution for `s`. Inserting
`(i*t-Log(2-exp(i*t)))/2` preserves this bound. Differentiation gives the
previously displayed `E^2*X` identity; its monodromy-derivative term must
remain.

An alternative direct Lean proof uses the logarithmic-cover kernel
`f(u)=exp((w+1)*u)*g_n(s,exp(u))`. It is analytic on `Re(u)<=0` and satisfies
`f(u+2*pi*i)=exp(2*pi*i*w)*f(u)`. Cauchy on the rectangle
`[log(e),0] x [0,2*pi]` gives

```
E(w)*int_e^1 x^w*g_n(s,x) dx = H_n(w,s)-H_{n,e}(w,s).
```

The first Taylor remainder bounds the small-circle term after its exact
`E*c_0*e^(w+1)/(w+1)` subtraction by `C*e^(Re(w)+2)`. Thus it gives precisely
the same first-subtracted Mellin moment. DN24 closes this rectangle proof, the source-derived remainder estimate, and the affine entirety/growth bound in Lean.

The forcing term can use only these first-subtracted moments. Integration
by parts, retaining both original forcing counterterms, gives for `n>=1`

```
w*J_n(w-1,s-1/2)
 = n*J_(n-1)(w,s-1/2)+(2*s-1)*J_n(w,s-1).
```

The endpoint at `x=1` is zero. At zero the leftover is `O(e^(Re(w)+2))`;
no finite constant is added. Consequently `w*Z` is the same combination for
`n=2,4`, multiplied by `2*amp^2*A` and `2*amp^2*B`. This avoids treating an
independent second-subtraction contour as a new object.

Nontriviality tests the *whole radial expression*, including onset and
forcing. Near `w=0`, on `s=-2*w-4`, `M` and `X` are analytic, `mu-2` has a
zero, and `w*Z` has removable value `F(0)`. At unit amplitude,
`A(-4)=6`, `B(0,-4)=45`, hence `F(0)=51/256`. The actual onset satisfies

```
T(-4,0) = int_0^infinity smoothTransition(u)*exp(-8*u) du > 0
```

because it is nonnegative and equals one for `u>=1`. Thus the radial
expression has value `51*T(-4,0)/256`. Since `lambda(0)=8` and
`E(w)/w -> 2*pi*i`, its proposed compact numerator satisfies

```
G(w)/w^2 -> -51*pi^2*T(-4,0) != 0.
```

The nonzero anchor and contour estimates would therefore apply to the
complete action, not merely to its scalar source moment. Their Lean proofs,
the actual finite-part identification, and the affine counting injection
are still required before claiming the matching obstruction.


## Attachment of the logarithmic moment

The remaining logarithmic contour can be proved without differentiating along
the physical parameter curve. Define

```
L_n(u) = f_n(u)*(u-Log(2-exp(u)))/2,
L_n(u+2*pi*i) = exp(2*pi*i*w)*(L_n(u)+pi*i*f_n(u)).
```

Applying the same rectangle identity gives the normalized relation
`E*X_n+pi*i*exp(2*pi*i*w)*J_n=H_X_n`. Its inner remainder is bounded by
`C*e^(Re(w)+2)*(1+abs(log(e)))`, hence tends to zero for `Re(w)>-2`.
The extra logarithm uses the derivative bound for `Log(2-z)` on `|z|<=1`;
its derivative has norm at most one. The actual transformed endpoint
constant is `-log(2)/2`: `tortoise(x*(2-x))=(log(x)-log(2-x))/2`.
Together with `z~2*x`, this agrees with the original `log(z)/2-log(2)`
constant. DN25 proves the fixed-direction derivative and contour monodromy;
DN26 proves its admitted integral and cutoff equality; DN27 proves the exact
nonlinear-radius counterterm transport. Their assembly with the complete
canonical action remains open in Lean.

The onset clearing can also retain the fixed-source derivative explicitly.
Put `F(lambda)=clearedOnset 0 lambda=1+lambda*onsetCorrection 0 lambda`.
The original correction depends only on `lambda=w-2*s`. Thus, away from
`lambda=0`,

```
lambda*T(s,w)=F(lambda),
lambda^2*T'(s,w)=lambda*F'(lambda)-F(lambda).
```

The derivative here keeps `s` fixed. Substituting `lambda=5*w+8` afterwards
does not insert an extra factor of five. The corpus's `clearedOnset_entire`
provides entirety of `F`; DN25 derives its finite-type bound from the fixed
compact transition integral and controls its derivative by Cauchy estimates. This reduces onset clearing to that same
source-defined entire function and its derivative, rather than a new clock.


## Nonzero anchor at the first Mellin pole

**DN25, Lean verified.** The full candidate cleared
numerator has a simpler nonzero anchor at `w=-1`, `s=-2` than at `w=0`.
At this point `E=0`, `lambda=3`, `mu=0`, `A=-3/2`, and `B=0`.
The source-normalized contour residue is

```
H_n(-1,s)=2*pi*i*2^(2*s),
H_M(-1)=-3*pi*i/8.
```

All terms of the complete numerator containing `E` vanish. The retained
logarithmic monodromy term therefore gives exactly

```
G(-1)=(mu-2)*lambda*Theta0*(-pi*i*H_M)
     =27*pi^2*T(-2,-1)/4 > 0.
```

Here `T(-2,-1)=int_0^infinity smoothTransition(u)*exp(-3*u) du` is positive:
the integrand is nonnegative everywhere and positive on `[1,2]`. This tests
the same full numerator, including onset, its derivative and forcing; their
other terms vanish by their explicit monodromy factors at this anchor.
The outer action factor `mu` is nonzero at every actual nonreal QNM, so its
zero at the auxiliary anchor does not affect the proposed critical-zero
counting argument. No off-shell nonzero action is being substituted for an
actual Xi-copy nonzero action.

For formal attachment of forcing, the displayed shifted `J_n(w-1,s-1/2)`
must mean its **two-subtraction** finite part when `Re(w)<=-1`; the Lean
first-subtraction definition cannot be used there. Avoid that ambiguity by
setting

```
Y_n = n*J_(n-1)(w,s-1/2)+(2*s-1)*J_n(w,s-1),
Y = 2*amp^2*(A*Y_2+B*Y_4)=w*Z.
```

Use the identical combination of compact contours as `H_Y=E*Y`. The final
forcing summand is then `lambda*Theta0*E*H_Y`; every Jacobi finite part in
this formulation is in its verified first-subtraction domain.

## Complete analytical matching obstruction

**Paper derivation; canonical-cutoff attachment and counting injections are
not yet Lean-verified.** Fix the `true/true` branch and unit amplitude.
For a critical copy write `rho=1/2+i*t`, `w=-rho/2-1`, `s=-2*w-4`.
Then `w` is nonreal, `-2<Re(w)`, and `mu`, `E(w)` and `lambda=5*w+8`
are nonzero. The exact proposed attachment is

```
E(w)^2*lambda^2*canonicalQNMValue(q,true,true,1)
 = -mu*physicalSelfSourceCoefficient(q)*G(w).
```

Here `G` is the complete numerator above with forcing written as `H_Y`.
This equality follows directly from DN22 as follows. Apply `z=x*(2-x)`
to its single positive-cutoff integral. For the scalar part DN24 identifies
the first-subtracted Jacobi periods. For the logarithmic part differentiate
only the Jacobi factor in the direction `(1/2,-1/4)`, holding `A,B` fixed.
The resulting counterterm is

```
c0*e^(w+1)*((log(e)-log(2))/(2*(w+1))-1/(2*(w+1)^2)).
```

The original counterterm at `z=e*(2-e)` differs from this by
`O(e^(Re(w)+2)*(1+abs(log(e))))`, which tends to zero. Indeed
`log(z)/2-log(2)=(log(e)-log(2))/2+log(1-e/2)/2`, and the other coefficient
factors are differentiable at zero. Differentiating the monodromy gives
`E^2*X=E*H_X-pi*i*exp(2*pi*i*w)*H_M`.

For forcing set
`g(x)=2*(A*(2-x)^(2*s-1)*(1-x)^2+B*(2-x)^(2*s-1)*(1-x)^4)`.
Its exact transformed density is `x^(w-1)*g(x)`. The original two forcing
counterterms transform into
`g(0)*e^w+w*g'(0)*e^(w+1)/(w+1)` with error `O(e^(Re(w)+2))`.
In particular `g(0)=2^w*F0` and
`g'(0)=-(w+1)*g(0)/2+2^(w+1)*F1`; these identities retain the slope term.
Integration by parts has zero upper boundary because `g(1)=0`, and its
lower remainder is `e^w*(g(e)-g(0)-e*g'(0))=O(e^(Re(w)+2))`.
It therefore gives `w*Z=Y`, the displayed combination of first-subtracted
Jacobi moments. Together with the fixed-source onset identities these are
exactly the claimed attachment, with no finite constant chosen afterward.

The compact contour bounds, their logarithmic weights, and the compact
onset correction show that `G` is entire of finite exponential type.
Cauchy's estimate on unit disks supplies the same property for the onset
derivative. The exact value `G(-1)=27*pi^2*T(-2,-1)/4>0` proves
nontriviality. Thus its zeros in disks centered at `-1` number `O(R)`.

Now take the simple critical Xi census up to height `N/3`, with `N` a large
natural number. The corpus's closed critical-density theorem gives
`Omega(N*log(N))` distinct members. The map `rho -> -rho/2-1` is injective
and sends this census into the disk centered at `-1` of radius `N`.
Consequently only `O(N)` members can have `G(w)=0`.

By DN23, a zero angular coefficient entails at least one of the three Xi
collisions. Reflect the first two, obtaining the injective affine maps

```
rho -> 2-5*rho/2,  rho -> 1-rho/2,  rho -> 3*rho/2.
```

All images have real part `3/4` and absolute ordinate at most `5*N/6`,
hence at most `N-2` for `N>=12`. `zetaLittlewoodZeroCountAbove` counts
analytic multiplicities for real part **at least** its threshold; it is
not the horizontal first-moment mass. Its uniform bound at `sigma=3/4`
is `O(N^(4/5)*(1+log(N))^16+(1+log(N))^16)=o(N)`.
The Xi/residue-unit zero equivalence and positivity of each zero's
multiplicity therefore bound the three affine exceptional sets by `o(N)`.

If the canonical action vanished at every critical copy, its exact
factorization would put the entire simple-critical census in the union of
these four exceptional sets. Their size is `O(N)`, contradicting the
`Omega(N*log(N))` lower bound. Hence some actual critical copy has nonzero
complete canonical action. The corpus's source-probe range classification
then excludes matching that action through the unit complementary source,
regardless of how the returned vector depends on the copy.

The positive survivor is stronger than one counterexample: once the
attachment and injections are formalized, only `O(T)` simple critical zeros
can have zero complete action, among an `Omega(T*log(T))` census. Thus the
nonzero action occupies asymptotic relative density one in that census.
This constrains the proposed unit-source-clock matching; it neither
falsifies RH nor excludes every possible source-retaining HB receiver.

## Integral formula for the fixed-source Jacobi derivative

**Lean verified in `FundamentalJacobiLogIntegral` (DN26).** Put
`F(v,x)=g_n(s+(w-v)/2,x)` and `J(v)=firstEndpointMellin(F,1,v)`.
Then the source direction is `v=w+u/2`, and `X_n=J'(w)/2`.
Writing `g0=2^(2*s)`, its exact first-subtracted formula is

```
X_n = -g0*(log(2)/(2*(w+1))+1/(2*(w+1)^2))
  + int_0^1 x^w*(g_n(s,x)*(log(x)-log(2-x))/2
                 -g0*(log(x)-log(2))/2) dx.
```

A uniform bound for the spatial derivative of `F` follows by compactness
on a closed parameter disk times the closed unit spatial disk. The mean
value estimate gives `|F(v,x)-F(v,0)|<=C*x` there. Choose `beta>-2` below
`Re(v)` on that parameter disk. The first-subtracted density is bounded by
`C*x^(beta+1)`, an integrable function. Cauchy's estimate on the smaller
parameter disk gives an integrable bound for its parameter derivative.
Thus differentiation under the integral supplies the formula and absolute
admission of its displayed remainder. The proof already used in
`CauchyDominatedIntegralHolomorphy.differentiableAt_integral_of_cauchy_dominated`
contains the required `HasDerivAt` result before discarding it. DN26 retains
that derivative identity and the admission of its derivative integral.

The leading primitive is
`g0*x^(w+1)*((log(x)-log(2))/(2*(w+1))-1/(2*(w+1)^2))`.
Its value at `x=1` is exactly the finite constant in the formula. Continuity
of the admitted remainder integral therefore gives the logarithmic cutoff
limit. This uses the fixed source frequency and the original counterterm;
it neither differentiates the physical curve nor introduces a limit premise.
