# HB: actual projected Einstein current and QNM pairing

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source →
physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
RH remains unproved. The frontier map is read-only.

## Sole active target: full temporal/metric/QNM matching

**OPEN. Neither full matching nor its impossibility is proved.** The target is
the complete original causal Einstein pairing against the unchanged physical
left mode, with its actual temporal, cusp, radial, horizon and onset contacts,
and its identification with the restored meromorphic pairing at the original
fundamental QNM. A scalar restoration, a local current identity, or construction
using a different order of limits does not settle this target.

Write `mu=physicalAngularParameter(q)^2-1/4`, `lambda=mu-2`,
`C=physicalSelfSourceCoefficient(q)`, `L=radialLift`, and
`G=continuedReducedGreen` at the unchanged physical parameters. The known
scalar restoration dictates the candidate full coefficient `h=C*(G+L)`.
It does not dictate a reconstructed angular square: integrating the original
coexact pairing produces `-mu` and its normal-flux correction. Thus the full
comparison must use that derived normalization. In particular, equality of
the original integrated current with `physicalProjectedModeAction` cannot be
inferred from the scalar projection's name.

For `f=R^2-1`, scalar radial profile `h`, its complete forcing `F`, and the
original radial test `g`, the candidate restored temporal density is

```
-mu * (-2*w*lambda*h*g/f - w*R^2*g*F/f^2).
```

Both the lift and its wave/source contact belong in `h,F`. At every fixed
exterior radius, `OriginalMetricTimeLimit.original_metric_time_limit` now
identifies this density with the independently removed onset and terminal
limits of the original angular-restored metric time integral, for
`Re(w)>3/2`, `Im(w)!=0`. Its scratch check and isolated exact leaf audit
passed; artifacts and umbrella import are installed. This takes the angular
finite part first. The finite-time
algebra retains the temporal endpoint. If `M(t,R)` denotes a sufficiently
regular scalar period before its time transform, then

```
int_0^T exp(-w*t)*(M_t+w*M) dt
 = exp(-w*T)*M(T,R)-M(0,R)+2*w*int_0^T exp(-w*t)*M(t,R) dt.
```

Consequently the original temporal current has the additional term
`mu*lambda*g/f * (exp(-w*T)*M(T,R)-M(0,R))` before its limit.
This sign follows from `Jstatic^t=Jingoing^p-Jingoing^R/f` and the complete
source contact. Its two endpoint terms vanish at fixed exterior radius:
the complete original scalar is zero at onset and has ingoing-time growth
at most `C_R*exp(Re(readerExponent(q))*p)`. The actual causal clock shift
then identifies its admitted Laplace integral with `exp(-w*x)*h(w,x)`.
The complete angular-first exterior cutoff comparison is now derived below.
The complete original radial finite part is now restored at one common
cutoff near either fundamental QNM. Its residue cancels the retained
temporal-corner residue exactly, without a critical-line assumption.
The restored radial-plus-corner expression also has a proved analytic
extension and a fixed finite QNM value. Identifying this continuation with
the complete original pairing under independent cusp/time/horizon removal
remains required.

### Complete outer frequency integral and QNM residue

Let `n_w(x)` be the unchanged normalizable mode, `K=reducedGreenGradient(chi,s,1)`
and `P_s(K,x)=forcingProfile(s,amp,1,K,radialUnit(x))`. The retained original
lift and forcing satisfy the exact identity

```
Q(x) = 2*(mu-2)*radialLift(s,0,amp,1,x)+P_s(K,x)
     = P_s(K-(mu-2),x).
J_T(w) = int_T^0 exp(w*x)*Q(x)*n_w(x) dx.
```

For each fixed `T<0`, `J_T` is entire. The proof derives a common bound from
the compact exponential/source factor and the original normalizable mode's
outer bound, then applies dominated holomorphy. Thus this statement concerns
the integrated complete lift/contact term, rather than only its pointwise
frequency behavior.

With `D_w(x)=(R(x)^2-1)*metricFrequencyDensity(w,R(x))`, the exact decomposition
on `-2<Re(w)`, off the connection and source poles, is

```
int_T^0 D_w(x) dx
 = 2*mu*w*(mu-2)*C*continuedReducedOuterPairing(chi,s,amp,T,w)
   +mu*w*C*continuedOnset(s,w)*J_T(w).
```

Both terms are proved integrable before splitting the original density.
At either physical fundamental frequency `w0`, the second term is analytic.
The first has residue `2*mu*w0*(mu-2)*C` times the existing exact reduced
outer-pairing residue, retaining its source moment, onset and mode-square
integral. `OriginalMetricOuter.originalMetricOuter_QNM_residue` derives this
after integration with the original angular factor `-mu`.

**Formal status:** the complete leaf passed scratch and its isolated exact
module audit; artifacts are installed, umbrella wired, and formal lint passed.
The original outer time interchange and exterior corner assembly are derived
below. **Remaining matching problem:** continue the complete original horizon
finite part and retain independent cusp control. The older projected
field `C*G+P` differs from the original restored `C*(G+L)` by `C*L-P`; its
radial restoration theorem cannot be substituted without that correction.

### Complete exterior temporal cutoff comparison

For each `T<0`, the complete original scalar satisfies
`norm(originalScalar(p,p-2*x)) <= B_T*exp(Re(readerExponent(q))*p)` uniformly
for `x in [T,0]`, `p>=0`. The original causal-response bound controls the
response; compactness bounds its retained lift through the outer endpoint.
With `V_w(x,p)=exp(-w*p)*originalScalar(p,p-2*x)` and
`E_w(x)=exp(w*x)*n_w(x)`, the original radial Jacobian gives exactly

```
f(x)*restoredMetricTime(a,b,R(x))
 = mu*E_w(x)*(
     (mu-2)*(V_w(x,b)-V_w(x,a)+2*w*int_a^b V_w(x,p) dp)
     +w*C*P_s(K,x)*int_a^b exp(-w*p)*timeOnset(2*s,p) dp).
```

For `Re(w)>3/2`, this complete density has an integrable outer bound uniform
in `0<=a<=b`. Its integrated limit as `(a,b)->(0+,infinity)` equals the
original frequency integral `outerIntegral(T,w)`. The original static cutoff
has upper ingoing time `p=b+x`; its integrated outer limit is the same.
Both statements derive admission and keep the original forcing and endpoints.

At the common interface `T=-L0/2`, define the complete exterior comparison by

```
exteriorCutoffDifference(L0,b)
 = metricCutoffDifference(L0,b)
   +outerStaticTimeIntegral(-L0/2,b)-outerIntegral(-L0/2,w).
```

`OriginalMetricOuterTime.original_exterior_cutoff_difference` proves that
some `L0>0` gives limit `physicalCornerCandidate(q,br,amp,w)`. Thus the whole
angular-restored exterior has the original temporal corner: the bounded
outer contribution tends to zero, while the collar retains its already-derived
first moment and fixed logarithmic coordinate term. This does not assume a
QNM expansion or make the angular cutoff independent of the other limits.

**Formal status:** the complete leaf passed scratch and isolated exact audit
(only this leaf built). Artifacts are installed, umbrella wired, and formal lint
passed. Full temporal/metric/QNM matching and its impossibility remain open.

### Temporal/height interchange — original causal field

Set `B=principalKernelGrowth(q)`, so `3/2<=B<2`, and let
`U(t)=causalJointForcedResponse(q,branch,a,t)` retain its complete causal
forcing `F(t)=causalCuspSourceVector(q,branch,a,t)`. For every `c>B`, the
original damped orbit is L2 in time by
`PhysicalCausalGreenBand.causalJointForcedResponse_memLp_of_native`.

`OriginalWeightedOrbit.heightSource` multiplies the literal forcing by height
in the original spatial measure. Its four separated terms keep the native
angular residual and all three principal cutoff commutators, with their
original time/radial coefficients. The explicit envelope is
`sourceEnvelope=(cuspWeightBase+y)*F`, and

```
A_c = sourceBound(q,branch,a,c)
    = int_0^infty norm(expRay(c,t)*sourceEnvelope(t)) dt < infinity.
```

The bound uses this envelope, rather than claiming the sharper constant
`int norm(expRay(c,t)*W*F(t))` from the earlier paper derivation. Every bounded
cusp multiplier `W_N` is dominated by the same envelope. The original rotated
resolvent and vector Plancherel give

```
norm(W_N*Uhat(c+i*xi))
 <= c*A_c / ((c^2-9/4)*sqrt(c^2+xi^2)),
int_0^infty exp(-2*c*t)*norm(W_N*U(t))^2 dt
 <= (c*A_c/(c^2-9/4))^2/(2*c).
```

The right sides are independent of the actual cusp cutoff. No spectral
expansion or supplied weighted-orbit hypothesis enters these estimates.

`OriginalCuspTime` removes the cusp weight in the time-dependent field itself.
Spatial Fatou bounds the limiting weight by the lower limit of cutoff norms;
temporal Fatou makes that lower limit finite almost everywhere. The ratios
`W_N/W` are bounded by one and converge to one, giving strong spatial
convergence on each admitted slice. This also proves Bochner measurability of
the limiting time field. The resulting actual representative
`V_c(t)=expRay(c,t)*W*U(t)` is L2 in time with the same energy bound.

For every complex `w` with `Re(w)>B`, choose `B<c<Re(w)`. Cauchy--Schwarz
admits `expRay(w-c,t)*V_c(t)` as a Bochner time integral. Bounded multiplication
by `1/W` identifies its integral with `W*Uhat(w)`. Bounded multiplication by
`y/W`, whose norm is at most three, then yields an admitted field `H_w` with

```
H_w(t) = expRay(w,t)*y*U(t)             (a.e. in the original measures),
int_0^infty H_w(t) dt = y*Uhat(w).
```

Thus the unbounded height multiplication and original time transform commute
on the whole native Laplace half-plane. In the physical Green band
`B<Re(w)<2`, `Im(w)!=0`, the unchanged angular reader satisfies

```
int_0^infty physicalJointProjection(r,H_w(t)) dt
 = causalPhysicalProjection(q,r,branch,a,w).
```

The existing `causalPhysicalProjection_ae_green` theorem identifies this
radial function with the complete physical Green profile. This is an identity
for the original weighted causal field; the bounded reading is applied before
the time integral with its integrability derived.

**Formal status:** `ThetaCuspHawkingBMOriginalWeightedOrbit` and
`ThetaCuspHawkingBMOriginalCuspTime` passed scratch checks and isolated exact
leaf audits. Their artifacts and umbrella imports are installed; no umbrella
build was run. The native damped-L2 interface in `PhysicalCausalGreenBand` also
passed its scratch check and isolated exact leaf audit.

**Meaning for full matching.** The residual temporal/height admission and its
bounded physical projection are closed. The finite-dimensional principal and
lift restoration must still be assembled with their original coefficients.
The separate `OriginalMetricTimeLimit` result closes the complete restored
metric's temporal endpoints at fixed radius. Metric derivative traces,
radial trace evaluation, independent cusp/time/horizon limits and the
complete QNM continuation remain open. These results neither identify a
finite-variation Jost expansion nor
fixes a zero-mode coefficient. It proves neither full matching nor its
impossibility.

### Decisive corner comparison: preserve the first temporal moment

**Full matching remains open.** The corner below, including its possible
QNM residue, is attached to the angular-restored original metric collar by
`OriginalMetricCorner` (F212–F213). Its first temporal moment and integrable
collar remainder are proved. Passage to the complete original action with
independent cusp/time/horizon limits and the outer region remains open.

The original normalizable mode has opposite coefficient
`beta(w)=connection(w,chi)/(2*w)`. Set `p=t+x`, with the original tortoise
coordinate `x<0`. At the future horizon its opposite stream tends to
`beta(w)*2^(-w)*exp(-w*p)*V`. If `H(p)` is the fully cusp-restored original
scalar horizon trace and `E(p)` the fully restored original forcing divided
by `z=1-R^(-2)` at the horizon, the angular-transposed temporal current's
opposite leading density in `dt dx` is therefore

```
A_w(p) = mu*beta(w)*2^(-w)*exp(-w*p) *
           (lambda*H'(p)+w*lambda*H(p)+w*E(p)).
```

This uses the complete source contact. The onset has `H(0)=0`. Neither
the original scalar response nor its contact is replaced by a homogeneous
mode. Define `K(w)=int_0^infty A_w(p) dp` and
`J1(w)=int_0^infty p*A_w(p) dp` whenever their absolute moments exist.
For a fixed collar endpoint `X<0`, direct integration over the original
triangle gives, when `T+X>0`,

```
int_0^T dt int_(-t)^X A_w(t+x) dx
  = int_0^(T+X) (T+X-p)*A_w(p) dp,
```

where the inner integral is zero for `t+X<0`, rather than an oriented
integral beyond the causal domain. If `int (1+p)*abs(A_w(p)) dp` is finite,
subtracting `T*K(w)` leaves the limit `X*K(w)-J1(w)`. In the other order,
integrating time first on `-L<=x<=X` gives `(L+X)*K(w)` exactly. Its
tortoise finite part is `X*K(w)`. Thus the difference is **`-J1(w)`**,
not zero; the estimate `T*int_T^infty abs(A_w)<=int_T^infty p*abs(A_w)`
justifies the first limit.

The prescribed radial finite part uses `z`, not `x`. Since
`log(z)=2*x+log(4)+o(1)`, its logarithmic subtraction contributes the
additional finite constant `K(w)*log(2)`. The comparison with that exact
radial prescription is consequently `-J1(w)-K(w)*log(2)`.

Write `a(w)=2^(-w)*Laplace(H)(w)` and
`e(w)=2^(-w)*Laplace(E)(w)`. Integration by parts in the first moment gives
the following single candidate for the entire missing corner:

```
Delta_corner(w) = mu*beta(w) *
  (lambda*a(w)+2*w*lambda*a'(w)+w*e'(w)).

FP_static_time(original current)
  = FP_z(time-transformed original current) + Delta_corner(w).
```

The two `log(2)` contributions cancel in these normalized amplitudes.
The incoming and opposite collar remainder is integrable after angular
restoration by F213. The first displayed equality evaluates the corner;
the second remains the **active full-current conjecture** for the complete
independently regularized pairing, including its outer region. It is not a
definition of that pairing.

The spectral consequence is sharp. At the physical fundamental root `w0`,
the inspected Gamma formulas give

```
connection'(w0)=2*w0*normFinitePart(w0),
beta'(w0)=normFinitePart(w0).
```

Both identities passed the exact Lean leaf audit in
`ThetaCuspHawkingBMOriginalCornerSpectralBalance`, for every actual Xi
copy and either original frequency. The same leaf proves the exact
fixed-radius response identity
`Res(beta*deriv(f))=-normFinitePart(w0)*Res(f)`, including zero residue,
and simplifies the existing full projected radial residue to its original
source factors. The leaf is wired into `RHTower`; its isolated audit built
only that leaf, with no warnings. If the actual normalized horizon
amplitude has residue `r`, and the restored source contact is analytic,
the corner candidate has residue `-mu*lambda*connection'(w0)*r`.
The restored radial temporal current has residue
`2*mu*w0*lambda*normFinitePart(w0)*r`; these coefficients cancel exactly.
An analytic logarithmic coefficient therefore does **not** suffice to
discard its temporal corner: a first temporal moment differentiates the
meromorphic horizon response.

### Original forcing and lift/contact horizon restoration

`ThetaCuspHawkingBMOriginalMetricHorizon` passed scratch and isolated exact
leaf audit. Its artifacts are installed and its umbrella import is wired.
For every fixed gradient `K`, the original forcing kernel has exact pullback

```
exp(w*x)*P_s(K,x)*n_w(x)*dx/dz
  = -z^(w-1)*A(w)*H(w,z)*S_K(w,z)
    -[connection(w)/(2*w)]*H(-w,z)*S_K(w,z)/z.
```

`S_K` is the original source remainder, `A` the actual regular Wronskian
coefficient, and `H` the actual Gauss factor. Proved uniform quadratic jets
produce two power counterterms and one logarithmic counterterm. Their
restored value is analytic at either actual fundamental QNM. The coordinate
substitution is proved for the original radial integral, not postulated.

For `K-(mu-2)`, joining the restored horizon to the original outer integral
proves the entire regular contribution, including its unchanged onset and
metric coefficient, has zero QNM residue. Its finite value is retained.

The complete density has a second exact form:

```
D_w = 2*mu*w*(mu-2)*C*G_native*n_w
      +mu*w*C*continuedOnset(s,w)*exp(w*x)*P_s(K,x)*n_w.
```

The lift cancels because `continuedReducedGreen=G_native-L`. The existing
`normalizableOuterPairing` uses native Green response on its horizon interval
and reduced Green response on its outer interval. Its matching regular terms
are therefore the unshifted forcing on the horizon and the shifted forcing
outside. Both have now been restored analytically at the physical QNM.

### Complete original radial restoration and temporal-corner balance

`ThetaCuspHawkingBMOriginalMetricRadial` passed scratch and isolated exact
leaf audit; artifacts are installed and its umbrella import is wired.
The strengthened `physicalNormalizableOuterPairing_residue_and_restoration_below`
chooses its interface below any prescribed positive cap. Its proof uses
canonical instances and no transparency override. This permits the actual
Green and forcing restorations to use the same cutoff.

Put `a_G(w)=2*mu*w*(mu-2)*C` and
`a_F(w)=mu*w*C*continuedOnset(s,w)`. For some source-derived interface `b`,
the complete original radial finite part is

```
R(w) = a_G(w)*normalizableOuterPairing(tortoiseOf(b),w)
       +a_F(w)*(nativeForcingHorizonFinitePart(b,w)
                 +shiftedForcingOuterMoment(tortoiseOf(b),w)).
```

`radialCutoff_decomposition` is an equality of the literal original metric
integral from `tortoiseOf(e)` to the outer endpoint, together with its
derived Green and forcing counterterms. The actual coordinate substitution,
integrability and interface split are proved. The theorem
`original_radial_restoration_and_corner_balance` constructs a frequency ball,
interface and three forcing coefficients, then proves this one-cutoff
integral tends to `R(w)` off the original connection zero.

For either actual fundamental QNM `w0`, write
`S=mu*(mu-2)*C*fundamentalSourceMoment(w0,s,amp)*continuedOnset(s,w0)`.
The same theorem proves

```
lim_(w->w0,w!=w0) (w-w0)*R(w) = -S,
lim_(w->w0,w!=w0) (w-w0)*(R(w)+physicalCornerCandidate(w)) = 0.
```

The corner is the one already obtained from the complete angular-first
exterior cutoff comparison. No new subtraction or nonvanishing premise is
used. **Meaning for the whole route:** the corrected original residue
vanishes for every actual Xi label, so this residue alone cannot select
horizontal zero locations. The finite value remains retained; zero residue
alone does not prove full matching. The analytic extension is established
below using the actual connection-cleared source expressions.

### Complete corrected QNM continuation and finite value

`ThetaCuspHawkingBMOriginalMetricQNM.original_corrected_action_QNM` passed
scratch and isolated exact leaf audit; its artifacts and umbrella import
are installed. The complete restored radial-plus-corner function has an
analytic extension across either actual fundamental QNM, with its original
source, forcing, onset, radial normalization and corner retained.

Let `c(w)=connection(w,chi)`, `A(w)=continuedCornerAmplitude(w)` and
`H(w)` be the analytic extension of `c(w)*A(w)`. Its center value is proved
to be `c'(w0)*cornerResidue`, from the original amplitude residue. If
`F(w)=continuedForcingTransform(w)`, the exact cleared corner is

```
N_corner(w) = mu*((mu-2)*(c*H/(2*w)+c*H'-H*c')
                   +c^2*C*F'/2).
```

The source-defined `greenNumerator` clears the native horizon and reduced
outer Green pairing at their common interface; its analytic proof retains
both horizon branches. With `J` the complete regular forcing finite part,

```
N(w) = a_G(w)*greenNumerator(w)+c(w)*a_F(w)*J(w)+N_corner(w),
N(w) = c(w)*(radialFinitePart(w)+physicalCornerCandidate(w))
```

on the original punctured frequency neighborhood. `N` is analytic at `w0`.
The already proved zero corrected residue and the original simple connection
zero imply `N(w0)=0`. Thus the actual corrected function agrees near `w0`
with the analytic quotient `dslope(N,w0)/dslope(c,w0)`, and

```
lim_(w->w0,w!=w0) [radialFinitePart(w)+physicalCornerCandidate(w)]
    = finiteQNMValue = N'(w0)/c'(w0).
```

The theorem also retains convergence of the literal radial cutoff plus the
actual temporal corner to this same punctured function. The companion
`original_radial_restoration_and_corner_balance_below` exports the original
regular-term analyticity and allows an arbitrary positive interface cap;
its previous public theorem is preserved. No nonvanishing or critical-line
premise is added. **Meaning for the whole route:** the local QNM singularity
is removable, but the finite value is not proved zero. It retains source
derivatives and the regular forcing contribution, which residues alone miss.

**Exact remaining test.** Identify this analytic continuation with the
complete original metric pairing under independent cusp/time/horizon
removal. This requires controlling all mixed corner contributions, not
only the limits on separate faces. The literal forcing's joint cusp/horizon
radial restoration is now closed below. Current compact cusp bounds have
constants depending on the time/radius compact set; they do not supply the
required unbounded moving-corner estimate. F207/F213 and F222–F232 need no
reproof. Full matching, impossibility, spectral nonvanishing and RH remain
unproved.

### Original forcing at the mixed cusp/horizon corner

**Lean closed.** Let `Q_Y` be the literal square period minus its three
principal counterterms, `D_Y=greenCut(Y)`, and
`K=reducedGreenGradient(chi,s,1)`. The actual finite-height forcing obeys

```
profileCut(Y,u) = (Q_Y-D_Y/2)*P_s(K,u) + (D_Y/2)*P_s(K+1,u).
```

The unchanged normalizable reader and radial integral preserve this exact
two-term decomposition. If `CT_K(e,w)` and `CT_(K+1)(e,w)` are the previously
derived two-power-plus-logarithm counterterms, the finite-height subtraction is

```
(Q_Y-D_Y/2)*CT_K(e,w) + (D_Y/2)*CT_(K+1)(e,w).
```

With this source-derived subtraction, the literal forcing radial integral
converges as `(e,k)->(0+,infinity)`, `Y=exp(k)`, at arbitrary relative rates,
to `C*horizonFinitePart_K(w)`. This holds throughout a neighborhood of either
actual fundamental QNM, including its center, and the limiting function is
analytic there. The proof uses `Q_Y->C`, `D_Y->0` only after each fixed
radial kernel has been restored. It therefore controls the otherwise
unbounded products with the horizon powers and logarithm. No finite constant
is inserted. Reference: `ThetaCuspHawkingBMOriginalForcingJointHorizon`,
`profile_two_kernels`, `radialCut_decomposition`,
`original_forcing_joint_horizon_QNM`. Scratch, exact isolated leaf audit and
repository lint passed; umbrella import installed without building it.

**Meaning for full matching:** the explicit forcing term has no remaining
cusp/horizon interchange gap with these derived counterterms. The causal
response, complete angular boundary current and temporal corner still need
their joint metric attachment. This theorem does not establish that attachment.

### Original source-square horizon jets: Lean closure

**Active full-current bridge.** Prove a uniform horizon Taylor estimate for the
literal source-square Jacobian times `compactForcing`, applied to the exact
principal-subtracted square and height-weighted gradient energy. Keep the
fixed onset, both triangles, and normalized circle integral. The proposed
bound is `C*exp(B*p-N*k)*abs(rho)` for every cusp order `N`, with independent
unbounded `p,k`. This is a bridge toward the unchanged full temporal/metric/QNM
matching target. Its decisive tests are the moving lower endpoint, collapsed
circle edges, and the sampled `Y^2` gradient factor; none may be dropped.

The exact complete integrated metric boundary is the four-transfer expression
`T(U,W), T(W,U), T(Delta U,W), T(F,W)` in `OriginalCompactBoundary`.
Its source-normal derivative is angular height derivative; temporal derivatives
are already represented by endpoints. The remaining mixed horizon comparison
requires controlling the horizon derivative of these actual source fields,
with the source-domain motion retained.

**[BRIDGE; scratch and isolated exact leaf audit passed]** In the original unit
source square, write `e=exp(-p*(1-alpha))`, `Z=sourceZ(image,p,rho,alpha,beta)`,
`Zrho=0` for the image and `(1-beta)*e` for the direct triangle, and

```
L=e/(1-rho*e)+1/(1+rho)+Zrho/(1+Z).
```

For `p>=0`, `abs(rho)<=1/4`, `alpha,beta in [0,1]`, every term is
nonnegative and at most `4/3`, so `0<=L<=4`. The actual horizon factor
satisfies `F_rho=-F*L`. Thus the exact original source-circle radius,
`d=2*arsinh(sqrt((1-alpha)*beta)*sqrt(F))`, satisfies
`d_rho=-t/sqrt(1+t^2)*L`, where `t=sqrt((1-alpha)*beta)*sqrt(F)`.
Consequently `-4<=d_rho<=0`, uniformly over all source times and the
complete source square, including collapsed circles. Equivalently the
transported invariant satisfies `I_rho=-(I-1)*L`. The direct triangle's
extra fixed-`z` derivative term is absorbed by the actual source-domain
motion `Zrho`; its Jacobian and forcing derivatives must remain in the
full integral.

The radius also satisfies `0<=d<=2*p+6` for `p>=0` and the full source
square. The exact native circle derivatives obey
`abs(offsetRadial),abs(heightRadial)<=exp(d)`; their defining identity is
`denominator^2-radialNumerator^2=sin(theta)^2`.

The resulting Taylor bound is now proved for every actual coordinate jet
`f=D^word R` of the square-source remainder or any gradient-product remainder.
Write `J(rho)=f(logCircle(unitRadius(image,p,rho,alpha,beta),theta,x,k))`.
For every `N : Nat`, the source supplies `C,B>=0` such that

```
norm(deriv J rho) <= C*exp(B*p-N*k),
norm(J(rho)-J(0)) <= C*exp(B*p-N*k)*abs(rho),
```

uniformly over `p,k>=0`, `abs(rho)<=1/4`, `alpha,beta in [0,1]`, all
`theta,x`, and both original source triangles. Constants depend only on the
fixed source parameter, derivative word and `N`. The mean-value proof retains
the actual moving source coordinate. `sample_eq_original` identifies this
sample with the original `arcosh(max(1,compactInvariant))` circle for `p>0`.
**References:** `OriginalHorizonSourceJets.square_jet_horizon_estimate`,
`gradient_jet_horizon_estimate`; radius statements use namespace
`D4BMOriginalHorizonRadiusDerivative` in the same leaf. Scratch and the single
isolated exact leaf audit passed; artifacts are installed and umbrella wired.

**Next complete-current attachment.** The literal `compactForcing` is linear
in `J,K`. Its coefficients depend on `Z` through `compactUnit(Z)`, inverse
powers of `1+Z` and `power(2*s,2/(1+Z))`; the latter base stays in `[1,8/3]`
on the original source square, so it has no characteristic-endpoint zero.
The original source Jacobian is `p*(1-sourceLower)`, with horizon derivative
bounded by `p`. The physical onset is `timeOnset(2*s,p*alpha)` and is independent
of `rho`. Beware normalization: `s=ModularCore.physicalRate`; the rate called
`CuspProjection.physicalRate` is doubled. Its real-part bound controls this
same `timeOnset(2*s,...)` through `timeOnset_pair_bound`.

The full gradient-energy remainder is the sampled height squared times the
sum of the two diagonal gradient-product remainders. This requires retaining
that height factor and its horizon derivative; arbitrary `N` in the proved
jet bounds absorbs its base-height power. The next formal target is the
Taylor bound for the original Jacobian times this complete forcing remainder,
then its actual normalized circle/unit-square integral. After exponential
time damping in a sufficiently far right half-plane, these bounds provide a
candidate common domination for independent cusp/time/horizon removal.
The complete metric angular products, finite-height horizon counterterms and
QNM continuation must still be identified explicitly. Full matching and its
impossibility remain unproved.

### Uniform native circle jets: source and source-chart estimates closed, metric attachment open

For every native radius/base-coordinate word `a` and every `N : Nat`, the
analytical target is

```
exists C>=0, B>=0, forall d,x,k, d>=0 -> k>=0 ->
  norm(nativeJet a cuspMeanRemainder [d,x,k]) <= C*exp(B*d-N*k).
```

The source estimate can be obtained directly from the defining Bessel
integral. For an integer `n>norm(nu)`, its literal kernel satisfies

```
x^n * norm(exp(-x*cosh(t))*cosh(nu*t))
  <= n!*2^n*exp((norm(nu)-n)*t),  x>0, t>=0.
```

This follows from `v^n*exp(-v)<=n!`, `cosh(t)>=exp(t)/2` and the proved
complex-cosh norm bound. Integration gives a global bound on
`x^n*norm(K_nu(x))`. The actual arithmetic coefficient bound is
`norm(coefficient(u,d,N)) <= (N+1)^(3*abs(Re(u))+1+d)`.
Choosing `n>max(norm(nu),3*abs(Re(u))+1+d+2)` makes the resulting Fourier
majorant summable. Thus every member of the literal signed Fourier–Bessel
family has a bound `C*exp(B*abs(k))` at height `exp(k)`.
`SquareCuspJets.Rapid` is already closed under actual coordinate derivatives,
products, complex height powers and finite sums. Its induction therefore
proves this global log-height estimate for every genuine square-source,
spin-two and gradient-product remainder jet, for every complex source
parameter. No modular higher-derivative theorem or Xi-zero premise is needed.
**Lean:** `AngularGlobalGrowth` and all three
`SquareCuspJets.*_jet_global_log_growth` statements passed scratch checks
and isolated exact leaf audits. Their artifacts are installed.

For a transported source jet `f`, write its global bound as
`norm(f([x,exp(l)]))<=A*exp(G*abs(l))`. The actual circle denominator lies
between `exp(-d)` and `exp(d)`, so its sampled log-height lies between
`k-d` and `k+d`. For any independent nonnegative integers `m,N`, split:

- `k>=d`: use the established positive-height source bound with weight
  `N+m`. Then `exp(m*k)*norm(f(circle))<=H*exp((N+m)*d-N*k)`.
- `0<=k<=d`: the global log-height bound gives
  `exp(m*k)*norm(f(circle))<=A*exp(m*k+G*(k+d))`, which is at most
  `A*exp((N+m+2*G)*d-N*k)`.

Hence each transported genuine source jet, with any generated height
monomial, has the required bound. There is no need to prove `m<=j` or to
preserve a sharp source growth exponent. The exact statements for the
square-source, spin-two and gradient-product remainders are closed in
`NativeSourceJetGrowth`; scratch and isolated exact leaf audit passed.

The remaining native-jet step is the *generated coefficient* estimate.
Each coefficient produced by the differentiation rules in `NativeCuspJets`
is a finite rational expression in `exp(d)`, `exp(-d)`, `sin(theta)`,
`cos(theta)` and inverse circle denominator. This class is closed under
those rules and every expression is bounded by `C*exp(A*d)`. Multiplying
by the transported source-jet estimate, finite summation and the actual
normalized circle average give the displayed native-jet target. Existing
`Represented` permits arbitrary smooth coefficients, so its smoothness
premise alone cannot supply this global estimate; the generated expressions
must be attached explicitly.

**Meaning for full matching:** the source's low-height region has a direct,
unconditional analytical bound. What remains is the generated-coefficient
attachment and uniform estimates through the original compact horizon
integral and complete metric boundary current, followed by independent
cusp/time/horizon removal. Full matching and impossibility remain unproved.

The same leaf proves a uniform bound for the original horizon source chart:

```
3*p/10 <= horizonFactor(image,p,rho,alpha,beta) <= (20/9)*p*exp(p),
p>=0, abs(rho)<=1/4, alpha,beta in [0,1].
```

This includes both complete original source triangles. For `p>=1`, the
factor under the characteristic square root is at least `3/10`, uniformly
over the source square. The proof uses the exact removable quotient
`expc(t)` with `1<=expc(t)<=exp(t)` for `t>=0`, and
`sourceZ in [-1/4,1]`. **Lean:**
`NativeSourceJetGrowth.horizonFactor_uniform_bounds`, same passed audit.
This permits a direct attack on the finite observer-coordinate derivatives
of the original compact integrand. A useful exact analytical identity is
`d/dp [p*expc(p*delta)]=exp(p*delta)`, including `delta=0`; for nonzero
`delta`, differentiate `p*expc(p*delta)=(exp(p*delta)-1)/delta`.
Its higher positive-order derivatives are bounded by `exp(p)` when
`p>=0` and `delta in [0,1]`. This derivative identity has not yet been
formalized here and is not a prerequisite of the horizon-derivative proof
above, where the exponential factor is fixed. The complete observer-jet estimates and joint metric
limit remain open; they do not follow from value bounds alone.

The actual compact source geometry supplies a useful estimate for this
remaining test. In `RetardedHorizonGeometry.compactInvariant`, write
`E=exp(p-a)>=1`, `0<=rho<=1/2` and `0<=z<=1`. On each original direct/image
integration domain the invariant `I` is at least one, and differentiation
in the observer coordinate gives exactly

```
I_rho(direct) = -((I-1)+2*(1-1/E)/(1+z))/(1+rho),
I_rho(image)  = -(I-1)*(1/(E-rho)+1/(1+rho)).
```

Consequently `abs(I_rho)<=3*(1+I)` uniformly in the entire original source
time interval. Also `abs(E*I_E)<=I+4` on both domains, by differentiating
their displayed numerators. There is no additional factor `exp(p-a)` in
these relative derivative bounds. For a smooth circle mean `M(I)` whose
angular action satisfies the bound `abs(DeltaMean(I))<=C*(1+I)^G`, its
Darboux equation gives, for `I>1`,

```
M'(I) = (I^2-1)^(-1) * int_1^I DeltaMean(v) dv,
abs(M'(I)) <= C*(1+I)^(G-1)  (G>=0).
```

Thus differentiating the actual compact kernel in observer radius or time
preserves its exponential growth order, once this angular-action bound is
supplied. The direct lower-end derivative is `1/E<=1`; the image lower end
is independent of `rho`. These are concrete original-domain estimates,
not an assumed uniform bound on an arbitrary wave orbit. To complete the
argument for the metric current one must supply the corresponding bounds
for the restored source's needed angular iterates and mixed derivative,
including their cusp finite parts. Then an `O(rho*exp(G*p))` remainder is
integrable in the original `dp dx` domain for `Re(w)>G`, since
`rho=exp(2*x)` and `x<0`. The following analytical derivation supplies
these bounds for the actual scalar finite part. Their Lean closure and
the resulting full matching remain open.

### Original circle period and the source-only temporal comparison

**Original circle-period identity formalized; subsequent temporal/metric
comparison remains analytical. Full matching in Lean remains open.** This supplies a concrete producer for the horizon quantities in the
preceding corner calculation. It also gives a stronger comparison than
cancellation of one Laurent coefficient. The time finite part below means
the constant after subtracting the linear term in the original static cutoff
`T`, with its original zero of time. It does not identify a different time-cap
prescription by definition.

Write `zeta=(q.1:Complex)`, `eta=1-zeta/2`, `mu=eta*(eta-1)`,
`G=Re(eta)`, and `C=physicalSelfSourceCoefficient(q)`. The actual Xi strip
gives `1/2<G<1`. The source powers are exactly
`alpha=(2*zeta,1,2-2*zeta)`, not half these exponents. The physical reader
has the one surviving cusp term `B*y^eta`, where
`B=reflectedCompletedLambda(zeta-1)`.

**1. Identify the original regularized circle period before time or horizon
limits.** Let `M_d(z)` be the actual native circle mean of the full original
half-square. Subtract its original counterterm

```
sum_i A_i*powerCircle(alpha_i,d)*B*Y^(alpha_i+eta-1)/(alpha_i+eta-1)
```

from `int_{FD,y<=Y} S(z)*M_d(z) dArea_hyp`, and call the limit `P(d)`.
Every denominator is nonzero: the three exponents are
`3*zeta/2`, `1-zeta/2`, `2-5*zeta/2`, whose imaginary parts are nonzero.
`NativeCuspTransport.mean_cusp_expansion` and
`NativeCuspJets.nativeCuspJet_rapid_bound` prove existence of this limit
and permit its first two radius derivatives, uniformly on every compact
radius interval. Products with the reader tail retain rapid decay; the
remaining principal-reader products are precisely the displayed powers.

For the scalar Green current `S*grad(M_d)-M_d*grad(S)`, modularity of both
fields cancels the vertical sides and the paired circular bottom. The
remaining top current has exactly the principal terms

```
sum_i (alpha_i-eta)*A_i*powerCircle(alpha_i,d)*B*Y^(alpha_i+eta-1)
```

plus a rapidly decreasing remainder. There is no constant term. This is
the scalar Green current itself, not an application of the earlier rough
vector-current theorem. Taking its finite part gives
`FP int S*Delta(M_d)=mu*P(d)`. The native Darboux equation therefore yields

```
P''(d)+coth(d)*P'(d)=mu*P(d),   P(0)=C.
```

Smoothness at zero excludes the singular solution. Explicitly, a difference
`v` with `v(0)=0` satisfies
`v'(d)=mu/sinh(d)*int_0^d sinh(t)*v(t) dt`. Hence
`sup_[0,D] abs(v) <= abs(mu)*D^2/4 * sup_[0,D] abs(v)` for small `D`;
use `tanh(t/2)<=t/2`. It vanishes there, and ordinary nonsingular ODE
uniqueness extends this to every positive `d`. The normalized solution,
identified by `NativeCircleGauss.powerCircle_eq_legendre`, is thus

```
P(d)=C*powerCircle(eta,d)=C*legendreKernel(-eta,cosh(d)).
```

No temporal transform, cutoff interchange over unbounded time, source
nonvanishing premise, or replacement angular field enters this identity.
The required modularity and differential identities are the inspected
`NativeModularTransport.mean_modular`, `NativeCircleMean.mean_darboux`,
`mean_laplacian_commutes`, and `mean_zero`; the zero-radius period is
`OriginalScalarRestoration.original_square_finitePart`.

The original period's existence, zero-radius value, right-continuity, and
first two radius derivatives are kernel-checked in
`ThetaCuspHawkingBMOriginalCirclePeriod`. Its
`D4BMOriginalCircleGreen.original_modular_area` proves the scalar Green
identity on the complete curved modular domain.
`ThetaCuspHawkingBMOriginalCircleFlux` proves the full normal-flux expansion,
including every source/reader remainder product. Its
`counterterm_gap_eq_normal` identifies that expansion with the unchanged
original counterterm multiplied by the physical angular gaps. The exact
hyperbolic-to-planar measure identity then gives
`original_angular_measure_green_finitePart`: the original scalar reading of
`Delta(M_d)-mu*M_d` has zero finite part. This leaf passed its exact Lean
module audit. `ThetaCuspHawkingBMOriginalCircleEquation` now combines this
limit with the admitted radius derivatives and the genuine metric Darboux
equation. Its zero Wronskian, continuous original endpoint and nonvanishing
reader kernel prove `original_circle_period` and
`original_circle_finitePart_kernel` for every nonnegative radius, without a
nonzero source-coefficient premise. The exact leaf audit passed. Integration through the original finite null source rectangle is also
kernel-checked in `ThetaCuspHawkingBMOriginalCausalPeriod`, using
`fullNullResidual_eq_nativeResidualIntegral` and `radialResponse_null_native`,
with the original onset lift retained.

**A global Wronskian reconstruction avoids singular-ODE uniqueness.** The
same module proves `reader_powerCircle_ne_zero` for every actual Xi copy
and every real radius. Indeed `Im(mu)=(Re(zeta)-1)*Im(zeta)/2<>0`, and the
Legendre flux identity is

```
Im((I^2-1)*conj(Phi(I))*Phi'(I))
 = Im(mu)*int_1^I abs(Phi(v))^2 dv.
```

Together with `Phi(1)=1`, this excludes a zero at every `I>=1`. Write
`phi(d)=Phi(cosh(d))`. For the actual finite-height period minus its three
original counterterms, `Q_Y(d)`, let `E_Y(d)` be its scalar top flux minus
`sum_i (alpha_i-eta)*A_i*powerCircle(alpha_i,d)*B*Y^(alpha_i+eta-1)`.
Finite-domain Green and the native Darboux equation give the exact
reconstruction

```
Q_Y(D)=phi(D)*(Q_Y(0)+int_0^D du/(sinh(u)*phi(u)^2)
                         *int_0^u sinh(v)*phi(v)*E_Y(v) dv).
```

The apparent origin singularity is removable in the integrated expression.
On `[0,D]`, put `m_D=min abs(phi)>0`, `M_D=max abs(phi)`. Using
`(cosh(u)-1)/sinh(u)=tanh(u/2)<=u/2`, its error is bounded by
`(M_D/m_D)^2*D^2/4*sup_[0,D] abs(E_Y)`. Thus the original compact-radius
cusp-jet bounds suffice to recover `P(D)=phi(D)*C` directly from finite
cutoffs. This reconstruction/error estimate is analytical; its Lean
assembly and the full temporal/metric/QNM comparison remain open.

Alternatively, the already admitted period derivatives permit a shorter
origin argument after establishing the limiting equation. Extend the first
derivative to zero by its actual residual-jet integral minus the derivative
of the original correction. This extension is right-continuous. The weighted
Wronskian `sinh(d)*(phi(d)*P'(d)-phi'(d)*P(d))` is therefore continuous at
zero with value zero; its derivative vanishes for positive radius by the two
Darboux equations. The fundamental theorem of calculus gives zero Wronskian
on every finite radius interval. Since `phi` never vanishes, the quotient
`P/phi` has zero derivative and original value `C`, yielding `P=C*phi`.
This uses the original period's proved boundary regularity; its assembly
with the limiting equation remains to be formalized.

The characteristic value `I=1` does not justify differentiating
`arcosh(I)` separately. For the native mean minus its transported powers,
the integrated Darboux formula expresses its `I` derivative as
`(I^2-1)^(-1)*int_1^I Delta(remainder)(v) dv`. The numerator has the
matching factor `I-1`; applying the same formula to angular Laplacian
iterates controls the next parameter derivatives. The native bounds for
all angular jets therefore retain rapid cusp decay uniformly through the
characteristic. This is the required domination when differentiating the
original finite parts in the following finite parameter integrals.

**Direct null-rectangle producer and horizon domination.** The original
native residual already equals `nativeResidualIntegral`; its integrand is
the cutoff circle mean times the unchanged `sourceWeight`. The circle-period
identity gives the kernel-checked exact original scalar value

```
C*(radialResponse(-eta,s,amp,(p+r)/2,(p-r)/2)+nullLift(s,amp,p,r)).
```

The finite-rectangle Fubini proof uses the uniform compact-radius bound on
height times the circle residual and the integrable physical dual density.
The integrated three correction coefficients are exactly the original
`principalNullResponse` coefficients, so their restoration cancels them.
`ThetaCuspHawkingBMOriginalCausalPeriod.original_native_period` proves this
restoration. Its `original_causal_finitePart_radial` identifies the original
height-cutoff limit, retaining the source, reader, null Jacobian and complete
onset lift. The exact leaf audit passed.

There is also a direct analytical domination for its horizon limit. Apply
`timeReducedCoefficient_physical_bound` with `c=1`. On the negative radial
half, at source coordinates `((a+b)/2,(a-b)/2)`, its bound is `C_s*exp(-b)`.
Odd reflection and the exact zero at radial coordinate zero consequently give

```
abs(sourceWeight(s,amp,a,b)) <= C_s*exp(-max(a,b)),  a,b>=0.
int_0^infty int_0^infty exp(-max(a,b)) db da = 2.
```

For `0<=p<=r`, `0<=a<=p`, `0<=b<=r`, put
`h=(p+r-a-b)/2`, `x=(p-r)/2`, `y=(a-b)/2`. The actual invariant obeys

```
1 <= I = cosh(h)/(cosh(x)*cosh(y))+tanh(x)*tanh(y)
       <= 1+4*exp(p-max(a,b)) <= 5*exp(p).
```

Indeed `h+x-abs(y)=p-max(a,b)`, `cosh(h)<=exp(h)`, and each
of the two denominator factors is at least half its corresponding positive
exponential. The existing power-circle bound, with `G=Re(eta)>0`, gives
`abs(legendreKernel(-eta,I))<=10^G*exp(G*p)`. The original reduced scalar
response is therefore bounded by `C_s*10^G*exp(G*p)/2`, uniformly for
`r>=p`. This proves a value bound in the original ingoing time, without using
the weaker static-time exponent as a horizon estimate.

Writing `rho=exp(p-r)`, `E=exp(p-a)`, `z=exp(a-b)` gives the exact direct
invariant `1+2*(E-1)*(z-rho/E)/((1+rho)*(1+z))`. At fixed `p`, dominated
convergence using the same finite source mass identifies the reduced horizon
value with

```
(1/4)*int_0^p da int_0^infty db sourceWeight(s,amp,a,b)*
  legendreKernel(-eta,1+2*(exp(p-a)-1)*exp(a-b)/(1+exp(a-b))).
```

The displayed Legendre integral representation remains analytical.
`OriginalCausalAdmission` proves the characteristic growth and horizon-trace
estimates. `OriginalHorizonTimeTrace` proves the complete differentiable
trace and its damped temporal moments, including the separately explicit
original lift. The original metric-current and moving-boundary comparison
still require attachment; no cusp/time interchange follows from these
scalar horizon statements.

### Characteristic transport of the actual horizon traces

The quantitative horizon estimates can be obtained from the original
characteristic equation without differentiating the Legendre kernel. Write
`eta=1-zeta/2`, `G=Re(eta)`, `mu=eta*(eta-1)`, and

```
U(p,r)=radialResponse(-eta,s,amp,(p+r)/2,(p-r)/2),
D(p,r)=oddSource(s,amp,(p+r)/2,(p-r)/2)/4
       + mu*U(p,r)/(4*cosh((p-r)/2)^2).
```

The original physical source obeys `abs(source)<=A*exp(-max(p,r))`.
For a source point in the original null rectangle, the actual invariant
satisfies `1<=I<=3*exp(p)`. The circle representation consequently bounds
its kernel by `exp(G*log(6))*exp(G*p)`. The weaker separable source
majorant `A*exp(-(a+b)/2)` has finite quadrant mass. Thus
`abs(U(p,r))<=B*exp(G*p)` for every nonnegative `p,r`, uniformly toward
the horizon.

The original Goursat identity supplies genuine derivatives

```
U_p(p,r)=int_0^r D(p,b) db,
U_r(p,r)=int_0^p D(a,r) da,
U_pr(p,r)=D(p,r).
```

Odd reflection gives `D(p,r)=-D(r,p)`. The exact metric potential obeys
`1/(4*cosh(x)^2)<=exp(2*x)`. These identities give, with a common constant,

```
abs(D(p,r)), abs(U_r(p,r)) <= K*exp(p-r)*exp(G*p),  0<=p<=r,
abs(U_p(p,r)) <= 2*K*exp(G*p).
```

For the last estimate, split the first integral at `b=p`; reflection
turns its lower piece into minus the second null derivative at
`r=p`, and the upper piece has an integrable exponential majorant.
Integrating the actual derivatives toward infinity produces unique traces
`H(p),H1(p)` and the quantitative errors

```
abs(H(p)-U(p,r)), abs(H1(p)-U_p(p,r))
  <= K*exp(p-r)*exp(G*p).
```

All the displayed source, kernel, derivative, and reduced-trace estimates
are proved in `ThetaCuspHawkingBMOriginalCausalAdmission`. The estimates
also imply locally uniform convergence in positive `p`; on paper this
identifies `H1=H'`. That derivative-of-the-trace statement is not yet a
Lean theorem.

The full original scalar is `M=C*(U+nullLift)`, already identified with
the unchanged height finite part. The same leaf retains the lift's exact
horizon coefficient

```
ell_s = -s*(s-1)*power(2*s,2)*amp^2/4.
```

Its value tends to `ell_s*timeOnset(2*s,p)`, its first null derivative
tends to `ell_s*timeOnsetFirst(2*s,p)`, and its second null derivative
tends to zero. Hence the full `M` and the ingoing-time derivative
`M_p+M_r` have actual horizon limits; neither limit is set to zero.
The null second derivative vanishes in this limit.

**Meaning for full matching.** In compact horizon coordinates
`rho=exp(p-r)`, the physical ingoing-time derivative is `U_p+U_r`.
The reduced trace error is therefore `O(rho*exp(G*p))` for both the value
and the required time direction. `OriginalCollarCurrentBounds` now proves
this for the complete scalar, uniformly over all `p>0` and sufficiently
large `L=r-p`, with `rho=exp(-L)`. On this collar the lift radius is fixed:
its two radial derivative terms cancel in the genuine time derivative.
Only its value error remains; differentiability of its compact-radius
profile at `radialUnit=1` gives that error at rate `exp(-L)`.

The same leaf derives the unchanged normalizable reader's exact two-branch
decomposition. With `N_L=exp(-w*L/2)*g(w,-L/2)` and
`N_inf=connection(w,chi)*power(-w,2)/(2*w)`, it proves
`abs(N_L-N_inf)<=B*(exp(-L)+exp(-Re(w)*L))` at every nonreal frequency.
Combining this with the actual scalar and slope gives, for `Re(w)>G`,

```
abs(exp(-w*p)*(N_L*(m_L'(p)+w*m_L(p))-N_inf*(H'(p)+w*H(p))))
 <= B*(exp(-L)+exp(-Re(w)*L))*exp(-(Re(w)-G)*p).
```

The full original `timeOriginalForcing/horizonCoordinate`, at each angular
point, satisfies the corresponding reader-product error with
`G` replaced by `Re(2*physicalRate)`. Both scalar and gradient source
channels remain. These are kernel-checked bounds on the original
expressions, not an assumed leading-density decomposition. Clean scratch
and isolated exact leaf audit passed; the umbrella imports the leaf.
The forcing constant can depend on the angular point.
`OriginalCornerCurrentAdmission` proves absolute product-measure integrability
of these actual remainders on some collar `L>L0>0, p>0`: the source-current
remainder for `Re(w)>G`, and the full-forcing remainder at each angular point
for `Re(w)>0`, always with nonreal `w`. Joint continuity of the original
scalar supplies measurability of its parameterized time derivative; the
unchanged forcing factorization supplies its own measurability.

For both remainders, static-time indicators `p+L/2<T` and radial indicators
`L/2<T` exhaust the same product integral. Their integral difference tends
to zero. The physical chart Jacobian is the constant `1/2`, which preserves
this zero difference. Clean scratch and isolated exact leaf audit passed;
the umbrella imports the leaf. This closes the remainder cutoff comparison
without supplying an arbitrary leading-density ansatz. The leading horizon
term's first temporal moment and fixed radial normalization are now closed
for the retained scalar-horizon sector below. Complete angular finite-part
assembly and attachment to the original metric moving-corner integral remain necessary.
No continuation of the assembled action to QNM frequencies follows yet.

### Original temporal corner and fixed radial normalization — Lean closure

`ThetaCuspHawkingBMOriginalTemporalCorner` retains the actual `horizonTrace`
and `forcingTrace` at the unchanged physical coefficients. With
`H=horizonTrace`, `E=C*forcingTrace(s,amp,1,reducedGreenGradient(chi,s,1))`,
`N=connection(w,chi)*2^(-w)/(2*w)`, its density is

```
A(p)=mu*N*exp(-w*p)*(lambda*(H'(p)+w*H(p))+w*E(p)).
```

All polynomially weighted absolute moments are derived for `Re(w)>G`.
Uniform convergence of the original collar on `[0,1]`, including its exact
zero onset, proves `H(p)->0` as `p->0+`. The actual growth bound proves the
damped endpoint at infinity is zero. Half-line integration by parts gives
`Laplace(H')=w*Laplace(H)` and
`int p*exp(-w*p)*H'=w*int p*exp(-w*p)*H-Laplace(H)`.

Put `K=int A`, `J1=int p*A`, and
`triangle(T)=int_(0<=t<=T) int_(-t<=x<=0) A(t+x) dx dt`.
The corpus's triangular interval Fubini theorem gives its exact weighted
integral; the first-moment tail bound proves `triangle(T)-T*K -> -J1`.
The unchanged radial coordinate itself gives

```
T+log(horizonCoordinate(-T))/2 -> log(2).
```

Thus the difference between the temporal finite part and the time-first
radial leading integral with its prescribed logarithmic subtraction tends
to `-J1-log(2)*K`. For `Re(w)>3/2`, `Im(w)!=0`, this equals exactly
`physicalCornerCandidate`, including the original forcing derivative.
The normalization is derived; no adjustable constant or endpoint premise
is supplied. References: `original_horizon_onset_zero`,
`horizon_derivative_firstMoment`, `original_radial_log_shift`,
`original_corner_moment_eq_candidate`,
`original_temporal_radial_leading_difference`.

**Meaning for full matching:** the scalar-horizon first-moment mechanism
in the corner conjecture has an original-field proof. This is not the
complete angular/metric boundary attachment: the forcing remainder bound
is still pointwise in the angular variable. The exact forcing decomposition
below separately supplies its joint angular/horizon/time moment transfer.
The assembled action's continuation to the physical QNM remains open. Together with the admitted
remainder comparison above, this identifies exactly which angular and
metric attachment remains before the candidate residue can decide matching.
Clean scratch checking and the isolated exact leaf build passed; the umbrella
is wired without an umbrella build. The latest repository lint status is
recorded with the forcing leaf below.

Broad/deep/method retrieval was partial and predominantly source-only. Its
proposed forcing-period ingredient set used unrelated finite-period lemmas
and supplies no bridge. The proofs instead use the inspected original
characteristic derivatives, onset bounds, horizon basis and analytic radial
factors. Broad primary-paper retrieval found the
[stationary-clock threshold subtraction](https://arxiv.org/html/2606.02718v1):
its transfer-matrix expansion separates a threshold background from a
phase-delay observable. Its real compact-potential assumptions and clock
definition do not identify the HB action or authorize an additional
subtraction here.

### Original metric moving-corner attachment — angular-first collar

The fixed full-matching target is unchanged. The actual coordinate identity is
`horizonCoordinate(x)=(R^2-1)/R^2`, with `R=tortoiseRadius(x)`.
Together with `radiusLift=R*modeProfile(x)`, this cancels every extra radial
factor in the retained forcing slot. The derived original
angular-restored metric density, after multiplying by `R^2-1`, is

```
A_L(p)=mu*N_L*exp(-w*p)*((mu-2)*(m_L'(p)+w*m_L(p))
       +w*C*forcingProfile(s,amp,1,reducedGreenGradient(chi,s,1),u_L)
         *timeOnset(2*s,p)).
```

Here `m_L` is the unchanged original scalar and `N_L` the unchanged normalizable
reader, with `x=-L/2`. `original_metric_current_finitePart` identifies
`integral_a^b A_L` with `(R^2-1)` times the complete original metric angular
finite part, for `L>0`, `0<a<=b` and nonreal `w`. Its original source endpoints,
full forcing and all cusp-flux counterterms remain.

`original_metric_remainder_integrable` proves `A_L-A_infinity` integrable on
`(L0,infinity) x (0,infinity)` for some `L0>0`, when
`Re(w)>Re(readerExponent(q))` and `Im(w)!=0`. The exact decomposition retains
both the evolved source and forcing remainders. The latter separates into an
integrable radial error and the literal damped onset; no angular uniformity
assumption is inserted. The true radial derivative is `dR/dL=-(R^2-1)/2`.

Let `K=integral_0^infinity A_infinity(p) dp`. For `Re(w)>3/2`, `Im(w)!=0`,
`original_metric_collar_cutoff_difference` proves

```
(staticCut(A,L0,T)-radialCut(A,L0,T))/2
 -(T+log(horizonCoordinate(-T))/2)*K
 -> physicalCornerCandidate(q,branch,amplitude,w).
```

The static cut is `p+L/2<T`; the radial cut is `L/2<T`. Product integrability
makes the complete remainder's cutoff difference vanish. The leading
difference tends to `-integral p*A_infinity(p) dp`; the coordinate shift
tends to `log(2)`. Their fixed combination is exactly the original corner
candidate, including its source contact. This attaches the scalar-horizon
correction to the complete angular-restored metric collar.

**Formal status:** the new leaf `ThetaCuspHawkingBMOriginalMetricCorner` passed
a clean scratch check and its isolated exact leaf audit; its artifacts are
installed and its umbrella import is wired without an umbrella build. The full
matching target is unchanged. The angular finite part is taken first;
independent cusp/time/horizon limits, original onset removal, outer-region
assembly and continuation of the complete action to QNM frequencies remain
open. The original weighted temporal/height admission and bounded physical
projection are closed by `OriginalCuspTime` above. Metric endpoint and radial
trace control remain needed for the full joint comparison. No full matching,
impossibility theorem or finite-variation Jost expansion follows.

### Complete metric time-period assembly — Lean closure on compact time intervals

`ThetaCuspHawkingBMOriginalMetricTimePeriod` identifies the angular finite part
of the time-integrated original Einstein current at every fixed `R>1`, for
`0<a<=b` and nonreal independent temporal frequency `w`. Both source branches,
both original radial reader normalizations and every amplitude remain.

Write `x=tortoise(R)`, `f=R^2-1`, `mu=eigenvalue(q)`, and
`E=exp(w*x)*radiusLift(modeProfile(q,w,outer),R)`. Define

```
S(p)=R*E*exp(-w*p)*originalRadialPeriod(q,br,amp,p,p-2*x),
F(p)=E*horizonCoordinate(x)*C*exp(-w*p)*timeOnset(2*s,p)
       *forcingProfile(s,amp,1,reducedGreenGradient(chi,s,1),radialUnit(x)),
A=mu*(mu-2)/(R^2*f),  B=mu*R*w/f^2.
```

The actual finite part is exactly

```
A*(S(b)-S(a)+2*w*integral_a^b S(p) dp)+B*integral_a^b F(p) dp.
```

The proof starts with `modeMetricDensity` on the complete finite modular
domain. Derived smoothness supplies compact product integrability and Fubini;
the original reader equation transfers the time derivative while retaining
both endpoints. The finite-domain identity prescribes the counterterm as the
source endpoint counterterms, source moment counterterm, forcing moment
counterterm and the three complete top-flux powers. The original source,
forcing and boundary restoration theorems then prove convergence to the
displayed value. The derivative source and cusp flux are kept through their
exact cancellation; no finite constant is chosen to enforce matching.

**Formal status:** `original_metric_time_transfer` and
`original_metric_time_finitePart` passed a clean scratch check and the isolated
exact leaf build; the leaf is wired into the umbrella without an umbrella
build. This closes the correspondence between the original metric integral
and its assembled source/forcing expression on compact positive time
intervals. The angular-first moving time/horizon collar is attached above.
The full matching target is unchanged: original onset removal, independent
cusp/time/horizon limits, complete radial/outer assembly and continuation
of that assembled action to QNM frequencies remain open. A compact-time
identity does not justify interchanging those limits or establish a
finite-variation Jost representation. Full matching and its impossibility
are not proved.

### Original forcing angular period and joint cutoff moments — Lean closure

`ThetaCuspHawkingBMOriginalForcingAngularPeriod` uses the literal full forcing,
the unchanged angular reader and all three prescribed principal counterterms.
Put `J=fullSquarePotential`, `D=Delta(J)-mu*J`, and

```
P(u)=forcingProfile(s,amp,1,reducedGreenGradient(chi,s,1),u),
B(u)=u^3*(1+u)^(2*s)*amp^2*s*(s-1)/4.
```

The actual profile equals `P(u)*J+B(u)*D`, and its principal coefficients
have the identical decomposition. Before taking any limit, its regularized
angular integral therefore equals

```
profileCut(u,Y)=P(u)*squareCut(Y)+B(u)*greenCut(Y).
```

The original square period gives `squareCut(Y)->C`. The original angular
Green theorem, including the curved modular core and the derived normal-flux
counterterm, gives `greenCut(Y)->0`. Thus the forcing finite part is exactly
`C*P(u)` at every original radius; its derivative source was not discarded.

On the actual collar, `u_L=radialUnit(-L/2)`, the normalized original source
at `(t,x)=(p+L/2,-L/2)` is the full profile times `timeOnset(2*s,p)`.
The same factorization holds for its finite angular integral and counterterms.
For nonreal `w` with `Re(w)>0`, all damped polynomial time moments are admitted.
Retaining the actual normalizable radial reader `N_L` gives

```
lim_(P,L,log Y -> infinity) N_L * int_0^P p^n*exp(-w*p)*normalizedCut(L,p,Y)
 = N_inf*C*int_0^infinity p^n*exp(-w*p)*forcingTrace(s,amp,1,reducedGradient,p).
```

This is a joint limit with arbitrary relative cutoff rates, proved by the
exact finite-height decomposition. References: `original_profile_cut_decomposition`,
`original_profile_finitePart`, `original_normalized_cut`,
`original_forcing_joint_angular_horizon_moment`, `original_forcing_three_cutoff_moment`.

**Meaning for full matching:** the actual forcing/contact angular coefficient
and these coupled moments are identified. The remaining full-current task
is the evolved response and complete metric boundary/corner assembly, with
the original static-time triangular domain, followed by continuation of that
assembled action to the physical QNM. The independent rectangular moment
limit does not itself prove that whole-current comparison or its impossibility.

Clean scratch and exact isolated leaf build passed; only the leaf was built
(2 jobs), and its source-identical artifacts were promoted. The umbrella is
wired without being built. Repository lint reports the unrelated unreachable
`RHTower.SuzukiFourierLivsicSecondJet`; no error names this new leaf.
Broad and deep corpus retrieval supplied the original Green-flux ingredient;
other proposed method combinations were source-only or partial, not matching
proofs. The experiment review retains F186–F187 and F192's scope distinctions:
persistent spectral cancellation, lift/lift horizon background, and physical
drive versus geometric monitoring are different assertions from this matching.

**2. Identify the complete causal scalar and its needed horizon bounds.**
Set `s=D4BMModularCore.physicalRate(q,branch)` (the undoubled rate),
`k=mu/2-(s+1)*(s+2)`, and

```
kappa(a,z)=compactForcing(s,amp,a,z,1,k),
Phi(I)=legendreKernel(-eta,I).
```

The full gradient identity is `Delta(J)=2*(s+1)*(s+2)*J+gradientEnergy`.
Consequently the actual regularized period of each original compact source
circle is exactly `C*kappa(a,z)*Phi(I)`. This retains the gradient term,
the whole source polynomial, and the fixed onset. Let `m(p,rho)` be the
original potential's scalar finite part at
`r=p-log(rho)`. The compact retarded identity then gives

```
m(p,rho) = C/4 * (
 int_0^p da int_(rho*exp(a-p))^1 dz kappa(a,z)*Phi(I_direct)
 - int_0^p da int_(exp(a-p))^1 dz kappa(a,z)*Phi(I_image)).
```

For each finite `p`, both invariants satisfy `1<=I<=3*exp(p-a)`, uniformly
for `0<=rho<=1` on their original domains. Thus the native compact-radius
jet bounds justify moving the scalar finite part through these finite
integrals. This also constructs its actual horizon value at `rho=0`.

The elementary power-circle norm bound gives
`abs(Phi(I)) <= (2*I)^G`. Its Darboux equation gives
`abs(Phi'(I))<=K*(1+I)^(G-1)` and
`abs(Phi''(I))<=K*(1+I)^(G-2)`: use the integrated equation for the first
derivative, the differential equation for `I>=2`, and smoothness on `[1,2]`.
All fixed radial derivatives of `kappa` through order two have a bound
`K*exp(-sigma*a)`, with `sigma=-Re(2*s)>0`; its time derivatives have the
same bound after enlarging `K` on the fixed onset transition.

The direct invariant obeys the earlier relative derivative formula. For
the image invariant, the nonsingular formula valid even near `E=rho=1`
is `I_rho=-((I-1)+2*(z-1/E)/(1+z))/(1+rho)`. Both mixed derivatives
`E*d_E(I_rho)` are bounded by a constant times `1+I`. The moving direct
lower end has derivatives `1/E`, `-rho/E`, and `-1/E`; its possible
`I_z=O(E)` occurs multiplied by these compensating factors. The image
lower end is independent of `rho`. Differentiating the displayed finite
integrals therefore gives one constant with

```
abs(m)+abs(m_p)+abs(m_rho)+abs(m_p_rho) <= K*exp(G*p)
```

on `p>=0`, `0<=rho<=1`. Endpoint terms at `a=p` contain the same decaying
onset. At `rho=1`, direct and image integrals coincide, so
`m(p,1)=m_p(p,1)=0`; the derivative bounds give their additional factor
`1-rho` near the outer boundary. Set
`H(p)=m(p,0)` and `E_h(p)=C*kappa(p,0)/4`. The latter is the actual full
forcing divided by `z_h=4*rho/(1+rho)^2` at the horizon.

**3. Compare the original whole temporal current on its convergent band.**
With `x=log(rho)/2`, let `g(w,x)` be the unchanged normalizable left radial
mode. The actual metric-current formula, its original wave equation, and
the scalar/coexact finite parts give the following density in `dp dx`:

```
D_w(p,x)=mu*exp(-w*(p-x))*g(w,x) *
 (lambda*(m_p(p,rho)+w*m(p,rho)) + w*F(p,x)/z_h),
F(p,x)=C*rho*kappa(p,rho).
```

The sign uses the original equation `Z_tt-Z_xx-z_h*Delta(Z)=F`, as in
`OriginalCausalPotential.originalPotential_wave`. In the initial band
`3/2<Re(w)<2`, `Im(w)<>0`, the complete density equals its earlier
opposite horizon term `A_w(p)` plus a remainder bounded on a horizon
collar by

```
K_w*(rho+rho^Re(w))*exp(-(Re(w)-G)*p).
```

The remainder is absolutely integrable in the original `dp dx` domain.
At the outer boundary, `m`, `m_p`, the normalizable mode, and `F/z_h`
have the factors just established, so there is no additional divergent
edge. All first temporal moments of `A_w` converge. Thus the finite-cut
triangle argument applies to the complete scalar-transposed current,
not an arbitrary horizon ansatz. It yields the original-clock comparison

```
I_time(w)=I_radial,z(w)+mu*beta(w)*(lambda*a(w)+2*w*lambda*a'(w)+w*e'(w)),
a(w)=2^(-w)*Laplace(H)(w),  e(w)=2^(-w)*Laplace(E_h)(w).
```

Here `I_time=lim_T (int_0^T dt int_(-t)^0 dx D_w(t+x,x)-T*K(w))`.
The cusp finite part is taken from the original finite slab, with its
derived powers; compact parameter bounds justify that finite-slab
passage. The equality does not assert a different joint limit in `T,Y`.
`I_radial,z` retains the original radial `z_h` subtraction. The ordinary
time transform of `m` is `h=C*(continuedReducedGreen+radialLift)`:
the transformed original forced equation, vanishing Dirichlet boundary,
and the proved `m`/`m_rho` bounds give the original incoming Green
boundary conditions on this band. The nonzero original connection gives
uniqueness by its two-mode Wronskian. This supplies the same causal
family, rather than defining a replacement radial field.

**4. Eliminate the response from this comparison, retaining its source.**
Write `Fhat(w,x)` for the time transform of the complete scalar forcing
`F`; it is the scalar period of `JointSourceTimeLaplace`'s original
forcing transform. The correctly signed original radial equation is

```
h_xx-(w^2-mu*z_h)*h=-Fhat.
```

For `W(g,h_w)=g*(h_w)_x-g_x*h_w`, differentiation gives
`d_x W=2*w*g*h-g*Fhat_w`. At the outer endpoint `W=0`. At the horizon,
`h~2^w*a*exp(w*x)` and the opposite part of
`g~beta*2^(-w)*exp(-w*x)`, so its nondecaying contribution is exactly

```
beta*(2*w*a'+a+2*w*(x+log(2))*a).
```

Restoring the original `z_h` finite part therefore gives

```
I_radial,z = -mu*lambda*beta*(2*w*a'+a)
 + mu*lambda*int g*Fhat_w dx + mu*w*FP_z int g*Fhat/z_h dx.
```

Combining this with the actual moving-corner term cancels the whole
response-dependent expression, leaving the sharper positive formula

```
I_time(w) = mu*(
 lambda*int g(w,x)*Fhat_w(w,x) dx
 + w*FP_z int g(w,x)*Fhat(w,x)/z_h dx
 + w*beta(w)*e'(w)).
```

The first integral is ordinary on the initial band. Its continuation uses
its own derived endpoint finite part; it must not be silently declared
convergent at the QNM. Since `kappa(a,rho)=k_s(rho)*timeOnset(2*s,a)`,
the actual source has
`Fhat=C*rho*k_s(rho)*exp(w*x)*continuedOnset(s,w)` and
`e=2^(-w)*C*k_s(0)*continuedOnset(s,w)/4`.
In `rho`, the incoming first-integral densities have powers
`rho^w` and `rho^w*log(rho)`; one Taylor subtraction continues them to
`Re(w)>-2`. The incoming second integral has `rho^(w-1)`; two Taylor
subtractions suffice on the same strip. The opposite terms have only
integrable logarithms or the already prescribed single logarithmic
subtraction. Their coefficients are analytic at both original nonreal
fundamentals. The only new local Mellin denominators are `w`, `w+1`,
and `(w+1)^2`; none vanishes there. The unchanged full source onset is
analytic there as well. Hence this source-only expression has a
holomorphic germ at each original fundamental frequency.

**Meaning for full matching.** For the explicit original-clock finite part
above, the analytical comparison predicts removal of the response QNM
pole after including the corner. Equality with the uncorrected restored
radial pairing would require the entire displayed corner to vanish; the
vanishing of `beta(w0)` alone does not establish that. No nonzero source
coupling counterexample has been supplied, and no claim of impossibility
for every possible matching is made. The original-period identity is now
kernel-checked. The horizon/time admission below is also proved. The complete
metric-current attachment, its regularized corner comparison, and source-only
continuation still require Lean closure. A separately
prescribed physical time-cap or a direct fixed-frequency order of limits
must be identified with these explicit limits, not substituted for them.

### Original horizon/time moments — Lean closure

`ThetaCuspHawkingBMOriginalHorizonTimeTrace` derives the horizon value `H`
from the actual `OriginalCausalAdmission.originalScalar`. It retains the
original arithmetic coefficient, reduced causal response, and unchanged
onset lift. Uniform convergence of the genuine reduced first null
derivatives proves that the limiting slope is the derivative of the trace.
Thus the complete `H` is differentiable for every positive ingoing time.

Put `eta=1-q/2`, `G=Re(eta)`, and `r=p+L`. The original source estimates
give one constant `B` such that, for all sufficiently large `L` and every
`p>0`, the complete scalar has norm at most `B*exp(G*p)`. The lift separates
exactly into `radialLift(s,0,amp,1,-L/2)*timeOnset(2*s,p)`; its coefficient
converges to the original `liftHorizon`. For every natural `n` and
`Re(w)>G`, dominated convergence therefore gives

```
lim_L int_0^infty p^n*exp(-w*p)*originalScalar(p,p+L) dp
 = int_0^infty p^n*exp(-w*p)*H(p) dp.
```

All limiting moments are integrable. Differentiation with respect to the
independent complex frequency is derived under the integral using the
first moment and a common majorant on a smaller half-plane. In particular,

```
a(w)  = exp(-w*log(2))*Laplace(H)(w),
a'(w) = exp(-w*log(2))*(-log(2)*Laplace(H)(w)
          - int_0^infty p*exp(-w*p)*H(p) dp).
```

The domain contains the original Green band because `0<Re(q)<1` gives
`1/2<G<1`. Both physical branches and all amplitudes are included; no
nonvanishing source coefficient is assumed. The scratch check and isolated
exact module audit passed, and the leaf is wired into the umbrella.

This closes the actual response horizon amplitude's temporal admission
required by the moving corner. The following characteristic-transform
theorem supplies the scalar Green identification at `eta=1-q/2`.
Cusp/time interchange, the complete metric-current comparison and its
fundamental-QNM continuation remain open.

### Original scalar time/Green identification — Lean closure

`ThetaCuspHawkingBMOriginalCharacteristicTransform` identifies the actual
original causal scalar time integral, retaining the Xi reader exponent,
arithmetic source coefficient, source lift and smooth onset. Put
`eta=1-q/2`, `s=physicalRate(q,branch)`, `C=physicalSelfSourceCoefficient(q)`.
For both branches, every amplitude, every `x<0`, and every independent
frequency with `Re(w)>3/2` and `Im(w)!=0`, the proved identity is

```
int_0^infty exp(-w*t)*originalScalar(q,branch,amp,t+x,t-x) dt
 = C*(continuedReducedGreen(w,physicalRadialFrequency(q),s,amp,1,x)
       + radialLift(s,w,amp,continuedOnset(s,w),x)).
```

The proof starts with the original characteristic solution
`A(p,L)=nullValue(-eta,s,amp,p,p+L)`, its first partial derivative `P`,
and its mixed density `D`. One source-derived exponential bound admits
their positive-time transforms. The original zero onset and genuine
partial derivatives give

```
d_L Ahat = w*Ahat - Phat,
d_L Phat = Dhat.
```

The transformed literal source includes its onset-derivative term.
Consequently `exp(w*x)*Ahat(-2*x)` satisfies the original forced radial
equation. A causal-delay identity identifies this expression with the
actual reduced time integral. Its boundedness on the negative half-line
and its zero outer trace follow from the original response estimates.
The existing bounded radial Wronskian uniqueness theorem then identifies
it with `continuedReducedGreen`. The lift's causal-delay identity restores
the full scalar formula above; integrability is proved before splitting
the complete integral. No scalar matching or cusp/time interchange is
supplied as a premise.

Clean scratch checking and the isolated exact leaf build passed; the
umbrella import is wired. This closes the scalar-period comparison on its
convergence domain. It does not exchange the unprojected cusp and time
limits, attach all metric/source/contact/corner faces, or identify the
continued complete action at a QNM. In particular, it gives no
finite-variation QNM expansion for that action. The experiment's spectral
no-go becomes applicable only after deriving such a representation;
the existing peripheral-spectrum theorem additionally identifies any
persistent limit, within its damped-plus-integrable-continuum class, with
the actual zero-frequency atom.

### Original horizon continuation and corner response residue — Lean closure

`ThetaCuspHawkingBMOriginalHorizonGreenMatch` identifies the actual normalized
horizon transform `a(w)=exp(-w*log(2))*Laplace(H)(w)` with a single
meromorphic coefficient of the same original Green response. Equality holds
for `Re(w)>3/2`, `Im(w)!=0`, with the original first temporal moment retained.
The continuation is meromorphic throughout `Re(w)>-2`, `Im(w)!=0`.

The coefficient is the horizon limit of `continuedResponse/horizon`.
The existing local Green split identifies it with the actual positive-radius
quotient minus the integrated source transport. That source primitive is
analytic across the fundamental QNM, so the local endpoint expressions glue
and the quotient's original source residue transfers to this horizon amplitude.
No horizon amplitude or continuation is supplied as a premise.

Put `w0=physicalFundamentalFrequency(q,side)`,
`M=fundamentalSourceMoment(w0,s,amp)` and `T=continuedOnset(s,w0)`.
For both physical branches and either fundamental QNM, Lean proves

```
Res(a,w0) = C*M*T/(-connectionSimpleSlope(w0,chi,side)),
Res(connection(w,chi)*a'(w),w0) = C*M*T,
Res(beta(w)*(a(w)+2*w*a'(w)),w0) = C*M*T.
```

Subtracting the first displayed pole leaves an analytic germ, also when its
coefficient vanishes. On the convergence half-plane, differentiation of this
continued amplitude equals the first moment of the original causal horizon
trace, including the normalization's `log(2)` term.

**Meaning for full matching.** The response-trace part of the proposed corner
now has the source-derived residue `mu*lambda*C*M*T`. This is the coefficient
needed in the cancellation test above. The forcing trace and its continued
first-moment contact are now derived below. Complete angular finite-part
attachment, whole-current remainder admission, and prescribed spacetime
finite-part comparison remain open; full matching and RH remain open.
Clean scratch checking and the isolated exact leaf build passed without warnings;
the new leaf is wired into the umbrella. Global lint still reports the existing
unrelated unwired `RHTower.Sieve.KloostermanGlobalCollisionCoprime` module.

Broad primary literature search also found [Hansen's March 2026 Radon-transform
paper](https://arxiv.org/html/2603.10804v1): Mellin pole cancellations sharpen
boundary expansion estimates that otherwise predict excess logarithms. This
provides a method comparison for the corner calculation, not an HB admission
theorem; the original current's remainder estimates must still be proved.

### Original forcing trace and complete corner candidate — Lean closure

`ThetaCuspHawkingBMOriginalCornerForcing` derives the normalized horizon source
from `JointSource.timeOriginalForcing`, before angular subtraction. With
`u=radialUnit(x)`, its exact coefficient after dividing by `z_h=1-u^2` is

```
P(u) = -2*u*(1+u)^(2*s)*amp^2 *
  ((5*s^2+15*s+4)*J/4 + s*(s-1)*u^2*((s+2)^2*J-K)/4),
E(p) = P(1)*timeOnset(2*s,p).
```

Here `J=fullSquarePotential(q,z)` and `K=fullGradientEnergy(q,z)/2` are the
full original angular fields. At `x=-L/2`, the actual normalized source differs
from `E(p)` by at most `B*exp(-L)*exp(Re(2*s)*p)`, uniformly in all ingoing
times `p`, for sufficiently large `L`. The constant can depend on the angular
point; this is not an unproved uniform cusp estimate.

The original collar Laplace integrals are admitted for `Re(w)>Re(2*s)` and
converge to the same normalized transform
`e(w)=exp(-w*log(2))*P(1)*continuedOnset(s,w)`. Every temporal moment of `E`
is integrable there. Its frequency derivative is the original first moment,
including the normalization's `log(2)` term. No numerical input or assumed
horizon trace is used.

The full angular equation gives the exact basis decomposition
`P(1)=b0*J+b2*Laplacian(J)`, where

```
b0 = -2*2^(2*s)*amp^2 *
  ((5*s^2+15*s+4)/4+s*(s-1)*(s+2)*(2*s+3)/4),
b2 = 2^(2*s)*amp^2*s*(s-1)/4.
```

The original Green gradient slot satisfies `P(1;1,K_green)=b0+mu*b2`
at the actual physical radial parameter. This verifies coefficient consistency;
it does not itself transpose the angular Laplacian through a finite part.

At either physical fundamental QNM, the source pole `w=2*s` is separated from
`w0`. Thus `e` and its derivative are analytic there and `beta(w)*w*e'(w)`
tends to zero. Combining this with the already identified original response
amplitude proves, with every physical coefficient fixed,

```
Res(physicalCornerCandidate,w0) = mu*(mu-2)*C*M*T.
```

**Meaning for full matching.** The forcing contact introduces no extra QNM
residue; the entire proposed corner has the response residue required by the
comparison test. Its equality with the original full spacetime finite part is
still unproved. The next obligation is the original current's angular
finite-part attachment and integrable remainder, followed by its exact finite
triangle/time-cap comparison. This result proves neither extinction nor RH.

Clean `lake env lean` scratch check and isolated exact leaf `lake build` passed
without warnings; the leaf is wired into `RHTower`. The final build ran two jobs
and took 37 seconds. Global lint reports only the existing unrelated unreachable
`RHTower.Sieve.KloostermanGlobalCollisionCoprime` error, alongside existing
large-file warnings.

## Complete original scalar and static current — Lean closure

`ThetaCuspHawkingBMOriginalOrbitCurrent.scalar_green_integral` supplies the
actual scalar Green transfer. Its specialization in
`ThetaCuspHawkingBMOriginalModularOrbit` fixes the full finite-cutoff current.
Let `U=sourceScalar`, `W=leftScalar`, `D_j=orbitDerivative`,
`mu=eigenvalue`, `lambda=mu-2`, `f=R^2-1`, and `F=originalForcing`.
Write `P(A,B)` for the literal truncated angular period and `T(A,B)` for
the actual top transfer. The complete boundary contribution is

```
B_j = T(D_j U,C(W))-T(C(U),D_j W)
      +mu*(T(D_j W,U)-T(U,D_j W)).
I_j = R^-2 * [mu*lambda*(P(U,D_j W)-P(D_j U,W))
               +mu*R^3/f*P(F,D_j W)+B_j].
```

The last Green flux comes from transferring the source Laplacian; it cannot
be omitted or covered by the existing theorem for only the first two terms.
The actual reader's time derivative is `W_p=-w*W`. Consequently the static
current with its physical orientation satisfies

```
I_0-I_1/f = mu*lambda/(R^2*f)*(P(U_p,W)+w*P(U,W))
            +mu*R*w/f^2*P(F,W)+(B_0-B_1/f)/R^2.
```

These are `original_source_orbit_green`, `original_forced_orbit_period`,
`original_metric_complete_scalar_integral`, `original_reader_time_derivative`
and `original_static_metric_scalar_integral`. They retain the literal source,
physical left QNM, complete forcing and finite angular periods, for all source
branches, reader sides, radial normalizations and amplitudes at `p>0`, `R>1`,
`Y>=1`. No assumed original source regularity, extra mode equation or division
by the source coupling is used.

**Meaning for full matching.** The temporal scalar density and all finite-domain
boundary terms are now derived from the original metric current. The next
section supplies the complete `B_j` cusp attachment at fixed time and radius.
The open comparison must still attach the varying-frequency family, bound the
full horizon remainder and identify the finite causal triangle/time-cap
correction. The existing corner candidate residue is not yet
a residue of that complete spacetime finite part.

Both clean scratch checks and isolated exact module builds passed without
warnings (117 seconds and 27 seconds; two jobs each). Both modules were already
wired into `RHTower`; no umbrella was built. Global lint still fails on the
unrelated unreachable `RHTower.Sieve.KloostermanGlobalCollisionCoprime`, with
existing large-file warnings. Source and audited copies agree byte for byte.

## Complete scalar-transposition cusp attachment — Lean closure

The additional Green flux in the full scalar reduction is now attached to
the original source and orbit reader. `OriginalCuspFlux.scalarGreenFlux`
is `S*partial_y(Z)-Z*partial_y(S)`. Its exact principal coefficients are
`coefficient_i*readerCoefficient*(principalExponent_i-readerExponent)`;
`original_scalarGreenFlux_expansion` proves that the integrated remainder
decays after every complex height weight, with all source/reader tail products
retained at fixed nonnegative null coordinates.

`OriginalContactCusp.original_source_normal` derives the physical normal
derivative of `U=R*Z`, retaining `R`. Write `alpha_i=principalExponent_i`,
`beta=readerExponent`, `b=readerCoefficient`, `A_i=R*coefficient_i`, and
`ell_j=readerOrbitAmplitude`. If `M_ji` denotes the previous signed two-transfer
metric coefficient, the complete coefficient is

```
N_ji = M_ji + mu*ell_j*b*A_i*(alpha_i-beta)/R^2,
gamma_i = alpha_i+beta-1.
```

`complete_scalar_top_cusp_limit` proves

```
B_j(exp(k))/R^2 - sum_i N_ji*exp(gamma_i*k) -> 0.
```

`complete_scalar_top_finitePart` subtracts only the nonconstant powers and
retains exactly `sum_{gamma_i=0} N_ji`. The original diagonal/reflected readers
have no such exponent, so their complete constant term is zero
(`complete_scalar_cusp_constant`). This classification keeps the possible
constant of an independent reader.

`original_static_cusp_transfer` then applies the actual finite-domain metric
identity. The static metric integral minus its full forced scalar periods has
exactly the subtraction coefficients `N_0i-N_1i/(R^2-1)`, and the subtracted
difference tends to zero. All source branches, reader sides, radial
normalizations and amplitudes are retained.

**Meaning for full matching.** The missing third cusp transfer in the preceding
section is closed at each fixed `p>0,R>1` for the original fundamental-QNM
reader. A fixed-point angular limit does not prove the compact-parameter
passage or an interchange with infinite time and the horizon. The following
frequency-family results now attach the reader and complete finite-domain
current on the convergence band. The original causal triangle/time-cap
comparison must still identify the corner correction. Neither full matching nor its impossibility
has been established.

Both clean scratch checks and isolated exact module audits passed without
warnings (25 seconds for `OriginalCuspFlux`, 32 seconds for
`OriginalContactCusp`; two jobs each). Both modules were already umbrella-wired;
no umbrella build ran. Global lint reports 159 existing large-file warnings
and the unrelated unreachable `RHTower.Sieve.KloostermanGlobalCollisionCoprime`
error. Audited copies match source byte for byte.

## Independent temporal-frequency reader — analytical attachment

Fix the original arithmetic source and reader labels `q,r`, and leave only
the temporal frequency `w` independent. Use the existing physical family
`physicalLeftModeStream r w outer`, with its unchanged radial mode
`g_w=tortoiseMode outer w (physicalRadialFrequency r)` and angular scalar `S`.
For every nonreal `w`, the continued radial equations give
`g_w''=(w^2-mu*z_h)*g_w`. Both radial normalizations have their actual first
and second derivatives; the smooth linear ODE gives all spacetime derivatives.

For `f=R^2-1`, `x=tortoise(R)`, and `H_w(R)=R*g_w(x)`, differentiation gives

```
H_w'  = g_w+R*g_w'/f,
H_w'' = (R*g_w''-2*g_w')/f^2,
-R^2*f*H_w''+R^2*w^2*H_w/f-2*R*H_w' = (mu-2)*H_w.
```

Hence the actual ingoing scalar
`W_w=exp(-w*(p-tortoise(R)))*H_w(R)*S` satisfies
`C(W_w)=(mu-2)*W_w`, `Delta(W_w)=mu*W_w`, and
`partial_p(W_w)=-w*W_w`. Its coexact derivative is the existing physical
stream, and composing with the original ingoing coordinate map returns that
same static stream. At `w=frequency r side`, this is definitionally the
previous original QNM reader and metric current.

The reconstructed metric-current identity applies to these actual smooth
stream jets. With the original source `U` and its full forced contact `D`,
it gives `R^-2*(pairing(D_j U,C(W_w))-pairing(D,D_j W_w))`.
Thus the same source, clock and normalization cover the Laplace convergence
band and the prescribed QNMs; no hypothesized matching identity supplies
the family. `OriginalReaderEquation` now proves this attachment in Lean:
`modeProfile_smooth`, `mode_scalar_contact`, `mode_angular_equation`,
`mode_time_derivative`, `mode_coexact`, `mode_metric_current_eq` and
`mode_metric_density`. `modeScalar_specialize` and
`modeMetricDensity_specialize` recover the original reader and current by
definitional equality. The clean scratch check and isolated exact module
audit passed; the audit built only this leaf (94 seconds, two jobs).
The complete angular-period and finite-time extensions are closed below.

**Meaning for full matching.** For fixed arithmetic labels, the cusp powers
`alpha_i+beta-1` do not depend on temporal `w`. Its variation changes the
reader amplitudes and their orbit derivatives. Consequently the angular
transfer can be organized as a finite linear combination of the same original
source angular periods and cusp fluxes. The remaining limit comparison must
still control the original time/radius domains and identify their moving
corner; this separation alone does not prove that comparison or RH.

### Complete frequency-family transfer — Lean closure

`OriginalModularOrbit.mode_metric_complete_scalar_integral` proves the
complete finite-domain metric identity for `W=modeScalar r w outer`, every
nonreal `w`, both original radial normalizations, and unchanged source data:

```
I_j = R^(-2) * [mu*(mu-2)*(P(U,D_j W)-P(D_j U,W))
                +mu*R^3/f*P(F,D_j W)+B_j].
B_j = T(D_j U,C(W))-T(C(U),D_j W)
      +mu*(T(D_j W,U)-T(U,D_j W)).
```

The proof applies the actual reader equation, full original forced contact,
and modular side/core cancellations. `mode_static_metric_scalar_integral`
then proves the original static combination

```
I_0-I_1/f = mu*(mu-2)/(R^2*f)*(P(U_p,W)+w*P(U,W))
            +mu*R*w/f^2*P(F,W)+(B_0-B_1/f)/R^2.
```

`modeCompleteTopFlux_specialize` returns the old complete QNM flux by
definitional equality. These identities hold at fixed `p>0,R>1,Y>=1`;
no temporal or horizon interchange is part of their statement.

`mode_time_transfer` separately integrates the actual source derivative at
fixed exterior radius and angular point, on every `0<a<=b`:

```
integral_a^b (U_p+w*U)*W dp
  = U(b)*W(b)-U(a)*W(a)+2*w*integral_a^b U*W dp.
```

Both endpoint values are retained. The proof derives the clock derivatives
from the original smooth fields and uses `W_p=-w*W`; it does not assume a
derivative formula for an already regularized angular period. Thus a route
to the subsequent limit comparison is to perform this transfer at finite
cutoffs, then pass the original source-value and boundary-flux finite parts.
The source-value compact angular/time interchange, including onset and
every polynomial time moment, is closed below. The complete metric boundary
flux is also restored on compact time intervals below; the unbounded causal
triangle still needs its own limit proof.

**Meaning for full matching.** The former frequency-family attachment gap is
closed for the full original finite-domain current. The remaining task is
to control its actual cutoffs and identify the moving corner, including its
residue. The corner candidate alone is not that identification.

The clean scratch check and isolated exact `OriginalModularOrbit` audit
passed without warnings (52 seconds, two jobs); the module was already
umbrella-wired. Only existing compiled dependencies were copied into an
isolated cache to avoid another agent's concurrent cache updates; no
dependency or umbrella build ran.

### Compact original cusp/time restoration — Lean closure

`OriginalCausalPeriod` now derives one integrable angular envelope for
`S*originalCutoffResidual(p,r)` uniformly over `0<=p,r<=T`. Its construction
retains the original circle kernel, compact modular core, all three smooth
cutoff corrections and the unchanged onset lift. If `P_Y` denotes the
literal finite-height scalar period minus the prescribed counterterms and
`P` its original restored radial value, then for `Y>=4`

```
P_Y(p,r)-P(p,r) = -integral_{height>Y} S*originalCutoffResidual(p,r),
sup_{0<=p,r<=T} norm(P_Y-P) <= integral_{height>Y} G -> 0.
```

The supremum notation summarizes the proved pointwise uniform bound;
`original_finiteHeight_uniform_error` supplies one real error function for
all targets. `original_finiteHeight_sub_radial` proves the exact identity.
Actual time-continuity follows from the original moving-rectangle integral
representation and domination, so the passage is not based on undefined
Bochner integrals. For every `n : Nat`, every complex `w`, `0<=a<=b`, and
fixed `x<=0`, `original_compact_time_moment_restoration` proves

```
lim_{Y->infinity} integral_a^b p^n*exp(-w*p)*P_Y(p,p-2*x) dp
  = integral_a^b p^n*exp(-w*p)*P(p,p-2*x) dp.
```

The onset endpoint is included. The first moment is the one entering the
moving-corner comparison; no temporal-frequency restriction is needed on
this compact interval. Independently,
`original_remainder_jet_compact_rapid_bound` proves arbitrary-order cusp
decay for every log-height angular jet of the full original source,
uniformly over bounded null targets and all horizontal positions. It adds
the actual bounded onset lift to the corpus's compact native-response jet
estimate.

**Meaning for full matching.** The source-value period and its compact time
moments can now pass through cusp restoration. Uniform source angular jets
are available for the complete metric cusp-flux attachment. Its forcing
flux and the unbounded causal triangle/horizon comparison remain to be
assembled; these theorems do not identify the whole metric action or prove
RH. Clean scratch and the exact isolated leaf audit passed without warnings
(42 seconds, two jobs). Only this leaf was built; it was already wired into
`RHTower`. Global lint still reports the unrelated unreachable module
`Sieve.KloostermanGlobalCollisionCoprime`.

The recent boundary-renormalization papers inspected during this step do
not discharge an HB hypothesis. Ivanov's
[quartic-model gluing theorem](https://arxiv.org/html/2608.23069v1)
requires additional interface counterterms in its compact Riemannian
setting. The [variational prescription](https://arxiv.org/html/2607.14330v1)
studies Euclidean black-hole solutions and subtracts finite exact variations
according to an ensemble choice. Neither identifies our fixed original
Lorentzian causal subtraction. The finite-height tail identity above is
derived instead from the corpus's actual source and prescribed counterterms.

### Static boundary cancellation removes reader radius derivatives

Apply the original physical static combination before any limit. Bilinearity
of `T(A,B)=integral(A*partial_y B)` and `W_p=-w*W` give

```
D_0 U-D_1 U/f = -U_p/f,
D_0 W-D_1 W/f = w*W/f,
(B_0-B_1/f)/R^2 =
  [-lambda*T(U_p,W)-w*T(C(U),W)
   +mu*w*(T(W,U)-T(U,W))]/(R^2*f).
```

Every radius derivative of the physical reader cancels in this actual static
boundary combination. With the notation `A_i`, `C_i`, `alpha_i`, `beta`, `b`
above and `W=ell*S`, its principal coefficient is

```
-ell*b/(R^2*f) *
  [beta*(lambda*partial_p(A_i)+w*C_i)
   -mu*w*A_i*(alpha_i-beta)].
```

This is an analytical consequence of the complete current, not a new source
ansatz. For the whole matching problem it reduces the required static collar
control to the original source time derivative, full forcing and reader value;
no reader radius-derivative bound is needed for this combined boundary term.
The source-value compact cusp passage is proved above; the complete flux
attachment and moving-corner comparison remain necessary.

At finite angular cutoff, further integration by parts on `0<a<=b` gives
an explicit normal form for that remaining flux. Since
`partial_p T(U,W)=T(U_p,W)-w*T(U,W)`, and the original forced equation is
`C(U)=Delta(U)-2*U+R^3*F/f`,

```
integral_a^b (B_0-B_1/f)/R^2 dp =
  [-lambda*[T(U,W)]_a^b
   +w*integral_a^b (mu*T(W,U)-T(Delta(U),W)
                    -2*lambda*T(U,W)-R^3*T(F,W)/f) dp]/(R^2*f).
```

This identity is now proved in Lean as
`OriginalModularOrbit.mode_complete_boundary_time_transfer`;
`mode_static_top_flux` proves the preceding static identity. The proof
derives all compact integral admission and Fubini hypotheses from the
actual fields, commutes the smooth reader derivatives, and keeps both
original endpoint values. The full forcing boundary term is retained.
Treating `C(U)` as `Delta(U)-2*U` would omit that term.

Clean scratch and the isolated exact leaf audit passed without warnings
(99 seconds, two jobs). The existing umbrella import is retained; no
dependency or umbrella build ran. Global lint still reports the unrelated
unreachable `Sieve.KloostermanGlobalCollisionCoprime` module.


### Complete compact-time cusp boundary — Lean closure

Fix `0<a<=b`, `R>1` and a nonreal temporal frequency `w`. Write
`W(p,R,z)=ell(p)*S_r(z)`, `S_r~c_r*y^beta`,
`U~sum_i A_i(p)*y^alpha_i`, with the original source amplitudes
`A_i(p)=R*coefficient_i(p,p-2*tortoise(R))`. The actual forcing has coefficients

```
F_i(p)=(forcingValueCoefficient(p)
       +forcingLaplacianCoefficient(p)*alpha_i*(alpha_i-1))*principalAmplitude_i.
```

The exact time-integrated boundary theorem fixes its three coefficients:

```
K_i = { -lambda*beta*c_r*[ell*A_i]_a^b
        +w*c_r*integral_a^b ell(p)*
          ((mu*alpha_i-beta*alpha_i*(alpha_i-1)-2*lambda*beta)*A_i(p)
           -beta*R^3*F_i(p)/f) dp }/(R^2*f).
```

These coefficients come from the unchanged metric current and its original
source contact. They are not freely chosen subtractions. The paper proof
of the corresponding compact-time cusp expansion is:

1. F198 gives arbitrary-order uniform cusp decay of source remainder jets
   on the bounded null rectangle containing `(p,p-2*tortoise(R))`.
   In log height, `partial_y=exp(-k)*partial_k` and
   `Delta=exp(2*k)*partial_X^2+partial_k^2-partial_k`. Thus the value,
   normal derivative and `Delta U` retain uniform rapid remainders.
   Only source jets through order two are needed: the normal derivative
   in `T(Delta U,W)` acts on `W`, not on `Delta U`. The extra exponential factors are absorbed by choosing
   a higher order in F198.
2. `OriginalMetricCusp.original_forcing_laplacian` expresses the full forcing
   as its two continuous time coefficients multiplying the original square
   source and its angular Laplacian. Those coefficients are bounded on
   `[a,b]`; the existing native cusp-jet estimates give the forcing remainder
   uniformly in time. This uses the full gradient-energy contribution.
3. The actual reader amplitude `ell` is bounded on `[a,b]`. Its complete
   angular scalar and normal derivative have their original principal terms
   and uniform rapid tails. Products with the source expansions leave only
   the powers `gamma_i=alpha_i+beta-1`; all product errors tend uniformly to
   zero in time and horizontal position. Integrating over the finite time
   interval and width-one top edge preserves this convergence.
4. Apply the exact boundary theorem, retaining both endpoint expansions.
   Its four transfer coefficients give precisely the displayed `K_i`. Hence

```
lim_{k->infinity} [ integral_a^b (B_0-B_1/f)(p,R,exp(k))/R^2 dp
                   -sum_i K_i*exp(gamma_i*k) ] = 0.
```

`OriginalCuspFlux.fluxExponent_nonzero_original` shows that every `gamma_i`
is nonzero for the original diagonal/reflected angular readers, independently
of `w`. Consequently their prescribed compact-time boundary finite part is
zero. `OriginalCompactBoundary.mode_complete_boundary_compact_cusp`
proves this exact complete-boundary expansion, and
`mode_complete_boundary_compact_finitePart` proves the zero prescribed finite
part for both original arithmetic reader relations. Its
`compactBoundaryCoefficient` expresses the displayed coefficient through
the four original transfer moments, retaining both endpoints.

The new leaf passed a clean scratch check and an isolated exact module
audit. It is umbrella-wired; no dependency or umbrella build ran.
`OriginalCuspFlux.original_source_logarithmic_remainders` supplies the exact
log-coordinate conversion used by the uniform estimates and passed its own
exact leaf audit. The original `OriginalContactCusp` module is unchanged.

This does not include `a=0` or a joint/unbounded time-height-horizon limit.
The next whole-route obligation is the original unbounded causal-triangle
comparison and its first temporal moment, with the actual current remainder
proved integrable before comparing the two finite-part prescriptions.

A broad literature search found the
[superfluid memory calculation](https://arxiv.org/html/2608.31172v1), where a
vanishing zeroth pulse moment coexists with a nonzero first-moment memory
at the stated EFT order. This supplies no HB premise; it is a useful
comparison for retaining the first moment in the corner calculation.
The [time-dependent medium scattering construction](https://arxiv.org/html/2602.19981v1)
uses operator-valued frequency coupling and a compact spacetime perturbation;
it does not identify our original metric/current or its subtraction.

The [2026 Radon mapping analysis](https://arxiv.org/html/2603.10804v1)
resolves boundary degeneracy geometrically and uses Mellin pole cancellation
to remove logarithmic terms overpredicted by general mapping estimates.
This suggests inspecting the actual coupled corner coefficients before
inferring an obstruction from separate face estimates; its Radon hypotheses
and density are not HB premises. The
[2026 AKSZ corner analysis](https://arxiv.org/html/2608.02928v1)
organizes signed face defects under an explicit formal mapping-space
hypothesis. That identity does not provide the analytic trace or unbounded
integral admission required by our original current.

## Actual RH closing obligation

The active target is the literal augmented Einstein causal pairing and its
fixed-clock extinction. The overtone source-moment argument below is an
unproved auxiliary approach; completing it alone does not close this target.

The constructed original retarded potential has its exact source-action
identity, joint interior smoothness and smooth future-horizon extension in
Lean (`OriginalRetardedIdentity.originalPotential_eq_retarded`,
`OriginalSpacetimeRegularity.originalPotential_smooth`, and
`OriginalHorizonRegularity.horizonPotential_smooth`, with the
`ThetaCuspHawkingBM` module prefix). The theorem
`OriginalHorizonRegularity.originalPotential_horizon_limit` identifies its
actual horizon trace with the complete compact-source integral. The source
and both image domains are retained before taking the limit.

The regular ingoing formulas for all four action-current components and
their attachment to the actual reconstructed causal metric fields have
passed exact Lean module audits in `ThetaCuspHawkingBMIngoingFullCurrent`
and `ThetaCuspHawkingBMActualIngoingCurrent`; both leaves are wired into
`RHTower`. The original causal current also vanishes identically in an
explicit horizon neighborhood on every finite static-time slab. That
neighborhood depends on the slab's time bound. The original left
QNM has the exact factor `exp(-w*p)*(1-1/R)^w`; its singular power must be
retained alongside the causal field's smooth horizon extension. The
current coefficients and finite Taylor subtractions are derived below.
The complete boundary pairing and its fixed-clock extinction remain open.

## Original modular boundary — Lean closure

**Lean:** `ThetaCuspHawkingBMOriginalModularGreen` passed its exact module
audit and is wired into `RHTower`. For the same full causal source `Z` and
physical reader `S`, modular pullback preserves `Z`, `S` and `Delta Z`. Differentiation transports each
scalar differential with the actual reciprocal-square Möbius Jacobian.
Consequently the weighted current `J=(Delta Z)*grad S-mu*S*grad Z`
transports as a covector; no scalar potential for `J` is required.
Inversion sends a radial vector at `z` to the negative radial vector at
`S*z`. On the unit circle it pairs `(X,Y)` with `(-X,Y)`, yielding

```
(X/Y)*(J_X(-X,Y)-J_X(X,Y))-J_Y(-X,Y)-J_Y(X,Y)=0.
```

Translation pairs the vertical-side currents. Apply the corpus's genuine
area-measure vector-current Green identity, separately to the real and
imaginary parts. Both side and circular boundary integrals cancel, leaving
`integral_domain(Y) defect = cuspFlux(Y)`. This is the actual curved
modular domain, including its compact lower core. Combining it with the
proved cusp-flux expansion gives a finite part equal to the grouped
constant coefficient; diagonal and reflected physical readers give zero.
Theorems `current_modular`, `original_arc_cancellation` and
`original_modular_area` prove the original boundary and area identities.
`original_modular_finitePart` retains every independent-reader constant
coefficient. `diagonal_modular_finitePart` and
`reflected_modular_finitePart` prove the two zero limits, with the compact
core and actual curved boundary included. This closes this angular
transposition. It does not settle the temporal, horizon, onset-corner or
joint counterterm limits of the full spacetime action.

### Original physical metric current — Lean closure

`ThetaCuspHawkingBMOriginalAngularCurrent` passed its exact module audit and
is wired into `RHTower`. Let `U=R*Z_tilde` be the actual reconstructed original
causal scalar, and let `W=ell*S` generate the unchanged original physical left
stream. For `B(F,G)=(Delta F)*grad(G)-(Delta G)*grad(F)`, the theorem
`original_physical_metric_current` proves both angular components of the
actual metric Einstein current are exactly

```
R^(-2)*(f*B(U_R,W_R)+B(U_R,W_p)+B(U_p,W_R)).
```

This holds for independent source and reader Xi occurrences, either source
branch, either physical fundamental frequency and either original radial
normalization, on `p>0`, `1<R<3`, `Y>0`. `leftStream_static` identifies the
actual test with the original static `physicalLeftModeStream` before its
metric derivatives are evaluated. Both fields' required smoothness and
coexact reconstruction are proved from their original definitions. No
regularity, left-mode admission or field-equation premise is supplied.
The generic `coexact_current` identity uses actual scalar derivatives and
commutes the mixed jets on neighborhoods; it is not an identity on freely
assigned derivative slots. The integrated spacetime pairing remains open.

### Original parameter boundary transfer — Lean closure

**[BRIDGE].** `ThetaCuspHawkingBMOriginalGreenBoundary` passed its exact module
audit and is wired into `RHTower`. This is a derivative-transfer theorem for
the original physical current, not a new restriction on Xi occurrences.

First, `originalPotential_exterior_smooth` composes the original joint
null-coordinate regularity theorem with
`(p,R,X,Y) -> (p,p-2*tortoise(R),X,log(Y))`. For every `R>1`, the tortoise
coordinate is negative, so the two null coordinates lie in the proved
interior region. The reconstructed scalar and stream are therefore smooth
on all `p>0`, `R>1`, `Y>0`; no upper-radius bound remains.
`original_metric_current_eq` identifies all four components of the actual
reconstructed metric current with their ingoing stream formulas, with the
unchanged original physical left field and both radial normalizations.

Write `B(F,G)=(Delta F)*grad(G)-(Delta G)*grad(F)`, and set

```
C=R^(-2),              A=1-C,                D=-2*R^(-3),
BR=A*B(U,W_R)+C*B(U,W_p),
Bp=C*B(U,W_R),
E=-D*B(U,W_R)+D*B(U,W_p)+A*B(U,W_RR)
    +C*B(U,partial_R partial_p W)+C*B(U,partial_p partial_R W).
```

The actual bilinear rule
`partial_i B(U,W)=B(partial_i U,W)+B(U,partial_i W)`, for `i=p,R`,
and the differentiated inverse-square weight give exactly

```
J^angular=partial_R BR+partial_p Bp-E.
```

`greenPair_partial` proves the rule on genuine field germs.
`original_current_boundary` and `original_metric_boundary` attach this
identity to the original causal source and metric, respectively.
`original_rectangle_boundary` then proves, for every finite rectangle with
`0<p0<=p1` and `1<R0<=R1`,

```
int_p int_R J^angular
 = int_p [BR]_(R0)^(R1)+int_R [Bp]_(p0)^(p1)-int_p int_R E.
```

All four oriented edges remain. Original field regularity supplies the
fundamental-theorem and Fubini hypotheses. Every term on the right contains
only angular derivatives of the source; time and radial derivatives act on
the original reader. No cusp limit is differentiated.

**Whole-route assessment.** The generic identity uses no special Xi-zero
arithmetic: that enters only when specifying the actual fields. Hence this
bridge cannot supply source-coupling nonvanishing or extinction. Its intended
use is to justify angular transposition in the complete original spacetime
pairing using undifferentiated source flux and retained edge terms. Further
local derivative-transfer variants are not the closing obligation.

The relevant correspondence already has two concrete sides in the corpus.
`PhysicalWeightedResponse.physicalJointProjection_height_integral` is the
literal bilinear scalar-reader integral of the height-admitted response.
`PhysicalCausalGreenBand.causalPhysicalProjection_original_profile` identifies
its actual Green profile in the right half-plane. But, by the original
field definitions,

```
originalPotential
 = fullNullResidual
   +sum_i principalNullResponse_i*cutoffPower_i
   +nullLift*sourceProfile.
```

Thus comparison with the original reconstructed Einstein pairing must
retain the three transported principal terms, the full onset lift and their
metric boundary contacts. Establishing this correspondence and its permitted
continuation to the original physical QNM is the next route-level target.
No equality of these complete pairings is asserted here. The source/onset
nonvanishing and fixed-Hawking-clock extinction obligations remain unchanged.

This scope decision applies the two project methods: the repeated irritant
is the source-derivative/cusp-limit interchange; the proved bridge moves those
derivatives to their actual edges. Asking where the argument uses Xi exposes
why it is not an RH-closing conjecture. The correspondence between the full
field and its weighted projection must be proved, not inferred from their
similar names or from local current identities.

### Full original scalar restoration

Use the same physical reader as the original self-response. Write
`rho=q.1`, `C=reflectedCompletedLambda(rho-1)`,
`alpha_i=principalExponent(q,i)` and `e_i=alpha_i-rho/2`.
The corpus proves every `e_i` and every same-copy angular gap nonzero.
`ThetaCuspHawkingBMOriginalScalarRestoration` passed its exact leaf audit.
For the literal modular integral truncated at height `Y`, it proves

```
int_(im<=Y) S*cutoffPower(alpha_i) dmu - C*Y^e_i/e_i
  = -scalarCutoffPeriod(physicalParameter,alpha_i)/gap_i   (Y>=4).
```

This is an actual integral theorem. Its proof uses the exact horizontal mean
of the full scalar reader and the
proved identity `cutoffBulkMoment = 4^e/e-nativeCutoffMellinContinuation(e)`.
The finite transition and terminal power determine the minus sign.
Together with absolute integrability of `S*squareResidual`, it proves
that the raw half-square finite part is exactly
`physicalSelfSourceCoefficient`. For `Re(rho)>1/2`, the existing source-value
theorem therefore evaluates this literal finite part as
`Lambda(5*rho/2-1)*Lambda(rho/2)^2*Lambda(1-3*rho/2)/2`.
The complete continued explicit field has finite part
`radialLift*physicalSelfSourceCoefficient-physicalSelfPrincipalResponse`.
Adding the existing continued residual profile yields exactly
`physicalSelfSourceCoefficient*(continuedReducedGreen+radialLift)`.

`ThetaCuspHawkingBMOriginalCausalRestoration` also passed its exact leaf audit.
Both leaves are wired into `RHTower`. At every nonnegative pair of original
null coordinates, its theorem `original_causal_restoration` proves that the
full original causal scalar has finite part

```
int S*fullNullResidual dmu
 -sum_i principalNullResponse_i*scalarCutoffPeriod_i/gap_i
 +nullLift*physicalSelfSourceCoefficient.
```

**Whole-route consequence.** The three principal corrections cancel against
their literal height-restored integrals. The original onset lift remains.
These are fixed-frequency, fixed-radius height limits; they do not commute
height restoration with a temporal transform or a QNM/horizon limit.
For the causal field, subtract its own three cutoff powers including the
lifted coefficients. The original uniform cusp-jet estimates bound its
height-weighted remainder; the compact truncated modular cell controls the
lower core. Pairing with the proved inverse-height physical reader then
supplies absolute integrability. This admission and its attachment to the
literal original potential are proved; no admission premise is supplied.
Full metric/onset/horizon matching, source nonvanishing and fixed-clock
extinction remain open.

**Next analytical test.** The causal finite part is now an explicit function
before any temporal transform. A bounded linear map commutes with an
integrable Bochner transform, but the inspected
`PhysicalCausalGreenBand.causalJointLaplace_height_memLp` only supplies height
admission of the transformed field. It does not supply time-integrability
of the height-weighted causal orbit. The corpus's
`FokasLenellsCausalGraphLaplace` gives a concrete alternative method: integrate
in a complete operator graph whose actual orbit has a proved norm bound.
Its generator and contraction theorem concern a different evolution; applying
that method here requires an HB graph/orbit estimate.

A second concrete target uses finite causal rectangles: transpose the literal
native circle mean against the physical scalar reader after the derived cusp
subtractions, and prove its period solves the reader's scalar Darboux equation
with initial value `physicalSelfSourceCoefficient`. The native mean's Darboux
equation and the causal remainder estimates are already in the corpus.
This would identify the causal scalar response before taking a Laplace
transform. This transposition/uniqueness claim is a conjecture, not a proved
consequence of the restoration theorem. Either approach must preserve the
original compact core, principal coefficients and onset lift.

### Physical pairing versus scalar projection — Lean closure

**[BRIDGE; Lean].** `ThetaCuspHawkingBMOriginalScalarPairing` passed its
exact module audit and is wired into `RHTower`. The primary target remains
the complete original Einstein pairing and its fixed-clock extinction.
The proved correspondence fixes the scalar projection normalization while
retaining the original boundary term.

Let `F` be the complete original causal scalar, `S` the independent physical
scalar reader, `Delta S=mu*S`, and `D_Y` the actual curved modular domain.
Define

```
V_Y(F) = integral_D_Y sum_j coexact(F)_j*coexact(S)_j dxdy,
M_Y(F) = integral_D_Y F(X,y)*S(X,y)/y^2 dxdy,
N_Y(F) = integral_(-1/2)^(1/2) F(X,Y)*partial_Y S(X,Y) dX.
```

The theorem `original_physical_pairing` proves exactly

```
V_Y(F) + mu*M_Y(F) = N_Y(F).
```

Proof: the planar divergence of `F*grad S` equals its left integrand.
Actual modular invariance transports this normal current with the same
Möbius Jacobian as the reader differential. Translation pairs the vertical
sides; inversion pairs the curved core. The surviving top term is `N_Y`.
No decay assumption or zero boundary value is inserted.

**Whole-route consequence.** The physical coexact pairing carries factor
`-mu`, together with an explicit normal-flux correction. Identifying the
complete Einstein pairing with a scalar projected residue therefore requires
this correction and the original principal/lift restoration. A scalar
projection identity alone does not establish that identification. The next
comparison must use this correspondence in the full radial/time current,
with every principal and onset contact retained.

For the infinite-cusp comparison, use the already-derived original
decompositions `F=sum_i A_i*y^alpha_i+R_F` and `S=C*y^beta+R_S`, where
`alpha=[2*rho,1,2-2*rho]`, `beta=1-sigma/2` and
`A_i=principalNullResponse_i+nullLift*principalAmplitude_i`. The normal flux
has principal terms

```
sum_i A_i*C*beta*Y^(alpha_i+beta-1).
```

Its exact remainder has three terms: `R_F*partial_y(C*y^beta)`,
`(sum_i A_i*y^alpha_i)*partial_y R_S`, and
`R_F*partial_y R_S`. The existing arbitrary-weight source bounds and genuine
reader-derivative bounds make each remainder rapidly decreasing at fixed
nonnegative null coordinates, uniformly in the horizontal coordinate.
Thus width-one integration preserves decay. Subtracting only the derived
nonconstant powers leaves the sum of coefficients with
`alpha_i+beta-1=0`. Those positions are exactly `sigma=4*rho` or
`sigma=4-4*rho`; neither occurs for the diagonal or reflected reader.

The normal-flux expansion, integrated remainder, finite part and resonance
classification passed the exact `ThetaCuspHawkingBMOriginalCuspFlux` audit.
The original source and reader estimates supply all their hypotheses.

The resulting **Lean theorem** `original_physical_pairing_finitePart` is that
`V_Y(F)+mu*M_Y(F)` minus those normal-flux powers tends to this actual
constant coefficient. The theorems `diagonal_physical_pairing_finitePart`
and `reflected_physical_pairing_finitePart` prove zero limits for those
original readers. This is a combined pairing correspondence; it does not assert
separate finite parts for `V_Y` and `M_Y`, nor identify their temporal or
horizon counterterms.

For that next attachment, write `U=R*Z_tilde`, `W=ell*S`, `f=R^2-1` and

```
C(U)=-R^2*f*U_RR-R^2*(U_pR+U_Rp)-2*R*U_R+2*R*U_p.
```

Direct substitution in `IngoingFullCurrent.contact` cancels its angular
operator. The Lean theorem `OriginalSourceContact.coexact_contact` commutes
the genuine mixed derivatives and proves
`contact(coexact(U))=coexact(C(U))`. The original left radial equation gives
`C(W)=(mu-2)*ell*S`. The resulting finite angular-current formulas are

```
integral_D_Y Jp
 = R^(-2)*((mu-2)*ell*N_Y(U_R)-ell_R*N_Y(C(U)))
   -mu*R^(-2)*((mu-2)*ell*M_Y(U_R)-ell_R*M_Y(C(U))),

integral_D_Y JR
 = R^(-2)*((mu-2)*ell*N_Y(f*U_R+U_p)
            -(f*ell_R+ell_p)*N_Y(C(U)))
   -mu*R^(-2)*((mu-2)*ell*M_Y(f*U_R+U_p)
            -(f*ell_R+ell_p)*M_Y(C(U))).
```

These amplitude-factored formulas are **analytical derivations**. The actual
metric-to-scalar-period identity, reader equations and paired angular-boundary
cancellation are formalized below. The original modular identity is
differentiated at finite time/radius values; no infinite-cusp limit is
differentiated. The formulas specify both the scalar current and normal-flux
correction to compare with the restored physical residue. Horizon and onset
contacts remain.

The original wave equation also supplies a direct source reduction of this
contact. Put `x=tortoise(R)` and
`F_orig=timeOriginalForcing(q,branch,amp,p-x,x,z)`. In the static chart,
the proved null wave equation becomes

```
Z_tt-f^2*Z_RR-2*R*f*Z_R-(f/R^2)*Delta(Z)=F_orig.
```

Substitute `U=R*Z` and then `p=t+x`. The contact above is therefore

```
C(U)=(Delta-2)*U+(R^3/f)*F_orig.
```

This source reduction is **proved in Lean** in
`ThetaCuspHawkingBMOriginalSourceContact`. `original_ingoing_wave` transports
`OriginalCausalPotential.originalPotential_wave` through the actual original
coordinate definitions; `original_scalar_contact` includes the radius
reconstruction. `original_stream_contact` identifies the complete original
Einstein stream contact with the coexact derivative of this expression.
The original fields supply all regularity on `p>0`, `R>1`, `Y>0`; the full
forcing and onset lift remain. No radial moment is divided out. The scratch
check and isolated exact leaf audit passed at default heartbeats, and the
umbrella is wired without an umbrella build. This closes the local source
attachment, including its weight and sign. Angular integration with its
complete normal flux is formalized below; the prescribed
temporal/horizon/QNM cutoff comparison remains open.

### Finite temporal/radial metric transfer — proved in Lean

`ThetaCuspHawkingBMOriginalOrbitCurrent.original_metric_integral` identifies
both original reconstructed metric-current components on every actual
finite modular domain, for `p>0`, `R>1`, `Y>=1`, and the unchanged left QNM.
Put `D_p U=U_R`, `D_R U=f*U_R+U_p`, and define

```
M_Y(A,B) = int_D_Y A*Delta(B)/y^2,
N_Y(A,B) = complete boundary normal flux of A*grad(B).

int_D_Y J_j = R^(-2)*[
  N_Y(D_j U,C(W))-N_Y(C(U),D_j W)
  -M_Y(D_j U,C(W))+M_Y(C(U),D_j W)].
```

`N_Y` explicitly includes the vertical-side jump, horizontal top and paired
curved-core flux, with the original orientations. The metric is reconstructed
and differentiated before the current is evaluated. Its actual source
contact is replaced by `(Delta-2)*U+R^3*F_orig/f` inside the theorem.
Symmetry of the coexact pairing places the angular derivatives on the reader
in both transfers: no additional angular derivative of the forcing is needed
in either the scalar bulk or its boundary expression. The identity admits
zero source coefficient and vanishing individual radial moments.

The original fields supply all smoothness and compact-domain integrability.
`ThetaCuspHawkingBMOriginalReaderEquation` also proves, for the unchanged
continued reader at every exterior time and both original radial normalizations,

```
C(W)=(mu-2)*W,  Delta(W)=mu*W,
Delta(D_j W)=mu*D_j W,  Delta(C(W))=mu*(mu-2)*W.

P_Y(A,B) = int_D_Y A*B/y^2,
int_D_Y J_j + R^(-2)*[
  mu*(mu-2)*P_Y(D_j U,W)-mu*P_Y(C(U),D_j W)]
 = R^(-2)*[N_Y(D_j U,C(W))-N_Y(C(U),D_j W)].
```

`original_metric_scalar_integral` attaches this identity to the actual metric
current and full original forcing. Its reader proof uses the genuine continued
radial equation and two-jet, without a positive-frequency convergence premise.
Clean scratch checks and isolated exact module audits passed at unchanged
heartbeats; the leaf import is wired. The explicit coordinate formula is exposed
by `ThetaCuspHawkingBMOriginalAngularCurrent.leftScalar_value`.
`ThetaCuspHawkingBMOriginalModularOrbit.original_transfer_boundary` proves
paired-side and curved-core cancellation for both fully transferred pairs.
With `T_Y(A,B)=int_(-1/2)^(1/2) A*B_Y dX`, its
`original_metric_top_integral` identifies the actual finite metric current as

```
int_D_Y J_j + R^(-2)*[
  mu*(mu-2)*P_Y(D_j U,W)-mu*P_Y(C(U),D_j W)]
 = R^(-2)*[T_Y(D_j U,C(W))-T_Y(C(U),D_j W)].
```

This retains the complete original forcing. The proof differentiates the
original modular identity only at finite time/radius values, and uses the
actual reader covector Jacobian. Clean scratch and isolated exact leaf audit
passed, with its umbrella import wired. The prescribed temporal/cusp/horizon
limit comparison and moving-corner attachment remain open. Full matching
and its impossibility remain unproved.

**[BRIDGE; proved in Lean, scratch and exact leaf audit passed]** Both genuine first null
derivatives of the restored remainder have arbitrary cusp decay, uniformly
for `0<p,r<=T` and all horizontal positions. The corpus already supplies the
exact Goursat derivative identities in `CausalResponseCusp`: each first null
derivative is a single integral of the remainder forcing. That forcing is
the native source remainder plus `Delta(responseRemainder)/(4*cosh^2)`.
The angular remainder bounds are uniform on the closed causal rectangle;
using decay order `N+2` absorbs the `exp(2*k)` Laplacian coefficient.
The source weight and null-potential coefficient are bounded there. The
single integrals therefore preserve decay order `N`. Restoring the original
lift adds its genuine null derivative times the native remainder; the lift
derivatives are continuous and bounded on the same rectangle. All three
original principal coefficients remain inside the differentiated remainder.
`ThetaCuspHawkingBMOriginalNullCusp.original_null_cusp_bound` proves the
uniform bound, and `original_null_cusp_limit` allows arbitrary complex cusp
weights and arbitrary bounded positive null-time and horizontal paths.
No convergence or regularity of those paths is assumed. The leaf is wired;
its isolated exact audit built only this module.

This is the derivative order required by the transferred finite metric
identity: the source-contact equation has already removed second time/radius
derivatives. Consequently no additional second-invariant estimate is needed
for this step. The existing native invariant Volterra formulas remain
available for higher derivatives.

**[BRIDGE; proved in Lean, scratch and exact leaf audit passed]** The physical
coordinate attachment is closed in `ThetaCuspHawkingBMOriginalOrbitCusp`.
Write `v=p-2*tortoise(R)`, `f=R^2-1`, and `U_pr` for `R` times the three
original principal terms. The genuine orbit differences are

```
partial_R(U-U_pr) = E-(2R/f)*partial_v E,
(f*partial_R+partial_p)(U-U_pr) = f*E+R*(partial_p E-partial_v E).
```

Continuous original Goursat partials first yield joint differentiability of
the principal coefficients. The actual chart chain rule then retains every
term from radius reconstruction and the original onset lift. Both differences
vanish with any complex cusp weight, uniformly in horizontal position and
after integration over the width-one cusp, at each fixed `p>0,R>1`.
The leaf is wired; its exact audit built only this module. Its explicit
principal orbit expansion is also proved. If
`A_i(p,R)=R*c_i(p,p-2*tortoise(R))`, the two coefficients are
`partial_R A_i` and `(R^2-1)*partial_R A_i+partial_p A_i`; the original
three height exponents are unchanged. `principal_orbit_expansion` proves
the exact differentiated principal identity, and `original_orbit_expansion`
attaches it to the actual field with a remainder vanishing after every
complex cusp weight along arbitrary horizontal paths. Genuine coefficient
differentiability is proved first, retaining the original onset lifts.
The complete principal metric top-flux coefficients and both actual cusp
remainders are proved below, including the original forcing contact and the
integrated signed difference of the two top fluxes.
The prescribed temporal/horizon/corner comparison remains open; these fixed
exterior bounds do not authorize arbitrary joint limits.

### Complete metric cusp coefficients — Lean closure at fixed time and radius

Keep the original `U=R*Z`, `W=ell(p,R)*S`, `Delta S=mu*S`, and
`C(U)=Delta U-2U+R^3/(R^2-1)*F`. Let `P` be the literal half-square
source. The original angular equation retains the entire gradient energy
and gives `F=B0*P+B2*Delta P`. The explicit coefficients `B0,B2` are
`forcingValueCoefficient` and `forcingLaplacianCoefficient` in
`ThetaCuspHawkingBMOriginalMetricCusp`; their common `forcingScale`
retains the original source amplitude and fixed onset.

Write `alpha_i=principalExponent q i`, `a_i=principalAmplitude q i`,
`A_i=R*coefficient q branch amp p (p-2*tortoise R) i`, and
`K_ji=principalOrbitCoefficient q branch amp j p R i`. The original
source contact's principal coefficients are therefore

```
C_i = (alpha_i*(alpha_i-1)-2)*A_i
    + R^3/(R^2-1)*(B0+B2*alpha_i*(alpha_i-1))*a_i.
```

For the physical reader, put `beta=readerExponent r`,
`b=readerCoefficient r`, and
`ell_j=readerOrbitAmplitude r side outer j p R`. Genuine exterior
derivatives give `partial_Y C(W)=(mu-2)*ell*partial_Y S` and
`partial_Y D_j W=ell_j*partial_Y S`. Thus the complete right-hand cusp
term of `OriginalModularOrbit.original_metric_top_integral` has coefficients

```
M_ji = R^(-2)*b*beta*((mu-2)*ell*K_ji-ell_j*C_i),
gamma_i = alpha_i+beta-1.
```

At fixed `p>0,R>1`, the original potential's angular jets and the literal
half-square remainder jets decay after every complex height weight.
Multiplication by `R`, the fixed forcing coefficients and the angular
Laplacian preserves this property. The full signed reader-normal tail also
has that decay. Expanding each product leaves a principal term plus three
rapid remainder terms. Arbitrary-horizontal-path bounds give the uniform
width-one integral bound. Consequently these coefficients prescribe the
entire cusp subtraction for both metric terms on paper. The existing
nonresonance theorem gives `gamma_i<>0` for original diagonal and reflected
readers, so there is no extra constant metric cusp contribution.

**Lean status:** the reusable full-reader normal-flux expansion and its
integrated remainder are audited in `OriginalCuspFlux`; `OriginalMetricCusp`
proves the first transfer, both reader normal identities and the complete
forcing decomposition. The audited and wired `OriginalContactCusp` now
proves the actual physical angular restriction, the full `C(U)` expansion,
and `second_metric_cusp_expansion`. Genuine continuity supplies interval
integrability before principal subtractions are moved outside the integrals.
`complete_metric_top_cusp_limit` proves that the original signed difference
of both top fluxes, minus the displayed three-power sum, tends to zero.
`complete_metric_cusp_constant` excludes a constant contribution for original
diagonal/reflected readers. The exact leaf audit built two jobs; no umbrella
build was run. No vanishing source amplitude or coupling is assumed.

This closes the complete cusp subtraction at each fixed `p>0,R>1`. It does
not exchange the original time and horizon limits or remove their
moving-corner term. The Lean reader identities concern the original
`frequency r side` in `leftScalar`; matching an independently varying
temporal-frequency family remains open.

### Connection to the complete Einstein angular current — analytical

Use the actual reconstructed causal stream `P=coexact(U)` with
`U=R*Z_tilde`; the factor `R` is retained. Write the unchanged left stream
as `Q=ell(p,R)*coexact(S)`, with `Delta S=mu*S`, and put
`J_S(F)=(Delta F)*grad(S)-mu*S*grad(F)`. At positive angular height,
commuting the genuine mixed derivatives gives

```
curl(P)_i = -Y^(-2)*Delta(U_i),
curl(Q)_i = -Y^(-2)*ell_i*mu*S,        i=p,R.
```

Substitute these identities and the coexact components directly into
both angular components of `D4BMIngoingFullCurrent.current`. Their common
vector expression is

```
(J^X,J^Y) = R^(-2)*((f*ell_R+ell_p)*J_S(U_R)+ell_R*J_S(U_p)),
f=R^2-1,
U_R=Z_tilde+R*Z_tilde_R,              U_p=R*Z_tilde_p.
```

For the original left factor, `f*ell_R+ell_p=(w/R)*ell`, so this becomes

```
(J^X,J^Y) = (w*ell/R^3)*J_S(Z_tilde)
             +(w*ell/R^2)*J_S(Z_tilde_R)
             +(ell_R/R)*J_S(Z_tilde_p).
```

Every sign and factor follows from the original two angular current
formulas; no radial equation for the causal source is used. Thus the
modular-transfer result above has a direct role in the complete action.
The remaining attachment is to the actual parameter derivatives of the
same causal potential: their modularity and differentiated cusp
expansions must be proved before applying the angular finite-part limit.
Differentiability alone does not justify differentiating that limit.
The original-field attachment is now proved by the bilinear identity above.
The displayed eigen-reader simplification remains analytical. A separate
boundary-transfer mechanism below can move the parameter derivatives off the
source before the cusp limit, while retaining their endpoint contributions.

### Moving the spacetime derivatives to retained boundaries — analytical

There is a second consequence of the angular-current formula, independent of
interchanging a derivative and a cusp limit. Fix the original physical reader
`S`, retain its proved equation `Delta(S)=mu*S`, and set

```
K=J_S(U),                         U=R*Z_tilde,
a=w*ell/R^3,                     b=ell_R/R^2,
c=(mu-2)*ell/R^4.
```

On `p>0`, `R>1`, `Y>0`, the actual fields are smooth. Since `S` is independent
of `p,R`, equality of mixed derivatives gives `K_R=J_S(U_R)` and
`K_p=J_S(U_p)`. Thus the two original Einstein angular components are
`a*K_R+b*K_p`. The original left factor gives

```
ell_p=-w*ell,                  ell_R=w*ell/(R*(R-1)),
mu-2=w*(w+3),
a_R+b_p=-w*(w+3)*ell/R^4=-c.
```

Indeed, `a_R=w*ell_R/R^3-3*w*ell/R^4` and
`b_p=-w*ell_R/R^2`; their `ell_R` terms sum to `-w^2*ell/R^4`.
The exact product rule therefore proves, component by component,

```
J^angular = partial_R(a*K)+partial_p(b*K)+c*K.
```

Consequently every closed rectangle `[p0,p1] x [R0,R1]` strictly inside the
smooth region has the exact identity

```
int_p int_R J^angular
 = int_p [a*K]_(R0)^(R1)
   +int_R [b*K]_(p0)^(p1)
   +int_p int_R c*K.
```

The fundamental theorem of calculus and Fubini apply because all integrands
are continuous on this compact rectangle. Both temporal and radial endpoint
terms remain. In particular the identity uses no limit and differentiates no
asymptotic assertion.

There is also an exact change of local current that preserves its divergence.
Put `div_A V=partial_X V_X+partial_Y V_Y` and define

```
Jnew^R=J^R+div_A(a*K),
Jnew^p=J^p+div_A(b*K),
Jnew^angular=c*K.
```

The difference in the four-dimensional divergences is zero by commutation of
actual mixed derivatives. The change in each separate boundary face is
retained; its edges match the adjacent face contributions. This does not
assert that either current or an individual face has zero flux.

**Whole-chain consequence:** the integrated angular contribution can be
expressed using only the original undifferentiated `K` and explicit endpoint
currents. The existing modular finite-part theorem applies to each fixed
parameter value of `K=R*J_S(Z_tilde)`. Passing that limit through a parameter
integral still requires a justified bound on compact parameter rectangles;
fixed-point convergence alone does not supply it. Extension to the onset and
horizon corners and removal of unbounded temporal cutoffs remain separate
obligations. Thus the derivative-transfer identity supplies an alternative to
differentiated cusp estimates, not a proof of fixed-clock extinction.

The supporting corpus is more specific than smoothness alone:
`D4BMCausalCusp.responseRemainder_jet_uniform_bound` bounds every angular jet
uniformly on `0<=p,r<=T`, over every horizontal position, by
`B*exp(N*(D-k))` for each natural `N`. Its
`responseRemainder_first_null` and `responseRemainder_second_null` give actual
null derivatives as one-dimensional integrals of `remainderForcing`. The
forcing contains the original native remainder times its source weight plus
the angular Laplacian of the causal remainder divided by
`4*cosh((p-r)/2)^2`. Hence there is also a route to derivative estimates that
uses these already identified forcing integrals. The full original onset
lift and the physical ingoing coordinate change still require attachment to
these estimates. On compact physical rectangles separated from `R=1`, the
corresponding two null coordinates stay bounded; this observation gives no
bound at the horizon.

**Status:** the displayed eigen-reader simplification has the paper proof
above; its direct Lean specialization remains open. The general original-field
identity and all four finite-rectangle edges are now proved in
`ThetaCuspHawkingBMOriginalGreenBoundary`, with the full reader remainder
retained. The uniform-bound and null-derivative statements cited here already
occur in the corpus; their combined application to the full original metric
pairing is not asserted.

### Horizon order after the parameter transfer — analytical

The exact reader specialization in the preceding paper proof gives
`BR=a*K`, `Bp=b*K`, and `E=-c*K`. With `v=1-1/R` and the original factor
`ell=exp(-w*p)*v^w`, these are

```
BR=exp(-w*p)*v^w*(w/R^3)*K,
Bp=exp(-w*p)*v^(w-1)*(w/R^4)*K,
E=-exp(-w*p)*v^w*((mu-2)/R^4)*K.
```

At fixed positive ingoing time and angular height, the proved source horizon
extension makes `K=J_S(U)` smooth in `v` through zero. Grouping the reader
remainder therefore cancels its apparent higher radial singularities. The
radial edge still needs only the degree-one subtraction and the temporal
edge the degree-two subtraction already identified for the original current.

For the interior radial integral, retain the exact Jacobian
`dR=(1-v)^(-2)dv`. Its density is `v^w*H(v)`, where
`H(v)=-exp(-w*p)*(mu-2)*(1-v)^2*K(p,1/(1-v),X,Y)` is smooth.
On a sufficiently small fixed interval, `|H(v)-H(0)|<=M*v`. The original
frequency strip `Re(w)>-2` therefore gives

```
int_0^epsilon |v^w*(H(v)-H(0))| dv
 <= M*epsilon^(Re(w)+2)/(Re(w)+2).
```

Only the constant Taylor term of this exact radial density must be removed
for absolute integrability of the remaining interior integral. This is a
paper consequence of the original reader factor and source horizon
regularity; its eigen-reader specialization and estimate are not yet Lean
theorems. It does not identify these subtractions with the transformed source
counterterm or control the onset corner. For the whole route it shows that
the derivative transfer does not worsen the horizon orders, while leaving
the physical counterterm correspondence explicit and unresolved.

## Original angular transfer and complete causal cusp jets

**Lean:** `ThetaCuspHawkingBMOriginalAngularGreen` passed its exact module
build and is wired into `RHTower`. `ThetaCuspHawkingBMOriginalCuspJets`
also passed its exact module build and is wired into `RHTower`. These results
concern the complete original potential, including the fixed onset lift.

Fix the original null coordinates `p,v`, source occurrence `q`, physical
branch and amplitude. In the positive-height chart write

```
Z(X,Y) = originalPotential(q,branch,amp,p,v,X,log(Y)),
S(X,Y) = literalScalar(u,X,Y),       mu = u^2-1/4,
P = coexact(Z),                     V = coexact(S),
Delta F = Y^2*(F_XX+F_YY).
```

The actual reader equation is `Delta S=mu*S`. Define

```
J_j = (Delta Z)*partial_j S - mu*S*partial_j Z.
D = sum_j ((coexact(Delta Z)_j-mu*P_j)*V_j).
```

Differentiating the two products gives `partial_X J_X+partial_Y J_Y=D`:
the extra term is `(Delta Z)*(S_XX+S_YY)-mu*S*(Z_XX+Z_YY)=0`.
The coexact/rough-Laplacian identity identifies this with
`sum_j ((roughLaplacian P)_j*V_j-P_j*(roughLaplacian V)_j)`.
The identity shift in the physical angular action cancels in this
bilinear difference. Thus this is the original vector-operator transfer.

Original modular periodicity makes `J_X(X+1,Y)=J_X(X,Y)`. For every
positive pair of heights `a,b`, the actual compact integral satisfies

```
integral_a^b integral_(-1/2)^(1/2) D(X,Y) dX dY
  = integral_(-1/2)^(1/2) J_Y(X,b) dX
    - integral_(-1/2)^(1/2) J_Y(X,a) dX.
```

Theorems `divergence_flux`, `defect_eq_rough`, `cuspFlux_hasDerivAt` and
`original_coexact_green` establish this with the full retarded source and
any original physical reader. Both height endpoints remain.

The complete source has precisely the following principal coefficients:

```
rho = (q.1 : Complex),              alpha = [2*rho,1,2-2*rho],
A_i(p,v) = principalNullResponse(q,physicalRate(q,branch),amp,i,p,v)
           + nullLift(physicalRate(q,branch),amp,p,v)*principalAmplitude(q,i),
R_Z(X,k) = originalPotential(q,branch,amp,p,v,X,k)
           - sum_i A_i(p,v)*exp(alpha_i*k).
```

Radius zero of the native circle is exactly the original half-square.
Consequently every actual ordered angular jet has the exact decomposition

```
jet_word R_Z = jet_word responseRemainder
              + nullLift*nativeJet_(map succ word)(nativeRemainder)(0,X,k).
```

The new leaf proves this equality and, for fixed `p,v>=0`, proves that
`exp(w*k)*jet_word R_Z(X(k),k)` tends to zero for every complex `w` and
every horizontal path `X(k)`. Choosing a violating path if uniformity
failed upgrades this to a bound uniform over all real `X`. The compact
integral norm bound then gives the same zero limit after integration in
`X` from `-1/2` to `1/2`. This retains the causal response and onset lift
in every derivative; the estimate is not a claim uniform as `p` or `v`
tends to infinity.

### Derived physical cusp flux expansion

**Lean closure:** `ThetaCuspHawkingBMOriginalCuspFlux` passed its exact
module audit and is wired into `RHTower`. The expansion is attached to
the actual differentiated flux and its original width-one integral.
Let the reader occurrence be `r`, put
`sigma=(r.1 : Complex)`, `beta=1-sigma/2` and
`C=reflectedCompletedLambda(sigma-1)`. The existing theorem
`PhysicalAngularCutoffCalibration.physicalScalar_principal` gives

```
S = C*Y^beta + T,                   mu=beta*(beta-1),
Z = sum_i A_i*Y^alpha_i + R.
```

The scalar reader tail `T` and its first height derivative have arbitrary
height-weighted bounds uniform in `X`. For `T`, use
`GlobalAngularResponse.weighted_tail_bounded`. For its derivative, use
`GlobalAngularResponse.tail_vertical_eq` and
`AngularSeries.value_coordDeriv_one`: it is a finite linear combination
of the original derivative-stable signed Bessel families, each covered
by `AngularSeries.weighted_value_bounded` at every complex weight.

The new source bounds imply the same arbitrary decay for `R`, `R_Y`
and `Delta R`, because
`R_Y=Y^(-1)*R_k` and `Delta R=Y^2*R_XX+R_kk-R_k` at `k=log(Y)`.
Writing `Z0=sum_i A_i*Y^alpha_i`, `S0=C*Y^beta`, the exact flux remainder is

```
J_Y-J0 = (Delta R)*S0_Y + (Delta Z0)*T_Y + (Delta R)*T_Y
         - mu*(T*Z0_Y + S0*R_Y + T*R_Y).
```

Every summand is a rapidly decaying factor times a finite power family
or another rapidly decaying factor. Hence the remainder decays after
any height weight, uniformly in `X`, also after the width-one integral.
Direct differentiation of the principal powers gives the complete
original flux expansion

```
J0(Y) = sum_i A_i*C*alpha_i*beta*(alpha_i-beta)
                    *Y^(alpha_i+beta-1).
```

This determines its constant-height coefficient without discarding any
nonconstant term. For independent original occurrences, that coefficient
can receive contributions only from `sigma=4*rho` or `sigma=4-4*rho`;
the cross channel would require the real value `sigma=2`, excluded by
the proved nonzero imaginary part of Xi occurrences. For the diagonal
reader the exponents are `[3*rho/2,1-rho/2,2-5*rho/2]`, all nonzero. For
the actual functional-equation reflection `sigma=1-rho`, their imaginary
parts are `[5/2,1/2,-3/2]*Im(rho)`, again all nonzero. The constant-height
coefficient therefore vanishes for both the diagonal and reflected
original readers, for every branch, amplitude and fixed causal cut.

Theorems `principalFlux_expansion` and `fluxRemainder_decomposition`
prove the differentiated principal formula and exact six-term remainder.
`original_flux_expansion` and `original_cuspFlux_expansion` prove the
arbitrary-weight remainder limit along every horizontal path and after
the actual cusp integration. `independent_constant_classification`,
`diagonal_constant_zero` and `reflected_constant_zero` prove the full
specialized constant-coefficient statements above.

There is also an exact infinite-cusp action limit. Write
`Gamma_i=A_i*C*alpha_i*beta*(alpha_i-beta)`,
`e_i=alpha_i+beta-1`, and

```
C_nc(k) = sum_(i: e_i != 0) Gamma_i*exp(e_i*k),
C_0     = sum_(i: e_i = 0) Gamma_i.
```

Every coefficient comes from the original causal response and restored
lift. Removing exactly these nonconstant powers, while retaining any
genuine constant contribution, gives

```
lim_(k -> infinity) [cuspFlux(exp(k))-C_nc(k)] = C_0,
lim_(k -> infinity) [integral_a^exp(k) cuspDefect(Y) dY-C_nc(k)]
  = C_0-cuspFlux(a),                 a>0.
```

These are `original_cuspFlux_finitePart` and
`original_cuspAction_finitePart`. For the actual reflected reader,
`C_0=0`, so the latter limit is exactly `-cuspFlux(a)`;
`reflected_cuspAction_finitePart` proves this without an added boundary
or nonresonance premise. The lower endpoint has not been erased.

**Effect on the complete chain:** original causal integration and onset
restoration preserve the angular exponent support needed for the
reflection pairing, and the actual integrated upper cusp contribution
is now identified in Lean. `OriginalModularGreen` also cancels the
paired lower modular boundary and proves the actual curved-domain finite
part. The complete action's other fluxes, temporal transformation and
identification with the original joint counterterm prescription remain
separate obligations.
All null coordinates are fixed in these limit theorems; they supply no
infinite-time/horizon interchange or fixed-Hawking-clock extinction.

## Actual causal metric current and finite static-time horizon exclusion

**Lean closure:** `ThetaCuspHawkingBMActualIngoingCurrent`; exact module audit
passed, cached artifacts installed and umbrella wired. The conclusions below
concern the original causal integral and its reconstructed local metric
current. They do not assert the complete physical pairing or RH.

Write `f=R^2-1` and
`x(R)=(log(R-1)-log(R+1))/2`. The actual ingoing potential is

```
Z_ing(p,R,X,Y) = Z(p,p-2*x(R),X,log(Y)),
P = R * (partial_Y Z_ing, -partial_X Z_ing).
```

For `p>0`, `1<R<3`, `Y>0`, equality with the constructed smooth horizon
extension holds on coordinate neighborhoods. Differentiating that equality
identifies all actual stream derivatives. The original substitution
`p=t+x(R)` has the full ordered two-jet used in
`IngoingFullCurrent.toStatic`; its radial second derivative includes the
coefficient `-2R/f^2`. This closes the causal-field attachment required by
the current formulas above.

The actual static-coordinate metric is formed from
`g_tA=f*partial_R P_A` and `g_RA=partial_t P_A/f`, with symmetric entries.
Its first coordinate derivatives are exactly

```
partial_k g_tA = 2R*delta_kR*partial_R P_A + f*partial_k partial_R P_A,
partial_k g_RA = partial_k partial_t P_A/f
                - 2R*delta_kR*partial_t P_A/f^2.
```

The Einstein action current depends only on metric values and first
derivatives. Consequently its value for these actual metric fields equals
the complete ingoing current, including both angular fluxes and source
contacts. The proof does not equate the actual second metric derivatives
with the stream table's unused zero slots. Theorems
`reconstructedMetric_first`, `reconstructedMetric_action` and
`original_causal_metric_current` prove these identifications.

There is also an exact causal support boundary. For any real `T`, set
`delta(T)=exp(-2*(T+1))>0`. If `t<=T` and `1<R<1+delta(T)`, then

```
log(R-1) < -2*(T+1),     log(R+1) > 0,
x(R) < -(T+1),          p=t+x(R) < 0.
```

The original potential vanishes for `p<=0`. Since `p<0` is open, the
potential and coexact stream vanish on a coordinate neighborhood. Every
stream jet used by the current is therefore zero, and all four current
components are exactly zero against every test two-jet. For actual test
metric fields, local C2 regularity suffices; no bound uniform at the
horizon is needed. This is
`original_current_finite_static_slab` and
`original_metric_current_finite_static_slab`.

This finite-static-time exclusion and the positive-ingoing-time horizon
trace are distinct statements. Holding `p>0` fixed while `R` tends to
one forces `t=p-x(R)` to infinity. The support neighborhood above shrinks
with `T`. Thus it removes the horizon face on finite static-time slabs,
but leaves the growing-time boundary, the original transformed
counterterm matching, onset-corner control and complete physical pairing
unresolved. None of these limit interchanges is supplied by local current
identification or causal support.

## Remaining original pairing obligation

`ThetaCuspHawkingBMSecondHarmonicPeierlsPolarizedLanding` requires an actual
source-pairing incidence in
`d4BMXiSecondHarmonicCokernelCausalCut_eq_PeierlsPolarizedCandidate`.
`ThetaCuspHawkingBMSourceFixedPeierlsReflectionRigidity` proves RH from this
incidence on source families exchanged by reflection in one cyclic/skew
Peierls theory. The packet model in
`ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence` has algebraic
incidence, but its required source covariance is itself an RH equivalent.
It does not discharge the literal metric's physical incidence.

A checked amplitude reduction targets this missing physical pairing. Put
`Q(p)=B(p,p)/2` and `Omega(f,g)=pairing(Delta(f),g)`. Under the existing
cyclicity and Peierls-skewness assumptions, the complete cubic cut is
`C(p,m)=2*Omega(Q(p),Q(m))`. Its double polarization is

```
C(pS+pV,mS+mV)-C(pS,mS+mV)-C(pV,mS+mV)
  -C(pS+pV,mS)+C(pS,mS)+C(pV,mS)
  -C(pS+pV,mV)+C(pS,mV)+C(pV,mV)
  = 2*Omega(B(pS,pV),B(mS,mV)).
```

This identity passed `lake env lean` in scratch at default resource limits
on 2026-09-12. Its proof expands the existing polarized-cut theorem by
bilinearity and symmetry of `B`. It is conditional Peierls algebra, not a
new unconditional physical theorem, and was not installed as a Lean leaf.
The selected quartic coefficient depends only on the mixed radiative
sources once physical cyclicity/skewness has been established. This does
not remove those physical assumptions or prove extinction.

The raw-source attachment is essential. The all-component theorem
`D4BMQuadraticMixedSource.einstein_component` states
`B(S,V)+L(k)=T`, where `k` is the explicit ingoing correction and `T` is
the constructed mixed tensor. Thus its source pairing must retain

```
Omega(Bplus,Bminus) = Omega(Tplus,Tminus)
  -Omega(L(kplus),Tminus)-Omega(Tplus,L(kminus))
  +Omega(L(kplus),L(kminus)).
```

The next physical incidence calculation must evaluate this entire
expression using the original retarded/advanced responses and the four
components of `D4BMMixedActionCurrent.stream_complete_action_current`,
including the correction's horizon/onset traces. No theorem presently
identifies it with the RH-detecting BM boundary concomitant. Nor is its
fixed-Hawking-clock extinction proved. These are the closing obligations;
the displayed algebraic reductions do not settle them.

## Incoming correction and its significance for the full chain

The incoming temporal correction is formalized in
`ThetaCuspHawkingBMCorrectionTemporalRestoration`. Scratch verification and
the exact leaf audit passed at default resource limits; the leaf is wired
into `RHTower` without an umbrella build. The starting points are the
original mixed correction jet, the
complete Einstein action current, the literal source amplitude and the
existing quadratic endpoint Mellin theorem.

Write `s=D4BMModularCore.physicalRate q branch`, `kappa=s*(s+1)/2`,
`r=-coth(x)`, `u=1/r` and `z=1-u^2`. The original onset amplitude is

```
A(w,x)=exp(w*x)*(1+u)^(2*s)*a^2*continuedOnset(s,w).
c(r)=kappa*A(w,tortoise(r))*(r^2-1)/r^3.
c'(r)-2*c(r)/r
  =kappa*A*((w-2*s)/r^3-3/r^2+(5+2*s)/r^4).
```

For the correction angular covector `J` and an independent left covector
`K`, the exact temporal Einstein density is
`w*d/(r^2-1)*(c'-2*c/r)*sum(J_j*K_j)`. The original correction's metric and
every first derivative are identified with this separated representation.
The covectors are not identified with each other. At the original
frequency `w=2*s`, the reduced derivative is
`kappa*B^2*((2*s+5)/r^4-3/r^2)`.

For the incoming left mode, the original radial Jacobian gives
`z^(w-1)*H(w,z)`, where

```
H = w*kappa*angular/2 * amplitudeProfile(s,a,continuedOnset(s),w,z)
    * gaussProfile(q,w,z)
    * ((w-2*s)*sqrt(1-z)-3+(5+2*s)*(1-z)).
```

The common-cutoff integral is restored with both terms
`c0(w)*e^w/w+c1(w)*e^(w+1)/(w+1)`. Its finite part is analytic at every
physical fundamental QNM, hence has zero pole residue. Its finite value
is retained. `incoming_corrected_residue` proves that subtracting this
restored correction preserves exactly the original incoming temporal
pole coefficient `FP(clearedDensityProfile)(w0)/denominatorSlope`.

The resulting no-go is specific: this incoming temporal contribution
cannot remove an already nonzero pole. Its positive content is exact
coefficient preservation, with the full restored correction still
present. This is not a proof that the full raw-source Peierls pairing is
unchanged. Opposite-horizon, radial, angular and outer contributions, and
the causal inverse's treatment of the correction, still need evaluation.

The full-chain implications determine the next conjectures, rather than
treating this component as the sole path to RH:

- `physicalSelfSourceCoefficient_zero_iff_xi` independently identifies
  angular-source cancellation with zeros at `5*rho/2-1`, `rho/2`, or
  `3*rho/2`. A regular correction does not exclude these incidences or
  radial source cancellation. A candidate replacement is detection by a
  family of original adjoint channels; joint detection must be proved
  without replacing the source.
- `physicalPrimitiveCurrent_balance` identifies integrated complete
  source work with the retained final-time physical primitive current.
  `retardedPulse_late_history` identifies the entire late onset-pulse
  response with its original initial-history strip. Thus the fixed-clock
  conjecture must estimate the retained response/current in the original
  observable. Vanishing of the shifted source alone does not give that
  estimate.
- `d4BMXiSourceFixedPeierls_global_BM_incidence_forces_rh` supplies another
  closing mechanism: actual oriented incidence and source exchange in
  one cyclic/skew theory force RH. The candidate bridge from the native
  physical Green balance to the joined Einstein Peierls action must
  retain its original source, pairing, conjugation and boundary terms.
  The abstract reciprocal half-jump construction supplies none of those
  physical identifications.

The literal source-exchange conjecture is now proved for independent,
unchanged scalar/vector amplitudes in
`ThetaCuspHawkingBMLiteralSourceReflection.lean`. The complete field and
every nonlinear Einstein-source coefficient exchange under functional-
equation reflection. Matching the RH candidate's normalized amplitudes
and physical pairing remains an obligation; the source identity alone
does not establish that incidence.

These are unproved closing mechanisms. The new correction theorem does
not prove angular coupling, full physical incidence, extinction or RH.

## Literal source reflection and consequences for closure

**Status:** paper proof closed; scratch checked with default Lean limits;
exact new leaf audit passed. The leaf is imported by `RHTower.lean`;
no umbrella build was run.

The successful conjecture is a field identity, rather than an inference
from an integrated Eisenstein vertex. For every positive integer `n`,
the original arithmetic coefficient obeys

```
a_u(n) = n^u * sum_(d|n) d^(-2u) = a_(-u)(n).
```

Divisor complement `d -> n/d` proves this equality term by term after
reindexing the finite sum. The corpus's `modifiedBesselKOrder_neg` then
preserves every signed Fourier mode and hence the complete infinite
zero-word tail. At nonreal `u`, the completed functional equation
exchanges `Lambda(2u)` with `Lambda(1+2u)` under `u -> -u`, simultaneously
exchanging their Weyl powers. Thus the full literal scalar satisfies
`scalar(-u)=scalar(u)` at every coordinate. Its actual coexact covector
and the complete metric reconstruction inherit the identity.

At each multiplicity-labelled Xi occurrence, put `u=rho-1/2` and use the
original fundamental rate `s=D4BMModularCore.physicalRate(q,b)`. The
metric frequency is `omega=I*s`, since the temporal factor is
`exp(-I*omega*t)`. The new `physicalPerturbation_eq_qnm` verifies both
frequency conversions against the original plus/minus QNM definitions;
`physicalPerturbation_first_source_zero` closes their linear Einstein
equations using the existing literal source theorem. Reflection gives

```
u(reflect(q)) = -u(q)
s(reflect(q),b) = s(q,!b)
h(reflect(q),b,aS,aV) = h(q,!b,aS,aV).
```

`physicalSource_reflect` proves equality of the actual full Einstein
source as a function of perturbation amplitude. Consequently
`physicalSource_coefficient_reflect` covers every derivative order,
including the original quadratic and cubic coefficients. These Xi
identities have no supplied symmetry, regularity or field-equation
premises. The amplitudes `aS` and `aV` remain independent.

**Effect on the complete RH chain:** source exchange is available for
the concrete on-shell metric family. Taking its two branches as `p,m`
supplies the exchange identities in the existing cyclic/skew Peierls
receiver at fixed amplitudes. The remaining construction must match
those fields, the actual source bilinear map, the causal inverse and
the normalized BM candidate in one physical pairing, with every
correction and boundary term retained. Neither an abstract reciprocal
half-jump nor an injective finite channel map makes that identification.
Source-coupling nonvanishing and fixed-clock extinction remain open.

The broad helicity search also found `collisionHelicity_reconstruct`
and `angularCoefficient_collisionHelicityPlus/Minus` in
`PolyatomicAngularHelicity.lean` (namespace
`RHTower.D4BMQuadraticAngularSource`). They give exact reconstruction
and factorization of the original quadratic angular tensor. This is a
concrete joint-detection candidate when one scalar angular projection
vanishes: prove the physical adjoint channel family detects these
components of the same source. Pointwise tensor reconstruction does
not itself prove a nonzero global left-QNM overlap.

Broad/deep/method retrieval also located
`SelbergModularCurrentGreen.current_green_identity`, retaining side,
top and curved-arc fluxes. It is a candidate integration mechanism for
the original current, not a ready-made Einstein reciprocity theorem.
The broad literature search found a related methodological example in
[Khankhoje–Kundu, arXiv:2606.14486, §III](https://arxiv.org/html/2606.14486v1):
full reaction integrals restore reciprocity missed by a reduced
scattering description. Its electromagnetic result is not imported
as a theorem about this gravitational source.

Keep the source's `center(q)` distinct from the original left probe's
`physicalAngularParameter(q)=(rho-1)/2`, and the fundamental rate above
distinct from the doubled rate in `D4BMCuspProjection`.

The next physical-pairing conjecture has a specific source in the corpus:
`EinsteinActionBoundary.densityPath_first_variation` gives the original
Einstein--Hilbert variation as minus the volume-weighted raised Einstein
residual plus its complete connection-current divergence. Differentiate
twice in independent on-shell directions, using the same volume branch.
The candidate identity is that the cyclicity defect
`<x,B(y,z)> - <z,B(x,y)>` equals minus the boundary divergence of the
`y`-variation of the original symplectic current of `x,z`. With the
corpus's relative-density convention, that variation must differentiate

```
volumeRatio J.metric Y.metric 0 0 t *
  actionSymplectic (affine J Y t) X Z a
```

rather than `actionSymplectic` alone. This is an unformalized conjecture
about the actual current; no global cyclicity is claimed. The existing
`CubicSource.pairedSource_cubic` separately exhibits the varying-test
weight multiplying the complete quadratic residual. These are concrete
terms to track when joining the source action and the boundary pairing.
If the resulting boundary flux cancels in the original common-cutoff
limit, it supplies the physical cyclicity premise. If it survives, its
exact value belongs in the full action incidence and in the fixed-clock
observable. Either outcome changes the whole closing argument.

## Closed local action attachment

The local action attachment uses three checked and audited leaves:

- `ThetaCuspHawkingBMModeActionReconstruction`: actual two-jets of separated
  fields, original radius reconstruction, full mixed Einstein current.
- `ThetaCuspHawkingBMPhysicalModeAction`: actual causal projection, original
  coexact Eisenstein covector, homogeneous original left stream, complete
  forced right stream, finite-interval Einstein flux including both contacts.
- `ThetaCuspHawkingBMPhysicalTimeActionContinuation`: actual temporal current
  continuation, exact fundamental residue, analytic Laurent remainder and
  transfer of local field-residue nonvanishing.

At an interior original tortoise point x<0 set R=-coth(x),
lambda=u^2-1/4, u=physicalAngularParameter(r). Let f be the complete physical
projected response, g either original radial mode, and F the complete projected
source. All three cutoff corrections remain in F. Reconstruct the stream
coefficients as Rf and Rg with time frequencies w and -w, and retain the actual
coexact angular covector J. Write N=sum_j J_j^2, a complex bilinear square.
The original volume-weighted Einstein current at time zero is

```
A^0 = [-2w(lambda-2)fg/(R^2-1) - w R^2 g F/(R^2-1)^2] N,
A^1 = [-(lambda-2)(g'f-gf') - C] N,
A^2 = A^3 = 0,
C = [Rg + R^2 g'/(R^2-1)] F.
```

Every derivative slot is an actual field derivative. The angular equation is
derived from the literal Eisenstein covector. The right stream master is
`-R^3 F J/(R^2-1)` and the left stream master is zero. No radial ODE or angular
eigen-equation is supplied as an extra physical assumption. In the causal
Green band the reconstructed field is the radius lift of the actual causal
transform's physical projection, almost everywhere in the original measure.

For interior s≤t<0 the checked Einstein flux identity is

```
A^1(t)-A^1(s) = [-(lambda-2) integral_s^t gF - (C(t)-C(s))] N.
```

This identifies a projected mixed sector. The temporal-current restoration
below retains the full normalizable left mode, joins both original radial
intervals and evaluates its residue after the horizon limit. Full angular
reconstruction, independent SS/VV sectors, retarded/advanced Peierls
identification and nonvanishing of the source-evaluated residue remain open.

## Closed local temporal QNM transfer

The temporal current has a proved meromorphic continuation from the actual
physical band. Its exact QNM residue is

```
-2 w0 (lambda-2) g(w0,x) Res(f)(x) N/(R^2-1).
```

Proof mechanism: the source-rate pole is distinct from either fundamental
frequency; all three principal cutoff responses are analytic there. Their
finite angular decomposition therefore makes the complete F analytic there.
The original radial mode is analytic there. Consequently the retained
source contact is regular and contributes zero residue. The existing exact
field-residue limit then transfers to the actual temporal Einstein current.
All three leaves pass scratch checks and exact leaf audits. The current has
an analytic Laurent remainder. At every interior point its radial
multiplier is nonzero, so a nonzero field residue and nonzero angular
bilinear square imply a nonzero local Einstein temporal residue.

## Closed original radial finite part

Set z=sech(x)^2 and u=-tanh(x), so z'=2uz and sqrt(1-z)=u
for x<0. The original fundamental mode is Psi_w=z^(w/2)sqrt(1-z).
Its bilinear square therefore has the exact finite-interval identity

```
integral_L^0 Psi_w(x)^2 dx
  = (1/2) integral_{z(L)}^1 z^(w-1) sqrt(1-z) dz,  L<0.
```

The exact endpoint decomposition is

```
sqrt(1-z)=1-z/2-z^2/[2(1+sqrt(1-z))^2].
I(w)=1/w-1/[2(w+1)]
     -(1/2) integral_0^1 z^(w+1)/(1+sqrt(1-z))^2 dz.
```

For Re(w)>-2 and w different from 0,-1, Lean proves the actual cutoff limit

```
lim_{L -> -infinity} [integral_L^0 Psi_w(x)^2 dx
  + z(L)^w/(2w) - z(L)^(w+1)/(4(w+1))] = I(w)/2.
```

The remainder has an explicit uniform O(z) bound after the first quotient,
which gives an analytic cleared finite part on Re(w)>-2. In Re(w)>0 the
restored integral equals the ordinary beta integral. Analytic continuation
of the cleared sides gives

```
w(w+1) I(w)=Gamma(w+2) Gamma(3/2)/Gamma(w+3/2).
```

At every nonreal w in this strip,

```
I(w)/2=Gamma(w) Gamma(3/2)/[2 Gamma(w+3/2)] != 0.
```

Both original Xi fundamental frequencies satisfy these frequency conditions
by the existing corpus theorem, without a new strip or simplicity premise.
The nonzero radial factor is now derived from the original cutoff integral.

For the actual temporal Einstein Laurent coefficient define

```
C = angularSource * fundamentalSourceMoment * clearedOnset / denominatorSlope,
K(z_angular) = -2 w0 (lambda-2) C N(z_angular).
```

The original radius derivative is R'=R^2-1. Lean proves

```
(R(x)^2-1) Res(A^0)(x,z_angular) = K(z_angular) Psi_w0(x)^2.
```

Its finite-interval integral and two-counterterm horizon limit are proved:

```
FP integral_{-infinity}^0 (R^2-1) Res(A^0) dx
  = K * Gamma(w0) Gamma(3/2)/[2 Gamma(w0+3/2)].
```

This result integrates the already derived Laurent coefficient. It does
not interchange the frequency-residue limit with horizon exhaustion of the
whole continued current. Angular integration, its original measure and
cusp terms, and survival of C remain open. The formal equality to zero is
exactly equivalent to K=0; the radial finite part adds no cancellation.

New modules:

- `GaloisForLFunctions.HTGeometry.HalfOrderBetaFinitePart`, namespace
  `GaloisForLFunctions.HTGeometry.HalfOrderBeta`:
  `finitePart_cutoff_tendsto`, `cleared_eq_gamma`, `finitePart_eq_gamma`,
  `finitePart_ne_zero`.
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalRadialNorm`:
  namespace `RHTower.D4BMFundamentalNorm` supplies `mode_square_intervalIntegrable`, `mode_square_integral`,
  `mode_square_cutoff_tendsto`, `normFinitePart_eq_gamma`,
  `normFinitePart_ne_zero`; namespace `RHTower.D4BMPhysicalModeAction`
  supplies `physicalTimeResidue_radial_density`,
  `physicalTimeResidue_radial_integral`, `physicalTimeResidue_radial_cutoff_tendsto`,
  `physicalRadialResidueFinitePart_eq_gamma`,
  `physicalRadialResidueFinitePart_eq_zero_iff`.

Validation of both new leaves: warning-free foreground scratch checks;
exact isolated leaf audits passed with two jobs each (Beta finite part
93 seconds; physical radial norm 136 seconds), using cached imports only.
Both imports are wired into their respective umbrellas. The formal lint
gate passed with only existing large-file warnings.

## Other unresolved source factors

The source-moment substitution produces an incomplete beta integral; it does
not supply a nonvanishing proof. Source transposition retains the onset
remainder and horizon finite part. The actual angular source, radial source
moment, fixed onset, angular integration, and Hawking-clock extinction remain
substantive open problems. No numerical experiments are used.

## Active angular conjecture: the original cusp jet pairing

Use s=u+1/2, so the unchanged physical parameter is s0=rho/2. The literal
constant term read from `ThetaCuspHawkingBMEisensteinFullCuspSectorAssembly` is

```
E(s;Y)=A(s)Y^s+D(s)Y^(1-s)+tail,
A(s)=reflectedCompletedLambda(2s),
D(s)=reflectedCompletedLambda(2s-1).
```

The candidate follows from the original Green boundary identity, before
choosing any dual. For two spectral parameters s,t, division of the constant
term Wronskian by t(t-1)-s(s-1) gives the four terms

```
 A(s)A(t)Y^(s+t-1)/(s+t-1)
-D(s)D(t)Y^(1-s-t)/(s+t-1)
+[D(s)A(t)Y^(t-s)-A(s)D(t)Y^(s-t)]/(t-s).
```

Expand in s-s0 and t-s0 first, then take the fixed-parameter cusp finite
part of each jet. Because 2s0-1=rho-1 is nonzero and nonreal, the first two
terms retain nonzero cusp powers and their log derivatives. Their finite
part is subtracted. The constant log coefficient of the last term is

```
K(s,t)=[D(s)A(t)-A(s)D(t)]/(t-s),
K(s,s)=D(s)A'(s)-A(s)D'(s).
```

This is an analytic divided difference near (s0,s0). If A vanishes to order
m at s0 and A_m=A^(m)(s0)/m!, its normalized Taylor matrix
G_ij=[(s-s0)^i(t-s0)^j]K, 0<=i,j<m, has

```
G_ij=0             for i+j<m-1,
G_ij=D(s0)A_m      for i+j=m-1,
det G=(-1)^(m(m-1)/2) [D(s0)A_m]^m.
```

The algebraic implication is a paper derivation. The substantive conjecture
is that G is the jet pairing of the **full original angular fields** after
integrating on the actual truncated modular cell. This requires the literal
Green identity, cancellation of paired modular sides, uniform cusp-tail
bounds for every spectral jet, and the stated order of differentiation and
finite part. It is not an analytically varying finite part at distinct
fixed parameters; changing that order discards the diagonal information.
The coexact covector pairing must then be attached, with its actual measure
and boundary contacts. The corresponding generalized modes must enter the
left-QNM action and full source projection. None of these identifications
is claimed proved by the radial-norm modules.

Corpus ingredients read: `ReflectedDividedDifference` gives factorial-exact
normalized jets; `XiHedenmalmMultiplicityChain` gives vanishing below and
nonvanishing at the actual Xi multiplicity; `GammaShiftConfluentCasoratian`
contains triangular jet determinant arguments. `KeldyshQNMAlgebra` assumes
an invertible finite modal basis, so it supplies subsequent matrix algebra
only after the physical pairing above is established. Broad/deep searches
for biorthogonal, confluent, and MaassSelberg were partial; unrelated search
hits were not treated as applicable proofs.

## Closed incoming Green horizon expansion

Write G for the original `continuedResponse`, h=z^(w/2)H for its incoming
mode, S for the literal `sourceRemainder`, and O(w) for the fixed continued
onset 1/(w-2s)+onsetCorrection(2s,w). The original Wronskian gives

```
Q=G/h,
Q' = T = M(z,w) O(w) / [2 z sqrt(1-z) h(z,w)^2],
M = firstEndpointMellin(H*S).
```

This is the actual quotient derivative on the punctured connection germ.
The connection denominator cancels exactly. Removing the incoming powers
gives T = Mhat O/[2 sqrt(1-z) H^2], where Mhat=M/z^(w+1).
The new normalized Mellin bound is

```
|Mhat-S(w,0)/(w+1)| <= C z/(Re(w)+2).
```

Lean derives one frequency-horizon neighborhood with 1/2<=|H|<=3/2.
Combining its reciprocal bound with the actual source estimate proves,
uniformly in frequency near every nonreal w with Re(w)>-2 and w!=2s,

```
d(w)=S(w,0) O(w)/[2(w+1)],
|T(w,z)-d(w)| <= C z.
```

The physical specializations discharge these frequency conditions at both
Xi fundamental frequencies. No nonvanishing horizon mode or uniform
source remainder is added as a physical premise.

Define the endpoint coefficient from a positive radius b by

```
A_b(w)=G(w,b)/h(w,b)-integral_0^b T(w,z) dz.
|G(w,z)/h(w,z)-A_b(w)-d(w)z| <= C z^2,  0<z<=b.
```

The quadratic bound is uniform in a frequency ball wherever the connection
is nonzero. The fundamental theorem of calculus proves it for the actual
Green block. The source integral is analytic through the connection zero:
spatial continuity and the derived common bound feed the corpus theorem
`differentiableAt_integral_of_cauchy_dominated`. Consequently A_b is
meromorphic. These statements have passed scratch checks and exact leaf
audits in `NormalizedFirstEndpointMellin`, `ThetaCuspHawkingBMIncomingSourceTransport`,
`ThetaCuspHawkingBMLaplaceHorizonGaussBound`, `ThetaCuspHawkingBMIncomingSourceBound`,
and `ThetaCuspHawkingBMIncomingHorizonExpansion`.

G here is an original Green block. Passing this expansion through the
explicit gradient lift, all principal corrections, and the full physical
current is still part of the assembly below.

## Original incoming density: explicit endpoint coefficients

The actual Gauss coefficients now give, uniformly near each nonreal
frequency and for 0<=z<=1/2,

```
H(w,z)=1+h1(w)z+O(z^2),
h1(w)=gaussA(w)*gaussB(w)/gaussC(w),
1/[2sqrt(1-z)]=1/2+z/4+O(z^2).
```

Lean proves the arbitrary finite-order Gauss remainder from its coefficient
majorant, as well as the second-order specialization above. The Jacobian
remainder has the explicit bound 2z^2. The coefficient h1 is analytic at
nonreal frequencies, and h1(w0)=-1/2 at either fundamental root.

Multiplying these bounds with the actual Green quotient expansion gives

```
core(w,z)=(G/h)*H^2/[2sqrt(1-z)],
core0(w)=A_b(w)/2,
core1(w)=(h1(w)+1/4)*A_b(w)+d(w)/2,
|core-core0-core1*z| <= C*(|A_b(w)|+|d(w)|+1)*z^2.
```

The constant C is uniform on a derived frequency neighborhood away from
connection zeros. The dependence on A_b is retained explicitly; its pole
has not been bounded away. The actual source coefficient d is analytic
through connection zeros. The exact geometric attachment is

```
z^(w-1)*core(w,z)=G(w,z)*h(w,z)/[2z sqrt(1-z)],  0<z<1.
```

This identity also covers zeros of h, using Lean's totalized division; no
nonvanishing-mode hypothesis is added to it. At a fundamental frequency,
the linear coefficient is -A_b/4+d/2. The analytic source term d/2 must
remain in a subtraction of the full current, even though it has no residue.

These statements pass the foreground Lean scratch check in
`ThetaCuspHawkingBMIncomingPairingEndpoint`. The supporting leaves
`HypergeometricTaylorEndpointBounds`, `QuadraticEndpointProducts`, and
`ThetaCuspHawkingBMLaplaceHorizonTaylorBound` have passed exact leaf audits.
The incoming pairing leaf also passed its warning-free exact audit (177 seconds,
two jobs, cached imports only). All four umbrella imports are wired.
The formal lint gate passed, reporting existing large-file warnings.

## Exact temporal-contact horizon factor

The complete projected forcing has a proved exact factorization F=z F_hor.
It is obtained from the existing affine-frequency decomposition and both
proved horizon zeros of the reduced source polynomial:

```
reducedPolynomial(s,w,v)=(1-v^2)*reducedHorizonQuotient(s,w,v),
reducedHorizonQuotient = [reducedHorizonPolynomial(s,v)
  + w*s*(s-1)*v^2*((2s+3)v+3)/2]/(1+v).
```

Here v=radialUnit(x), 1+v>0, and z=1-v^2. The three cutoff coefficients
already carry z. Thus F_hor retains the native residual angular period and
all three complete principal-difference/cutoff periods. The exact original
radius identity R^2 z=R^2-1 then gives

```
(R^2-1) A^0 = [-2w(lambda-2)fg-w g F_hor] N.
```

This is the full continued temporal current, including its source contact.
The apparent additional horizon denominator cancels against a zero of the
literal source. The identities passed Lean in
`ThetaCuspHawkingBMTemporalContactHorizonFactor`, including a warning-free
exact leaf audit using cached imports; its umbrella import is wired. Uniform endpoint estimates
for F_hor and the restored full-current integral are still required.

All six new leaves passed their exact audits. The formal lint gate passed
with only existing large-file warnings.

## Active residue/interchange target

The complete temporal horizon-mode current now has a source-derived
uniform quadratic jet, exact identification with the original current,
spatial/frequency regularity, two-counterterm restoration at every
sufficiently small cutoff, and a residue theorem after integration.
The inner lift, all three principal channels and temporal source contact
are retained in this result, detailed below.

The complete normalizable left-mode current still needs its opposite
horizon branch and original outer interval joined at the same cutoff.
The original mode decomposition has opposite coefficient connection/(2w).
Its cancellation against the original Green denominator suggests an
analytic logarithmically restored opposite-current profile. Evaluating
and proving survival of the complete joined residue remain open.

### Direct analytic split for the incoming channel

The quotient derivative and its integrable endpoint bound give, by the
fundamental theorem of calculus, the exact paper identity

```
Q(w,z)=A_b(w)+P(w,z),       P(w,z)=integral_0^z T(w,t)dt.
M(w,z)=H(w,z)^2/[2sqrt(1-z)],
m1(w)=h1(w)+1/4,
M=1/2+m1*z+O(z^2),         P=d*z+O(z^2).
```

Here T is analytic through the connection zero. The same dominated-integral
argument already used for integral_0^b T gives pointwise analyticity of P.
The estimates imply P*M=d*z/2+O(z^2), uniformly on a smaller frequency
neighborhood. This leads to the following concrete finite parts:

```
N_b(w)=b^w/(2w)+m1(w)*b^(w+1)/(w+1)
       +integral_0^b z^(w-1)*(M-1/2-m1*z)dz,
J_b(w)=d(w)*b^(w+1)/(2(w+1))
       +integral_0^b z^(w-1)*(P*M-d*z/2)dz,
FP incoming integral = A_b(w)*N_b(w)+J_b(w).
```

The active formalization extends the existing source-transport module with
one common-neighborhood theorem for P: spatial continuity, pointwise
frequency analyticity through connection zeros, |P|<=Mz,
|P-dz|<=Cz^2, and the exact Q=A_b+P identity. It uses the already derived
transport neighborhood, the fundamental theorem of calculus, and the
Cauchy-dominated integral argument. The extension passed its warning-free
scratch check and exact module audit (118 seconds, two jobs, cached imports).
Its API is `incomingSourcePrimitive_common_data`.

`HTGeometry.QuadraticEndpointMellin` also passed its warning-free scratch
check and exact leaf audit (47 seconds, two jobs). For a fully frequency-
dependent F and a common bound |F-a0-a1*z|<=Cz^2 it proves integrability of
the subtracted density, its explicit norm bound and vanishing endpoint
limit, the exact original cutoff identity, convergence after restoring
both counterterms, and analyticity of the restored finite part. The APIs
are `remainder_integrable`, `remainder_norm_le`, `remainder_tendsto_zero`,
`remainder_analyticAt`, `cutoff_eq`, `cutoff_tendsto`, and
`finitePart_analyticAt`. The new umbrella import is wired.

The application to M and P*M passes its warning-free Lean scratch check.
`incomingPairingFinitePart_horizon_restoration` derives all analyticity,
spatial continuity, and uniform remainder conditions from the literal Gauss
family and actual source primitive, on the same fixed b. Its endpoint
limit has the original density G*h/[2z sqrt(1-z)], with coefficients
A_b/2 and (h1+1/4)A_b+d/2. Both restored pieces and P(w,b) are analytic
through the connection zero. The exact leaf audit passed (35 seconds,
two jobs, cached imports); the new umbrella import is wired.

The remainder integrands are bounded by a common constant times
z^(beta+1), for beta>-2. Thus the paper reduction is to prove N_b and J_b
analytic near the nonreal fundamental frequency, using the actual Cauchy-
dominated integral theorem. At a simple pole of A_b this yields
Res(FP incoming)=N_b(w0)*Res(A_b). The finite-part definitions and native cutoff-limit identity now pass
Lean. The physical residue exchange now passes its Lean scratch check.
The integral from b to the outer endpoint must also be restored before
identifying the complete Gamma radial norm.

The physical incoming residue is derived from a direct paper proof and
a successful Lean scratch check. For
K=reducedGreenGradient(chi,s,1), set

```
B_b(u)=[(normalizable(u,b)/h(u,b))*sourceMellin_b(u)
        +outerSourceIntegral_b(u)]*continuedOnset(u).
Q(u,b)=B_b(u)/[-connection(u,chi)].
```

At either physical fundamental frequency w0, h is nonzero on 0<b<1,
normalizable=h, and the two source moments combine into the already proved
fixed `fundamentalSourceMoment`. The derivative of -connection is the
proved nonzero -connectionSimpleSlope. Hence the actual punctured limit is

```
lim (u-w0)*Q(u,b)=sourceMoment(w0)*continuedOnset(w0)/[-connectionSlope(w0)].
```

Subtracting analytic P(u,b) gives the same residue for A_b. Analyticity of
N_b and J_b then gives the residue of the restored integral. The physical leaf
`ThetaCuspHawkingBMPhysicalIncomingPairingResidue` proves this and the actual
cutoff restoration at one common b, for every Xi copy, source branch and
fundamental side, without a supplied residue or interchange premise. Its
exact leaf audit passed without warnings (29 seconds, two jobs, cached
imports); its umbrella import is wired.
`physicalIncomingPoleAmplitude_eq_cleared` identifies the coefficient with
the existing sourceMoment*clearedOnset/physicalDenominatorSlope.
`physicalIncomingQuotient_residue` proves the pointwise quotient residue
at every interior radius; `physicalIncomingPairing_residue_and_restoration`
proves the residue after restoring the original horizon integral.
The source moment and onset may still vanish; no pole-survival claim is
added by these exact residue identities.

For the opposite left mode, the actual coefficient is c_minus=C/(2w),
where C=connection(w,chi). Its opposite Gauss product is
V=H(w,z)*H(-w,z)/[2sqrt(1-z)]=1/2+O(z). The exact logarithmic finite parts
suggested by the same source split are

```
L_b(w)=log(b)/2+integral_0^b (V-1/2)/z dz,
K_b(w)=integral_0^b P(w,z)*V(w,z)/z dz,
FP opposite integral = c_minus*(A_b*L_b+K_b).
```

The counterterm added at e is c_minus*A_b*log(e)/2. The paper proof of
analytic restoration uses the common O(z) bounds for V-1/2 and P, giving
bounded subtracted integrands. The actual quotient numerator above gives
C*A_b=-B_b-C*P(w,b) on the punctured connection germ. Consequently the
restored opposite pairing has the explicit analytic extension

```
[(-B_b-C*P(w,b))*L_b+C*K_b]/(2w).
```

Its value at a fundamental frequency is -B_b(w0)*L_b(w0)/(2w0), and its
residue is zero.

The general logarithmic restoration now passes a warning-free Lean scratch
check in `HTGeometry.LogarithmicEndpointFinitePart` (namespace
`LogarithmicEndpoint`). It proves integrability and |remainder|<=C*b,
vanishing remainder at zero, exact cutoff identity, actual cutoff limit,
and analyticity of the restored finite part for a frequency-dependent
kernel with a common O(z) endpoint remainder. Its warning-free exact
audit passed (6.3 seconds, two jobs, three cached project imports); its
umbrella import is wired.
The native opposite-mode application derives a common nonzero
incoming-mode interval; unlike the incoming square, the opposite density
cannot use totalized division at a zero of h. Shrinking to that interval
preserves A_b by the exact Q=A_b+P identity evaluated at the new cutoff.

`ThetaCuspHawkingBMOppositePairingFactor` passes its warning-free scratch
check and exact leaf audit (338 seconds, two jobs, 4,004 cached project
imports). Its narrowed imports avoid the unrelated field-wave layer.
It derives the original product's common bounds |V-1/2|<=Cz and |V|<=M,
frequency analyticity and spatial continuity, and its exact density
identity under h!=0. Its source and artifacts are installed and its
umbrella import is wired.
`ThetaCuspHawkingBMOppositePairingFinitePart` combines the Gauss nonzero
neighborhood with the source primitive's neighborhood, proves A_b is
preserved at their common smaller cutoff, and derives the original
c_minus*G*h(-w)/[2z sqrt(1-z)] logarithmic cutoff limit. Its scratch check
and exact leaf audit passed without warnings (87 seconds, two jobs,
4,335 cached project import metadata entries). Source, artifacts and
umbrella import are installed. The theorem
`oppositePairingFinitePart_horizon_restoration` supplies analytic L_b,
K_b and P_b at the same cutoff used by the original integral.

`ThetaCuspHawkingBMPhysicalOppositePairingRegularity` proves the physical
analytic extension, its source-determined resonance value, the punctured
limit of the actual restored pairing, its zero residue, and its original
logarithmic cutoff restoration on the same common cutoff. Its exact leaf
audit passed without warnings (107 seconds, two jobs, 4,341 cached project
import metadata entries). Source, artifacts and umbrella import are
installed. Denominator cancellation is isolated in a seven-variable scalar
lemma, avoiding normalization of expanded Green integrals; resource limits
are unchanged. Analyticity is proved for the explicit extension, not
inferred from the totalized pairing's assigned value at the pole.

Corpus searches include broad single-word queries, deep all-view method
retrieval, unlimited per-module results, pagination and exclusion of HB
modules. All candidate, source-method, idea and ingredient-set sections
are inspected. The latest division deep query was partial over 56,948
inventoried files (compiler metadata mostly pending); its order-theoretic
division suggestions do not establish a complex residue theorem. The
source-moment query completed its retrieval and located the exact
`fundamental_source_sum_eq_moment` method used in the physical proof.
The Cauchy-dominated integral mechanism, source primitive, Gauss remainder
and actual connection slope are the useful verified ingredients. Broad
arXiv queries also explored transgression, gluing and renormalization;
no retrieved June–September 2026 theorem supplied an applicable ingredient.

Latest repository lint exits with five unreachable modules outside these edits:
`RHTower.DeningerOriginalGreenPoleCalculus`,
`RHTower.ThetaCuspHawkingBMHorizonCoordinateJets`,
`HTGeometry.ElementaryHorizonJets`,
`HTGeometry.SecondEndpointMellinLaurentInterchange`, and
`HTGeometry.UniformSecondOrderJet`.
The new restoration and outer-pairing leaves are wired and their exact
audits passed. The global lint gate is not claimed passed for this state.


### Frequency Lagrange route for full radial assembly

The corpus supplies the complex compact-interval Lagrange identity in
`HTGeometry.SturmLagrangeIdentity` and the actual forced radial bracket in
`ThetaCuspHawkingBMOriginalForcedBoundaryPairing`. The next candidate uses
frequency differentiation of the original normalizable solution n. In the
tortoise equation G''-(w^2+V)G=F, where F is minus the corpus
`originalForcing`, and n''-(w^2+V)n=0, putting v=partial_w n
gives v''-(w^2+V)v=2*w*n, hence

```
2*w*integral_L^0 G*n = [G*v'-G'*v]_L^0 + integral_L^0 F*v.
```

This is a paper mechanism, not yet an endpoint theorem in Lean. It requires
the actual mixed frequency/radial derivatives and restored Wronskian limit;
the compact-interval identity alone does not supply those conclusions.
The original outer source already has a common bounded majorant through
z=1 (`outerSource_uniform_bound`), and its actual integral is entire
(`outerSourceIntegral_entire`). These are available ingredients for the
remaining outer-endpoint proof.

The mechanism has an exact normalization check from the existing Gamma
formulas. At a fundamental connection zero, the other Gamma argument is
w+3/2, so Gamma recurrence gives

```
connectionSimpleSlope(w,chi,side) = 2*w*normFinitePart(w).
```

Consequently the already integrated temporal Laurent density simplifies
on paper to

```
(physicalAngularParameter(q)^2-1/4-2) * physicalSelfSourceCoefficient(q)
  * fundamentalSourceMoment(w,s,a) * continuedOnset(s,w)
  * modeAngularSquare(physicalModeAngularJet(q,z)).
```

This cancellation identifies the desired source quantity in the full
restored action. It does not by itself interchange the original current's
radial exhaustion and frequency residue. This exact simplification is not
yet a new Lean theorem.

Latest broad searches include transposition and Lagrange, with all retrieval
views, uncapped module hits and (for Lagrange) exclusion of HB modules.
The Lagrange method retrieval located the actual integrated Sturm bracket;
its proposed polynomial-interpolation ingredient set is not applicable.
Retrieval completed, but compiler metadata remains mostly pending and
semantic coverage unavailable. The scoped outer search located the actual
uniform-bound and entire-integral theorems above. ArXiv Volterra and
isospectral searches with a recent-date preference returned older papers;
`Isospectrality and heat content` (arXiv:1304.4030, revised 2014) was opened.
No external theorem from it has been used in these proofs.


The outer-integral candidate uses the regular tortoise ODE rather than a
Gauss estimate at z=1. `continuedTortoiseGreen_hasDerivAt` and
`continuedTortoiseGreen_equation` supply its actual two spatial derivatives
and forced equation on t<0. On a fixed interval T<=t<0, the potential
horizonCoordinate(t)*(1/4+chi^2) is bounded. A common frequency ball and
bounded initial values of the connection-cleared response and its first
derivative at T therefore give a uniform bound on both via Gronwall.
The same argument applies to the normalizable mode. Their product then
has a constant integrable majorant on (T,0), allowing frequency analyticity
of the cleared outer pairing by the Cauchy-dominated integral theorem.

The stronger usable corpus estimate is
`forcedSecondOrder_horizon_bound_symmetric` in `HTGeometry.SymmetricHorizonGrowth`.
Its original principal-frequency application is
`JointSourceClearedUniformBound.clearedPrincipalDifference_compact_bound`.
The independent-angular-frequency application now passes Lean in
`ThetaCuspHawkingBMReducedGreenUniformBound` (scratch and exact leaf audit
passed without warnings; 67 seconds, two jobs, 4,326 cached project imports).
Its source, artifacts and umbrella import are installed. It uses the already
defined `clearedReducedGreen`, including its explicit gradient lift, and
proves the corresponding first jet and actual cleared ODE:

```
U'' = w^2*U + z(t)*(1/4+chi^2)*U - F_clr,
F_clr = -connection(w,chi)*reducedCoefficient(s,w,a,clearedOnset(s,w),t).
```

Both initial jets are analytic in frequency. The existing
`reducedCoefficient_family_norm_le_exp` derives the compact-family forcing
bound. The resulting theorem `clearedReducedGreen_compact_bound` states

```
|U(w,t)| <= C*exp(-|Re(w)|*t),
  w in interior(Omega), t<0,
```

for every compact Omega in the nonreal strip Re(w)>-2. The estimate extends
through source and connection zeros using continuity of the explicit
analytic numerator. It does not require an ODE for a totalized response at
those zeros. `physicalClearedReducedGreen_outer_uniform_bound` then derives,
for each Xi copy, branch, side and finite T, a frequency ball and one
constant bounding the actual full reduced numerator for all T<=t<0.
No forcing, growth, initial-data or resonance-regularity premise is supplied
to that physical theorem. Denominator algebra is isolated in scalar lemmas;
resource limits are unchanged.

The common bound for the frequency-dependent normalizable left mode and
Cauchy-dominated integration of its product with this numerator now pass
Lean in the outer-pairing leaf described below. `outerGauss_uniform_bound`
and the positive-radius power formula supply the concrete estimates. Spatial
continuity of the undivided moments is available through
`horizonFirstMoment_hasDerivAt` and `outerSourceIntegral_hasDerivAt` in
`JointSourceClearedRadialAdmission`. The full temporal current still needs
all four source channels and both contacts assembled before its residue
interchange is proved.

A broad deep `Gronwall` search also located the phase-pair proof in
`HTGeometry.LinearSecondOrderComparison.phasePair_norm_le`. Its existing
statement is real and homogeneous; its useful mechanism is controlling
the solution and first derivative together. The native application needs
the complex forced pair and actual source bounds described above. The
retrieval completed over 56,989 inventoried files, with 44,547 compiler
entries pending and stale snapshots reported; candidates, source methods,
proof ideas and ingredient sets were inspected, not treated as verified
applications.

Further broad searches used `forced`, `normalizable`, and OR matching for
`bound uniform`, plus a deep query describing the paired complex forced
ODE mechanism. The bound query was partial; its candidate and method
sections led to the existing cleared-principal estimate and its underlying
symmetric growth theorem. The normalizable query completed retrieval over
56,998 files, with compiler metadata mostly pending and stale coverage
snapshots reported. Its normalizable boundary theorem still assumes the
original chamber and is not used as a uniform continued-frequency bound.
Broad arXiv searches for Volterra and impedance included
[Volterra Generative Models](https://arxiv.org/abs/2606.18071), submitted
16 June 2026. Its approximate stochastic lifts supply no exact theorem
used in this deterministic Green-response proof.

### Actual outer pairing and residue

The explicit outer Gauss factor and positive-radius power formula derive
one uniform bound for `normalizable(u,chi,z(t))` on a frequency ball and
T<t<0. Combined with the full reduced numerator bound above, this gives
absolute integrability and frequency analyticity of

```
R_T(w) = integral_(T,0) clearedReducedGreen(w,chi,s,a,t)*n(w,t) dt.
```

The original pairing is
`Q_T(w)=integral_(T,0) continuedReducedGreen(w,chi,s,a,1,t)*n(w,t) dt`.
Its original scalar denominator gives the exact identity
`R_T(w)=D(w)*Q_T(w)`, where `D(w)=-(w-2*s)*connection(w,chi)`.
At each physical fundamental w0, the actual fixed-source factorization
then gives

```
lim_(w->w0) (w-w0)*Q_T(w)
  = [fundamentalSourceMoment(w0,s,a)*clearedOnset(s,w0)
       /physicalFundamentalDenominatorSlope(q,branch,side)]
      *integral_(T,0) n(w0,t)^2 dt.
```

The same amplitude already occurs in the restored incoming horizon block.
The outer integral is taken before the frequency limit. This argument
retains the original reduced response's gradient lift. The prepared Lean
leaf `ThetaCuspHawkingBMReducedOuterPairing` passes its scratch check and
exact leaf audit without warnings (34 seconds, two jobs, 4,332 cached
project imports). Source, artifacts and umbrella import are installed.
Matching the inner and
outer coordinate cutoffs and assembling the complete source/contact
current remain separate obligations. No source-moment or onset
nonvanishing follows from the residue identity alone.

### Common-cutoff fundamental norm

The joining identity is now proved for every actual fundamental frequency
and every T<0, with b=horizonCoordinate(T):

```
incomingNormFinitePart(chi,b,w0)
  + integral_(T,0) n(w0,t)^2 dt = D4BMFundamentalNorm.normFinitePart(w0).
```

`D4BMFundamentalNorm.physicalFundamentalNorm_join` in
`ThetaCuspHawkingBMFundamentalNormJoin`
identifies the incoming Gauss factor with sqrt(1-z), its first coefficient
with -1/2, and the pairing kernel with sqrt(1-z)/2. Its two subtraction
coefficients are exactly 1/2 and -1/4. The exact
`QuadraticEndpointMellin.cutoff_eq` identity then cancels the arbitrary
cutoff against the original tortoise-coordinate outer integral. The
finite part at upper endpoint one equals the already established
`D4BMFundamentalNorm.normFinitePart`; no new normalization is assigned.

Scratch and exact leaf audit passed without warnings (28 seconds, two
jobs, 4,415 cached project imports). Source, five artifacts and umbrella
import are installed. Small scalar identities and integral congruences
keep elaboration local; no resource limits were raised.

### Regular horizon branch joined to the original outer integral

The verified `ThetaCuspHawkingBMRegularOuterPairing` derives frequency
analyticity of the actual Wronskian coefficient Aplus(w), with Aplus(w0)=1
supplied by the original fundamental normalization theorem. Continuity of
the original horizon coordinate and the intermediate value theorem match
the restored horizon cutoff to an actual T<0. Thus

```
S_T(w) = Aplus(w)*incomingPairingFinitePart(s,chi,a,1,K,z(T),w)
           +continuedReducedOuterPairing(chi,s,a,T,w)
lim_(w->w0) (w-w0)*S_T(w)
  = physicalIncomingPoleAmplitude(q,branch,side,a)*normFinitePart(w0).
```

`regularOuterPairingCutoff` retains the original positive-cutoff incoming
integral and both derived counterterms, multiplied by Aplus(w), then adds
the original outer integral. Its cutoff limit is S_T(w) on the actual
connection-nonzero germ. This restoration precedes the frequency-residue
limit. The theorem constructs its matching cutoff and frequency ball;
neither is an added premise. Scratch and exact leaf audit passed without
warnings (37 seconds, two jobs, 4,419 cached project imports). Source, five
artifacts and umbrella import are installed; no resource limits changed.

The opposite horizon block and inner explicit lift still need admission
at this same cutoff, followed by all four source channels and both
Einstein contact terms. The assembled current, retained pairing survival,
fixed Hawking-clock extinction and RH remain unproved.

Broad searches for gluing, cutoff and tortoiseOf and natural-language deep
method searches were inspected alongside candidate lemmas, source
arguments and proposed ingredient sets. The exact quadratic Mellin
identity was applicable; generic lattice-join suggestions were not. The
Wronskian search recovered both actual frequency-analytic radial jets.
Coverage inventoried about 57,010 files, with most compiler metadata
pending and semantic coverage unavailable; the Wronskian deep request was
partial. New candidate applications were verified by Lean. Broad arXiv
factorization searches included the July 2026
[Landweber unique-factorization paper](https://arxiv.org/abs/2607.03475);
its algebraic finite-jet result is not used in this analytic cutoff proof.

The repository lint gate still reports unreachable modules outside this
work, including the pending horizon-jet and endpoint-interchange leaves.
Both new joining modules are wired and passed exact audits; global lint
is not claimed passed. Frontier map and universal STATUS were not edited.

### Simultaneous incoming/opposite cutoff restoration

The two restoration theorems now hold at every sufficiently small positive
cutoff, using one frequency ball and one upper cutoff. The endpoint
amplitude is re-centered exactly by Q(z)=Q(b)-P(b)+P(z), so restriction
preserves the original response and counterterms. Existing theorem
signatures remain as corollaries at the upper cutoff. Scratch checks and
exact leaf audits passed for `ThetaCuspHawkingBMIncomingPairingFinitePart`
(124 seconds, two jobs, 4,337 cached project imports) and
`ThetaCuspHawkingBMOppositePairingFinitePart` (9.3 seconds, two jobs, 4,335
cached project imports). Updated sources and artifacts are installed.

The active joining proof takes a cutoff below both bounds and retains the
actual normalizable decomposition n=Aplus*horizon+connection/(2w)*horizon(-w).
The proposed finite part is Aplus*incomingPairingFinitePart plus
oppositePairingFinitePart. Its original single-integral restoration keeps
both power counterterms and the logarithmic counterterm. Spatial
integrability is derived from `continuedResponse_hasDerivAt` and the
actual mode jets before applying integral additivity. The incoming
residue is the original fixed-source amplitude times N_b; the opposite
block has an analytic extension and zero residue at this same b. Joining
the original outer integral should then give the established full radial
norm with the same source amplitude. The original single-integral splitting theorem in
`ThetaCuspHawkingBMNormalizableHorizonPairing` has passed scratch and exact
leaf audit (100 seconds, two jobs, 4,341 cached project imports); source,
five artifacts and umbrella import are installed. The physical residue
and simultaneous restoration theorem is now proved in
`ThetaCuspHawkingBMPhysicalNormalizablePairing`:

```
F_T(w) = Aplus(w)*incomingPairingFinitePart(w)
           +oppositePairingFinitePart(w)+Q_T(w)
lim_(w->w0) (w-w0)*F_T(w)
  = physicalIncomingPoleAmplitude(q,branch,side,a)*normFinitePart(w0).
```

`physicalNormalizableOuterPairing_residue_and_restoration` constructs one
T<0 and one frequency ball. On the original connection-nonzero germ,
`normalizableOuterPairingCutoff` tends to F_T(w): this expression contains
the single original normalizable horizon integral, both power
counterterms, the logarithmic counterterm, and the original outer
integral. The proof derives ordinary spatial integrability before
splitting the horizon integral. The opposite analytic extension and its
zero residue are established at exactly the same b=horizonCoordinate(T)
as the incoming block. The source amplitude and normalization remain the
original ones. Scratch and exact leaf audit passed without warnings
(10 seconds, two jobs, 4,425 cached project imports); source, five
artifacts and umbrella import are installed. The scalar source-endpoint
step uses explicit normalization and mul_sub instead of expanding the
source integral inside ring. No resource limits were raised.

The incoming full-current result below retains the inner lift and complete
source contact. Their opposite-branch restoration and full outer-current
assembly remain open for the normalizable left mode.

The next inner-lift correction has a concrete source-derived kernel.
Writing r=sqrt(1-z), the actual definitions give

```
radialLift(s,w,a,T,t)
  = (-s*(s-1)/4)*z^(w/2)*(1+r)^(2*s-w)*a^2*T*r^3.
```

Thus its incoming pairing density is z^(w-1) times
`(-s*(s-1)/8)*amplitudeProfile(s,a,T,w,z)*(1-z)*H_w(z)`;
the opposite pairing has z^(-1) and H_(-w) instead. The leading kernel
need not vanish. The proposed correction therefore retains two incoming
power subtractions and one opposite logarithmic subtraction.
`ThetaCuspHawkingBMHorizonCoordinateJets` already supplies
`radialLift_eq_profile`, `amplitudeProfile_jet` and `liftProfile_jet`.
Combining the amplitude jet with the exact factor 1-z and the Gauss jet
avoids introducing an inverse-square-root estimate. The fixed onset is
analytic off its source pole, separated from every physical fundamental
frequency by the existing source-rate theorem. The incoming full-current proof below retains this lift directly inside
its source-derived profile; a separate lift-only finite part is not needed
for that result. Its opposite-channel restoration remains open.

The restriction, cutoff-method, continuedResponse and lift searches used
broad and deep corpus retrieval, including source arguments and proposed
ingredient sets. The actual spatial derivative theorem and explicit
amplitude/lift jets supplied applicable ingredients; generic restriction
and transport suggestions did not replace the required source identity.
Retrieval completed with compiler metadata mostly pending and semantic
coverage unavailable. Broad arXiv sewing/localization searches included
[nonlocal localization](https://arxiv.org/abs/2606.27387), June 2026. Its
normalized detector-kernel variance law supplies no theorem used in this
complex bilinear radial pairing. No computation was run.

All four affected leaves passed scratch and exact-module checks with no
resource-limit increases. New imports are wired; no umbrella build ran.
Final lint status is recorded with the full-current result below.

## Full temporal horizon current: original density, restoration and residue

`ThetaCuspHawkingBMTemporalCurrentHorizonIdentification` identifies the
complete horizon-mode temporal current with the existing uniform profile.
The proof separately reconstructs the reduced self response, all three
principal cutoff channels, the full source contact and the radial Jacobian.
`clearedDensityProfile_eq_actualAction` identifies the same expression
with component zero of the actual projected Einstein action on its physical
Laplace band. This is the horizon left-mode leg (`outer=false`).

`ThetaCuspHawkingBMTemporalCurrentHorizonRegularity` proves spatial
continuity and frequency analyticity of the full cleared profile through
the fundamental QNM. Its continuity proof differentiates the undivided
source moments directly; it never obtains a value at the QNM by dividing
by the vanishing connection coefficient. Frequency analyticity requires
only the existing nonreal strip and separated source/principal poles,
which the physical restoration theorem discharges on one neighborhood.

Write D(w)=-(w-2s)*connection(w,chi), F(w,z)=clearedDensityProfile(w,z),
and j(w,z)=continuedTemporalRadialDensity(w,z). The checked identity is

```
z^(w-1)*F(w,z) = D(w)*j(w,z).
```

The density j is the original temporal current evaluated at tortoiseOf(z),
including the exterior radial Jacobian. Let N_b(w) be the two-term Mellin
finite part of F, with c0(w),c1(w) supplied by its proved uniform quadratic
jet. `physicalTemporalCurrent_horizon_restoration_and_residue` proves,
without supplied regularity or residue assumptions, that actual physical
q, branch, side, amplitude and angular point determine R>0 and B>0 such
that for EVERY 0<b<=B:

- N_b is analytic at the physical fundamental frequency w0.
- For w in the common frequency ball and connection(w,chi) nonzero,
  the original cutoff expression
  `integral(e..b,j(w,z)) + [c0(w)*e^w/w+c1(w)*e^(w+1)/(w+1)]/D(w)`
  tends to N_b(w)/D(w) as e tends to zero from above.
- After radial integration and endpoint restoration,
  `(w-w0)*N_b(w)/D(w)` tends to
  `N_b(w0)/physicalFundamentalDenominatorSlope(q,branch,side)`.

The source lift and contact are retained inside F. The power counterterms
come from the common source-derived jet; neither a residue nor a finite
part is assigned. Allowing every smaller cutoff permits later joining to
the opposite branch at exactly the same endpoint.

The proofs use explicit continuity/analyticity composition and polynomial
evaluation instead of broad tactic expansion of the full source. Redundant
ring/cast steps were removed. All three modules passed scratch checks at
default resource limits. Exact leaf audits passed warning-free: identification 80 seconds,
regularity 36 seconds, restoration/residue 110 seconds; each built only
the requested leaf (two Lake jobs) against cached dependencies. Sources,
five artifacts per new leaf and umbrella imports are installed. The three
used jet-support modules are also wired into HTGeometry. No umbrella,
full or dependency build ran; no resource limit was raised.

The full-normalizable-current conjecture is proved in the four companion
leaves described below: the actual opposite coefficient cancels the
self-channel pole, its uniform jet gives a logarithmic subtraction, and
the original complete horizon integral is restored before residue extraction.
The full radial join below now supplies the original outer interval and
evaluates the joined residue. Nonvanishing of its explicit source amplitude,
Hawking-clock extinction and RH remain unproved.

Broad amplitude/profile/logarithmic searches and mechanism-based deep
searches inspected candidate lemmas, source arguments and ingredient sets.
`QuadraticEndpointMellin.finitePart_analyticAt` and its cutoff theorem were
applicable and verified in the new Lean proof. Retrieval reported stale
coverage snapshots, unavailable semantic coverage and one unfinished
reranking stage; corpus search coverage was not treated as a proof.
A broad arXiv transmutation search also found the
[June 2026 revision of the Kannai-transform paper](https://arxiv.org/abs/2601.03616).
Its diffusion/wave representation was not used as a premise here.

Repository lint passes after the full radial join and all four new
imports. Previously pending companion modules are now reachable.
Frontier map and universal STATUS remain untouched.

## Full normalizable temporal horizon current

The pole-cancellation conjecture succeeds for the original current, with
the complete self response, all three principal channels, explicit lift
and temporal source contact retained. Four leaves supply the construction:

- `ThetaCuspHawkingBMTemporalOppositeCurrentProfile`: the exact ratio
  `-1/(2w*(w-2s))`, a uniform analytic quadratic jet for the opposite
  profile, and its spatial/frequency regularity through the physical QNM.
- `ThetaCuspHawkingBMTemporalNormalizableCurrentDensity`: the opposite
  contribution is the difference between the original normalizable
  current and its actual incoming-mode component. The original
  homogeneous-mode connection formula identifies this difference with
  the derived opposite profile divided by z. Finite-cutoff integrability
  is proved before decomposing the current integral.
- `ThetaCuspHawkingBMTemporalOppositeCurrentRestoration`: the profile's
  own constant jet coefficient supplies the logarithmic counterterm.
  Its restored integral is analytic through the QNM and has zero residue.
- `ThetaCuspHawkingBMTemporalNormalizableCurrentRestoration`: one original
  normalizable-current integral has a common-cutoff restoration with
  both power counterterms and the logarithmic counterterm. Residue
  extraction follows this restoration.

Let A(w) be the original normalizable mode's horizon-regular coefficient,
j_n the original temporal radial density with `outer=true`, j_h its
`outer=false` counterpart, and D(w)=-(w-2s)*connection(w,chi). The exact
opposite-mode coefficient is connection(w,chi)/(2w). Consequently

```
j_o = j_n - A(w)*j_h = F_o(w,z)/z,
F_o = [-1/(2w*(w-2s))] *
      N * [-2w(lambda-2)*selfPart - w*contactPart] * H_(-w)(z)
      / (2*sqrt(1-z)).
```

Here selfPart and contactPart are the original cleared source profiles,
N is the actual angular bilinear square, and H is the original Gauss
factor. The connection zero cancels algebraically; no self-connection
nonvanishing assumption is used for the profile's analytic germ.
The Gauss lower bound supplies a common spatial/frequency neighborhood
for the original finite-current decomposition.

For the source-derived incoming coefficients c0,c1 and opposite coefficient
d, set

```
N_b(w) = QuadraticEndpointMellin.finitePart(F,c0,c1,b,w),
L_b(w) = LogarithmicEndpoint.finitePart(F_o,d,b,w),
M_b(w) = A(w)*N_b(w)/D(w) + L_b(w).
```

The physical data determine R>0 and B>0, B<=1/2, such that for EVERY
0<b<=B and every w in the common ball with connection(w,chi) nonzero,

```
integral(e..b,j_n(w,z))
 + A(w)*[c0(w)*e^w/w + c1(w)*e^(w+1)/(w+1)]/D(w)
 + d(w)*log(e)  -->  M_b(w)                       (e --> 0+).
```

The actual normalizable coefficient satisfies A(w0)=1. The separately
proved analytic continuation of L_b and incoming restored residue give

```
(w-w0)*M_b(w) --> N_b(w0)/physicalFundamentalDenominatorSlope.
```

This closes the original normalizable left-mode temporal current's
horizon restoration at each angular point. The full radial join below
adds its original outer interval; a nonzero retained action is still open.

The proved residue-evaluation identity below is the exact factorization
`F(w0,z)=K*incomingPairingFactor(w0,chi,z)`, where

```
K = N * (-2*w0*(lambda-2)) * physicalSelfSourceCoefficient(q)
    * fundamentalSourceMoment(w0,s,a) * clearedOnset(s,w0).
```

The existing fundamental Green factorization gives its self-channel
identity; the clearing factor kills the principal/contact terms at w0.
The new proof identifies the actual endpoint coefficients, retains their
uniform-jet witnesses through restoration, and evaluates N_b(w0) as K
times the original incoming norm finite part. The corpus's
`JetCoefficientUniqueness` supplies the coefficient-uniqueness mechanism,
and `physicalFundamentalNorm_join` supplies the norm's exact cutoff join.
Neither substitutes for the full-current outer-integral proof or
nonvanishing of the physical coefficient.

Broad opposite-mode retrieval and mechanism-based deep searches inspected
candidate lemmas, source arguments and proposed ingredient sets. The
original connection identity, analytic jet closure and logarithmic
endpoint theorem were applicable and checked in Lean. A later deep
coefficient/finite-part search returned a proposed gamma-pole ingredient
set whose premises do not identify this current; it is not used.
That search completed, but its coverage was a snapshot with mostly
pending compiler metadata and unmeasured semantic coverage. A broad
arXiv confluence/impedance search included the August 2026
[finite-array active-impedance paper](https://arxiv.org/abs/2608.17844);
no result from it is used in the proof. No computation was run.

All four new leaves passed `lake env lean` scratch checks and exact
`lake build <module>` audits against cached dependencies. Audit times:
opposite profile 88 seconds, original current density 133 seconds,
opposite restoration 57 seconds, normalizable restoration 9.8 seconds.
Each audit built only the requested leaf (two Lake jobs). The proofs use
explicit analytic composition, local identities and narrow associative
rewrites; no heartbeat or other resource limit was raised. Sources, five
artifacts per leaf and all four RHTower imports are installed. No full,
umbrella or dependency build ran, and no axiom checks were run. Repository
lint now passes with the full radial join and its imports.

Owned Lean/Lake processes have completed. Scratch files, search outputs
and the isolated audit package/helper were removed; installed proofs and
artifacts remain.

The full radial join below integrates the companion sources
`ThetaCuspHawkingBMTemporalCurrentClearedDensityBound`,
`ThetaCuspHawkingBMTemporalCurrentRadialCutoff` and
`ThetaCuspHawkingBMTemporalCurrentRadialPackage`. The last exposes the
incoming current's endpoint-jet witness, analytic outer integral and
original full radial cutoff limit. The full normalizable join retains
the opposite branch and passed a combined import check before assembly.

## Full normalizable radial current: source evaluation and outer join

The checked full radial join attaches the original normalizable temporal
horizon current to its original outer integral. Its source-evaluated residue is

```
K * normFinitePart(w0) / physicalFundamentalDenominatorSlope,
K = N * (-2*w0*(lambda-2)) * physicalSelfSourceCoefficient(q)
    * fundamentalSourceMoment(w0,s,a) * clearedOnset(s,w0).
```

`ThetaCuspHawkingBMTemporalCurrentFundamentalFactor` is installed and
audited. It evaluates the complete cleared horizon profile as
`K*incomingPairingFactor`, proves uniqueness of its actual two endpoint
coefficients, and evaluates its quadratic finite part as K times the
original incoming norm finite part. The source moment is the original
fixed endpoint pairing; no residue value is assigned.

`ThetaCuspHawkingBMTemporalOppositeOuterCurrent` is also installed and
audited. Its density is the coefficient `-1/(2w*(w-2s))` times the
complete cleared source factor and the original opposite homogeneous
mode. The original connection formula identifies it with
`(R^2-1)*A^0_normalizable - A(w)*(R^2-1)*A^0_incoming`. Uniform source
bounds and the horizon-mode bound centered at -w0 give a common outer
majorant. Spatial continuity, frequency analyticity and dominated Cauchy
integration prove an analytic original opposite outer integral through
w0. The full source, principal terms, lift and source contact are retained.

`ThetaCuspHawkingBMTemporalNormalizableOuterCurrent` proves integrability
of the original normalizable outer current before splitting its integral,
extracts its residue and evaluates its cleared fundamental density as
K times the square of the original normalizable mode. It also proves
`physicalTemporalFundamentalRadialResidue_ne_zero_iff`: the radial residue
is nonzero exactly when K is nonzero. This leaf is installed and audited.

`ThetaCuspHawkingBMTemporalNormalizableRadialJoin` is installed and audited.
Its `physicalNormalizableTemporalCurrent_full_radial_restoration_and_residue`
joins the restored horizon current and original outer integral at the same
negative tortoise cutoff, for every sufficiently small positive cutoff.
It proves the original cutoff limit, integrability of the outer current,
the displayed source-evaluated residue and independence of the joined
numerator from that cutoff.

The two existing horizon-restoration leaves now expose their uniform-jet
witnesses in `physicalTemporalCurrent_horizon_restoration_data` and
`physicalNormalizableTemporalCurrent_horizon_restoration_data`. Their
original public theorem statements are preserved as wrappers. Thus the
coefficient evaluation applies to the same source-derived counterterms;
no second choice of endpoint coefficients is assumed. The original norm
and denominator are nonzero at every physical fundamental frequency.
Nonvanishing of K, full angular/action comparison and Hawking-clock
extinction remain open.

All six affected leaves passed `lake env lean` scratch checks and exact
`lake build <module>` audits. Final audit times: fundamental source factor
52 seconds, opposite outer current 22 seconds, incoming horizon data
6.3 seconds, normalizable horizon data 58 seconds, original normalizable
outer current 74 seconds, full radial join 36 seconds. Each audit built
only its requested leaf against cached dependencies (two Lake jobs).
Four new leaves are wired into RHTower; the two modified leaves retain
their existing imports. No full, umbrella or dependency build was run
by this work. No heartbeat or other resource limit was raised, and no
axiom checks or mathematical computations were run.

The independent incoming-current work now includes
`ThetaCuspHawkingBMTemporalCurrentRadialLaurent`. Its source was inspected;
an untested duplicate incoming-radial draft was discarded and this work
continued with the missing opposite outer contribution. A scratch import
check confirmed that the incoming radial package and normalizable horizon
module can be imported together. The broad moment search and deep
endpoint/source-factorization search inspected candidate lemmas, source
arguments and proposed ingredient sets; the Fokas matrix proposal does
not supply this current's endpoint identity. Retrieval completed with
snapshot coverage and unmeasured semantic coverage. Broad transmission
and factorization arXiv searches did not return verified June–September
2026 matches; the opened [soft-collinear factorization paper](https://arxiv.org/abs/hep-ph/0109045)
is not used as a premise. No computation was run.

### Exact source-moment reduction

The original physical `fundamentalSourceMoment` now has a Lean-checked
polynomial-coordinate evaluation. Set `z=x*(2-x)`, with `0<x<=1`, and write

```
A = (5*s^2+15*s+4)/4,
B = s*(s-1)*((s+2)*(2*s+3)-(w+1)*(w+2)/2)/4,
H_n(x) = (1-x)^n*(2-x)^(2*s),
I_n = firstEndpointMellin(H_n,1,w),
d = 2*s-w,  e = w+2*s+2.
```

The actual source density times the substitution's Jacobian is exactly
`2*a^2*x^w*(A*H_2(x)+B*H_4(x))`. Both A and B come from the original source.
The original integral above `epsilon*(2-epsilon)` therefore equals the
polynomial integral above epsilon. The counterterm difference is exactly

```
F(0)/(w+1) * epsilon^(w+1)*((2-epsilon)^(w+1)-2^(w+1)).
```

Its last factor is a differentiable endpoint difference. The slope limit
and `Re(w)>-2` prove that the whole difference tends to zero. Compact
bounds on the actual derivatives of H_n prove admission of each moment;
no new regularity hypothesis is supplied for the physical source.
Consequently the proved identity is for the same original finite part:

```
M = 2*a^2*(A*I_2+B*I_4).
```

Integration by parts with the primitive
`x^(w+1)*(1-x)^n*(2-x)^(2*s+1)` retains its upper boundary:

```
n*I_(n-1) + d*I_n - (n+e)*I_(n+1) = -0^n.
e*(e+1)*I_2 = (e+d^2)*I_0+d,
e*(e+1)*(e+2)*(e+3)*I_4 =
  (d^4+(6*e+8)*d^2+3*e*(e+2))*I_0+d*(d^2+5*e+8).
```

In particular, the zeroth recurrence has right side -1. The exact physical
source evaluation is the denominator-cleared identity

```
D*M = 2*a^2*(P*I_0+Q),
D = e*(e+1)*(e+2)*(e+3),
P = A*(e+d^2)*(e+2)*(e+3)
    + B*(d^4+(6*e+8)*d^2+3*e*(e+2)),
Q = d*(A*(e+2)*(e+3)+B*(d^2+5*e+8)).
```

`ThetaCuspHawkingBMFundamentalMomentPolynomial` proves the exact original
source substitution. `ThetaCuspHawkingBMFundamentalMomentCounterterm`
provides the endpoint limit mechanism.
`ThetaCuspHawkingBMFundamentalJacobiMoment` derives moment admission from
its actual core. `ThetaCuspHawkingBMFundamentalJacobiRecurrence` proves
the recurrence and second/fourth reductions.
`ThetaCuspHawkingBMFundamentalSourceMomentTransport` proves
`physicalFundamentalSourceMoment_polynomial` and
`physicalFundamentalSourceMoment_base_period`, for every actual Xi copy,
branch, side and amplitude, without extra physical hypotheses.

All five leaves passed `lake env lean` scratch checks and exact
`lake build <module>` audits. Audit times were 71, 75, 25, 78 and 134
seconds, respectively; each built only its requested leaf against cached
dependencies (two Lake jobs). All five are installed and wired into
RHTower. No heartbeat or other resource limit was raised; no umbrella,
full or dependency build, axiom check or mathematical computation was
run by this work.

`scripts/formal_tools.py lint` passed with existing large-file warnings.

The remaining source problem is nonvanishing or joint survival of the
specific physical family `P*I_0+Q`, together with the actual angular
source factors in K. The base period is a half-interval finite part;
complete-beta nonvanishing does not evaluate it. A concrete next candidate
uses the physical relations `s=2*w+1` or `s=2*w+2`: the common phase then
comes from `x*(2-x)^4`, whose interior stationary point is `x=2/5`.
The corpus theorem `norm_sqrt_mul_besselPhaseIntegral_sub_le` in
`BesselJZeroConstant.lean` supplies an inspected proof mechanism for a
Fresnel main term with an explicit remainder after a quadratic change of
variables. Transferring that mechanism requires bounds for this original
subtracted source, and a range covering the physical frequencies. No
such dominance or source nonvanishing theorem is claimed here. Full
angular/action comparison, Hawking-clock extinction and RH remain open.

Broad incomplete and saddle retrieval and deep endpoint, stationary-phase
and period-nonvanishing requests inspected candidate lemmas, source
arguments and ingredient sets. First-endpoint subtraction and compact
primitive continuity supplied the endpoint proof. The last period search
completed with snapshot coverage (57,084 files, 735,656 declarations),
mostly pending compiler metadata and unmeasured semantic coverage. Its
continued-fraction and Suzuki beta candidates supply no applicable
nonvanishing theorem for this complex half-period. Earlier deep requests
returned partial auxiliary queries. Broad monodromy/holonomic searches
reached the September 2026
[line-arrangement monodromy paper](https://arxiv.org/abs/2609.06416) and
the August 2026 [multivariable monodromy paper](https://arxiv.org/abs/2608.26087).
Their abstracts were inspected; neither is used as a proof premise.

### Intermediate-height source and retained horizon contact

Two analytical conjectures now have Lean proofs: boundary recovery from
the original moments, and all-height survival of the original intrinsic
horizon contact. Both retain the prescribed endpoint subtraction.

Write `I_n=fundamentalJacobiMoment n w s`, `d=2*s-w`, and
`e=w+2*s+2`. The admitted first, second and third recurrences give

```
2*I_0 = (d^2+5*e+8)*I_2 - (e+2)*(e+3)*I_4,
(e+d^2)*(e+2)*(e+3)*I_4
  - (d^4+(6*e+8)*d^2+3*e*(e+2))*I_2 = 2*d.
```

The second identity holds whenever `Re(w)>-2` and `w+1!=0`, without
dividing by `e` or `e+1`. Its norm gives a lower bound for a weighted
sum of the two moment norms. At each of the four physical branch/side
choices, `d!=0`, so `I_2!=0` or `I_4!=0`. The mathematical work still
needed for this survivor is identification of independent retained
physical projections detecting those moments: the identity alone does
not exclude cancellation in the specified combination `A*I_2+B*I_4`.

For the actual true/true choice, set `v=w+1`, so
`-1/2<Re(v)<0`. The original endpoint polynomial is

```
E(v)=30*v^4+81*v^3+80*v^2+19*v-6=4*(A+B),
fundamentalSourceCore(w,s,a,0)=2^(2*s-w)*a^2*E(v)/4.
```

Lean proves `E(v)!=0` on the entire closed strip
`-1/2<=Re(v)<=0`, with no restriction on `Im(v)`. Put `t=-Re(v)`
and `y=Im(v)`. When `y!=0`, the imaginary zero equation gives
`(81-120*t)*y^2=19-160*t+243*t^2-120*t^3`.
The right side is at most `19-(137/2)*t`; its nonnegativity gives
`t<=1/3`, then `y^2<=1/2`. On that interval
`-180*t^2+243*t-80<=-19`. Thus the imaginary correction to the real
polynomial, `y^2*(30*y^2-180*t^2+243*t-80)`, is nonpositive,
whereas the existing real coefficient bounds give `E(-t)<=-15/4`.
The case `y=0` follows from the same real bound. The proof uses factored
polynomial inequalities and restricted `nlinarith only` inputs.

With the unchanged angular-gradient prescription
`K=reducedGreenGradient(physicalRadialFrequency(q),s,1)`, Lean identifies
the original `sourceRemainder` at the horizon with this endpoint core.
Consequently, for every physical copy and every nonzero amplitude,

```
intrinsicContact = fundamentalSourceCore(w,s,a,0)/(2*(w+1)) != 0,
incomingResponseSlope(s,a,1,K,w)
  = intrinsicContact * continuedOnset(s,w),
incomingResponseSlope(s,a,1,K,w)=0 iff continuedOnset(s,w)=0,
(eventually as b tends to 0 from above,
  incomingSourceTransport(s,chi,a,1,K,w,b)!=0)
  iff continuedOnset(s,w)!=0.
```

The last equivalence concerns the existing analytic continuation of the
original Green-quotient derivative and remains valid at the target
connection zero. Its reverse direction uses the admitted horizon limit
and the nonzero slope; its forward direction retains the exact onset
factor in the transport formula. All-height intrinsic contact
cancellation is therefore closed. The unchanged onset, identification
with the full retained physical action, and intermediate-height total
source-moment cancellation remain open. Contact survival does not by
itself prove nonvanishing of the total moment or its QNM residue.

Three leaves passed scratch checks and exact leaf audits, then were
installed with their audited artifacts and wired into the umbrella:
`ThetaCuspHawkingBMSourceEndpointPolynomial` (31 seconds),
`ThetaCuspHawkingBMFundamentalBoundaryRecovery` (9.6 seconds), and
`ThetaCuspHawkingBMPhysicalSourceContactSurvival` (269 seconds).
Each audit built only its named leaf and reported two jobs. No heartbeat
or other resource limit was raised; no umbrella build, dependency rebuild,
axiom check or mathematical computation was run. The frontier map and
universal STATUS remain unchanged.

Broad contiguous and exact OR Casoratian/Wronskian searches, followed by
deep moment-system and source-contact method requests, inspected
candidate lemmas, source arguments and ingredient sets. All four
requests returned `partial=false`; the latest snapshot covered 57,158
files and 737,205 declarations. Most compiler metadata was pending and
semantic coverage was unmeasured. Second-kind moment Wronskians suggested
boundary recovery; their positivity assumptions were not transferred to
these complex moments. The exact original recurrences supplied the
proof above.

A broad arXiv biorthogonality search reached September 2026 papers on
[radial potential-density bases](https://arxiv.org/abs/2609.04012),
[boundary control of damped beams](https://arxiv.org/abs/2609.07806), and
[non-Hermitian Hawking analogues](https://arxiv.org/abs/2609.05632).
Their abstracts were inspected. Boundary-adapted combinations and
retained modal projections are candidate mechanisms to investigate;
none of these papers supplies a proof premise here.

The next onset conjecture can be stated for the exact existing pulse
transform: `onsetPulseTransform(-lambda)!=0` at
`lambda=3-(5/2)*q`, whose real part lies in `(1/2,3)`.
The existing integration-by-parts theorem identifies this transform with
`lambda*continuedOnset(s,w)`. Broad Laguerre/Hurwitz retrieval and a
single-term `smoothTransition` search recovered the original pulse
identity, real-exponent positivity and isolated-zero theorems, but no
applicable zero-free theorem on this complex curve. A possible stronger
target is a real-zero theorem for the centered Fourier transform of the
specified transition derivative; that target is an unproved conjecture.
No adjustable onset duration or new kernel is substituted.
These two additional searches returned `partial=false` with a snapshot
covering 57,202 files; semantic coverage remained unmeasured.

The formal lint run reported one error outside these three leaves:
`GaloisForLFunctions.HTGeometry.InversePowerCancellation` was unreachable
from its theorem-area umbrella. It also reported existing large-file
warnings. No error was reported in the new HB leaves; the unrelated
module was not edited or rebuilt.

### Fixed onset on the actual overtone ladder

The current analytical attack retains the prescribed unit-duration
onset and varies only the original physical QNM overtone. The exact
formula gives `w_n=w_0-2*n`, hence
`clearedOnset(s,w_n)=onsetPulseTransform(2*s-w_0+2*n)`.
`ThetaCuspHawkingBMFixedOnsetRealTilt` proves that, for every fixed
complex `z`, this original pulse transform at `z+2*n` is nonzero for
all sufficiently large `n`. Its scratch check and exact module audit
passed with default heartbeats; the exact audit took 24 seconds.
`ThetaCuspHawkingBMFixedOnsetOvertoneSurvival` proves the physical
corollary: for every original Xi copy there is one `N` such that, for
every `n>=N` and both source-rate and QNM-side choices, the original
`clearedOnset` and `continuedOnset` are nonzero. Its scratch check and
exact module audit passed; the latter took 21 seconds. Both leaves
are installed with their audited artifacts and wired into `RHTower`.
No dependency or umbrella build, heartbeat increase, or axiom query
was used. The formal lint gate passed, with existing large-file
warnings. Integral measures and integrand forms are explicit, and
the phase estimates use restricted arithmetic hypotheses. A slow
scratch initialization was traced to import loading, before tactics;
the physical leaf imports 4,328 cached project dependencies in its
isolated audit.

The paper mechanism is endpoint concentration. Write
`p(u)=deriv Real.smoothTransition u`, so `p>=0`, its total integral is
one, and every interval ending at one has positive mass. For fixed
imaginary part, choose a terminal interval where the phase, rotated by
its endpoint value, has real part at least one half. A smaller terminal
interval gives a positive lower bound with a strictly larger exponential
rate than the entire possibly negative earlier contribution. This yields
strict positivity of a rotated real part at all sufficiently large real
tilts. It changes no onset profile, clock duration or Xi copy.

The remaining physical obligation is to establish nonzero original
radial/left-QNM coupling on a compatible high-overtone subsequence and
retain all endpoint subtractions there. Fundamental-mode contact
survival alone does not identify that higher-overtone coupling.

The current radial conjecture uses the terminating polynomial of the
original plus branch. Put `w_n=w_0-2*n`, `w_0=-3/2-I*chi`,
`t=1-z`, `A=fundamentalMomentConstant s`, and
`B=fundamentalMomentQuadratic w_0 s`. The source coefficients `A,B`
remain fixed when `n` changes. Direct substitution of the actual outer
Gauss parameters gives
`P_n(t)=₂F₁(-n,n+w_n+3/2;3/2;t)`.
The radial source density is therefore proportional to
`t^(1/2)*(1-t)^w_n*(1+sqrt(t))^(2*s-w_n)*(A+B*t)*P_n(t)`.

The verified Rodrigues identity is
`(3/2)_n*t^(1/2)*(1-t)^w_n*P_n(t)
 = D_t^n[t^(n+1/2)*(1-t)^(n+w_n)]`.
`ThetaCuspHawkingBMJacobiRodrigues` proves the general weighted derivative
and its iterated identity from the actual Gauss ODE. Its scratch check
and exact leaf audit passed (182 seconds). The proof isolates power
derivative values before polynomial normalization and uses default
resource limits. `ThetaCuspHawkingBMOvertoneSourceRodrigues` identifies
both original QNM ladders with that terminating factor and proves the
exact original source density identity, retaining the fixed angular
gradient, amplitude and arbitrary original onset factor. Its scratch
check and exact leaf audit passed (105 seconds). Both leaves are
installed with audited artifacts and wired into `RHTower`; dependency
sources and umbrella builds were excluded from the audits.

The identities hold at every interior radius. Higher-order endpoint
restoration and overtone-tail nonvanishing are not yet Lean theorems.
Neither generic polynomial completeness nor a positive moment measure
has been identified with this pairing.

### Unproved auxiliary overtone-tail survival approach

The recurrence attack keeps the original source coordinate `u=sqrt(t)`.
With `mu=(1-u)^w0*(1+u)^(2*s)`, set
`L p=(1-u^2)*p'+(2*s-w0-(w0+2*s+2)*u)*p`.
Then `(mu*(1-u^2)*p)'=mu*L p`. For `p_k=(1-u)^(-k)`,

```
L p_k=2*(k-w0-1)*p_k+(w0+2*s+2-k)*p_(k-1).
```

The cutoff integral has the upper primitive minus `1`; its canonical
finite part therefore predicts the affine pole-moment recurrence
`2*(k-w0-1)*J_k+(w0+2*s+2-k)*J_(k-1)=-1`.
The primitive's endpoint powers have nonzero imaginary exponent, so
none contributes a constant term. The missing part of this approach is
an actual overtone block recovering that nonzero boundary: an abstract
moment recurrence does not prove source-pairing survival. No such block
determinant has been established.

The alternative overtone argument sums the Rodrigues kernels. Strip only
the external amplitude and onset from the original source pairing:

```
R_n=FP integral_0^1 t^(1/2)*(1-t)^(w0-2*n)
      *(1+sqrt(t))^(2*s-w0+2*n)*(A+B*t)*P_n(t) dt,
S(lambda)=sum_n (3/2)_n/n! * R_n * lambda^n.
H(t)=t^(1/2)*(1-t)^w0, g(t)=t/(1-t).
```

For each interior t, Cauchy's coefficient formula at the nearby root
`T=t+x*g(T)` gives the local analytic identity
`sum_n x^n/n!*D^n[H*g^n](t)=H(T)/(1-x*g'(T))`.
Set `x=lambda*(1+sqrt(t))^2`. Then

```
T^2-(1+t-lambda*(1+sqrt(t))^2)*T+t=0,
Delta=(1+sqrt(t))^4*(1-lambda)*(((1-sqrt(t))/(1+sqrt(t)))^2-lambda),
H(T)/(1-x*g'(T))=sqrt(T)*(1-T)^(w0+1)/sqrt(Delta).
```

This local identity alone does not justify integrating the infinite sum
through the horizon. The proposed identification uses one fixed keyhole
contour around `u=1`, based at `u=0`. Every overtone has the same horizon
monodromy `exp(2*pi*I*w0)`, because its exponent differs by `-2*n`.
On a fixed contour away from the horizon the kernel series can be summed
uniformly. Proving its normalized contour integral equals the original
canonical finite parts is a required step, not an assumed interchange.

The exact algebraic substitution is particularly restrictive. Put
`beta=sqrt(1-lambda)` and `v=sqrt(T)`. The chosen local branch gives

```
u=v*(beta-v)/(1-beta*v),
1+u=(1-v^2)/(1-beta*v),
sqrt(Delta)=beta*(1-v^2)*du/dv.
```

The transformed generating integrand is therefore

```
F_beta(v)=(2/beta)*v^2*(beta-v)*(1-v^2)^(2*s)
           *(1-beta*v)^(w0-2*s-1)
           *[A+B*v^2*(beta-v)^2/(1-beta*v)^2].
```

The lifted contour surrounds `v=1` and `v=1/beta`, excluding `v=-1`.
An endpoint-preserving decomposition into `0..1` and `1..1/beta` periods
is the next exact identity to establish. With one consistent side of
the cuts, its second-period multiplier is predicted to be

```
kappa=exp(-2*pi*I*s)
       *(1-exp(2*pi*I*(w0-2*s-1)))/(1-exp(2*pi*I*w0)).
```

The orientation and normalization must be checked against the original
contour before this is treated as a proved physical formula.

For the original `branch=true, side=true` choice,
`s=q-2`, `w0=-s/2-2`, and direct algebra gives
`B=3*s*(s-1)*(s+2)*(5*s+8)/32`, which is nonzero because s is nonreal.
Scaling `y=beta*v` in the second period predicts the concrete limit

```
beta^(4*s+9)*S(1-beta^2)
  -> -2*kappa*B*Gamma(4*s+8)*Gamma(w0-2*s-2)
                   /Gamma(w0+2*s+6).
```

All three Gamma arguments are nonreal on this physical channel; the
two monodromy denominators/numerators are also nonzero. Thus the proposed
limit is explicitly nonzero. Moreover `0<Re(4*s+8)<4`. A polynomial S
would give limit zero, so this exact limit would directly disprove an
eventually zero source-pairing tail and meet the previously established
cofinite onset-survival tail.

The analytical estimate to prove keeps both endpoint subtractions.
After scaling, the B term tends to
`-2*B*y^(4*s+7)*(1-y)^(w0-2*s-3)`. The moving lower-endpoint contribution
is of order `beta^(4*s+8)` after normalization, and the fixed-endpoint
period is of the same vanishing order. The A term is lower order.
At `y=1`, two Taylor subtractions suffice throughout the physical strip;
at the moving `y=beta` endpoint, four suffice for the exponent `2*s`.
Uniform bounds for those subtracted remainders and the contour identity
remain to be proved. The limit, tail survival, complete retained action,
fixed-clock extinction and RH are not yet established in Lean.

Current corpus retrieval also used single-word Gegenbauer, Bürmann and
contiguous searches, broad Bernstein/Bessel, holonomic/telescoping and
finite-part searches, and deep derivative-transfer, recurrence-recovery
and Abel-jump mechanism requests. Returned candidate lemmas, source
arguments and proposed ingredient sets were inspected. Some broad and
deep requests were partial; the completed recurrence snapshots covered
57,228 files and 738,760 declarations with mostly pending compiler
metadata. The lexical contiguous search exposed the finite Pfaff and
Jacobi coefficient proofs in `SemilocalDiagonalPfaffTransformation` and
`SemilocalBoostContiguousRelations`. They do not yet supply this physical
generating period or its endpoint limit.

A broad resurgence search reached the June 2026
[Weak-Strong Resurgence Duality](https://arxiv.org/html/2606.26637v1#S8)
Mellin-transform section, which relates different asymptotic expansions
through explicit Gamma factors, and the April 2026
[Resurgence of high-energy string amplitudes](https://arxiv.org/html/2604.07444v1#S3),
whose period difference systems are obtained by integration by parts.
These supply comparison methods; no theorem from either paper has been
substituted for the required physical contour identity or uniform limit.

Broad and deep corpus searches covered Hermite–Biehler, Lee–Yang,
Sturm, oscillation, overtones, endpoint concentration, Rodrigues,
moment recurrences, Mellin subtraction and contiguity. Candidate
statements and source arguments were checked for matching premises.
The moment-tail request was partial (unfinished asymptotic query and
reranking); the later subtraction and contiguity requests completed.
The latter snapshots covered 57,213 files and 738,617 declarations,
with most compiler records pending. Suggested ingredient sets remain
unverified. In particular, the Hurwitz order-independence proof and
the BM Gauss coefficient coboundaries supply methods, not the missing
physical endpoint or coupling theorem.

### Monotone-phase source survival

The source-survival proof uses the actual `branch=true, side=true`
choice: `w=-1-q/2`, `s=q-2=-2*w-4`, hence `-3/2<Re(w)<-1`.
The original polynomial moments become

```
I_n = FP integral_0^1 [x/(2-x)^4]^w * (1-x)^n/(2-x)^8 dx.
phi=x/(2-x)^4, p=phi/phi'=x*(2-x)/(2+3*x).
T f=(p*f)'-f
   =x*((2-x)/(2+3*x)*f'-4*(4+3*x)/(2+3*x)^2*f).
```

The proved integration-by-parts identity keeps the original endpoint
subtraction and has a remainder with an explicit factor x:
`(w+1)J(f)=f(1)/5-J(T f)`. On the physical strip, the remainder is
uniformly integrable against `x^(-1/2)`. For
`f_n=(1-x)^n/(2-x)^8`, the first n upper endpoint terms vanish, and
`T^n f_n(1)=(-1)^n*n!/5^n`. This gives

```
(w+1)^(n+1)*I_n = n!/5^(n+1) + O(1/abs(w+1)).
```

With `v=w+1`, exact source coefficients simplify to
`A=5*v^2+(5/2)*v-3/2` and
`B=(15/2)*v^4+(81/4)*v^3+15*v^2+(9/4)*v`.
For unit amplitude, the complete source now has a Lean-proved bound
`norm(v*(v*M-172/625)) <= K`, with one nonnegative K uniform on the strip
when `norm(v)>=1`. The exact physical identification retains the original
endpoint subtraction. The installed source-survival theorem proves

```
exists H>0, forall q:XiZeroCopy, H<=abs(Im(q)) -> forall a:Complex,
  (86/625)*norm(a)^2 <= norm((w+1)*fundamentalSourceMoment(w,s,a)).
```

Consequently every nonzero original amplitude has a nonzero source moment
in this channel above H. The proof chooses
`H=2*(1+2*K/(172/625))`; no numerical evaluation is needed. Bounded-height survival,
angular factors and affine Xi collisions, fixed onset survival, the full
retained action and Hawking-clock extinction remain open; RH is unproved.

To avoid expanding high rational derivatives, the exact weights
are `T^j f_n=P_j(x)/((2-x)^8*(2+3*x)^(2*j))`, with

```
P_0=(1-X)^n,
P_(j+1)=X*((2-X)*(2+3*X)*P_j' +(6*(j+2)*X-12*j)*P_j).
```

Every positive-order numerator has the required factor X. Seven new leaves
are installed and wired after scratch checks and exact leaf audits:
`ThetaCuspHawkingBMNonstationaryWeight` (60 seconds),
`ThetaCuspHawkingBMNonstationaryMoment` (22 seconds),
`ThetaCuspHawkingBMNonstationaryIntegrationByParts` (24 seconds), and
`ThetaCuspHawkingBMNonstationaryPolynomial` (7 seconds),
`ThetaCuspHawkingBMNonstationaryAsymptotic` (31 seconds),
`ThetaCuspHawkingBMPhysicalNonstationarySource` (143 seconds), and
`ThetaCuspHawkingBMFundamentalSourceSurvival` (18 seconds). They prove the
rational derivative recurrence, original finite-part recurrence, uniform
remainder admission and bound, exact upper endpoint coefficients, uniform
leading-term error bounds, identification with the original source, and
the uniform high-height lower bound and nonvanishing theorem.
The first isolated audit visited cached dependency jobs and printed one
built module; subsequent audits reported two jobs each. No umbrella or
full build was run. No heartbeat or other resource limit was raised.
No axiom checks or mathematical computations were run. The frontier map
and universal STATUS remain unchanged.

Formal lint passed with existing large-file warnings after restoring the
missing umbrella import for the already compiled
`ThetaCuspHawkingBMScalarJetQuadraticEinstein`. Its source was unchanged;
no re-audit or umbrella build was run.

Broad Wronskian retrieval and deep Stieltjes and endpoint-asymptotic
requests inspected candidate lemmas, source arguments, proof ideas and
ingredient sets. The finite-interval integration-by-parts mechanism led
to the retained-boundary recurrence above. The later inverse-density
request returned partial results with reranking unfinished; snapshot
coverage was 57,113 files and 735,918 declarations, mostly pending compiler
metadata and unmeasured semantic coverage. Exact phrase retrieval for
"Lagrange inversion" found no hits. Broad Pick/univalence arXiv searches
reached July 2026 papers on
[harmonic-map Landau bounds](https://arxiv.org/abs/2607.04377) and
[directed univalence](https://arxiv.org/abs/2607.02420); their abstracts
were inspected and neither is used as a premise.

For the remaining bounded-height problem, an analytical candidate moves
the frequency polynomials onto one density. In the phase coordinate
`z=x/(2-x)^4`, set

```
rho_n(z)=(1-x(z))^n/((2-x(z))^3*(2+3*x(z))),
theta=z*d/dz,
R=(5*theta^2-(5/2)*theta-3/2)rho_2
  +((15/2)*theta^4-(81/4)*theta^3+15*theta^2-(9/4)*theta)rho_4.
```

The endpoint values are `R(0)=-3/32` and `R(1)=86/625`.
The phase-coordinate form of the reduction is
`v*M/(2*a^2)=86/625-integral_0^1 z^v*R'(z) dz` for nonzero a.
It follows on paper by retaining the phase-change counterterm and using
the second/fourth endpoint vanishing when moving the polynomials across
the Mellin integral. The equivalent fixed-weight reduction in the original
x coordinate is now formalised below; no inverse phase coordinate is
needed in Lean. The global target is excluding the value `86/625` from that
integral for `-1/2<Re(v)<0`, `Im(v)!=0`; no density sign or Stieltjes
representation is assumed. The deep inverse-density search returned
Lagrange interpolation rather than inversion candidates, so it supplies
no proof of this target.

The current analytical attack removes every frequency polynomial before
applying a nonvanishing argument. Write `P_nk=nonstationaryPolynomial n k`
and `D=2+3*X`, and define the single fixed polynomial

```
N=5*D^4*P_22-(5/2)*D^6*P_21-(3/2)*D^8*P_20
  +(15/2)*P_44-(81/4)*D^2*P_43+15*D^4*P_42-(9/4)*D^6*P_41.
```

The identities `M=2*a^2*J(W(N,8))` and
`v*M=2*a^2*(86/625-Dsource(w))` now pass Lean for the original physical
source, where `Dsource(w)=J(W(Step(N,8),10))`. The last pairing is an
ordinary absolutely convergent integral for `Re(w)>-2`, with one
frequency-independent rational weight. The fixed polynomial satisfies
`N(0)=-384`, `N(1)=268750`, and `W(N,8,1)/5=86/625`.
The exact endpoint identity is `Dsource(-1)=86/625+3/32`.
One common `x^(-1/2)` majorant proves continuity of Dsource on the closed
physical strip, including its subtracted-pole endpoint.

### Complete-source real coercivity and a uniform complex band

Transferring the frequency polynomials gives the fixed-weight reduction
above, but a sign for its single density has not been established.
The successful positive replacement compares the admitted second and
fourth remainder kernels. For real `-3/2<=u<=-1`, put

```
kappa=x^u*(2-x)^(-4*u),
g2=x*(1-x)*(8-4*x+6*x^2)/((2-x)^8*(2+3*x)^2),
g4=4*x*(1-x)^3*(4+x)/((2-x)^8*(2+3*x)^2),
U2=integral_0^1 kappa*g2, U4=integral_0^1 kappa*g4.
```

Both integrals are admitted for every `u>-2`. Lean proves `U2>0` and
`0<=U4<=2*U2`; the comparison follows from the positive numerator
`4*x^2*(1-x)*(5+x-x^2)` of `2*g2-g4`. For the complete source
coefficients, Lean proves `A<=-3/2`, `B<=9/16`, hence

```
A*U2+B*U4 <= -(3/8)*U2 < 0.
```

The coefficient proof factors B as
`(3/4)*t*(1-t)*(5*t-1)*(3-2*t)`, with `t=-(u+1)` in `[0,1/2]`.
The original endpoint recurrence identifies this combination with
`(u+1)*J(W(N,8))` for `u<-1`. Consequently
`Re(Dsource(u))>86/625` throughout the closed real interval; the exact
endpoint value handles `u=-1` separately.

Applying the corpus's `CompactPatchGenericity` theorem to this strict gap
and the admitted integral's continuity gives a Lean-proved `delta>0`:

```
-3/2<=Re(w)<=-1, abs(Im(w))<=delta  ->  Dsource(w)!=86/625.
```

The physical identification uses `w=-1-q/2` and proves

```
exists h>0, forall q:XiZeroCopy, abs(Im(q))<=h -> forall a:Complex,
  a!=0 -> fundamentalSourceMoment(w,physicalRate(q,true),a)!=0.
```

Here `h=2*delta`. Together with the existing high-height source theorem,
this supplies uniform low-height and high-height survival ranges. No
comparison making these ranges cover all heights has been proved.
Intermediate-height cancellation, the full angular/retained-action
identification, fixed onset survival, Hawking-clock extinction and RH
remain open. Ordinary polynomial-moment completeness still lacks an
identification with the actual higher-QNM pairings.

The proof uses factored weight recurrences and separate algebra,
integrability, coercivity and compactness leaves. No heartbeat or other
resource limit was raised. All seven new leaves passed scratch checks
and exact audits, and are installed with audited artifacts and wired:
`ThetaCuspHawkingBMNonstationaryMomentAlgebra` (37 seconds),
`ThetaCuspHawkingBMFixedSourcePolynomial` (127 seconds),
`ThetaCuspHawkingBMRealSourceWeights` (40 seconds),
`ThetaCuspHawkingBMFixedSourceDefect` (52 seconds),
`ThetaCuspHawkingBMRealSourceCoercivity` (71 seconds),
`ThetaCuspHawkingBMSourceRealBand` (17 seconds), and
`ThetaCuspHawkingBMPhysicalFixedSource` (23 seconds).
Only the requested leaf was reported built in each audit; the defect
audit visited cached dependency jobs, while the others reported two jobs.
No full or umbrella build, axiom check, or mathematical computation ran.
The frontier map and universal STATUS remain unchanged.

The final lint run reports no error for the seven new leaves. It still
reports unreachable concurrently added modules `MaassCircleKernel`,
`MaassCircleTransfer`, and `CompactSmoothParameterIntegral`, alongside
existing large-file warnings. Missing imports for the already compiled
`ThetaCuspHawkingBMScalarJetEntries`, `SmoothCylinderKernel`, and
`SmoothCylinderIntegral` were restored without changing their sources or
rebuilding them. No umbrella build was run.

Broad Hurwitz, contiguous and overtone retrieval and deep density,
completeness, Xi-height, compactness and moment-ratio searches inspected
candidate lemmas, source arguments and proposed ingredient sets.
`CompactPatchGenericity` supplied the applicable uniform-band mechanism.
The final moment-ratio request completed with snapshot coverage of
57,137 files and 736,578 declarations; compiler metadata remains mostly
pending and semantic coverage unmeasured. Its proposed differential-adjoin
ingredient set concerns field generation, not a differential adjoint
identity. The inspected `PositiveSourceQuadraticStability` theorem requires
a transverse sector inequality; that inequality has not been established
for this original source, so it supplies no middle-band conclusion yet.
Broad passivity and total-positivity arXiv retrieval reached the July 2026
[impedance-passive stability paper](https://arxiv.org/abs/2607.01861) and
August 2026 [reciprocity paper](https://arxiv.org/abs/2608.30778).
Their abstracts were inspected; neither is used as a proof premise.

## Original action cyclicity with its boundary divergence

**Status:** paper proof closed; both leaves passed scratch Lean and exact
leaf audits with default limits. Only the new geometry leaf (84 seconds)
and new physical leaf (65 seconds) were built; dependencies were reused
from cache. Both are wired into their umbrellas; no umbrella build ran.
The formal lint gate passed; it reported existing large-file warnings.

Formal statements:
- `HTGeometry/CoordinateEinsteinCyclicAction.lean`:
  `paired_cyclicity_defect`, `cubicAction_eq_density_third`,
  `cubicAction_cyclic` in `HTGeometry.EinsteinCyclicVariation`.
- `RHTower/ThetaCuspHawkingBMCyclicActionBoundary.lean`:
  `metricFamily_jet`, `physical_cubicAction_cyclic`,
  `physical_cubicAction_eq_density_third` in `RHTower.D4BMCyclicAction`.
  The physical theorems have no supplied regularity, symmetry,
  nondegeneracy, field-equation or boundary-cancellation premises.

For the complete metric jets put `G(a)=J+sum_k a_k U_k` in jet
coordinates, `w(a)=exp(log(det(G(a))/det(J))/2)`, and

```
L(a)   = w(a) * (R(G(a))-2 Lambda)
P_k(a) = w(a) * sum_ij (G(a)^(-1) U_k G(a)^(-T))_ij
                         * (Einstein(G(a))+Lambda G(a))_ij
D_k(a) = w(a) * EinsteinActionBoundary.divergence(G(a),U_k).
```

The original Einstein--Hilbert first variation gives
`partial_k L=-P_k+D_k` near zero. Nondegeneracy puts the determinant
ratio near `1` in one fixed logarithm branch. Rational curvature and
this density are smooth there. Differentiating twice and commuting
mixed derivatives proves

```
partial_i partial_j P_k - partial_i partial_k P_j
  = partial_i partial_j D_k - partial_i partial_k D_j,
C_ijk := partial_i partial_j P_k - partial_i partial_j D_k
       = -partial_i partial_j partial_k L.
```

All values here are at zero. Consequently `C_ijk=C_ikj`; the retained
action has cubic symmetry without assuming a vanishing boundary flux.
This is a positive identity from the original action, not a proof that
the bulk source alone has the required cyclic pairing. No route is
retired by this result.

For the physical specialization, `J` is the actual BM background jet and
`U_k` is the actual complete spatial jet of
`physicalPerturbation(q_k,b_k,aS_k,aV_k)`. All three Xi occurrences,
branches, and scalar/vector amplitudes are independent. Background
nondegeneracy follows from the explicit exterior metric; symmetry of
every mode and its first derivatives follows from the original
covariant metric expression. The actual metric family is formed
before spatial differentiation; its field-to-jet identity retains
every ordered second coordinate derivative.

**Consequences for the full proof chain:** this supplies a local
variational identity for the retained source, before projection onto
radial or left-QNM channels. It does not yet supply the abstract
Peierls receiver's `hcyclic`: that receiver needs one common source
map, pairing and causal propagator, including sourced response fields.
Identifying the second variation of `P` with a frozen pairing of the
quadratic residual still requires discharging the background and
linearized residual terms. Integrating `D` requires the original
volume measure, all boundary components and the common-cutoff limit.
The formal divergence has not been replaced by a bare radial endpoint.

Two closing possibilities remain in view. If the complete physical
incidence equals the original normalized BM candidate, the existing
source-reflection/Peierls receiver can force the critical line. If the
boundary contribution survives in that incidence, its value also
belongs in the proposed fixed-clock observable; extinction must be
proved for that same observable. Neither incidence identification,
causal reciprocity, channel nonvanishing, extinction nor RH is proved
by the local cubic identity.

Broad/deep/method corpus retrieval found the original EH variation and
actual Einstein Hessian symmetry. Some deep requests returned partial
coverage; source statements were inspected and candidate use was
checked in Lean. Broad arXiv searches for `variational` and
`transgression` found [Monroy, arXiv:2606.08659](https://arxiv.org/abs/2606.08659)
and [Bildhauer--Fuchs, arXiv:2608.01105](https://arxiv.org/abs/2608.01105).
Their abstracts did not provide the missing gravitational pairing or
extinction theorem; no mathematical claim from them enters the proof.

## Original on-shell quadratic pairing and boundary assembly

**Status:** both geometric and physical source reductions are paper-proved,
scratch-checked and leaf-audited with default Lean limits. Exact audits built
only the new geometry leaf (13 seconds) and physical leaf (54 seconds),
reusing cached dependencies. Both umbrella imports are wired; no umbrella
build ran. Formal lint passed with existing large-file warnings. RH and
global physical incidence remain open.

For the same complete family `G(a)`, let `E_rs(a)` be its original
cosmological Einstein residual and let `W_k,rs(a)` be its original
volume-weighted raised test coefficient. The exact derivative identities are

```
partial_k E_rs(a) = DEinstein_rs(G(a))[U_k] + Lambda*(U_k)_rs,
partial_i partial_j E_rs(0) = D²Einstein_rs(J)[U_i,U_j],
partial_i partial_j sum_rs W_k,rs(a)*E_rs(a) at 0
  = sum_rs W_k,rs(0)*D²Einstein_rs(J)[U_i,U_j]
```

when the actual background residual and first residuals vanish. The proof
retains all four Leibniz terms. The extra three terms vanish because they
multiply `E(0)`, `partial_i E(0)` or `partial_j E(0)`, rather than because
the volume or inverse metric is held constant during variation. The
cosmological term contributes at first order and vanishes at second order
because the metric family is affine.

`HTGeometry/CoordinateEinsteinOnShellPairing.lean` contains
`residual_first`, `residual_second` and `bulk_second_eq_hessian` in
`HTGeometry.EinsteinOnShellPairing`. Its scalar product lemma records the
precise residual conditions that permit freezing a varying coefficient.
The geometric statement applies to arbitrary complete jet directions;
it does not restrict future source, test or response directions to one
angular parameter.

The concrete application uses the actual BM vacuum and the previously
proved full physical mode equations to discharge every residual premise.
The source convention matters: the original quadratic Taylor source is
one half the Einstein Hessian. Thus, writing `B_ijk` for its paired
coefficient, the target identity is

```
B_ijk - B_ikj
  = (partial_i partial_j D_k - partial_i partial_k D_j)/2.
```

The diagonal is also compared with the actual field-source coefficient
`iteratedDeriv 2 (D4BMActualMetricSource.source ...) 0 / 2`, fixing this
normalization independently. This Taylor factor is distinct from a
causal half-jump convention.

`RHTower/ThetaCuspHawkingBMOnShellCyclicSource.lean` proves
`physical_bulk_second_eq_hessian`,
`quadraticPairing_diag_eq_sourceCoefficient`,
`physical_quadratic_cyclicity_defect` and
`physical_quadratic_with_boundary_cyclic` in
`RHTower.D4BMOnShellCyclicSource`. These physical statements supply their
own background and linearized equation proofs, using three independent
Xi occurrences, branches and scalar/vector amplitudes.

For the causal construction, a forced response is not itself covered by
the homogeneous first-residual condition. The needed producer is the
original homogeneous equation for the retarded--advanced difference,
with the same full source and every contact retained. Terms involving a
first residual must remain until that producer is proved; the on-shell
identity is not permission to discard them on each forced branch.

The concrete hard producer is a pair of full metric corrections satisfying
the original component equations `L(k_ret)=L(k_adv)=-B(h,h)`, including
the source contacts and all independent scalar/vector channels. A solved
projected scalar wave equation alone does not establish those equations.
Their proved common source would give `L(k_ret-k_adv)=0`, placing the
actual causal difference within the reduction above. The scalar-stream
master-row identities are ingredients for constructing that producer,
not a substitute for constructing the corrections.

**Boundary assembly and whole-chain consequences:** broad Green and
method searches found exact paired modular side/arc cancellation in
`ThetaCuspHawkingBMEisensteinActualGreenBoundaryCancellation.lean`. Its
parameters explicitly require `Re(s)>1`; it is not yet a producer for
the physical Xi parameters. A continuation or direct full-field
identification must be proved before using that cancellation.

A different, physically specialized result is available in
`ThetaCuspHawkingBMQuarticTestedNativeCurrent.lean`: the full scalar-tested
centered response current has zero upper trace under every complex height
power. Its exact improper integral retains the negative lower current.
The candidate assembly therefore keeps the original lower endpoint,
mean terms and contacts while comparing the tested native current with
the Einstein boundary quantity above. Neither scalar identity alone
identifies the full nine-channel action, its physical left reader, or
the causal inverse.

The next decisive test is equality with the original global
causal/left-QNM pairing, with those terms retained on one common cut.
A surviving boundary term changes both the candidate incidence and the
observable whose fixed-clock extinction is required. Source reflection,
local cubic symmetry and local Hessian reduction do not imply that
incidence or extinction.

Broad arXiv searches for `corner`, `interface`, `gluing` and `cobordism`
were also used. The August papers
[Jia--Tan, arXiv:2608.05071](https://arxiv.org/abs/2608.05071) and
[Bais--Kjuchukova, arXiv:2608.07788](https://arxiv.org/abs/2608.07788)
concern boundary-defect algebras and branched-cover cobordism respectively.
Their inspected abstracts supply no theorem about this Einstein pairing;
no claim from them is used in the formal proof. Corpus deep requests
returned partial coverage; applicable source statements and method
arguments were inspected and their uses checked in Lean.

### Sourced scalar-stream reconstruction

The current target is a converse to the original master-row identity:
recover full metric amplitudes from a sourced master solution and prove
every original Einstein row, before imposing retarded/advanced domains.
Writing `f=r²−1`, the code's master is
`M=r F0/f−f F1/s−rf F2+4rH`. Its `F1` term has no extra factor `r`.
For original row values `T=E_TF`, `B=E_TR`, `D=E_T`, direct elimination gives

```
(2−μ)H = fD/s +(μ/2−f)T−frT' +fM'/2 +frB/(2s)−μM/(4r).
```

The formal first derivative `H'` is recovered by differentiating this
expression with all source derivatives retained. The other values are

```
F1 = s(4rH+2rT−M)/f
F2 = rB/(2sf)+μF1/(4srf)−2H/f²+2rH'/f
F0 = f²F2+2fT.
```

These identities and all three original harmonic Bianchi row identities
are formalized in `ThetaCuspHawkingBMScalarStreamReconstruction.lean`
and have passed the isolated leaf audit. The angular convention is
the **trace-free** Hessian: its divergence coefficient is `μ/2−1`, and
its angular trace is zero. For residual rows
`A=TT, B=TR, C=RR, D=T, E=R, F=TF, G=L`, the exact defects are

```
Wt = fB' +(4r−2/r)B−2sA/f+μD/r²
Wa = fE' +(4r−2/r)E−2sD/f+((μ/2−1)F+G)/r²
Wr = fC' +(5r−2/r)C−2sB/f+rA/f²+μE/r²−2G/r³.
Q  = 2rC+4E
Q' = 2C+2rC'+4E'

(μ−2)(E+F/r)/r²
  = Wr+2Wa/r−fQ'/(2r)−(2−1/(2r²))Q−rA/f²+2sB/f+4sD/(rf).
```

The last identity is verified without a compatibility premise. If the
three defects, `B,B',D,F,Q,Q'` vanish and `s,r,f,μ−2` are nonzero,
the verified conclusion is `A=C=E=0` and `G=−r²fE'`. A pointwise claim
that `G=0` would be too strong: a value `E=0` does not force its separate
first-jet slot to vanish. The positive replacement is exact: once these
relations hold for genuine differentiable residual functions on a
neighborhood, `E` vanishes there, hence `E'=G=0`. This differential
closure must be constructed for the original forced source.

The parameter `μ` here is the angular eigenvalue of `Delta`, not the
shifted physical angular resolvent parameter. The latter's proved
nonrealness cannot discharge `μ≠2` for a general source. A broader
construction replaces division by `2−μ` with the actual modular form
of `2−Delta`: on the existing value-plus-gradient energy domain, its
bounded form operator is `I+J*J`, where `J` is the original embedding
into modular L². Its form is the sum of both gradient terms plus twice
the scalar mass. The corpus coercive-operator inverse theorem supplies
the full-domain inverse. The concrete application in
`ThetaCuspHawkingBMAngularReconstruction.lean` has passed its foreground
scratch check and isolated final leaf audit: for every modular L² forcing `F`,
there is exactly one `h` in the original energy domain such that

```
sum_i <D_i v,D_i h> + 2<Jv,Jh> = <Jv,F>     for every energy test v,
||h||_energy <= ||F||_L2 / 2.
```

The estimate controls both gradient components and scalar mass. It
follows from `||h||²+||Jh||² <= ||Jh|| ||F||`, retaining all terms,
and supplies quantitative control for differentiating the reconstructed
response once the original forcing is admitted.

The joint next conjecture is to extend the literal residual identity
from a separated angular harmonic to the original angular scalar
potentials, replacing `μ−2` by `Delta−2`. The newly constructed inverse
then eliminates that residual in the actual energy domain without a
spectral-expansion premise. Its principal cusp part requires a separate
exact reconstruction. The nonreal physical resolvent theorem and the
existing native-response cusp-flux reconstruction have different
parameters and do not by themselves establish this extension.

**Whole-chain consequence:** reconstruction now has explicit source
terms and a precise completeness test. The two attacks, radial
elimination and modular coercivity, address different parts of the
same full metric producer. Still required are genuine derivative
realization, compatibility of the original quadratic source in all
channels, admission of the reconstruction forcing with every cusp
principal part and cutoff contact, and the common causal boundary
domain. Only those producers can place the actual causal difference
in the earlier on-shell cyclic pairing. Its global left reader,
nonzero coupling and fixed-clock extinction remain open; the local
identities alone establish none of those conclusions.

**Formal verification:** both new leaves passed `lake env lean` scratch
checks and their exact `lake build` audits at default limits. Each audit
built only its new Lean leaf (plus configuration), using cached
dependencies. Both are wired into the RHTower umbrella; no umbrella or
full build was run. The frontier map and universal-law ledger are
unchanged, since these new statements concern this route's reconstruction.
The formal lint gate passed, with existing large-file warnings.

### Original source compatibility by contraction

The next target is conservation of the original full quadratic Einstein
source, needed to discharge the reconstruction's Bianchi conditions in
every channel. The existing actual metric Bianchi identity is uncontracted.
The contraction is now formalized using the metric and inverse
compatibility identities. Commuting two actual metric derivatives gives
`R_ij.transpose * g + g * R_ij = 0` for the original connection's
curvature matrices. Together with their proved alternation in `i,j`, this
provides the two skew symmetries needed for the contraction, without
requiring a separate general pair-exchange theorem first.

The contracted expression has been identified with the literal covariant
divergence of the original cosmological Einstein tensor, including actual
spatial derivatives through a neighborhood identity. The next step is
to differentiate twice in amplitude. The proved background and first-order
equations remove lower-order coefficient terms; the original quadratic
source and its spatial derivatives remain. This conservation producer,
combined with genuine radial derivative realization and full angular
source admission, is intended to connect reconstruction to the common
retarded/advanced metric equations. It does not itself supply the causal
boundary domain, the global left reader or fixed-clock extinction.

For the contraction, write `T k i j u v = (nabla_k R_ij)^u_v`, retaining
connection action on both curvature-form slots. The proved algebraic
step uses `T k i j = -T k j i`, symmetric `gInv`, and
`T k i j * gInv + gInv * (T k i j).transpose = 0`.
Let `P k v j = sum_u T k u j u v`. Contracting differential Bianchi with
`gInv b k`, then using these skew identities, gives

```
2 * sum_(k,b) gInv b k * P k b j
  = sum_(b,k) gInv b k * P j b k.
```

The right side is proved equal to the actual scalar-curvature derivative;
the left side is twice the actual Ricci divergence. The inverse metric
is differentiated in this identification. Metric compatibility also
supplies the cosmological metric term's zero divergence. For the derivative-level skew law, differentiate
`R.transpose*g+g*R=0` on a genuine neighborhood. Substituting
`g'=A.transpose*g+g*A` shows that `R'+A*R-R*A` is again metric-skew;
the remaining connection actions are scalar combinations of metric-skew
curvature matrices. All these steps pass Lean in the new leaf modules
`ComplexMetricCurvatureSymmetry`, `ComplexMetricCovariantCurvature`,
`ComplexMetricBianchiContraction`, `ComplexMetricContractedDerivative`,
and `ComplexMetricEinsteinConservation`. Their exact leaf audits passed;
only new leaves were built, with cached dependencies. The geometry umbrella
imports them without an umbrella build.


#### Consequence for the whole proof chain

The original full Einstein source has a proved local conservation producer.
This moves source compatibility upstream of scalar/vector/tensor separation:
the retained source must inherit it through the actual coefficient extraction,
and reconstruction must preserve it. It does not produce a retarded or advanced
inverse, common boundary domain, nonzero left-QNM coupling, or fixed-clock
extinction. The previously proved cyclic action identity leaves its original
boundary defect explicit. Those boundary terms must remain attached when the
conserved source is used in the causal action; dropping them would lose the
connection to the later extinction problem.

The next conjecture is conservation of the original quadratic source under the
background covariant derivative. Write `E(e,x)` for the original full source
and `D(e)` for its metric-dependent divergence. The new theorem gives
`D(e)E(e)=0` on a genuine amplitude neighborhood. The existing physical
background and first-order equations give `E(0)=0` and `E_e(0)=0` on the
exterior. Twice differentiating, including every operator coefficient, gives
`D(0)E_ee(0)=0`: terms involving `D_e` and `D_ee` multiply those vanishing
lower-order fields. Spatial derivatives of the zero fields also vanish locally.

The unclosed Lean identification is the full mixed spatial/amplitude
interchange and its physical field-jet specialization. The spatial side
is now proved for actual real jet paths. For complete jet fields `q(x), p(x)` and Einstein component `F`, the
spatial derivative of the Hessian is

```
∂x [F''(q)[p,p]]
  = F'''(q)[q_x,p,p] + F''(q)[p_x,p] + F''(q)[p,p_x].
```

The second amplitude derivative of
`F'(q+e*p)[q_x+e*p_x]` gives the same expression, using the corpus's proved
`thirdVariation_symm_left`, `thirdVariation_symm_right` and
`secondVariation_symm`. Real-coordinate differentiation must be connected to
these complex derivatives by restriction of scalars and actual field-jet
regularity; a supplied derivative array is insufficient. Corpus search also
found the Fokas–Lenells mixed-derivative workflow: identify each iterated actual
derivative with its produced expression before comparing them. Its scattering
operators are different, so only that proof mechanism transfers here.

Analytical status: the coefficient argument above is derived from the proved
full identity and existing Hessian symmetry. Formal status: the full identity
is proved; the quadratic coefficient's spatial/amplitude interchange and its
physical specialization still need Lean closure. This remaining work is
necessary before claiming that reconstruction's quadratic Bianchi defects
have been discharged.

The full identity is also specialized to the actual literal theta-cusp field
in `RHTower/ThetaCuspHawkingBMLiteralConservation.lean`.
`sourceField_apply` identifies every exterior component with the existing
`D4BMActualMetricSource.source`. The theorem
`literal_source_conservation_near_zero` supplies conservation on an actual
complex amplitude neighborhood, with regularity, symmetry and nondegeneracy
proved from the literal field and background. Its scratch check and isolated
exact leaf audit passed (new leaf only, cached dependencies); the RHTower
umbrella is wired without building it. This is full nonlinear source
conservation, not yet the separate quadratic coefficient conservation theorem.


The spatial Hessian identity is formalized in
`HTGeometry/CoordinateEinsteinQuadraticSpatialDerivative.lean`.
`secondVariation_hasDerivAt_real` differentiates the original Einstein Hessian
along actual real jet paths, retaining all three terms.
`secondVariation_hasDerivAt_real_symmetric` uses the proved second/third
variation symmetries to give
`F'''(q)[p,p,q_x] + 2*F''(q)[p,p_x]`, the expression needed for the amplitude
comparison. These statements require the actual path derivatives; the next
specialization must produce them from the physical field's complete spatial
jets. Both the scratch check and exact leaf audit passed at the default
heartbeat limit; only the new leaf was built, with cached dependencies.

The remaining conservation target is still the background covariant divergence
of the original quadratic source. The real Hessian derivative theorem closes
one side of the mixed-derivative comparison. The amplitude side, actual
spatial-jet realization, and cancellation using the physical zero/first-order
equations must be connected before this target is declared closed. Even after
that closure, source conservation alone will not establish global causal
solvability or left-QNM incidence. Those questions must be tested against the
same retained boundary/contact functional that survives in the original
cyclic action and would have to enter fixed-clock extinction.

Validation: all seven new leaf modules passed scratch checks and isolated exact
leaf audits. `scripts/formal_tools.py lint` passed; it reported existing large-file
warnings. Both umbrellas are wired but were not built. No mathematical computations,
axiom-printing, heartbeat increases, frontier-map edits or STATUS edits were used.

All owned scratch/search/log/staging paths for this turn were removed after
validation. All owned Lean/Lake and search processes completed; none were left
running. Other agents' temporary files and processes were left untouched.

### Quadratic conservation: actual derivative interchange

Current conjecture: the original physical quadratic source has zero background
covariant divergence. The full nonlinear conservation theorem and real Hessian
path derivative are proved. The next producer must identify actual spatial
jet paths, compare the amplitude derivative of the full spatial Einstein
variation, and cancel the lower-order fields on an exterior neighborhood.

The corpus's `ScalarJetSpatial3ConnectionTable` uses coordinate index `3`, not
third-order regularity; it cannot supply the required third spatial jet.
`EisensteinActualThirdJet` concerns the actual Eisenstein Poincare field in its
convergence chamber, rather than the literal scalar/vector metric here. The
literal metric's already proved all-order exterior regularity provides the
proper starting point: differentiate its complete two-jet along the actual
real coordinate line, retaining ordered derivatives in every slot. Boundary
and contact currents remain attached to the later causal and left-QNM action.

The amplitude side is now proved in
`HTGeometry/CoordinateEinsteinAffineSpatialVariation.lean`:
`affineSpatialEinstein_second` differentiates the original spatial Einstein
variation `F'(q+e*p)[qx+e*px]` twice and gives
`F'''(q)[p,p,qx]+2*F''(q)[p,px]`. Both varying factors are retained;
nondegeneracy is used on a genuine amplitude neighborhood. Scratch checking
and the isolated exact new-leaf audit passed at default heartbeats, with
cached dependencies. Its umbrella import is wired without an umbrella build.

A broad `transgression` paper search found Anghel,
[AKSZ Descent on Manifolds with Ordinary Corners](https://arxiv.org/abs/2608.02928)
(August 2026). The paper organizes defects using signed incidences of boundary
faces under explicit mapping-space hypotheses. No AKSZ or gravity reduction
hypothesis has been supplied for HB. The proposed transfer is only a method:
assemble the actual finite radial, temporal and cusp faces together with shared
corner/contact terms before taking their respective limits. The claimed HB
cancellation or extinction is not a consequence of that paper.

The actual-field side is now verified in `ComplexMetricJetDerivative`:
`jetSpace_coordinateLine_hasDerivAt` produces the derivative of every ordered
slot from C3 field regularity, and `jetSpacePartial_add_smul` proves affine
variation of that genuine spatial derivative. `ComplexMetricMixedEinsteinDerivative`
then proves `einstein_mixed_derivatives`: the two amplitude derivatives of the
actual spatial Einstein field equal the actual spatial derivative of its Hessian.
`ComplexMetricEinsteinSourceVariation` retains the cosmological term and proves
actual first and second amplitude coefficients, amplitude regularity, and the
spatial derivative of the first variation. All three new leaves passed scratch
checks and isolated exact leaf audits (15s, 12s, 29s respectively); their umbrella
imports are wired without umbrella builds.

Whole-chain consequence: these results make coefficient conservation derivable
from the original field identity, instead of adding a divergence assumption to
a projected source. The remaining coefficient step is to use the original zero
and first-order equations on a spatial neighborhood and contract the resulting
second coefficient with the background connection and inverse metric. This does
not yet supply the full causal inverse, common boundary domain, physical left-mode
incidence, or fixed-clock extinction. The same original boundary/contact defect
continues to constrain all those later steps.

Broad/deep searches for matrix smoothness found a public real-matrix inverse
lemma, while the needed complex local inverse lemmas in the metric modules are
private. Searches for `Peano` and then `Taylor remainder` found the exact
`AnalyticSlopeFactor.eq_taylor_two_add_sq_mul` decomposition. It exposes a useful
stronger possibility: after the source's first two coefficients vanish, dividing
out amplitude squared can extract conservation using only continuity of the
metric weights. This is an alternative analytical proof mechanism, not a proved
HB specialization or a new extinction claim. The current finite Leibniz argument
already has the stronger regularity available and remains the direct closure.

`ComplexMetricEinsteinSpatialSource` now proves actual spatial-source amplitude
regularity and identifies its first and second amplitude derivatives with the
spatial derivatives of the original linear source and Einstein Hessian. Its
scratch check and exact leaf audit passed; the audit built only this new leaf
(9.1s), with existing dependencies cached.

`ComplexMetricQuadraticConservation.hessian_conservation` is now proved and
leaf-audited (11s). For actual C3 symmetric complex metric and perturbation
fields, background nondegeneracy, and the original background and linearized
equations on a spatial neighborhood, it produces zero background covariant
divergence of the full Einstein Hessian. The proof derives the actual inverse
metric and connection's amplitude regularity, expands both tensor-index actions,
uses finite Leibniz at the original source's double zero, and differentiates the
already proved nonlinear Bianchi identity. The output is the original Hessian
tensor, with no prescribed source derivative arrays. Constant-scalar divergence
linearity is also verified, to retain the Taylor factor one half.

The physical Xi-labelled specialization is the remaining local conservation
check. Full causal solvability and original boundary-domain matching remain
separate producers; the scalar stream's residual identities alone cannot stand
in for those fields and their genuine radial derivatives.

Two full-field construction mechanisms remain under comparison after this
conservation result. The radial route must transport the original conserved
source into the actual harmonic source rows, realize all reconstructed radial
jets, and solve the common physical boundary problem. A second candidate is to
identify the original linearized Einstein operator with a gauge-fixed tensor
wave operator plus its gauge term, solve that tensor equation, and prove that
the gauge constraint propagates from admissible data. Either route must produce
the same original causal solution and retained boundary action before claiming
physical left-QNM coupling or any clock law.

Broad/deep `Lichnerowicz` and `gauge propagation` corpus searches did not identify
an applicable producer for the second mechanism. Both searches reported partial
filter/judge and decomposition coverage; this is not a claim that the corpus
lacks one. The returned Fokas–Lenells Hardy propagation statements concern their
own analytic slices and boundary corrections, and do not identify the metric's
tensor operator or boundary domain. No such identification has been assumed.

The physical specialization now passes scratch checking in
`ThetaCuspHawkingBMQuadraticConservation`.
`physical_hessian_conservation` discharges regularity, symmetry, background
nondegeneracy, and the original background and linearized equations for every
physical Xi-labelled theta-cusp perturbation on the actual exterior chart.
`physicalQuadraticSource_eq` identifies the resulting tensor, divided by two,
with the original source's actual second Taylor coefficient.
`physical_quadratic_source_conservation` proves its zero background covariant
divergence with no supplied conservation, derivative-jet, or reconstruction
certificate. The physical leaf's isolated final audit passed (56s); it built only the new leaf with cached dependencies.

Analytical proof: write the original cosmological tensor as E(e) and its actual
covariant divergence as D(e). Nonlinear Bianchi gives D(e)E(e)=0 on an amplitude
neighborhood. Both E(0) and its first amplitude derivative vanish on an exterior
spatial neighborhood. The verified mixed derivative identities therefore kill
their spatial derivatives as well. Finite Leibniz retains only D(0)E''(0), which
is zero. E''(0)/2 is the original quadratic coefficient Q, hence D(0)Q=0.
The inverse metric and both covariant tensor-index actions are included in D.

This closes the local quadratic-conservation conjecture. The hard remaining
producer is a full causal field solving the original sourced linearized tensor
equations in the physical domain. Transport to harmonic constraints, actual
radial reconstruction, common retarded/advanced boundary data, and the original
left-mode boundary action must still be supplied. Conservation does not prove
that field exists, select a physical left-mode coupling, or establish extinction.

Validation for this producer: all seven new leaf modules passed `lake env lean`
scratch checking and exact isolated `lake build <module>` audits. The authoritative
formal lint passed, reporting existing large-file warnings. Both umbrellas are
wired without being built. No mathematical computations, heartbeat increases,
axiom printing, Git commands, frontier-map edits, or STATUS edits were used.

All owned scratch, search, audit, log and staging paths for this producer were
removed after validation. No owned Lean/Lake, search or lint processes remain;
other agents’ files and processes were left untouched.


### Independent harmonic rate and a finite Laurent source inverse (0912x)

Fresh corpus inspection changes the construction problem. The cached
`ThetaCuspHawkingBMScalarStreamReconstructionField` already derives all seven
sourced harmonic equations from genuine twisted radial derivatives, and
`ThetaCuspHawkingBMScalarStreamGreenSourced` supplies a smooth interior Green
solution. Its current dictionary ties the source rate and output angular
parameter to the same `chi`; its integration cutoffs are interior. Neither
interface yet identifies the full original source with a physical endpoint
solution. `ThetaCuspHawkingBMForcedMetricField.forcedMetricField_einstein`
already solves all sixteen components for its specified scalar-vector mixed
source. These are usable producers, not gaps to rebuild.

The explicit scalar-scalar master source admits a
particular solution y(r)=r+A/r+B/r^3 at independent complex rate s and angular
eigenvalue mu. Clearing the twisted master operator gives

    r^2(r^2-1)y'' + (2r^3+4sr)y' + (mu-2s-4s^2)y.

On r^k this equals k(k+1)r^(k+2) +
[mu-(k-2s)(k-2s-1)]r^k. The source's two highest Laurent coefficients match
this operator applied to r exactly. The remaining two coefficients determine
B and A by triangular elimination. The apparent B denominator
mu-(2s+3)(2s+4) cancels against an exact factor of the source numerator;
that cancellation is proved in `ssMasterSource_laurent`. The remaining possible denominator
is mu-(2s+1)(2s+2), besides the existing angular factor 2-mu.

Whole-chain consequence: this is a source-specific particular inverse
without tying parent rate to output angular eigenvalue. The original source
transport and the homogeneous correction enforcing causal horizon/AdS data
still need to be derived. Any correction or resonance must be carried into
the original left-mode pairing and fixed-clock question; a particular solution
alone supplies no extinction. The new leaf proves the actual derivative identity,
exact source cancellation, and smooth sourced reconstruction with this field.

The exact boundary decomposition is proved: for the finite Laurent particular
field, subtracting its r term gives
A/r+B/r^3. In reciprocal radius x=1/r, the scaled full field is the polynomial
1+A*x^2+B*x^4; the subtracted remainder is A*x+B*x^3. Thus its boundary germ
can be retained exactly before reconstruction and pairing. Whether the original
metric boundary conditions select this affine master boundary datum must be
proved from the reconstruction; it is not assumed here.

Broad/deep searches used reconstruction, hyperbolic, endpoint extension, and
rational/Laurent mechanisms, including candidate lemmas, proof-method source
arguments and ingredient sets. Results were partial (source/compiler and
retrieval coverage reported), so missing hits are not absence claims. The
Laurent search returned rational-function/Laurent-series operator transport,
but no matching particular solution among its reported candidates. Exhaustive
source references to `ssMasterSource` and `SSMasterEquation` identify the
existing interior Green construction described above.

A broad renormalization paper search found Rogers and Whitehill,
[What are the consequences of independent factorization and renormalization
scales?](https://arxiv.org/abs/2608.01489) (August 2026). Its QCD discussion
relates subtraction choices through conservation constraints. The transferable
question here is whether source and boundary subtractions preserve the same
original Einstein identity. Its QCD hypotheses do not prove any HB identity;
the proposed Laurent decomposition is being derived directly from the corpus
source instead. The separate broad resonance search returned no useful recent
paper in its reported results.

The finite Laurent conjecture now passes `lake env lean` in scratch, including
actual first/second radial derivatives and the twisted sourced equation. The
original lower source coefficient factors exactly as predicted. No numerical
or symbolic external computation was used.

The analytic coefficients simplify further. With d=(2s+1)(2s+2),

    A = s(5s+2)/2 + s^2(s+1)(s+2)/(2-mu)
        + 3s(s+1)^2(3s+4)/(2(mu-d)),
    B = -s^2(s+1)^2/8 - s^2(s+1)^3(s+2)/(4(2-mu)).

These simplifications are proved in `laurentMasterA_resolvents` and
`laurentMasterB_resolvent`. The parameter d is exactly
the existing mixed-source angular parameter, as seen in
`D4BMModularCore.parameter_physicalRate`. Moreover,
`fullAngularField_equation` already supplies
Delta H=d H+(d/2)S^2 for the original literal scalar S. This suggests lifting the
Laurent coefficients to actual angular fields using the existing inverse at d
and the inverse at 2, instead of decomposing the entire quadratic source into
individual spectral harmonics. That is a new full-field construction candidate
exposed by the radial solution. It still requires the original source identity,
matching the inverse-at-2 domain, and proving the reconstructed metric's physical
boundary and time-onset conditions. Those conditions determine whether this
particular field can enter the causal action and the extinction argument.

The exact angular lifting candidate is now explicit. Let F=S^2,
(2-Delta)U=F, and (Delta-d)V=F, with d=(2s+1)(2s+2). Then set

    A_field = s(5s+2)F/2 + s^2(s+1)(s+2)U
              + 3s(s+1)^2(3s+4)V/2,
    B_field = -s^2(s+1)^2 F/8 - s^2(s+1)^3(s+2)U/4,
    y(r,z) = r F(z) + A_field(z)/r + B_field(z)/r^3.

The existing full angular field supplies V=2*fullAngularField/d. The existing
`ThetaCuspHawkingBMAngularReconstruction` supplies the bounded weak inverse
for U on L2 forcing. To restore the full source, its cusp principal response
at shift two is explicit: for F_pr=(A*y^rho+D*y^(1-rho))^2,

    U_pr = A^2*y^(2rho)/(2-(2rho)(2rho-1)) + A*D*y
           + D^2*y^(2-2rho)/(2-(2-2rho)(1-2rho)).

Neither nonconstant denominator vanishes for a Xi occurrence.
`xi_cusp_two_denominators` discharges those factors, and
`xi_cusp_two_response_equation` proves the full principal-part differential identity. Then a smooth modular cusp cutoff and its compact
commutator can reduce the remaining forcing to the native L2 problem; global
smooth reconstruction and restoration must still be supplied at this shift.
This is a construction target, not an assumed full angular solution.

The tensor matching test remains essential: the source-harmonic coefficient
file describes scalar harmonic images of the full quadratic source. Lifting
those coefficients must identify the actual angular tensor, including any
remaining trace-free tensor component, instead of declaring the projection
complete. The already proved full quadratic conservation supplies compatibility
but does not by itself prove that tensor identification. Likewise the explicit
r term must remain through reconstructed metric boundary conditions, physical
time onset, and original left-QNM pairing. The scalar Laurent construction does
not yet establish a causal tensor inverse or fixed-clock extinction.

### Full original angular reconstruction at shift two

The Laurent coefficients require U solving (2-Delta)U=S^2. The proved weak construction uses the actual cusp response Q=cuspPowerResponse(2,rho,A,D),
whose equation is (Delta-2)Q=P^2 for the original principal part P. With the
existing smooth height cutoff chi, put K=chi*Q and
G=S^2-(Delta-2)K. Above height three G=S^2-P^2, which the existing literal
Fourier-tail theorem bounds; on the remaining compact cell G is smooth.
Thus G belongs to the original modular L2 space. The already constructed
coercive inverse gives the unique native finite-energy solution W of
(2-Delta)W=G. The intended complete response is U=W-K.

Full cell-germ compatibility preserves K and every cutoff derivative
at modular seams. The restored field U now satisfies (2-Delta)U=S^2 against
every compact chart test on the full modular half-plane; the cutoff Green
identity and integrability are proved before separating the integrals.
The exact theorem is `D4BMAngularTwo.fullResponse_distribution_equation`.
After this original forcing admission, W still requires
local weak-to-smooth reconstruction and pointwise restoration. The tensor
matching question remains separate: the trace-free harmonic reconstruction
must account for the whole original angular tensor, including any component
invisible to its scalar divergence. Neither step is assumed from conservation.

The source tensor suggests a second construction test once U is smooth. Write
F=S^2 and lambda=rho(rho-1), and let HessTF be the actual hyperbolic trace-free
Hessian. The source-harmonic dictionary predicts

    [Hess(F)-dS tensor dS]^TF = HessTF(F+lambda*U).

Their divergence agrees when (2-Delta)U=F and Delta S=lambda*S. The missing
statement is vanishing of their divergence-free, trace-free difference, rather
than an assumed completeness of scalar harmonics. For each original principal
power y^(2rho), y, y^(2-2rho), direct differentiation predicts exact equality:
HessTF(y^a) has diagonal entries -a(a+1)y^(a-2)/2 and its negative. The residual
native homogeneous cusp power y^(-1) has zero trace-free Hessian. These are
paper-level checks to formalize, not yet facts in the working log. A modular
holomorphic quadratic-differential or energy argument may then identify the
remaining tensor globally, provided its actual cusp admission is proved.

The broad weight-four corpus search found a concrete uniqueness ingredient in
`Bottcher2Cusp.quarticDefect_eq_zero`: it applies
`CuspForm.rank_eq_zero_of_weight_lt_twelve` to a constructed level-one
weight-four cusp form. The source declaration in the installed
`Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula` is verified.
Thus a weight-four cusp-form identification can close the tensor remainder
without a scalar spectral-completeness assumption. That identification is still
open. Since the tensor is complex-valued, both its holomorphic and
antiholomorphic components must be retained; real-valuedness is not assumed.

The same-copy physical parent rates sum to -3, so their combined expression
(sum+1)(sum+2) is exactly 2. This gives the new inverse a second potential role
in the opposite-parent-branch channel; the original cross-branch Einstein
reduction must still be derived. More generally, all four principal exponents
of a product of two Xi scalar sources have real part in (0,2), so none meets
the shift-two roots 2 or -1, even when imaginary parts cancel. These algebraic
facts are recorded separately from the still-unproved cross-source construction.

### Smooth source inverse and the undetected tensor component

The next construction uses the proved shift-two native response equation,
with its negative residual forcing in (Delta-2)W=-G, to derive the full planar
localization identity. Compact-local forcing is smooth, so the existing
Sobolev gain can be iterated from local L2 to all orders. Gluing the resulting
representatives and retaining the original cusp field must give an actual
smooth modular U with (2-Delta)U=S^2 pointwise.

The tensor test is then source-specific: compare
[Hess(S^2)-dS tensor dS]^TF with HessTF(S^2+lambda U).
Vanishing of their divergence is not their vanishing. The proposed completion
must identify both complex tensor polarizations with weight-four cusp forms,
including their actual cusp bounds, before using the corpus dimension theorem.

The smooth construction is checked in Lean: `ThetaCuspHawkingBMAngularTwoRegularity`
constructs `smoothFullResponse` and its original-coordinate `coordinateResponse`.
The pointwise equation is `(2-Delta)U=S^2`; the full-volume distributional field
and native finite-energy correction are preserved. No smoothness premise on the
weak response is supplied.

The remaining tensor simplifies algebraically. Set
`E=[dS tensor dS]^TF+lambda HessTF(U)`, where `Delta S=lambda S`.
Then the proposed source-tensor identity is equivalent to `E=0`.
Its coordinate components are
`A=(S_x^2-S_y^2)/2+lambda*((U_xx-U_yy)/2-U_y/y)` and
`B=S_x*S_y+lambda*(U_xy+U_x/y)`.
Direct differentiation gives `A_x+B_y=0` and `B_x-A_y=0`:
for the Hessian terms, the two divergence components are respectively
`(partial_x Delta U-2U_x)/(2y^2)` and
`(partial_y Delta U-2U_y)/(2y^2)`;
for the gradient-square terms they are `S_x Delta S/y^2` and
`S_y Delta S/y^2`. The two scalar equations cancel both components exactly.
Consequently `A-iB` obeys the holomorphic Cauchy–Riemann equation and `A+iB`
the antiholomorphic equation, without a reality assumption. This differentiation
is the current Lean target. Modular weight and cusp admission remain separate
obligations; no tensor-vanishing conclusion is being inferred from divergence.

A second cusp-admission candidate uses the existing native L2 correction directly.
Once both tensor polarizations are holomorphic/antiholomorphic and periodic,
compact mean-value tests can transfer their derivatives onto the tests. The
coordinate weight converts the local flat L2 norm of W to a polynomial height
bound using its native norm. The explicit principal fields have polynomial
height bounds. Polynomial growth of a periodic holomorphic field excludes all
growing Fourier modes. Its possible constant mode must then be excluded using
the original principal subtraction and native L2 admission: a nonzero constant
trace-free Hessian contribution would force a y^2 term in the mean of U, whereas
all explicit source principal exponents have real part strictly below 2 and W
is native L2. This is a conjectured proof mechanism, not a proved bound or cusp
admission theorem. It may replace a stronger global Hessian L2 estimate.

The constant-mode test can be weaker still. Pair the period mean of the tensor
with a smooth height test supported in [Y,2Y], and move both derivatives from W
onto that test. Native L2 gives an O(Y^(3/2)) bound for the unweighted L1 pairing
of W there; two transferred height derivatives contribute Y^(-2). After dividing
by the test's height mass O(Y), the correction contributes O(Y^(-3/2)) times
the native L2 tail norm. The explicit principal tensor contribution tends to zero
because each squared-source exponent has real part below 2. A constant tensor
Fourier mode would survive that averaging, hence must vanish. This scaled-test
argument is a proposed replacement for solving the mean-field ODE, and still
requires exact test normalization, integration-by-parts and source bounds in Lean.

### Automorphic ladder candidate for the tensor weight

Broad Maass/raising search found the exact generic argument
`weightLift_ladder_preserves` (private) in
`GaloisForLFunctions/RHTower/MaassAutomorphicDifferentialLadder.lean`.
It uses only a smooth `FunctionSpace` field and automorphic invariance of its
`weightLift`; no Maass eigenvalue or cusp/L2 premise enters that argument.
It differentiates invariance along two actual group curves and solves for the
raised and lowered fields using the public `weightLift_diagonal_hasDerivAt`
and `weightLift_quarterDiagonal_hasDerivAt` laws. The public
`raised_automorphic`/`lowered_automorphic` specializations assume real Maass cusp
eigenforms; the generic argument is the applicable ingredient for S and U.

The literal operator conventions are `X=i*y*partial_x`, `Y=y*partial_y`,
`raise(m)=X-Y-m` and `lower(m)=-X-Y+m`. Direct differentiation gives

    (lower(0) S)^2 + lambda*lower(-1)(lower(0) U) = -2*y^2*(A-iB),
    (raise(0) S)^2 + lambda*raise(1)(raise(0) U) = -2*y^2*(A+iB).

For example the first iterated term expands to
`-y^2*U_xx+y^2*U_yy+2i*y^2*U_xy+2i*y*U_x+2y*U_y`, exactly
`-2y^2` times the Hessian contribution to `A-iB`. The squared first derivative
has the same factor for the gradient-square contribution. The other identity
has both imaginary signs reversed. These operator identities, the actual
`FunctionSpace` embeddings and conversion of the weight lifts to the original
weight-four transformation are formalized in
`ThetaCuspHawkingBMAngularTwoWeight`. The separate BM second-jet
Maass bridge also retains the relevant connection terms, but its conventions
must be matched explicitly rather than identified by name.

The tensor differentiation and holomorphic reconstruction are now checked in
`ThetaCuspHawkingBMAngularTwoTensor`. `defectTensor_components` identifies the
actual metric tensor; `defect_cauchyRiemann_x` and `defect_cauchyRiemann_y` derive
both differential identities; `holomorphicPolarization_differentiableAt` and
`conjugatePolarization_differentiableAt` prove complex differentiability on the
entire upper half-plane. The source identity still requires the tensor to vanish.
The weight-four transformation is also proved. Cusp admission remains open.
Physical causal boundary admission and Hawking-clock extinction
remain beyond that angular identification.

Validation: both new exact leaf audits passed, and formal lint passed. Both leaves are imported by the RHTower umbrella; the umbrella was not built.

### Proved weight-four transformation and current cusp target

`ThetaCuspHawkingBMAngularTwoWeight` proves the transformation of both actual
holomorphic polarizations for every Xi occurrence and every original integral
modular matrix. `lowerTensorFunction_eq` and `raiseTensorFunction_eq` identify
the genuine smooth Maass ladder expressions with `-2y²(A-iB)` and
`-2y²(A+iB)`. `holomorphicPolarization_weight_four` and
`conjugatePolarization_weight_four` give `H(gamma*z)=(c*z+d)^4 H(z)`.
The conjugate proof retains the independent complex polarization.

The generic ladder proof differentiates invariance along the two actual group
curves. The exact identity `orbit_phase_four` cancels the height ratios when
converting compact weights to the original modular denominator. No Maass
cuspidality or eigenform premise is imposed on the constructed inverse.

Validation: the exact weight leaf audit passed (2 jobs, 302 seconds), with no
Lean warnings. Formal lint passed. The RHTower umbrella imports the new leaf;
no umbrella or dependency source was built. The cached dependency artifacts
were retained, and the new leaf artifacts were copied to the normal cache.

The missing Lean angular step is cusp admission for these actual holomorphic
weight-four fields. The exact principal cancellation and native derivative
estimates below now give an analytical proof of the source tensor identity.
That assembly is not yet formalized. Physical causal boundary admission and
Hawking-clock extinction remain unproved.

### Exact cancellation of the complete cusp principal tensor

Let `r=rho`, `s=1-r`, `lambda=r(r-1)=s(s-1)`, and
`P=A*y^r+D*y^s`. The actual restored principal response is

    U_pr = -A²*y^(2r)/(2(r-1)(2r+1)) + A*D*y
           -D²*y^(2s)/(2(s-1)(2s+1)).

Its denominators are nonzero for every Xi occurrence by
`xi_cusp_two_denominators`. This is precisely the negative of
`cuspPowerResponse 2 rho A D`, after factoring the two denominators.
For a height-only power `C*y^(2r)`, the first trace-free Hessian component is
`-r(2r+1)C*y^(2r-2)`; for `A*D*y` it is `-A*D/y`.
Multiplying these three components by `lambda` gives respectively

    (r²*A²/2)*y^(2r-2),  r*s*A*D/y,  (s²*D²/2)*y^(2s-2).

Their sum is `P_y²/2`, exactly cancelling the first component of
`[dP tensor dP]^TF`. Both off-diagonal components are zero because both
fields depend only on height. Thus the complete principal tensor is zero,
including the mixed Weyl term. The actual signed eigenvalue is
`lambda=-scalarQ(rho-1/2)=rho(rho-1)`. The original-field identity is now
proved in Lean by `D4BMAngularTwoPrincipalTensor.actual_principal_tensor_zero`,
with the original metric and connection. Its proof combines the genuine
Euler derivative with the already proved shift-two response equation through
the exact identity `lambda*(P²+2*Q+2*y*Q_y)=(y*P_y)²`.

Consequently, above the cutoff transition, writing `S=P+R` and `U=W-Q`
reduces the exact tensor remainder to

    [dP tensor dR + dR tensor dP + dR tensor dR]^TF
      + lambda HessTF(W).

This supplies a sharper cusp-admission target: estimate only the Fourier
tail terms and the distributional derivatives of the retained native L2
correction. Exact principal cancellation does not itself establish those
estimates, cusp admission, tensor vanishing or causal radial admission.

### Cusp-gap route from a weak growth estimate

Deep search for periodic holomorphic growth returned the source argument
`HTGeometry.normedPeriodic_exp_decay_of_zero_at_inf` in
`GaloisForLFunctions/HTGeometry/PeriodicCuspBoundaryGap.lean:148`.
Its exact inputs are positive period `h`, periodicity, eventual holomorphy and
`ZeroAtFilter I∞ f`; its conclusion is `f=O(exp(-2*pi*Im(z)/h))`.
The theorem uses the removable singularity of the periodic cusp function.
It does not assume the Fourier coefficients or supply a bound for our tensor.

Analytical consequence: if a periodic holomorphic `H` has growth strictly below
the first increasing Fourier exponential, apply this theorem to
`g=qParam(h,z)*H(z)`. The growth hypothesis gives `g→0`. The theorem gives
`||g||≤C*exp(-2*pi*Im(z)/h)`. Since `||qParam(h,z)||` equals this positive
exponential, cancellation gives `||H||≤C`. Thus a polynomial bound from compact
mean-value tests would already give bounded cusp admission, without constructing
all Fourier coefficients. A globally periodic extension of the original
upper-half-plane field and the actual weak-growth estimate still need Lean
proofs. The constant mode remains to be removed by the normalized height test
against the retained native L2 correction. This is a candidate mechanism for
that missing estimate, not an admission theorem for the actual tensor.

Search coverage: the multiword deep request was partial; the broad
`subexponential` request completed, but its leading RH growth equivalences do
not provide the missing local bound. Candidate/source-argument and ingredient
results were inspected; no absence claim is made from those searches.

### Current compact evaluation construction

The next weak-growth proof uses the source-verified
`HTGeometry.integral_dzbar_kernel` from `HTGeometry/DbarSolve.lean`.
It reconstructs any compact C1 field from its actual Wirtinger derivative.
Apply it to a smooth cutoff times a holomorphic tensor polarization. Holomorphy
kills the derivative of that polarization. A cutoff equal to one near the
center makes the remaining divided-cutoff derivative smooth and supported in
an annulus. This gives a fixed compact evaluation test without assuming a
chosen `ContDiffBump` is radial. Translating that fixed test will let both tensor
derivatives move onto a uniformly controlled test. The immediate target remains
a polynomial growth bound for the actual retained native correction.

### Native L1 control of the inverse's cusp contribution

The actual native measure has finite volume. The constructed correction `W`
is therefore native L1 by its proved native L2 membership. Write
`M(q)=integral_fd |W(q)| dmu`, with `dmu=dx dy/y²`.

For a compact planar test `g` supported in the closed radius-`1/4` ball about
`c`, `Im(c)>3`, exact modular unfolding gives

    integral_plane g*W = integral_fd periodize(y²*g)*W dmu.

The proved high-cusp periodization identity removes nonparabolic terms. At
most the three integer translations `floor(Re(c))-1`, `floor(Re(c))`,
`floor(Re(c))+1` can contribute. Thus, if `|g|<=B`,

    |integral_plane g*W| <= 3*(Im(c)+1)²*B*M(q).

The fixed divided-cutoff Cauchy kernel and each fixed first or second
directional derivative have uniform compact-support bounds after translation.
Two compact Green identities therefore bound the actual tested second
derivatives of `W` by `C(v,w)*(Im(c)+1)²*M(q)`. For the connection terms, use
`g/y` and one integration by parts:

    D_v(g/y) = D_v(g)/y - g*Im(v)/y².

On the support, `y>1`, so the derivative test is bounded by
`sup|D_v(g)|+sup|g|*|Im(v)|`. This controls every actual `y^(-1) D_v W`
term by the same polynomial height factor. No pointwise derivative bound on
`W` is assumed. These estimates replace the proposed sharper local L2 norm
estimate; assembly with the literal source and principal inverse is still
required for a polynomial bound on either full tensor polarization.

### Vanishing normalized cusp mean of the correction's actual Hessian

This is an analytical proof for the constructed `W`, not yet a Lean theorem.
Choose `chi` smooth and compactly supported in `(1,2)` with integral one, and
put `psi_Y(y)=chi(y/Y)/Y` for `Y>1`. Integrate over the horizontal period
`[-1/2,1/2]` and all positive heights. `W` and its actual derivatives are
periodic and smooth. Horizontal total derivatives integrate to zero.

The original trace-free Hessian components are

    H00 = (W_xx-W_yy)/2-W_y/y,
    H01 = W_xy+W_x/y,  H10=H01,  H11=-H00.

The normalized means of `H01` and `H10` are zero. Two integrations by parts
in height give the exact diagonal mean

    integral psi_Y*H00 dx dy
      = integral W*(-psi_Y''/2+psi_Y'/y-psi_Y/y²) dx dy.

All boundary terms vanish because `psi_Y` is compactly supported. Let
`B=||chi''||_infty/2+||chi'||_infty+||chi||_infty`. The coefficient has
absolute value at most `B/Y³` and support in `Y<y<2Y`. This entire strip
belongs to the original fundamental cell. Consequently its absolute pairing
is at most

    (B/Y³)*integral_strip |W| dx dy <= (4*B/Y)*M(q) -> 0.

The `H11` mean is its negative. Thus all four normalized means of the actual
correction's trace-free Hessian tend to zero, without a pointwise decay
estimate or an assumption on its differentiated native norms. Combined with
the exact principal cancellation and rapid source cross terms, this is the
constant-mode mechanism for both independent tensor polarizations. The
normalized mean estimate, periodic cusp removal, tensor vanishing and physical
causal boundary admission remain separate formal obligations.

### Analytical closure of the actual angular tensor identity

**Lean theorem:** `D4BMAngularTwoCuspDecay.actual_tensor_zero`. For every
original Xi occurrence `q`, let `S` be the literal scalar, `lambda` its original
Laplace--Beltrami eigenvalue and `U=W-K` the constructed smooth shift-two
inverse. Then, pointwise throughout the upper half-plane,

    [dS tensor dS]^TF + lambda*HessTF(U) = 0.

This statement concerns the actual squared-source angular tensor. It does not
assert physical radial/left-QNM endpoint admission or Hawking-clock extinction.

1. **Exact high-cusp reduction.** Above height three, the proved cutoff germ is
   `K=Q`, the complete principal response. Integer translation invariance
   extends this equality from the fundamental cell across the entire high
   cusp, including the vertical seams. Write `S=P+R`. The explicit principal
   cancellation proved above gives

       E = [dP tensor dR+dR tensor dP+dR tensor dR]^TF
             +lambda*HessTF(W).

   `D4BMSquareCuspJets.gradientProductRemainder_jet_weighted_bound` now proves
   all complex height-weighted bounds for every coordinate jet of each actual
   product `D_i S*D_j S-D_i P*D_j P`.
   `gradientProductRemainder_jet_tendsto_zero` proves its weighted vanishing
   along every horizontal path. Thus the source contribution's full component
   estimates are formalized, including both principal--tail cross terms and
   the tail--tail product. `ThetaCuspHawkingBMAngularTwoCuspGrowth` now joins
   these terms to the actual inverse. `globalCuspCutoff_high` and
   `coordinateResponse_high_germ` identify its full high-cusp germ, and
   `defectA_high` and `defectB_high` give the exact components

       A=(G00-G11)/2+lambda*((Wxx-Wyy)/2-Wy/y),
       B=G01+lambda*(Wxy+Wx/y),
       Gij=DiS*DjS-DiP*DjP.

   `correction_planar_first` and `correction_planar_second` identify every
   displayed derivative with the native correction's actual planar derivative.

2. **Polynomial growth of both actual polarizations.** The established actual
   tensor components give `H_minus=A-iB` and `H_plus=conj(A+iB)`. They are
   holomorphic, and each satisfies the full weight-four transformation law.
   The fixed compact evaluation identity reconstructs `pi*H(c)`. The rapid
   term has a uniformly bounded pairing. The second-derivative and connection
   estimates proved above bound the remaining pairing by
   `C*(Im(c)+1)²*M(q)`. Thus, for each fixed `q`, both polarizations satisfy
   `|H(c)|<=C_q*(Im(c)+1)²` for `Im(c)>4`. The actual statements
   `holomorphicPolarization_growth` and `conjugatePolarization_growth` in
   `ThetaCuspHawkingBMAngularTwoCuspGrowth` are proved in Lean.

   Its `evaluationKernel` and `evaluationTest` include both the original
   kernel and its conjugate. `exists_second_test_bound` and
   `exists_connection_test_bound` establish the needed bounds for each.
   The second polarization is reconstructed by conjugating the integral
   against the conjugate kernel. This assumes no reality of the source,
   response or tensor components.

3. **Bounded cusp admission from the periodic gap.** Integral translation has
   automorphy factor one, so each `H` is periodic of period one. Extend it by
   zero to nonpositive height; this preserves global real periodicity and
   eventual holomorphy. Put `g(z)=exp(2*pi*i*z)*H(z)`. The polynomial bound
   implies `g->0` uniformly as `Im(z)->infinity`. The source-verified theorem
   `HTGeometry.normedPeriodic_exp_decay_of_zero_at_inf` gives
   `|g(z)|<=C*exp(-2*pi*Im(z))`. Cancel the strictly positive norm of the
   exponential to obtain a uniform bound for `H`. The proved
   `analyticAt_normedPeriodicCuspFunction_zero` consequently extends its
   periodic cusp function holomorphically to zero.

4. **Vanishing normalized tensor averages.** Choose real smooth `chi` with
   compact support in `(1,2)` and integral one. For `Y>3`, write
   `psi_Y(y)=chi(y/Y)/Y`. For either actual polarization put

       A_Y(H)=integral_0^infinity psi_Y(y)
                *integral_(-1/2)^(1/2) H(x+i*y) dx dy.

   Apply the height-weight-one bound of F82 to each `Gij`. On `Y<y<2Y`,
   it bounds the complete source contribution by `C_G/Y`. The exact
   correction Hessian mean proved above contributes at most
   `4*|lambda|*B*M(q)/Y`; its off-diagonal terms integrate to zero by
   periodicity of `W`. Complex conjugation preserves these estimates and
   commutes with the real normalized test. Hence `|A_Y(H)|<=C_q/Y` for
   both polarizations, so each normalized average tends to zero.

5. **Actual cusp vanishing.** The holomorphic cusp extension from step 3
   has a value `L` at zero and gives `H(x+i*y)->L` uniformly in `x`.
   The normalized strip tests have integral one and fixed absolute mass
   `integral_1^2 |chi(t)| dt`. Therefore

       |A_Y(H)-L| <= (integral_1^2 |chi(t)| dt)
                       *sup_(x real, y>=Y) |H(x+i*y)-L| -> 0.

   Step 4 gives `L=0`. Thus each actual polarization vanishes at infinity.
   This limit argument directly identifies the cusp value from normalized
   averages. The full modular transformation law supplies vanishing at
   every cusp: `OnePoint.isZeroAt_iff_forall_SL2Z` is the exact interface
   used in `Bottcher/QuarticModularForm.lean` to construct `CuspForm` objects.

6. **Weight-four uniqueness.** Each polarization is now a cusp form of weight
   four for the full integral modular group. The corpus uses the unconditional
   `CuspForm.rank_eq_zero_of_weight_lt_twelve` together with
   `rank_zero_iff_forall_zero` for this exact space. Both polarizations vanish.
   Therefore `A-iB=A+iB=0`, so `A=B=0`; the already proved original tensor
   component identity gives the stated geometric equality.

The full pointwise tensor identity has a Lean proof through the expanding-disk
argument below. Its actual cusp forms and their vanishing are constructed in
`ThetaCuspHawkingBMAngularTwoCuspDecay`. Periodic cusp removal and normalized
Hessian means remain an alternative analytical proof, with no role in the
formal dependency chain. Physical causal radial/left-QNM admission and
fixed-Hawking-clock extinction remain open.

The cusp-growth leaf passed `lake env lean` and its exact `lake build` audit
under Lean 4.32.2 without warnings. Its umbrella import is wired. Formal lint
with generated-index checking passed; no umbrella build was run.

### Direct cusp vanishing from expanding evaluation disks

**Lean theorems:** `holomorphicPolarization_decay` and
`conjugatePolarization_decay` in `ThetaCuspHawkingBMAngularTwoCuspDecay`.
For each original Xi occurrence `q`,
both actual polarizations satisfy `|H(c)|<=C_q/Im(c)` when `Im(c)>4`.

Put `Y=Im(c)` and let `k_b` be the original fixed evaluation kernel or its
complex conjugate. Define

    K_(b,Y,c)(z)=Y^(-2)*k_b((z-c)/Y).

Its support lies in `|z-c|<=Y/4`, hence `3Y/4<=Im(z)<=5Y/4`. Real dilation
has Jacobian `Y^2`, so the kernel's absolute integral is independent of `Y,c`.
The original compact holomorphic evaluation identity, applied to
`u -> H(c+Y*u)`, gives `integral K_(false,Y,c)*H=pi*H(c)`.
The entire open ball of radius `Y` about `c` has positive height.

Every second directional derivative of `K` has bound `B2/Y^4`. On its
support `Im(z)>=Y/2`, so

    |D_v(K/Im(z))| <= (2*B1+4*B0*|Im(v)|)/Y^4.

Compact Green identities transfer each correction Hessian derivative to one
of these tests. For any such test `g`, write `|g|<=B/Y^4`. Exact high-cusp
periodization removes all nonparabolic elements. For a point in the closed
fundamental cell, surviving integer translations belong to

    floor(Re(c))-ceil(Y)-2 <= n <= floor(Re(c))+ceil(Y)+2.

Their number is `2*ceil(Y)+5<=4Y` for `Y>4`. On support the original
hyperbolic-to-flat density factor is at most `4Y^2`. Consequently

    |periodize(y^2*g)| <= 16B/Y,
    |integral g*W| <= 16B*M(q)/Y.

These bounds apply to both conjugated tests and all original connection
terms. The weight-one case of F82 gives `|Gij(z)|<=2*Cij/Y` on the same
support. The scale-independent absolute kernel integral then bounds every
complete gradient-remainder pairing by `C/Y`.

Substitute the exact component identities F83 and reconstruct the two
holomorphic polarizations. For the second, conjugate the integral against
`K_(true,Y,c)` of `A+iB`. Division by the positive constant `pi` yields the
stated `C_q/Y` bounds, with no reality premise. Both actual polarizations
therefore tend uniformly to zero at the cusp. Their proved modular laws and
vanishing of the weight-four cusp-form space give the original tensor
identity F81. The scaled compact tests, exact translation count, `C_q/Y`
assembly, both actual cusp forms and the original tensor identity are proved
in Lean. The scratch check passed without warnings, followed by the exact
leaf audit under Lean 4.32.2. The new leaf is wired into its umbrella.


### Original scalar-source reconstruction from the angular tensor identity

The scalar--scalar source identification is proved in Lean for every original Xi
occurrence, either physical branch, arbitrary scalar amplitude and every exterior
point. `ThetaCuspHawkingBMScalarSourceIdentification.physical_scalar_source_coefficient`
identifies all sixteen components with the second Taylor coefficient of the
original nonlinear metric source, including its factor `1/2`.

Put `F=S^2`, `U=coordinateResponse(q)` and `lambda=(s+1)(s+2)`. The actual
angular identity `[dS tensor dS]^TF=-lambda*HessTF(U)` gives the complete
trace-free tensor `HessTF(F)+lambda*HessTF(U)`. Each affine harmonic
coefficient `c(mu)` becomes `c(0)*F+(c(1)-c(0))*Delta(F)`. This applies
to `TT`, `RR` and the angular trace. `TR` multiplies `F`; the mixed angular
rows multiply the actual `dF`. The trace-free coefficient is

    kappa(s,r)=s^2*((s+1)^2-4*r^2)/(8*r^4),
    ssSourceTF(s,r,mu)=kappa(s,r)*(1+lambda/(2-mu)).

Thus the literal trace-free source is
`kappa(s,r)*(HessTF(F)+lambda*HessTF(U))`. The source matrix retains the
actual envelope squared. All six lower Ricci slots are derived through the
original connection tables; full Einstein symmetry is a conclusion. The
original physical perturbation's complete field jet is matched by its exterior
germ, so the theorem concerns the original metric source. It assumes neither
harmonic completeness nor that `S^2` is a single harmonic.

The scratch check and exact leaf audit pass without warnings under Lean 4.32.2.
Only the new leaf was built; its artifacts are installed and its umbrella import is wired. The remaining construction is the literal Laurent metric response,
followed by its causal correction with the forced growing radial term, actual
onset, horizon data and original left-QNM pairing retained.


### Cancellation of the reconstruction's apparent double shift-two pole

Analytical identity from the original Laurent coefficients and `recH`, on the
physical exterior `r>1`, with `s` nonreal and away from the displayed spectral
poles. No numerical or symbolic experiment is used. Write `R=1/(2-mu)`, `V=1/(mu-d)`,
`d=(2s+1)(2s+2)`, `lambda=(s+1)(s+2)` and
`kappa=s^2*((s+1)^2-4r^2)/(8r^4)`. Decompose

    M = M0 + R*M2 + V*Md,
    M0 = r+s*(5s+2)/(2r)-s^2*(s+1)^2/(8r^3),
    M2 = s^2*lambda/r-s^2*(s+1)^2*lambda/(4r^3) = -2*lambda*r*kappa,
    Md = 3*s*(s+1)^2*(3s+4)/(2r),
    tauTF = kappa*(1+lambda*R).

Consequently `M+2r*tauTF=M0+2r*kappa+V*Md`: the original source
cancels the entire shift-two term in this reconstructed combination.

Let `D_s=d/dr+2s/(r*(r^2-1))` be the original twisted derivative and
`f=r^2-1`. The verified jet formula for the angular metric amplitude is

    H = R*(-mu*M/(4r)+f*D_s(M)/2-r*f*tauTR/(2s)
           -f*tauT/s+(f-mu/2)*tauTF+r*f*D_s(tauTF)).

The coefficient that could produce a double pole at `mu=2` is

    -M2/(2r)+f*D_s(M2)/2+(f-1)*lambda*kappa+r*f*lambda*D_s(kappa).

Since `M2=-2*lambda*r*kappa` and
`D_s(M2)=-2*lambda*kappa-2*lambda*r*D_s(kappa)`, this coefficient is
`lambda*kappa-f*lambda*kappa-r*f*lambda*D_s(kappa)
 +(f-1)*lambda*kappa+r*f*lambda*D_s(kappa)=0`.
The remaining factors `R*V` split as `(R+V)/(2-d)`. For either actual
physical branch, `d-2=2s*(2s+3)` is nonzero because `s` is nonreal.
Thus `H` has at most simple poles at the two original shifts and remains
bounded as `mu` tends to infinity. Hence its rational dependence on `mu`
lies in the span of `1,R,V`. Radial differentiation does not increase pole
orders because both shifts are independent of `r`. The original source-retaining
reconstruction identities then read

    F1 = s/f*(4r*H-2r*tauTF-M),
    F2 = -r*tauTR/(2s*f)+mu*F1/(4s*r*f)-2H/f^2+2r*D_s(H)/f,
    F0 = f^2*F2-2f*tauTF.

The leading value of `H` at spectral infinity is exactly
`H_infty=M0/(4r)+kappa/2`. The constant part of `F1` therefore also cancels:
`s/f*(4r*H_infty-2r*kappa-M0)=0`. Thus `F1` is proper and lies in the
span of `R,V`; multiplication by `mu` leaves it bounded at infinity.
Consequently `H,F0,F2` lie in the span of `1,R,V`. The apparent iterated
angular inverse and the apparent positive spectral power both cancel from
the metric amplitudes. Their proposed literal angular fields consequently
need only the three existing fields `F=S^2`, `U=(2-Delta)^(-1)F` and
`V_field=(Delta-d)^(-1)F`; the source itself still retains `Delta(F)`.
This classifies the actual rational coefficients. Proving that their substitution
solves the nonseparated metric equation, and establishing causal endpoint
conditions, remain obligations.

Paper proof: closed by the displayed identities. Lean status: all four original
amplitude decompositions, actual twisted derivatives, exterior smoothness and
physical noncollision are proved in `ThetaCuspHawkingBMThreeFieldReconstruction`. Sources: `ThetaCuspHawkingBMScalarStreamLaurentMaster`
(`laurentMasterA_resolvents`, `laurentMasterB_resolvent`) and
`ThetaCuspHawkingBMScalarStreamReconstructionJet.recH`.


### Explicit three-field coefficients of the original reconstructed response

Current construction: prove the literal sourced metric equation using the exact
three-field reduction of F87, then impose the original causal/onset and radial
endpoint data. Set `f=r^2-1`, `d=(2s+1)(2s+2)`, `R=1/(2-mu)`, `V=1/(mu-d)`
and use the original twisted derivative `D_s`. The reduced master is

    N=M+2r*tauTF=N0+Nd*V,
    N0=r+s*(3s+2)/(2r)+s^2*(s+1)^2/(8r^3),
    Nd=3s*(s+1)^2*(3s+4)/(2r).

The original reconstruction formula simplifies exactly to

    H=R*(f*D_s(N)/2-mu*N/(4r)-r*f*tauTR/(2s)-f*tauT/s).

Define coefficient fields, independent of `mu`, by

    H0=N0/(4r),
    Hd=(f*D_s(Nd)/2-d*Nd/(4r))/(2-d),
    H2=f*D_s(N0)/2-N0/(2r)-r*f*tauTR/(2s)-f*tauT/s-Nd/(4r)+Hd.

Then `H=H0+H2*R+Hd*V`, with every original source term retained. This
follows by `mu*R=2R-1`, `mu*V=1+dV` and `R*V=(R+V)/(2-d)`.
The remaining actual reconstruction coefficients are determined by

    F1_2=4sr*H2/f,                 F1_d=s*(4r*Hd-Nd)/f,
    F2_0=-r*tauTR/(2s*f)+(F1_d-F1_2)/(4s*r*f)-2H0/f^2+2r*D_s(H0)/f,
    F2_2=F1_2/(2s*r*f)-2H2/f^2+2r*D_s(H2)/f,
    F2_d=d*F1_d/(4s*r*f)-2Hd/f^2+2r*D_s(Hd)/f,
    F0_0=f^2*F2_0-2f*kappa,
    F0_2=f^2*F2_2-2f*lambda*kappa,
    F0_d=f^2*F2_d.

The proposed actual field is the sum of three original `harmonicMetricField`
recipes with profiles `F=S^2`, `U=(2-Delta)^(-1)F` and
`V_field=(Delta-d)^(-1)F`, using the corresponding coefficient columns.
These profiles are not supplied as harmonics. Their actual Laplacians must be
used: `Delta(U)=2U-F`, `Delta(V_field)=d*V_field+F`, and the full already
proved square Laplacian. The existing `harmonicMetricField_jet` permits arbitrary
smooth profiles, and `metricJet_cosmological_i_j` gives all sixteen unrestricted
angular-jet components. Thus no spectral-completeness theorem is needed for
this direct verification. Equality with the literal source from F88 and causal
admission are separate proof obligations.

Status: the complete four-amplitude decomposition and smooth radial columns
passed scratch Lean and the isolated exact-module Lake audit. No new
nonseparated metric-equation theorem is claimed yet.


### Source-retaining ingoing horizon cancellation

For `v=t+r_*`, `f=r^2-1`, the ingoing radial coefficients are
`Gvv=F0`, `Gvr=F1-F0/f`, `Grr=F2-2F1/f+F0/f^2`.
Write `N=M+2r*tauTF`, `W=4r*H-N`. The original reconstruction identities give

    Gvr=N'/2-tauT/s-2r*H'+2*tauTF+s*W/(r*(r+1)),
    f*Grr=4r*H'-N'+2*tauT/s-2*tauTF-2s*W/(r*(r+1)).

Primes here are ordinary radial derivatives. This follows by substituting
`D_s g=g'+2s*g/(r*f)` and eliminating `tauTR` with the original `H` identity;
no source term is dropped. The three angular amplitudes have the Laurent form
`H_k=a_k+b_k/r^2+c_k/r^4`. With
`C=3*(s+1)^2*(3s+4)/(8*(2s+3))`, their coefficients are

    a=(1/4, C-(3s^2+6s+2)/4, C),
    b=(s*(3s+2)/8, C*(2s^2+s)-s*(4s^3+9s^2+6s+2)/4, C*(2s^2+s)),
    c=(s^2*(s+1)^2/32, -s^2*(s+1)^3/16, 0).

Write `N_k=n1_k*r+n_1k/r+n_3k/r^3` and
`W_k=w0_k*r+w2_k/r+w4_k/r^3`. Then
`w0=4a-n1`, `w2=4b-n_1`, `w4=4c-n_3`. The polynomial part of `f*Grr`
has no constant term: it is `p2/r^2+p4/r^4`, with

    p2=-8b+n_1+indicator(k=0)*s*(s+2)/2+tensorWeight_k*s^2,
    p4=-16c+3n_3+indicator(k=0)*3s^2*(s+1)^2/8
       -tensorWeight_k*s^2*(s+1)^2/4,
    tensorWeight=(1,(s+1)*(s+2),0).

Direct substitution gives the horizon residue identity
`p2+p4=s*(w0+w2+w4)` in each original column. Consequently

    Grr = [-2s*w0*r^3+(p2-2s*w0)*r^2
           +(-2p4+2s*w4)*r+(-p4+2s*w4)]/[r^4*(r+1)^2].

This expression extends smoothly across `r=1`. The other ingoing coefficients
are then `Gvr=tauTF-f*Grr/2`, `Gvv=s*W-f*tauTF+f^2*Grr/2` and `H`.
The original time-radial envelope also has its already-proved regular ingoing
form (`ThetaCuspHawkingBMIngoingCoordinates.envelope_staticPoint`). This removes
an apparent horizon singularity of the particular metric. It does not yet impose
retarded onset, the radial boundary condition or the left-QNM action.

Paper status: algebraic derivation above. Lean status: exact Laurent expressions,
source-retaining residue cancellation, equality of every transformed original radial
column and its smooth ingoing extension, and specialization to both physical branches
are proved in `ThetaCuspHawkingBMThreeFieldHorizon`. Scratch Lean and the isolated
exact-module Lake audit passed without warnings. The full nonseparated metric
equation is proved below; retarded onset, boundary admission and left-QNM action
remain unproved.


### Direct nonseparated metric equation from the three original columns

The actual summed metric's original cosmological Einstein operator equals minus
the identified literal scalar-square source in all sixteen components. Its actual
profiles are `F=S^2`, `U=coordinateResponse` and `V=2*fullAngularField/d`, satisfying
`Delta U=2U-F` and `Delta V=dV+F`. No profile is supplied as a harmonic and no
completeness statement is assumed.

For each of the seven original operator rows write `L(mu)=L0+mu*L1`, and
let `c0,c2,cd` be the actual twisted radial jets of the three proved columns.
The source has exact form `t0+mu*t1+t2/(2-mu)`; only its trace-free row has a
nonzero `t2`. Expanding the already-proved harmonic residual produces

    mu*A+B+C/(2-mu)+D/(mu-d),
    A=L1(c0)+t1,
    B=L0(c0)-L1(c2)+L1(cd)+t0,
    C=L0(c2)+2*L1(c2)+t2,
    D=L0(cd)+d*L1(cd).

Clearing the two denominators gives a polynomial of degree at most three.
Its vanishing follows from the original sourced reconstruction identities at
independent admissible spectral values; polynomial rigidity then forces
`A=B=C=D=0`. These are precisely the nonseparated coefficient equations after
substituting the actual Laplacians of `F,U,V`. All twisted jets must first be
transported through the proved exterior field identity. The final operator is
applied to the actual sum of metric fields using jet addition and the original
linearized Einstein derivative, with `envelope(2s,a^2)=envelope(s,a)^2` retained.

The actual twisted-jet decomposition and all 28 coefficient identities are now
proved in `ThetaCuspHawkingBMThreeFieldRows`. The free-angular-jet operator and
all sixteen assembled source cancellations are proved in
`ThetaCuspHawkingBMThreeFieldTensor`. The actual summed metric and its complete source identity are proved in
`ThetaCuspHawkingBMThreeFieldMetric.literalMetric_einstein`, with its actual
coordinate regularity in `literalMetric_smooth`. The field uses the original
radial columns and both constructed angular inverses. Its jet is obtained from
`harmonicMetricField_jet` without a harmonic hypothesis; actual field-jet addition
and the linear Einstein derivative give the full sum. The original physical
quadratic source is substituted through `physical_scalar_source`, including the
factor `envelope(2s,a^2)=envelope(s,a)^2`. All three exact leaf audits passed without
warnings at default proof budgets, and all three imports are wired.

The constructed response now has both the full sourced metric equation and the
previously proved radial ingoing extension. This does not establish retarded
onset, boundary admission, left-QNM incidence or fixed-Hawking-clock extinction.
The next causal identification must retain the fixed source and its initial
terms; multiplying this particular response by an onset function alone does not
supply a proof of that identification. Broad Volterra search found the existing
`D4BMJointSource.principalTimeResponse_duhamel`, `_zero_of_nonpos` and `_unique`
theorems. Their source and potential definitions must be identified with the
present full metric construction before they can discharge any remaining gap.

## Original causal potential in null coordinates

The native full theta response already satisfies its actual mixed-null wave
equation and Dirichlet condition (`D4BMNativeResponse.fullNullResponse_wave`,
`fullNullResponse_boundary`), and has joint angular smoothness
(`fullNullResponse_angular_smooth`). The existing original-source retarded
reconstruction also retains the onset pulse; these are available ingredients,
not missing constructions.

The direct source attachment is proved in `ThetaCuspHawkingBMOriginalCausalPotential`. Set
`p=tau+x`, `r=tau-x` and
`Z(p,r,z)=fullNullResponse(p,r,z)+L((p-r)/2)*eta(p)*F(z)`,
where `L` is the original radial lift, `eta` the fixed physical-rate onset
and `F` the literal theta half-square. On `0<p<=r`, the actual derivatives satisfy
`4*Z_pr-Delta(Z)/cosh((p-r)/2)^2=timeOriginalForcing`.
The lift contributes `-L''*eta-2*L'*eta'` to `4*Z_pr`; the reduced source
contains exactly the opposite differentiated-onset term. Thus the full
original gradient source is restored. The same field has proved zero
pre-onset support, the Dirichlet value, angular smoothness and modular
invariance. This is a scalar potential
attachment for the mixed stream, not yet the full Einstein action incidence.

The proof in null coordinates uses the actual first and mixed derivatives
inside `FullNativeWave`, now exposed by public differentiability theorems,
plus the original lift jets. It assumes no joint spacetime smoothness.
Converting the result
into the full metric/action and evaluating its admitted boundary traces
remains a separate obligation.

The direct/image source identification is proved in
`ThetaCuspHawkingBMOriginalRetardedIdentity`. Its
`fullNullResponse_eq_retarded_reduced` identifies the native odd-source
rectangle with the direct-minus-image triangles for
`timeReducedCoefficient*F`. The proof splits along `a=b` and swaps the
lower triangle, retaining the source, one-quarter normalization and both
image signs. Actual joint continuity of the original half-square and
full gradient source justifies every finite source integral interchange.

`retarded_original_source_difference` retains the complete gradient
absorption under the original retarded operator. Together with the
existing retarded lift identity, `originalPotential_eq_retarded` proves
`Z=R(timeOriginalForcing)` for both physical branches, all amplitudes and
all nonnegative null endpoint/width pairs. No inverse-uniqueness premise
is supplied. `originalPotential_onset_reconstruction` then proves the
exact original decomposition `Z=lift-seed/d+R(onsetPulse)/d`. The source
pulse is retained. Full Einstein action/boundary pairing remains open.

The scratch check and exact `lake build
GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalRetardedIdentity`
audit pass at default proof budgets; the new leaf is wired. The audit built
only this leaf against cached dependencies. Repository lint reports the
unrelated unreachable `Sieve.KloostermanGlobalCollisionCoprime` module.

## Smooth physical parameters after exact triangle rescaling

The following interior joint-smoothness argument is formalized by
`ThetaCuspHawkingBMRetardedTriangleGeometry` and
`ThetaCuspHawkingBMOriginalSpacetimeRegularity`. It applies to the actual
original-source retarded potential identified above.

Fix `0<p<r`, set `x=(p-r)/2`, and use `alpha,beta in [0,1]`. Write
`A=p*alpha`, `D=r-p*alpha>0`, `U=p*(1-alpha)`, and
`c=sqrt((1-alpha)*(1-beta))`. Rescale the direct and image source triangles
by

```
B_direct = A+D*beta,       Jacobian_direct = p*D,
B_image  = A+U*beta,       Jacobian_image  = p*U.
```

Define `sinhc(t)=integral_0^1 cosh(v*t) dv`. This is smooth and positive
on all real `t`, equals `sinh(t)/t` off zero and has value one at zero.
Compact differentiation proves smoothness; positivity of `cosh` proves
positivity; the fundamental theorem of calculus proves the quotient
identity. This agrees with the corpus's positive removable `sinhc` in
`HTGeometry.ConstraintMotiveRelativity.PrimeGammaReesEventGerm`.

With `y_direct=(A-B_direct)/2`, `y_image=(A-B_image)/2`, put

```
H_direct = p*D*sinhc(U/2)*sinhc(D*(1-beta)/2)
           /(4*cosh(x)*cosh(y_direct)),
H_image  = p*D*sinhc(U*(1-beta)/2)*sinhc(D/2)
           /(4*cosh(x)*cosh(y_image)).
```

Both are strictly positive, including every square edge. The two original
circle radii are exactly

```
radius_direct = 2*arsinh(c*sqrt(H_direct)),
radius_image  = 2*arsinh(c*sqrt(H_image)).
```

Indeed the original invariant obeys
`invariant-1=2*sinh((p-A)/2)*sinh((r-B)/2)/(cosh(x)*cosh(y))`
for the direct channel. The image channel replaces those numerator
arguments by `(p-B)/2` and `(r-A)/2`. The displayed factorizations follow
from `sinh(t)=t*sinhc(t)`. Finally
`cosh(2*arsinh(v))=1+2*v^2` and nonnegativity identify the original
`arcosh` radius, including the characteristic edges where `c=0`.

On any sufficiently small compact neighborhood of a fixed `0<p<r`,
`H_direct` and `H_image` have positive lower bounds uniformly in the
unit square. Thus every ordered derivative in the physical parameters
`p,r,X,k` of the displayed radii and original circle-source integrands
exists and is continuous jointly with the integration parameters.
The nonsmooth factor `c` is an integration parameter and is never
differentiated. The original source is smooth in time, radial coordinate
and positive-height angular coordinates: its fixed smooth onset,
original amplitude, half-square and full gradient field remain present.
The two Jacobians are polynomial and the three integration intervals
(including the circle angle) are fixed and compact. Repeated dominated
differentiation proves joint `C-infinity` regularity of
`originalPotential q branch amplitude p r X k` on `0<p<r`.

This supplies the actual spacetime jets needed for mixed metric
reconstruction and the original action current. It
claims no boundary regularity at `p=0`, `p=r`, the horizon limit, or the
angular cusp, and supplies no current extinction or RH conclusion.

### A globally smooth representation for compact parameter integration

The same formula admits a global smooth extension in the physical and
auxiliary variables. Set `p=exp(u)`, `r=exp(u)+exp(v)`, replace
`alpha,beta` by `sin(a)^2,sin(b)^2`, and replace `c` by `cos(a)*cos(b)`.
The factors `H` are then strictly positive for every real `u,v,a,b`:
`r-p*sin(a)^2=exp(v)+exp(u)*cos(a)^2>0`. The resulting radius is globally
smooth. Negative cosines outside the integration chart cause no problem
for smoothness of `arsinh`; no radius identification is claimed there.

On the original unit square, take `a=arcsin(sqrt(alpha))` and
`b=arcsin(sqrt(beta))`. These maps are continuous, their squared sines
recover the original variables, and their cosine product equals the
original nonnegative edge factor. Thus the original integral is a
globally smooth function evaluated at continuous compact integration
parameters. Its original linear triangle Jacobians remain unchanged;
this uses no trigonometric change of integration variable. The existing
compact-parameter smoothness theorem applies directly to this extension.
Finally `u=log(p)` and `v=log(r-p)` recover the original physical chart.

The exact invariant factorization, positive factors, characteristic-edge
radius identity, smooth logarithmic radius and its original-chart recovery
are formalized in `ThetaCuspHawkingBMRetardedTriangleGeometry`.
Its exact leaf audit passes. `NativeAngularGreen.unitCube_integral_smooth`
exposes the already proved compact-parameter theorem; that leaf's audit also
passes. Neither audit rebuilds other source modules.

`ThetaCuspHawkingBMOriginalSpacetimeRegularity.originalPotential_smooth`
proves joint `ContDiffAt` of order infinity for the actual potential on
`0<p<r`. The complete original forcing is smooth through every positive
circle chart. Exact affine triangle rescaling and circle normalization
identify the smooth compact integral with the original retarded action,
then F94 identifies it with the constructed native potential. Both source
gradients and the fixed onset remain. Scratch verification and the exact
leaf audit pass at default proof budgets, and the module is wired.
Repository lint's sole error is the unrelated unreachable
`Sieve.KloostermanGlobalCollisionCoprime` module.

## The original causal source at the future horizon

**Lean closure:** `ThetaCuspHawkingBMRetardedHorizonGeometry` proves the exact
compact kernels, source cancellation and closed-square radius chart.
`ThetaCuspHawkingBMOriginalHorizonRegularity` identifies the complete
original action, proves its joint smooth extension and its actual horizon
limit. Both exact leaf audits pass. The derivation below displays their
mathematical content.

The following is an analytical smooth-extension proof, not yet Lean.
Keep the actual ingoing time `p>0` fixed and put `rho=exp(p-r)`.
For each source point set `z=exp(a-b)` and `E=exp(p-a)`. The original
target and source radial units are `(1-rho)/(1+rho)` and
`u=(1-z)/(1+z)`. Direct hyperbolic expansion gives the exact invariants

```
invariant_direct-1 = 2*(E-1)*(z-rho/E)/((1+rho)*(1+z)),
invariant_image-1  = 2*(E-rho)*(z-1/E)/((1+rho)*(1+z)).
```

In the direct triangle, `rho/E <= z <= 1`; in the image triangle,
`1/E <= z <= 1`. The source itself remains at the original, unreflected
radial coordinate. Since `db=-dz/z`, the original forcing's factor
`1-u^2=4*z/(1+z)^2` cancels this Jacobian exactly. For the original
angular fields `J=fullSquarePotential` and `K=fullGradientEnergy/2`, the
complete resulting source density is

```
-8*u/(1+z)^2 * power(2*s, 2/(1+z)) * amplitude^2 * timeOnset(2*s,a)
  * ((5*s^2+15*s+4)*J/4 + s*(s-1)*u^2*((s+2)^2*J-K)/4).
```

Every factor is smooth for `z>-1`, including `z=0`. Both original angular
fields and the entire fixed onset remain; no source term is discarded.
The action still has its factor `1/4` and direct-minus-image sign.

Set `a=p*alpha`, `alpha,beta in [0,1]`, and rescale

```
z_direct = rho/E + (1-rho/E)*beta,
z_image  = 1/E   + (1-1/E)*beta.
```

Their Jacobians are respectively `1-rho/E` and `1-1/E`. Both invariant
increments now have the common numerator
`2*(E-1)*(1-rho/E)*beta`, with their own denominator
`(1+rho)*(1+z)`. Write
`expc(t)=integral_0^1 exp(v*t) dv`, so
`E-1=p*(1-alpha)*expc(p*(1-alpha))`. The actual circle radii are

```
2*arsinh(sqrt((1-alpha)*beta)*sqrt(H)),
H = p*expc(p*(1-alpha))*(1-rho/E)/((1+rho)*(1+z)).
```

For `p` in any compact positive interval and `abs(rho)<1/2`, both `H`
are smooth and strictly positive uniformly on the whole unit square:
`E>=1`, `1-rho/E>0`, and both `1+z>0`. The edge factor depends only on
integration variables. Equivalently use the continuous inverse-sine
parameters above, with `cos(a)*sin(b)` as the edge factor. Compact
differentiation supplies a smooth continuation of the complete original
retarded potential across `rho=0`, in ingoing time and both angular
coordinates. Original-chart equality uses F94 for `rho>0`; no value of
`log(rho)` is used in the extension at or below zero.

Since the physical radius is `R=(1+rho)/(1-rho)`, this is regularity at
the actual future horizon `R=1`. For any smooth reconstructed stream
`P_A`, the original blocks `h_tA=f*partial_R P_A` and
`h_RA=partial_t P_A/f`, `f=R^2-1`, become
`h_pA=f*partial_R P_A+partial_p P_A` and `h_RA=-partial_R P_A`
in ingoing coordinates. The apparent horizon pole cancels with its
original coordinate transformation. This establishes the analytical
regularity mechanism for the causal reconstruction. It does not evaluate
or annihilate the horizon action current, prove the full sourced tensor
equation, or supply fixed-clock extinction.

## Horizon transport of the actual normal derivative

The smooth extension above and the proved original wave equation give an
exact boundary transport law. Write the same potential as `W(p,rho,X,k)`,
where `rho=exp(p-r)`, and let `F_compact` be the complete density displayed
above at the target point. The original source is `rho*F_compact`.
At fixed original `p`, `partial_r=-rho*partial_rho`; at fixed original `r`,
`partial_p=partial_p_new+rho*partial_rho`. Consequently

```
4*Z_pr = -4*rho*(W_p_rho+W_rho+rho*W_rho_rho),
1/cosh((p-r)/2)^2 = 4*rho/(1+rho)^2.
```

The interior equation therefore becomes

```
W_p_rho+W_rho+rho*W_rho_rho+Delta_H(W)/(1+rho)^2 = -F_compact/4.
```

Every term extends continuously to `rho=0` by the joint smooth extension,
so the actual horizon value satisfies

```
partial_p U + U = -Delta_H(W(p,0))-F_compact(p,0)/4,
U(p)=partial_rho W(p,0).
```

Here `Delta_H` acts on both original angular coordinates, and
`F_compact(p,0)` retains the full half-square, full gradient energy and fixed
onset. This is an analytical proof, not yet a Lean theorem. It determines
transport of the normal jet required by the original action current; it
neither sets that jet to zero nor supplies the missing physical pairing or
fixed-clock extinction.

## Complete stream current in regular ingoing coordinates

The existing `BMMixedRadialActionCurrent.stream_complete_action_current`
identifies all four original Einstein flux components with the stream
current. Its coordinate poles cancel exactly before taking a horizon
trace. Write `R` for physical radius, `f=R^2-1`, and use `p=t+tortoise(R)`.
All derivatives below are ingoing derivatives. For either full angular
stream `P`, put

```
M_P = R^2*f*P_RR + R^2*(P_pR+P_Rp) + 2*R*P_R - 2*R*P_p + A(P),
C_P = A(P)-M_P,
D_P = partial_X P_1-partial_Y P_0,
```

where `A` is the existing complete angular covector action, component by
component. The two ordered mixed derivatives are retained. The exact
static derivatives are `P_t=P_p`, `P_R_static=P_R+P_p/f` and
`P_RR_static=P_RR+(P_pR+P_Rp)/f+P_pp/f^2-2*R*P_p/f^2`.
Substitution in the existing master gives precisely `M_P` above.

The current's coordinate transformation has determinant one. Thus
`J^p=J^t+J^R/f`; the complete transformed current is

```
J^p = (1/R^2)*sum_A (P_A,R*C_Q,A-Q_A,R*C_P,A),
J^R = (1/R^2)*sum_A ((f*P_A,R+P_A,p)*C_Q,A-(f*Q_A,R+Q_A,p)*C_P,A),
J^X = -(Y^2/R^2)*(f*(P_1,R*D_Q,R-Q_1,R*D_P,R)
        +P_1,R*D_Q,p+P_1,p*D_Q,R-Q_1,R*D_P,p-Q_1,p*D_P,R),
J^Y = +(Y^2/R^2)*(f*(P_0,R*D_Q,R-Q_0,R*D_P,R)
        +P_0,R*D_Q,p+P_0,p*D_Q,R-Q_0,R*D_P,p-Q_0,p*D_P,R).
```

These identities follow by direct substitution in all four displayed
corpus current components: both inverse powers of `f` cancel in each
angular component, and the time pole cancels against `J^R/f`.
No field equation, angular integration or boundary cancellation is used.
For smooth ingoing streams the expressions therefore extend smoothly
across `R=1`. Their actual radial horizon flux is
`sum_A(P_A,p*C_Q,A-Q_A,p*C_P,A)` at `R=1`.
The two-jet identity is formalized in
`ThetaCuspHawkingBMIngoingFullCurrent.original_ingoing_current`, using the
existing complete Einstein action current. The exact module audit passed
and the leaf is wired into `RHTower`. `ActualIngoingCurrent` attaches this
formula to the actual reconstructed causal metric and every locally C²
testing stream. Every angular flux and original source contact is
retained; no extinction is asserted.

## Original left QNM: exact horizon power and surviving current coefficients

Put `u=1/R`, `v=1-u`, and let `w=physicalFundamentalFrequency(q,side)`.
The original fundamental radial identities give, for either normalization,
`Psi_w=z^(w/2)*sqrt(1-z)` with `z=1-u^2`.
The stream reconstruction multiplies by `R`, cancelling `sqrt(1-z)=u`.
In ingoing time `p=t_static+x`, the exact identity
`1-u=exp(2x)*(1+u)` therefore gives

```
Q_A(p,R,X,Y) = exp(-w*p)*v^w*V_A(X,Y),
V = literal coexact covector at physicalAngularParameter(q),
lambda = physicalAngularParameter(q)^2-1/4-2 = w*(w+3).
```

This is the original opposite-time-frequency left stream; both original
radial normalizations give this same expression. In particular, a regular
coordinate formula for the current cannot be specialized by treating both
streams as smooth at the horizon. The source field's proved smoothness
and this exact left-mode power must be used together.

Differentiation at positive `v` gives

```
Q_p = -w*Q,
Q_R = w*Q/(R^2*v),
f*Q_R+Q_p = (w/R)*Q,
A(Q)=lambda*Q,  M_Q=0.
```

The last master identity follows either from the original left-mode
Einstein equation or directly from these derivatives and the displayed
angular eigenvalue. Let `P` be the full ingoing source stream; retain its
original contact `C_P=A(P)-M_P` and curl `D_P=dX(P_1)-dY(P_0)`.
Writing `D_V=dX(V_1)-dY(V_0)` and `K=exp(-w*p)`, substitution in every
component of the complete current gives the exact decomposition

```
J^R = K*v^w/R^2 * sum_A V_A*(lambda*(f*P_A,R+P_A,p)-(w/R)*C_P,A),
J^p = K*v^(w-1) * sum_A V_A*(v*lambda*P_A,R/R^2-w*C_P,A/R^4),
J^X = -K*v^(w-1)*Y^2/R^2 *
  ((w*v/R)*(P_1,R*D_V-V_1*D_P,R)+(w/R^2)*(P_1,p*D_V-V_1*D_P,p)),
J^Y = +K*v^(w-1)*Y^2/R^2 *
  ((w*v/R)*(P_0,R*D_V-V_0*D_P,R)+(w/R^2)*(P_0,p*D_V-V_0*D_P,p)).
```

The causal stream used here is explicit. With `H=horizonPotential`, set
`Z_tilde(p,R,X,Y)=H(p,(R-1)/(R+1),X,log(Y))` and
`P=R*(partial_Y Z_tilde,-partial_X Z_tilde)`, retaining the original Xi,
branch and amplitude parameters of `H`. On the exterior horizon strip,
the proved value identity identifies `Z_tilde` with the original retarded
potential before taking derivatives.

For this reconstructed causal stream, all coefficients multiplying the
explicit powers are smooth at `v=0`, at fixed positive `p` and positive
angular height. This follows from the proved joint horizon
smoothness of the original causal potential, angular differentiation and
`R=1/(1-v)`. The assertion retains every master-source contact and both
angular fluxes; it does not require those coefficients to vanish.

There is a precise analytical endpoint consequence. Write these formulas
as `J^R=K*v^w*B_R(v)` and `J^j=K*v^(w-1)*B_j(v)` for `j=p,X,Y`.
Taylor's theorem gives

```
B_R(v)=B_R(0)+v*B_R'(0)+O(v^2),
B_j(v)=B_j(0)+v*B_j'(0)+v^2*B_j''(0)/2+O(v^3).
```

The original frequency theorem gives `Re(w)>-2`. For positive real `v`,
`abs(v^w)=v^Re(w)`, so subtracting exactly these coefficient terms leaves
`O(v^(Re(w)+2))`, which tends to zero. These are boundary terms derived
from the original current, not a replacement weighted observable.

The decomposition and Taylor consequence are analytical results pending
full Lean attachment to the reconstructed causal stream. They do not yet
identify these counterterms with `continuedHorizonSourceCounterterm`:
that corpus expression is a source-determined radial primitive after the
temporal transform. Exchanging that transform with horizon restoration,
retaining onset and cusp boundaries, remains an obligation. The proved
horizon smoothness covers `p>0`; this argument supplies no uniform estimate
through the onset corner `p=0`, no complete pairing and no fixed-clock
extinction.

The original left-factor identity, angular eigenvalue and actual time and
radial-chart derivatives are formalized in
`ThetaCuspHawkingBMLeftHorizonFactor`. Its theorem
`ingoingField_transport` proves `(partial_x+partial_p)Q=(w/R)*Q` for the
original field, where `x` varies the exact tortoise-radius chart at fixed
`p`. The exact module audit passed; the leaf is wired into `RHTower`.
The full current-coefficient substitution and its finite-part matching
have the analytical status stated above.
