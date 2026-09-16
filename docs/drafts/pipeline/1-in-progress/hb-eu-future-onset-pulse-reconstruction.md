# Future source reconstruction through the fixed onset pulse

Target: full temporal/metric/QNM matching. ES proves the corrected future
field's original bulk equation; ET identifies the admitted retarded inverse
with the actual original field and retains the cap in the causal pairing.

[FORMALISED SCALAR BRIDGE] Future reconstruction is the following exact source identity.
Write `s=physicalRate(q,branch)`, `kappa=parameter(q,branch)`,
`B=fullAngularField(q,branch)`, `Seed=timeAngularSeedField(q,branch,a)` and
`P=fullSourceOnsetPulse(q,branch,a)`. Let `A_Q` be the existing actual future
response of `timeReducedCoefficient*fullSquarePotential`.

Define `A_P` independently as the actual future integral of
`onsetDirichletKernel(q,branch,a,tau+h,y,h,x,y,X,k)` over `h>0,y<0`.
Define `H_B(v;tau,x,z)` as the direct-minus-image source-horizon kernel
with the circle mean of `B` replacing the circle mean of the theta square;
retain the kernel factor `1/2` and characteristic indicators
`v>=tau+x`, `v>=tau-x`.

The seed's horizon coefficient is
`cSeed=-kappa*power(2*s,2)*a^2`: the inspected radial polynomial at
`u=1`, `lambda=kappa=(2*s+1)*(2*s+2)`, is exactly `-kappa`.
The independently specified seed cap is

```
CSeed = -2*cSeed * integral_(v>0) timeOnsetFirst(2*s,v)*H_B(v).
```

Verified scalar bridge:

```
kappa*A_Q + Seed = A_P + CSeed.
```

Together with the already constructed lift cap `CLift`, this gives algebraically

```
correctedFutureField = timeLiftField - Seed/kappa
                    + A_P/kappa + CSeed/kappa - CLift.
```

**Exact input, already proved in the corpus:**
`FullSourceOnsetReduction.fullSourceOnset_wave_identity` and original
gradient absorption imply `wave(Seed)=P-kappa*S*Q` with actual derivatives.
`fullSourceOnsetPulse_transition` expresses `P` using the derivative of the
original smooth transition; `fullSourceOnsetPulse_zero_outside` confines it
to ingoing time `v=tau+x` in `[0,1]`. ET's `retardedResponse_onset_pulse`
attaches the corresponding proved retarded reconstruction to the admitted
source-event inverse. None of these statements supplies the future identity.

**Analytical mechanism to test:** integrate the seed wave identity against
the actual future kernel on finite source regions. Retain every boundary
term, then prove its limit equals the independently defined `CSeed`.
Do not infer this from equality of bulk wave equations or define the cap
as the discrepancy.

For pulse admission, change source coordinates to `(v,y)` with `v=t_source+y`.
The exact existing invariant formula is

```
I(v-y-tau,x,y)
  = [cosh(v-tau)+(sinh(v-tau)-sinh(x))*radialUnit(y)]/cosh(x).
```

For `v in [0,1]`, `y<0` and compact target variables, `radialUnit(y) in [0,1]`
makes this a compact parameter family; the image uses `x -> -x`.
Thus the circle radius stays bounded even at the infinite source corner.
The inspected definitions `amplitudeRate(s,0,u)=2*s*(u-1)` and
`sourceSeedFieldFirst` expose factors vanishing at `u=1` in the pulse
coefficients. A bound proportional to `exp(2*y)` is the proposed integrable
majorant. Pulse admission is now verified by the product estimate below;
admission of differentiated metric/current kernels still requires proof. The characteristic supports and
seed-cap limit are verified below. Pulse localization alone does not
justify discarding a horizon current.

Current status: the finite future seed Green identity and its original
pulse-minus-source balance are Lean verified in
[FutureSeedFiniteGreen](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFutureSeedFiniteGreen.lean).
The actual angular mean growth and its integrable physical-clock majorant
are Lean verified in
[FullAngularMeanGrowth](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullAngularMeanGrowth.lean).
The independent seed cap is absolutely admitted, its actual terminal
limit is proved, and the finite original pulse-minus-source actions have
the exact null-exhaustion limit `Seed-CSeed`, all Lean verified in
[FutureSeedHorizonCap](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFutureSeedHorizonCap.lean).
Pulse admission and exhaustion of the original future integral by outgoing
source cuts are Lean verified in
[FuturePulseAdmission](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFuturePulseAdmission.lean).
Those cuts are identified with the finite null Green action in
[FutureSourceBridge](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFutureSourceBridge.lean).
Its `future_source_balance` proves the complete scalar bridge for all real
times, every nonnegative radial depth, both physical branches and arbitrary
source amplitude and angular base point. Full temporal/metric/QNM matching
and RH remain open. The finite upper direct pulse now has an exact smooth
two-triangle representation through its characteristic corner, verified in
`ThetaCuspHawkingBMFuturePulseCorner`; see
[future pulse corner regularity](hb-fa-future-pulse-corner-regularity.md).
The remaining pulse regions and the exact vanishing of the outgoing compact
cutoff strips are verified in `ThetaCuspHawkingBMFuturePulseAssembly`; see
[full future pulse assembly](hb-fb-full-future-pulse-assembly.md).
`ThetaCuspHawkingBMFuturePulseIdentity` identifies the full compact action
with the admitted original response and proves its joint smoothness in
physical interior coordinates. Cap regularity and noncompact left-QNM
admission remain required for full differentiated matching.
`ThetaCuspHawkingBMFixedSourceHorizon` now puts both independently specified
caps in one fixed source-radius representation and factors their late weights
through a smooth compact parameter. The resulting temporal/radial regularity
proof and the still-open angular admission are specified in
[fixed-source horizon matching](hb-fd-fixed-source-horizon-matching.md).

## Finite future Green identity with the actual terminal face

Fix `x<0`, `p=tau+x`, `r=tau-x` and a cutoff `L>max(r,0)`.
Use source null coordinates `v=t_source+y`, `w=t_source-y`. Thus
`y=(v-w)/2`, `h=(v+w)/2-tau`, and `dt_source dy=(1/2) dv dw`.
The direct and image source regions cut at `w=L` are exactly

```
D_L = { r <= w <= L, p <= v <= w },
I_L = { r <= w <= L, r <= v <= w }.
```

Let `f(y)=sourceSeedField(s,0,a,1,kappa,y)`, `o(v)=timeOnset(2*s,v)`,
and `b(v,w)=f((v-w)/2)*o(v)`. The letter `a` remains the original
amplitude. Let `K_D(v,w)` and `K_I(v,w)` be the circle means of `B` at
the direct and image radii, respectively, **without** the factor `1/2`.
The reciprocal closed-cone Goursat identity already proved in
[FullAngularGoursat](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullAngularGoursat.lean)
supplies their mixed source derivatives, including one-sided cone edges.
It gives

```
K_D(v,r)=B(z),       partial_w K_D(p,w)=0,
partial_w K_I(r,w)=0,
K_D(v,v)=K_I(v,v),   b(v,v)=0.
```

The first identity is used only for `p<=v<=r`; the two derivative
identities are used on their respective characteristic edges. The
source-circle mean of `wave(Seed)`, multiplied by `1/4`, is
`K*b_vw-b*K_vw`: one factor `1/2` comes from the physical kernel and the
other from the null-coordinate Jacobian. Its exact divergence is

```
K*b_vw-b*K_vw = partial_w(K*b_v)-partial_v(b*K_w).
```

Integrating first over `D_L`, the lower characteristic segment contributes
`B(z)*b(p,r)`. Its diagonal contributes
`-integral_(r..L) K_D(v,v)*b_v(v,v) dv`. The remaining contribution is
`integral_(p..L) K_D(v,L)*b_v(v,L) dv`.
The `partial_v` boundary terms vanish by `b(v,v)=0` and
`partial_w K_D(p,w)=0`. Integrating over `I_L` gives the corresponding
terminal integral over `r..L` and the image diagonal, with no vertex
term. The two diagonals cancel exactly. Therefore, with `A_W^L` the
actual truncated future integral of `wave(Seed)`,

```
A_W^L = Seed(tau,x,z) + T_L,
T_L = integral_(p..L) K_D(v,L)*b_v(v,L) dv
    - integral_(r..L) K_I(v,L)*b_v(v,L) dv,
b_v(v,L) = f'((v-L)/2)*o(v)/2 + f((v-L)/2)*o'(v).
```

This orientation of Green's identity leaves **no derivative of the
angular kernel** in `T_L`. The theorem `finite_future_seed_wave` formalises
this exact boundary expression. The theorem `finite_future_source_balance`
identifies its left side with the original pulse minus `kappa*S*Q`,
using the actual wave identities and positive-height source circles.
Both public theorems quantify over the original Xi copy, branch and
amplitude; nonnegative width and terminal span encode geometric bounds.
No wave, matching or vanishing-terminal premise is supplied.

## Angular-mean growth from its actual forced equation

Put `g=sourceGrowthExponent(q)` and `gamma=(g+2)/2`, the existing
`decayExponent(q)`. For the fixed angular base point write
`M(d)=angularMean(q,branch,d,X,k)` and `N(d)=NativeCircle.mean(q,d,X,k)`.
The inspected theorem `angularMean_forced` gives, for `d>0`,

```
M'' + coth(d)*M' = kappa*(M+N).
```

The actual characteristic roots of its constant limiting equation are
`nu=2*s+1` and `mu=-2*s-2`. Their difference `delta=4*s+3` is nonzero:
`-2<Re(s)<-1` makes `Re(delta)<-1`.
Writing `b0=Re(q.1)`, the corpus definitions give

```
g=max(2*b0,2-2*b0),
Re(mu)=2*b0 or 2-2*b0,
Re(nu)<-1,          Re(mu)<=g<gamma<2.
```

These are consequences of the proved open Xi strip, not RH. Define

```
Z_nu=(M'-mu*M)/delta,     Z_mu=(nu*M-M')/delta,
epsilon(d)=coth(d)-1=2/(exp(2*d)-1),
F(d)=kappa*N(d)-epsilon(d)*M'(d).
```

Direct differentiation yields
`Z_nu'=nu*Z_nu+F/delta`, `Z_mu'=mu*Z_mu-F/delta`,
`M=Z_nu+Z_mu`, and `M'=nu*Z_nu+mu*Z_mu`.
Integrate these two first-order equations from `1` to `d>=1`.
The existing `mean_global_growth` bounds `|N(t)|` by `C exp(g*t)`
at the fixed base point. With
`V(d)=exp(-gamma*d)*(|Z_nu(d)|+|Z_mu(d)|)`, the two integrating-factor
identities and `Re(nu),Re(mu)<gamma` give

```
V(d) <= C0 + C1 * integral_(1..d) epsilon(t)*V(t) dt.
```

Here the source contribution is uniformly bounded by a constant times
`integral_(1..d) exp((g-gamma)*t) dt`, which is bounded since `g<gamma`.
Also `epsilon(t)<=2*exp(-2*t)/(1-exp(-2))` for `t>=1`.
For completeness, set `Y(d)=C0+C1*integral_(1..d) epsilon(t)*V(t) dt`.
Then `V<=Y` and `Y'<=C1*epsilon*Y`; differentiating
`Y(d)*exp(-C1*integral_(1..d) epsilon)` bounds it by `C0`.
Thus `V` is bounded on `[1,infinity)`. Smoothness on `[0,1]` gives

```
|M(d)|+|M'(d)| <= C*exp(gamma*d)       (d>=0).
```

The constant may depend on `q,branch,X,k`; this is not a global bound
uniform in angular position. Compact sets of angular base points permit
uniform constants by continuity of the initial means and their radial
derivatives. No lower bound on a Legendre function, spectral projection,
or numerical estimate enters this derivation.

An equivalent energy proof uses unscaled modes
`A=M'-mu*M`, `B=M'-nu*M` and `E=|A|^2+|B|^2`. Both equations have the
same forcing `F=kappa*N-(coth(d)-1)*M'`. With
`eta=gamma-g>0` and `K=(|nu|+|mu|)/|nu-mu|`, the exact mode identities
give `|M'|<=K*(|A|+|B|)`. Young's inequality then gives

```
E' <= (2*g+eta+4*K*(coth(d)-1))*E + (2*|kappa|^2/eta)*|N|^2.
```

The existing `CothInfra.rcoth_lt_one_add_inv` bounds the hyperbolic
excess by `1/d`. On `d>=max(1,4*K/eta)`, this yields
`E'<=2*gamma*E+C*exp(2*g*d)`. Thus
`exp(-2*gamma*d)*E + C/(2*eta)*exp(-2*eta*d)` is nonincreasing there.
This gives the same growth bound, with the finite initial interval
handled by continuity. This alternative avoids a variable-coefficient
Volterra theorem while preserving the characteristic growth exponents.
This energy argument is Lean verified for the actual field in
`FullAngularMeanGrowth.angularMean_growth`. The theorem supplies constants
at each fixed angular base point; the compact-uniform angular extension
described above remains a paper statement.

The geometry admits a stronger uniform estimate than a compact-target
bound. For `v>=0,y<=0` and **every** real target radius `x`,

```
arcosh(max(1,I(v-y-tau,x,y))) <= v+|tau|+log(4).
```

Indeed, the exact invariant formula is affine in `u=radialUnit(y) in [0,1]`.
The combination `cosh(v-tau)+u*sinh(v-tau)` is a convex combination of
`exp(v-tau)` and `exp(-(v-tau))`, both bounded by `exp(v+|tau|)`.
Also `-u*sinh(x)<=cosh(x)` and `cosh(x)>=1`, giving
`I<=2*exp(v+|tau|)`. Comparison with `cosh(v+|tau|+log(4))` proves the
radius bound. `source_horizon_radius_bound` formalises this argument.
The theorem `angularMean_source_horizon_majorant` combines it with the
actual growth estimate: `exp(2*Re(s)*v)*(|M|+|M'|)` has an integrable
majorant `C*exp((2*Re(s)+gamma)*v)` uniform in both radial variables.
The angular base point is fixed. The image kernel uses the same bound
with target radius `-x`.

## Admission of the fixed pulse

For `u=radialUnit(y)` and `y<=0`,
`u=(1-exp(2*y))/(1+exp(2*y))`, so
`|1-u|<=2*exp(2*y)` and `|1-u^2|<=4*exp(2*y)`.
The actual seed polynomial at `lambda=kappa` is `-kappa*u`.
Consequently

```
f(y)=-kappa*a^2*power(2*s,1+u)*u,
f'(y)=-kappa*a^2*power(2*s,1+u)
        *(2*s*(u-1)*u+(u^2-1)).
```

The positive base `1+u` lies in `[1,2]`; its complex power is bounded.
The inspected `liftFirstPolynomial(s,0,u)` also contains `u-1` or
`u^2-1` in every term. Hence `|f'(y)|+|radialLiftFirst(s,0,a,1,y)|`
is bounded by `C exp(2*y)` on the entire negative ray.

The proved pulse transition formula contains exactly these derivatives
times circle means and `smoothTransition'(v)*exp(2*s*v)`. Its support
has `v in [0,1]`. On this interval the invariant formula in the first
part of this card confines both causal circle radii to a compact
interval, uniformly in `y<0`. The actual smooth angular fields therefore
have bounded means there. In coordinates `(v,y)`, whose Jacobian has
absolute value one, the pulse kernel is bounded by

```
C * indicator_[0,1](v) * exp(2*y) * indicator_(y<0).
```

This is integrable. Thus the independently defined `A_P` is absolutely
convergent, and its truncations by `t_source-y<=L` converge to `A_P`.
This argument proves admission of the pulse values; it does not assert
admission of all differentiated metric/current kernels.

A second paper proof now follows directly from the verified global angular
growth estimate, without using the compact transition support to change
integration coordinates. Set `alpha=(gamma+2)/2`, so `gamma<alpha<2`.
The original derivative has the exact horizon factorisation

```
f'(y)=exp(2*y)*kappa*power(2*s,1+u)*amp^2*(1+u)*((2*s+1)*u+1).
```

This follows from `1-u=exp(2*y)*(1+u)` and the displayed derivative above.
The remaining profile is continuous on `[0,1]`. The existing theorem
`radialLiftFirst_horizon` gives
`2*radialLiftFirst(s,0,amp,1,y)=exp(2*y)*sourceHorizonProfile(s,amp,1,u)`
with another profile continuous on `[0,1]`.
The transition factor satisfies
`smoothTransition'(v)*exp(2*s*v)=timeOnsetFirst(2*s,v)-2*s*timeOnset(2*s,v)`.
The inspected `timeOnset_pair_bound` therefore bounds it by
`C exp(-alpha*v)` at the unchanged physical rate.
For each original direct/image causal cone the circle radius is at most
`h`; `angularMean_growth` and `mean_global_growth` bound both circular
channels by constants times `exp(gamma*h)` at the fixed angular base point.
Thus the actual kernel
`onsetDirichletKernel(q,branch,amp,tau+h,y,h,x,y,X,k)` has the bound

```
C * exp(-alpha*tau) * exp((gamma-alpha)*h) * exp((2-alpha)*y),
                         h>0, y<0.
```

This product is integrable in the original future time/radius coordinates.
`FuturePulseAdmission.seedFirst_horizon`, `density_bound`, and
`density_integrable` formalise the exact factorisation and absolute admission.
The earlier compact-support argument remains valid. The constants depend on
the angular base point; no uniform angular estimate is asserted.

`futureRegion(tau,L)` is the original region `h>0,y<0,tau+h-y<=L`.
Its monotone union over real `L` is the entire original future region.
`truncatedResponse_limit` proves convergence to the independently defined
`A_P`; `sourceBalance_limit` proves convergence of the original cut
pulse-minus-source integral to `A_P-kappa*A_Q`. Both are Lean verified
using actual absolute admission. `FutureSourceBridge.finite_source_balance_coordinates`
identifies these cuts with `FutureSeedFiniteGreen.finiteFutureAction`.

## Limit of the retained terminal face

The explicit seed formulas give `f(y)->cSeed` and `f'(y)->0` as
`y->-infinity`. For fixed `v`, therefore,
`b_v(v,L)->cSeed*o'(v)`.
The exact invariant formula gives the direct horizon argument
`(exp(v-tau)-sinh(x))/cosh(x)` and the image argument with the plus sign.
The circle means converge by continuity, with the original characteristic
indicators retained.

For a dominating function, both causal invariants for `v>=0`, `y<=0`
are at most `C exp(v)`; hence both radii are at most `v+C'`.
The angular estimate above bounds `K_D,K_I` by `C'' exp(gamma*v)`,
uniformly over the terminal faces. The seed and its first derivative
are bounded on `y<=0`, and the original onset satisfies
`|o(v)|+|o'(v)|<=C exp(2*Re(s)*v)` for `v>=0`, with both zero for
`v<=0`. After extending each terminal integrand by zero outside its
interval, an integrable common majorant is

```
C * indicator_(v>0) * exp((2*Re(s)+gamma)*v).
```

Its exponent is strictly negative because `Re(s)<-1` and `gamma<2`.
Dominated convergence therefore gives the independently defined cap,
with its original factor and sign:

```
lim T_L = 2*cSeed * integral_(v>0) o'(v)*H_B(v) = -CSeed.
```

This terminal limit is Lean verified by
`FutureSeedHorizonCap.seedTerminal_horizon_limit` for the actual
`FutureSeedFiniteGreen.seedTerminal`. The definitions `halfKernel`,
`horizonKernel`, `seedTraceCoefficient` and `seedCapField` are independent
of the terminal integral. `seedCap_integrable` proves absolute admission;
the moving direct/image arm integrals converge by dominated convergence
on the fixed domain `v>0`. Their equality with the original interval
integrals includes the source-coordinate identities and characteristic
inequalities. No terminal face is set to zero.

The theorem `finite_source_balance_limit` proves that the original finite
pulse-minus-source actions converge to `Seed-CSeed`.
`FutureSourceBridge` identifies the original cut integral with that finite
null action using `v=tau+h+y,w=tau+h-y`. Open and closed source boundaries
agree almost everywhere. The direct cone becomes
`p<=v,r<=w,v<=w,w<=L`; the image becomes `r<=v<=w<=L`.
Indicator/Fubini decomposition gives the exact rectangle-plus-triangle
integrals, retaining Jacobian `1/2` and kernel factor `1/2`.
Both individual cone integrals are admitted before subtraction.

The original cut integral also tends to `A_P-kappa*A_Q` by absolute
admission. Uniqueness of the limit proves in Lean

```
kappa*A_Q + Seed = A_P + CSeed.
```

**Whole-route consequence:** this verified identity reconstructs the actual
future field from the same original seed and fixed pulse used by the
retarded field, retaining an independently determined horizon cap. It
does not yet identify the differentiated future metric/current or its
noncompact left-QNM action. The remaining target is to prove the required
regularity and admission for the physical metric/current and identify its
noncompact left-QNM pairing. `OriginalAngularCurrent.ofField_germ` already
transfers ordered two-jets once the relevant fields agree on a neighborhood;
it does not supply regularity or integrability by itself. No matching or
decay premise may replace those remaining proofs.

## Source and method checks

The finite Goursat primitives, actual angular mean equation, physical-rate
definitions, seed/lift derivatives, and source mean bound above were
checked in their Lean sources. The new finite Green assembly passed a
scratch check with no errors or warnings and the exact
`ThetaCuspHawkingBMFutureSeedFiniteGreen` leaf audit in 36.61 seconds,
two jobs, no warnings. Its umbrella import is wired; no umbrella build
was run. This audit does not cover the paper-only infinite-limit assembly.
The actual angular growth, physical-clock majorant and uniform radial
radius bound passed a warning-free scratch check and the exact
`ThetaCuspHawkingBMFullAngularMeanGrowth` leaf audit in 19.25 seconds,
two jobs, no warnings. Its umbrella import is wired without a build.
The seed bounds/limits, independent cap admission, actual terminal limit
and original null-exhaustion limit passed a warning-free scratch check
and the exact `ThetaCuspHawkingBMFutureSeedHorizonCap` leaf audit in
28.91 seconds, two jobs, no warnings. Its umbrella import is wired without
a build. The actual pulse admission and outgoing-cut exhaustion passed
the `ThetaCuspHawkingBMFuturePulseAdmission` scratch check in 43.68 seconds
and exact leaf audit in 65.20 seconds, two jobs. The audit emitted an
informational `ring_nf` suggestion, with no errors or warnings. Its
umbrella import is wired without a build. The audited source matches
the repository leaf. The coordinate identification and complete scalar
bridge passed a warning-free scratch check in 74.69 seconds and exact
`ThetaCuspHawkingBMFutureSourceBridge` audit in 25.57 seconds, two jobs.
The audited source matches the repository leaf; its umbrella import is
wired without a build.
Current repository lint reports unreachable
`ThetaCuspHawkingBMOnsetTransgressionHorizon` and
`MobiusDivisorQuadraticCompletionSPEWeld`, plus file-size warnings; it
reports no error for the new leaf. Both unrelated modules are unchanged
by this work.
Deep searches for Goursat and future Green mechanisms completed; the
terminal-boundary search returned partial results. Retrieved methods
requiring vanishing endpoints do not apply to this terminal face.
Search compiler coverage contains mostly source-only/pending entries;
retrieval alone is not formal verification.

The moving-boundary deep search completed and recovered dominated-convergence
methods. The seed/horizon search was partial and recovered the existing
`invariant_source_horizon`; composing it with the actual full angular mean
supplied the kernel limit in `FutureSeedHorizonCap`. The new proof checks
the common bound, measurability, moving supports, seed limits and interval
identification explicitly. Search metadata remained mostly source-only.
Broad asymptotic-completeness/trace searches also led to
[on-shell amplitudes and black-hole perturbations](https://arxiv.org/abs/2608.11703)
(12 August 2026). No result from that paper is used in this formalisation.

The broad energy-method search recovered the weighted-energy monotonicity
proofs in `ProlateTurningLayer` and `HTGeometry.KleinGordonAdiabatic`.
The interval monotonicity argument was instantiated afresh for the actual
forced complex modes; none of those theorems' unrelated operator hypotheses
was imported. The energy search completed; the boundary-method search was
partial and did not discharge the terminal-limit obligations. Both used
snapshot coverage with mostly pending/source-only compiler metadata.

Broad arXiv searches for dissipativity and resolvent found
[asymptotically hyperbolic resolvent estimates](https://arxiv.org/abs/2609.14914)
(14 September 2026) and
[dissipative stochastic averaging](https://arxiv.org/abs/2608.23462)
(24 August 2026). No theorem from these papers is used in the Lean proof;
the two-mode estimate and uniform radial enclosure above follow from the
inspected corpus equations.

The deeper reciprocal-circle method search recovered the existing
closed-cone Goursat primitives. They were instantiated and verified in
the new leaf. Its terminal face comes from source derivatives and exact
integral identities, without increasing heartbeats or changing instances.

Broad arXiv searches for radiation, characteristic, and compactification
included [metric compactification](https://arxiv.org/abs/2608.15508) and
[compactification independence](https://arxiv.org/abs/2608.06234), both
August 2026. Their stated theorems concern different geometric objects;
neither is used as a premise or a transferred theorem here.
The broad transmutation search also returned
[a diffusion/wave propagator transform](https://arxiv.org/abs/2601.03616),
revised June 2026. Its positive-operator setting does not supply the
source-domain identities or cap limit used here; no theorem is transferred.

The coordinate deep search returned partial results; the indicator/Fubini
search completed. `Zeta23.PrimeSide.sqIntegral_shear` supplies the method
of transporting an indicator through a measure-preserving chart;
`HTGeometry.TriangularIntervalFubini` supplies the interval-intersection
method. Their stated integrands differ from the full source here, so the
required general source argument is proved in `FutureSourceBridge`.
Search coverage was a snapshot with mostly pending/source-only compiler
metadata; the new instances were checked in Lean. A broad regularity
search also recovered the existing `nativeMean_joint_smooth`; it concerns
the native mean and does not by itself establish differentiated admission
of the full future field.
