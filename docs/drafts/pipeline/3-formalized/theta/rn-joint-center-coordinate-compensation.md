# RN: joint-center coordinate compensation

Status: paper proof and exact Lean sign proof complete. Both targeted builds,
both final direct-file audits, and all20 public theorem axiom checks passed
on 2026-10-02.
This targets the necessary compensation sign left open by the fixed-y
confluent theorem. It does not yet prove finite-pair propagation.

## Literal quantities

Let k be the actual source, p=-(log k)', c=p', v=c', q=c(0),
P=k(0)^2, I=integral t*k'(t)^2, S=integral t*k''(t)^2,
J=H(0,0)=2 integral t*k(t)^2. All integrals are over t>0.
The target is

    D=S/6-2qI+2qP/3+I^2/J > 0.

The joint Taylor diagnostic in rn-center-schur-coordinate-row-flow.md
identifies -D/P as the leading diagonal E_y coefficient. That Taylor
identification remains a separate formalization obligation.

## Corpus inputs

ThetaConfluentCoordinateCurrent proves actual slopeEnergy=c^2-q^2-pv>0
and chordReserve=p(c+2q)-qt(2c+q)>0 for t>0. Its proof uses the actual
projective reserve cc'-pc''>0. ThetaConfluentCoordinateEnergy supplies
the Schwartz polynomial integral identities and vanishing logarithmic flux.
Deep searches found these exact ingredients and weighted_second_integral;
no sign for D was returned. Results were checked against source; compiler
metadata was source-only and refresh pending.

## New positive current

Define

    G=pc+3tc^2-tpv-12qtc+20qp-12q^2t.

The exact decomposition is

    G=t*slopeEnergy + (c+20q)/(c+2q)*chordReserve
        +2t(c-q)^3/(c+2q) > 0.

All denominators and summands have proved source signs. This is stronger
than reusing coordinateEnergy>0 alone.

Let F=2S-12qI+8qP-3q^2J. Integration by parts, retaining the existing
logarithmic flux t*k'^3/k, gives integral G*k^2=2F>0. Avoid assuming
integrability of logarithmic quotients: subtract the Schwartz polynomial
gap t*k'^2-t*k*k''+3*k*k'+2qt*k^2 from the existing polynomialCurrent,
with multiplier 6q, and use its exact boundary flux.

Equivalently, F=2*coordinateEnergy-3q*delta, where
delta=2I+qJ-2P is the unresolved integrated diagonal-comparison sign.
The current pays its possible adverse contribution. Resolving delta's sign
is therefore unnecessary for this joint-center compensation theorem.

Finally the actual inverse-Gram term completes an exact square:

    D=F/12+(I-qJ/2)^2/J > 0.

No variance correction is discarded and no numerical bound is required.

## Outstanding scope

The exact source sign is formalized and audited. Identify the joint
Taylor coefficient in Lean and attack finite positive old-node spacing;
arbitrary-rank positivity and arithmetic RH transfer remain open.

## Formal certificate

Namespace: `RHTower.ThetaCoordinate`.

- `ThetaConfluentCoordinateCurrent.lean`: `jointCoordinateCurrent_decomposition`
  and `jointCoordinateCurrent_pos`.
- `ThetaConfluentCoordinateEnergy.lean`: `jointCoordinateEnergy_pos`,
  `jointCoordinateCompensation_decomposition`, and `jointCoordinateCompensation_pos`.

The Energy leaf retains the literal J=thetaTailFirstMomentKernel 0 0 and
imports ThetaTailTwoPointPositivity explicitly. A shared private flux lemma
now proves both the previous coordinateEnergy sign and the new linear energy
sign; all previous public statements are preserved.

Both targeted `lake --old build GaloisForLFunctions.RHTower.<leaf>` checks
passed. Both final `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean`
checks passed without diagnostics. All20 public theorem axiom queries in /tmp
returned only propext, Classical.choice, Quot.sound. Both modified leaves
were already imported by RHTower. No full/umbrella build was run.
No numerical experiment, extra axiom, heartbeat increase, subagent, or commit.

Formal lint found no violation in these leaves. Its12 unrelated reachability
errors at this audit were CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
SuzukiSpectralMarginLimit, SuzukiSpectralMarginSource,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.

## Next consequence: uniform small triangular chamber (paper plan)

Use R(x,y)=H(x,y)/(k(x)k(y)), C=R(0,0), h(y)=R(0,y), and
E(x,y)=(R(x,y)-h(x)h(y)/C)/(xy), extended smoothly across the axes by
double integration of the mixed derivative. Its center Hessian should be

    E_yy(0,0)=-2*coordinateEnergy/(3P)<0,
    E_yx(0,0)+E_yy(0,0)=-D/P<0,
    E_y(0,0)=0.

Continuity preserves both strict Hessian signs in one neighborhood. For
0<=z<=y in that neighborhood, radial integration yields

    E_y(z,y)=integral_0^1 [z*(E_yx+E_yy)(tz,ty)
                            +(y-z)*E_yy(tz,ty)] dt < 0.

Then 0<z<y<epsilon implies E(z,y)<E(z,z), hence the actual coordinate
port is positive. This avoids nonuniform fixed-y coalescence thresholds.
The Hessian calculation, smooth axis extension, and actual residual
identification are still Lean obligations; no uniform chamber theorem is
currently claimed.

For the source port, set L(y)=(C-h(y))/y. The expected L'(0) is
(2I-qJ)/(2P)>0 (use qJ<=P<2I). On a smaller neighborhood L increases.
In normalized projection coordinates, d1<y/z from the coordinate port,
and L(y)>L(z)>0 imply
1-h(y)/C-d1*(1-h(z)/C)>0, proving the source port as well.
