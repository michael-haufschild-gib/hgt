# RN: arbitrary-anchor Schur cross positivity

Status: paper proof and Lean generalization complete; both targeted builds,
both final direct-file audits, and all29 public theorem axiom checks passed
on 2026-10-02.
Actual target: for 0<=a<x and a<y,

    H(a,x) H(a,y) < H(a,a) H(x,y).

This extends the audited center inequality to every nonnegative anchor. It is
the lower sign of the positive-node inverse-Gram coefficient, not its coordinate
upper bound, a three-node principal determinant, or RH.

## Corpus basis and novelty

`ThetaTailGaussianSubmodular` proves V_xy<0 on the nonnegative quadrant and
decreasing center amplitudes. `ThetaTailCenterSchurCross` integrates their full
positive covariance. The anchored amplitude was not covered by those statements.
The corpus search for coarea/anchored Schur/massRate returned partial deep
results with source-only metadata and a background refresh still pending.
Relevant hits were checked against the actual sources and then compiled;
the actual derivative below supplies the missing anchor term.

## Paper proof

Use the existing exact coarea V, L, t and R=H/(kx ky). For fixed u>0 and x>a>=0,
put s=a+t, r=x+t, L=s+r, P=p(s)+p(r), M=L(c(s)+c(r))-2P>0.
The exact derivative is

    d_x V_u(a,x,u) =
      [L((a+r)c(r)-(s-a)c(s))-(a+x)P]/L^3.

Its numerator decomposes as

    (x-a)(L c(r)-P) + L s(c(r)-c(s)) + a M > 0.

Here c(r)>c(s), s c(s)>p(s), r c(r)>p(r), and M>0 are
unconditional source consequences already used in the center proof. Thus
V_u(a,x,u)>V_u(a,a,u). The amplitude

    A[a,x](u)=exp(V(a,a,u)-V(a,x,u))

strictly decreases in u and lies in (0,1]. Integrating V_xy<0 over
[a,x]x[a,y] gives V(x,y)+V(a,a)<V(a,x)+V(a,y). Therefore

    density(x,y)>density(a,a) A[a,x] A[a,y].

All terms are integrable by the existing coarea theorem and domination by
density(a,a). Same-direction covariance gives

    R(a,x)R(a,y) <= R(a,a) integral density(a,a) A[a,x] A[a,y]
                  < R(a,a)R(x,y).

Cancel positive source factors. No covariance term is discarded.

## Remaining hard problem

The finite-pair coordinate-port upper bound still requires a compensated
derivative estimate. The new lower sign alone does not supply it. General
rank and transfer to the arithmetic off-diagonal kernel remain open.

## Formal certificate

Namespace: `RHTower.ThetaGaussianCoarea`.

- `ThetaTailGaussianSubmodular.lean`: generalized rectangle comparison,
  exact endpoint derivative of massRate, strict increase above every anchor,
  decreasing bounded anchored amplitudes, and strict product-density comparison.
- `ThetaTailCenterSchurCross.lean`: `anchored_schur_cross_pos` and
  `anchored_positive_node_coefficient_pos`. Existing center theorems remain
  specializations, and the covariance proof is shared rather than duplicated.

Both `lake --old build GaloisForLFunctions.RHTower.<leaf>` checks passed.
Both final `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean` checks
passed without diagnostics. All29 public theorem axiom queries in /tmp
returned only propext, Classical.choice, Quot.sound. Existing umbrella imports
cover both modified leaves; no new module or umbrella build was needed.
No numerical experiment, added axiom, heartbeat increase, subagent, or commit.

Formal lint found no violation in these leaves. It reported12 unrelated
unreachable modules: CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
RoutePNativeUndampedBalance, ThetaCuspC5PositiveDescentIntegral,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
