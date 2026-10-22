# SZ: source collapse under every raised metric shift

- **ID:** SZ-RAISED-SHIFT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route SZ; actual prescribed-shift full-carrier classification.
- **Statement:** Every nonnegative increment of the actual prescribed metric shift retains the zero carrier limit on the interior imaginary segment, uniformly over the increment schedule.

## Hard problem and failed attack

Unshifted actual canonical-head signed Gamma–prime–polar positivity remains open. Ground-state stationarity alone does not determine this sign: adding a scalar to the operator preserves its ground vectors and all normalized variational differences. No stationarity wrapper was added. The exact coherent phase square still contains the unknown signed gap; its separate chi-square budget is already disproved in the corpus.

The new question concerns genuine shift selection after the prescribed carrier collapse: can increasing the coercive shift recover the Xi target? This is not a change of exponential source parameter. The construction below changes the resolvent of the same actual Friedrichs operator.

## Corpus evidence

Search1190250 (joint phase),1190318 (ground stationarity),1190336/1190344 (checkpoint) and1190351 (shift resolvent) were partial, with source-only applicability and compiler enrichment pending. Candidate statements and source arguments were inspected; no new mathematical sign theorem was inferred from retrieval. Direct source inspection verified the actual covariance positivity and shift equation, the mixed Gram limits and the prescribed source-profile limit. The checkpoint convexity receiver does not supply the missing prime moment sign.

## Dependency-closed paper proof of the source law

Fix aperture a. Write A for the actual interval Friedrichs operator,
c=norm(B)+1, C=(A+c)^(-1), p for the literal exp(x) source, and t>=0.
The bounded operator T=I+tC is coercive: Re<Tv,v> >= norm(v)^2.
It is invertible and its inverse R is a contraction. Set x_t=C R p.
The existing actual covariance equation gives

    (A+c+t)x_t = R p+t C R p = p.

Thus x_t is an actual solution for the raised metric shift, with no assumed
source or inverse equation. Since C commutes with T, direct expansion gives

    T((c+t)x_t-p) = c C p-p.

Consequently norm((c+t)x_t-p) <= norm(c C p-p), for every t>=0.
This is an exact source-defect contraction, independent of the size or
regularity of the shift increment schedule.

For any schedule t(a)>=0, the audited prescribed profile and
c_a<=K exp(a) imply

    exp(-a) norm((c_a+t(a))x_t-p_a) -> 0.

For 1/2<s<1, both testing vectors p_(+s),p_(-s) have norm<=exp(sa).
After multiplication by exp(-(1+s)a), both complex pairing errors tend
to zero. The exact mixed Gram laws then give

    (c+t)exp(-(1+s)a)<p_s,x_t> -> 1/(1+s),
    (c+t)exp(-(1+s)a)<p_-s,x_t> -> 0.

Their quotient, and hence the literal Fourier quotient carrier on z=is,
tends to zero for every such s. No reality assumption on the response,
Schur property for the new family, or bound on t(a) is needed here.

The Xi target has a nonzero derivative at I by its audited positive first
defect. The derivative's punctured-neighborhood nonconstancy supplies an
s in (1/2,1) with XiTarget(is) nonzero. Thus even pointwise convergence to
Xi on this segment is impossible for every cofinal raised-shift schedule;
locally uniform convergence on the upper half-plane is excluded as well.
This argument uses no holomorphy premise for the new quotient family.

## Frontier implication and limits

This rules out repairing prescribed-shift collapse by *raising* the
metric shift, including unbounded and irregular aperture-dependent choices.
Positive survivor is the exact actual-operator source law and uniform
complex mixed-pairing classification. It does not control shifts below c,
prove unshifted positivity, identify Xi, or prove/falsify RH.

## Audit log

- 2026-10-02: paper mechanism recorded before Lean implementation. No numerical experiments, added axioms, heartbeat changes, subagents, or full builds.
- Source scratch57265 and final42847 passed without warnings. `SuzukiRaisedMetricShiftSource` is wired once. The exact actual shift equation, source-defect contraction and zero-increment raw-vector identification are verified. Joint-filter limit and Xi-separation drafts remain under audit; no claim of their Lean completion yet.
- Joint-filter scratch21196 and final93705 passed without warnings. `SuzukiRaisedMetricShiftLimit` is wired once. Both complete complex normalized mixed pairings now have the asserted limits uniformly over all nonnegative increments. Carrier identification, reflection and Xi-separation scratch audit is running.
- Carrier final61584 passed without warnings after an explicit continuity type annotation resolved the scratch35399 elaboration error. All three leaves are wired once. Axiom audit50108 checked all seventeen public theorems: only `propext`, `Classical.choice`, `Quot.sound`. Both no-go roots have no hypothesis binders.

Final commands, run separately in the foreground from `formal/`:

```text
lake --old env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiRaisedMetricShiftSource.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/Suzuki/SuzukiRaisedMetricShiftSource.olean
lake --old env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiRaisedMetricShiftLimit.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/Suzuki/SuzukiRaisedMetricShiftLimit.olean
lake --old env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiRaisedMetricShiftCarrier.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/Suzuki/SuzukiRaisedMetricShiftCarrier.olean
```

Global lint78784 exited1 on eleven unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
RoutePNativeUndampedBalance, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving. No prohibited proof declarations were reported;
none of this work's three leaves appears among failures. Global lint is
not green. Unrelated work is preserved.

This closes the raised-shift question, not RH. Next exact conjecture:
P1:sz-spectral-edge-shift-necessity. Actual unshifted signed positivity and
source residues near the spectral floor remain open.
