# Hedenmalm--Sonin Cartan/Gamma-six mass shell

- **Label:** `P-G132`
- **Route:** P
- **Parents:** `P-G129`, `P-G131`, `SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature`, `BurnolSoninProjectedEvaluationTransport`
- **Status:** theorem proved in Lean; umbrella integration complete

## Conjecture tested

P-G131 leaves open whether Gamma-six positive opposite-boundary curvature and Burnol signed
bilateral aperture holonomy give two independent observables capable of forcing neutral Cartan
saturation.  Test their exact relationship on the literal forward/inverse Mellin orientation pair.

For squared leg norms `u,v`, define trace excess `K=u+v-2` and orientation current `J=u-v`.
The determinant-one law predicts the universal mass shell

```text
(K+2)^2-J^2=4, equivalently K(K+4)=J^2.
```

## Scientific decision gate

- **Success:** identify Gamma-six curvature and actual Burnol defect current coefficient-exactly,
  then prove whether they are independent or lie on one algebraic orbit.
- **Failure:** abstract hyperbolic algebra without literal Burnol and Gamma-six identifications is
  theatre and must not be recorded as Route-P progress.
- If dependent, retire every proposal that combines them as separate constraints and pivot to a
  singular or discrete source observable not determined by the Cartan rapidity.

## Prior-research audit

- 2026-08-13 — Gamma-six paired-defect work proves the positive codiagonal curvature
  `2(cosh(a)-1)` and its neutral radical, but does not relate it to Burnol aperture holonomy.
- 2026-08-13 — Burnol projected-evaluation work proves signed bilateral defect energy with
  coefficient `r^(2 Re(w)-1)-r^(1-2 Re(w))`.
- 2026-08-13 — P-G131 identifies the reciprocal Mellin legs and determinant one, but leaves open
  whether a second source trace adds independent rigidity.

## Conjecturing log

- 2026-08-13 — C1 proved in scratch: trace excess of squared Burnol legs equals Gamma-six
  curvature at rapidity `log(r)(2 Re(w)-1)`.
- 2026-08-13 — C2 proved in scratch: signed orientation current is exactly the coefficient of the
  literal Burnol bilateral aperture defect energy.
- 2026-08-13 — C3 proved in scratch: determinant one forces `(K+2)^2-J^2=4` and
  `K(K+4)=J^2`; hence curvature and current are algebraically dependent.
- 2026-08-13 — C4 proved in scratch: `K=0`, `J=0`, lower gain one, and `Re(w)=1/2` are equivalent;
  `K` is strictly positive off wall.
- 2026-08-13 — C5 proved in scratch: on actual right-oriented Xi support,
  `K=2(cosh(2 log(r) lambda(q))-1)`.

## Verification log

- 2026-08-13 — Direct foreground check passed:
  `lake env lean GaloisForLFunctions/RHTower/HedenmalmSoninCartanGammaSixMassShell.lean`.
- 2026-08-13 — Imported by `GaloisForLFunctions/RHTower.lean`.
- 2026-08-13 — Exact module build passed:
  `lake build GaloisForLFunctions.RHTower.HedenmalmSoninCartanGammaSixMassShell`
  (`12959/12959`).
- 2026-08-13 — Axiom audit passed for every new theorem; dependencies are exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

## Result and pivot

- Gamma-six curvature and Burnol holonomy are Lorentz coordinates on one determinant-one Cartan
  mass shell.  They are not independent source constraints; either neutralizes exactly when the
  other does.
- On off-wall actual Xi support both merely measure the same positive rapidity.  Combining them,
  taking their determinant, or applying any algebraic identity forced by the mass shell cannot
  produce neutral saturation.
- Remaining producer must be transverse to Cartan rapidity: singular source boundary data,
  discrete-divisor rigidity with a uniform growth/type budget, or an arithmetic trace not
  determined by the two orientation-leg norms.
