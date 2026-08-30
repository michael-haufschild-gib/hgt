# T2 natural square-energy three-quarter transfer (2026-08-30)

VERIFIED PROGRESS: significant T2 premise discharged.

New literal-source energy:
`RHTower.WoldNatResidualSquareEnergy t :=
  Summable (fun N => N^(2t-1) * |R_N|^2)`,
where `R_N = xiHeatCassiniWoldNatResidualLogDiscrepancy N`.

Formalized:
- `woldNatResidualSqrtMeanSpectrum_of_squareEnergy`
- `woldNatResidualPowerSpectrum_of_squareEnergy`
- `riemannHypothesis_of_woldNatResidualSquareEnergy_cofinal_threeQuarter`

Mathematics:
For `W_N=[N-sqrt N,N+sqrt N]`, `sqrt n ≤ 2|W_N|` on the window. If `c<t-1/4`, then `d=2c-(2t-1)<1/2`, hence `n^d≤sqrt n≤2|W_N|`. Finite Cauchy-Schwarz and the total energy `Q` give uniform local mean `≤sqrt(2Q)`. Existing Wold sqrt-mean persistence converts this into all pointwise rates below `t-1/4`. Choosing `t=(c+1)/2<3/4` for every `c<1/2` yields RH.

Interpretation:
T2's terminal-control plus height-cofinal zero-width receiver burden collapses to one explicit producer: prove literal Wold square energies cofinally for `t↑3/4`. This sharpens the previous generic graph sufficient radii `t↑1` by a quarter power.

Rejected strengthening:
Initial claim that any energy with `t>3/4` is impossible was not included. Fixed sqrt persistence has additive `N^-1/2` drift and cannot produce pointwise exponents above half. Adaptive windows predict a sharper `c<2t/3` transfer, but this remains a separate conjecture, not part of the result.

Artifacts:
- Lean: `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldNaturalSquareEnergyThreeQuarter.lean`
- Card: `docs/drafts/pipeline/3-formalized/t2-natural-square-energy-three-quarter-transfer.md`
- Umbrella: imported at EOF of `formal/GaloisForLFunctions/RHTower.lean`
- Frontier map was read-only and not edited.

Verification:
- direct `lake env lean`: PASS
- targeted `lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergyThreeQuarter`: PASS
- axioms: only `[propext, Classical.choice, Quot.sound]`
- global lint red only on unrelated concurrent unreachable modules; new module reachable/clean
- no own Lean processes left running.

Continue by attacking adaptive-window `2t/3` transfer only if it materially kills supercritical energy producers, or attack the remaining cofinal energy producer itself. Persistent user goal remains active across many RH routes.