# Route-P transverse source-budgeted reporter (2026-08-18)

Formal module: `formal/GaloisForLFunctions/RHTower/SourceHorizontalEulerWoldTransverseDefectBudgetReporter.lean`; imported by `RHTower.lean`. Stage-3 card: `docs/drafts/pipeline/3-formalized/source-horizontal-euler-wold-transverse-defect-budget-reporter.md`.

Construction:
- Let `B = routePPrimitiveBaseCauchyCubicTraceBudget`.
- Define reporter coefficients `(a,b,d)=(-1,-1,B/4)`.
- Finite identity:
  `T_N = sourceHorizontalEulerWoldJordanPostCompressionVariation N * sourceHorizontalLiteralConormalShort c + (B/4) * sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N`.
  Thus first leg is exact positive coefficient-faithful Euler–Wold defect, not blind compensated energy.
- Cofinal character is exactly half source budget:
  `character = sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c / 2`.
- For `c != 0`, character is nonzero/transverse and eventually `0 < T_N < sourceBudget c`.
- Actual multiplicity-split Xi coefficient specialization preserves support-copy constancy and fibre sum equals analytic multiplicity.
- Capstone: `sourceHorizontalActualXiTransverseDefectBudgetReporter_producer`.

Sharp limitation:
`not_eventually_sourceBudgeted_and_endpointDominating_linearReporter` proves no linear reporter can both eventually stay below source budget and eventually dominate literal endpoint response; proof combines the two assumptions with existing cofinal endpoint overspend. Therefore requested existence is closed, but it cannot close RH through linear endpoint domination. Remaining Route-P core: nonlinear/order-indefinite source relation annihilating endpoint excess before scalar domination.

Verification:
- scratch Lean PASS;
- exact tree `lake env lean ...` PASS;
- exact leaf `lake build GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldTransverseDefectBudgetReporter` PASS (13563/13563);
- axiom audit only propext, Classical.choice, Quot.sound;
- forbidden declaration scan empty;
- no umbrella build.

Literature audit: generic Krein shorting (Arlinskii 1109.4020), BV pushforward SDR (Cattaneo–Mnev 2605.30558), and Connes–Consani semilocal Sonin/Weil theory do not supply this corpus-specific arithmetic coefficient/fibre law. Classified as [BRIDGE], not novelty claim.