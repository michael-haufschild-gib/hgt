# HC95 real-linear vacuum detector no-go (2026-09-02)

- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadiativeSourceFEVacuumRealDifferentiableNonlinearDetectorNoGo`.
- New sharp law: `d4BMXiSecondHarmonicBoundaryTransfer_normSq_reflect_eq_iff_re_eq_half`.
- Mechanism: injective ℝ-linear scalarizer pulls back `X²-2 Re(c)X+|c|²`; both gains lie in `{c,conj c}`, hence equal norms; HC92 transfer quotient plus strict BM transfer-modulus monotonicity forces criticality.
- Final certificate: `d4HBVacuumRealDifferentiableNonlinearDetectorScalarizationRouteKilled`.
- Global faithful nonlinear scalarization with real/conjugate-linear vacuum derivative iff RH.
- Direct Lean PASS; targeted build 13100/13100; axioms propext/Classical.choice/Quot.sound; umbrella wired.
- Status/card: `docs/drafts/pipeline/3-formalized/hb-vacuum-real-differentiable-nonlinear-detector-scalarization-no-go.md`.