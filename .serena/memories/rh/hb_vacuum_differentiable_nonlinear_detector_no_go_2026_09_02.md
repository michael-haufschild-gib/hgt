# HB nonlinear detector no-go (2026-09-02)

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMRadiativeSourceFEVacuumDifferentiableNonlinearDetectorNoGo.lean`.
- Certificate: `d4HBVacuumDifferentiableNonlinearDetectorScalarizationRouteKilled`.
- Fact: exact nonlinear scalarization `D(C_q x)=cD(x)` plus real-ray vacuum first variation `a⁻¹D(ax)→Lx` forces linear intertwiner `L∘C_q=cL`.
- Sharp survivor: off line, `L` kills horizon or boundary detector axis. Locally faithful scalarization iff `Re(q)=1/2`; copy-dependent global existence iff RH.
- Scope killed: arbitrary nonlinear complex-amplitude postprocessing into any Hausdorff complex topological module; no continuity away from vacuum/locality/positivity/invertibility/order assumptions.
- Survivors: vacuum-singular, real/conjugate-linear first variation, or first-order readout erasure.
- Audit: direct Lean PASS; targeted build `13099/13099`; axioms `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Status/card docs updated.