# Route-P Xi-fibre conormal co-short admission (2026-08-18)

Formalized module: `formal/GaloisForLFunctions/RHTower/SourceHorizontalEulerWoldJordanConormalCoShortAdmission.lean`, imported by `RHTower.lean`.

Main result: for literal non-spectral conormal short `S(c)=4*normSq c`, componentwise Euler/Wold admissions are `A_-=-M_- S(c)`, `A_+=M_+ S(c)`; finite Green–Stokes identity proves `A_+ + R = 2*S(c)` for existing regularized Xi-conormal endpoint response `R`. Actual coefficient uses multiplicity-split completed Gamma–Julia residue and Burnol nested-window conormal tomography; support-fibre sum restores analytic multiplicity.

C0 (identify Jordan masses with mixed primitive/Xi Gram innovations) was falsified: mixed innovation depends on Xi horizontal rate/ordinate, masses only on source clock, so equality needs forbidden q-fitted scaling.

Cofinal classification: every real reporter `a A_- + b A_+ + d R` tends to `(8/3)*normSq(c)*(-a+b+2d)`. For `c != 0`, blind plane is exactly `-a+b+2d=0`. Existing compensated primitive-budget energy equals reporter `(1,-1,1)`, hence is exactly blind and cannot control nonzero endpoint. Next open core: construct a source-budgeted arithmetic reporter transverse to that plane; complete-positive transverse reporting remains blocked by overspend firewall.

Verification: `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalEulerWoldJordanConormalCoShortAdmission.lean` PASS; exact leaf `lake build GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldJordanConormalCoShortAdmission` PASS (13562/13562); axiom audit for capstone/fibre/limit/classification declarations: only propext, Classical.choice, Quot.sound. No umbrella build run.

Formalized card: `docs/drafts/pipeline/3-formalized/source-horizontal-euler-wold-jordan-conormal-coshort-admission.md`. Frontier and literature-exchange docs updated.