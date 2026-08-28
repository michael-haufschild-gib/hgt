# No-gap stationary support and bound-state mass law (2026-08-28)

New formally closed theorem:
- Module: formal/GaloisForLFunctions/RHTower/StationaryRecurrenceSupportIntervalLaw.lean
- Closed capstone: RHTower.universalStationaryRecurrenceNoGapBoundStateMassLaw
- For every probability energy law mu, stationary survival-fidelity support is exactly one closed interval [rho, p^2], where p is total pure-point mass.
- Scaled perfect-return endpoint belongs to support and is its maximum.
- p = sqrt(max support).
- If p=0, stationary law is delta_0.
- If p>0, normalized point spectrum is countably carried and support scales from [1-M,1].
- Pure-point deficit identity: 1-|sum_i w_i exp(it E_i)|^2 = sum_(i,j) w_i w_j (1-cos((Ei-Ej)t)).
- No simplicity, rational independence, finite support, locality, decay, or genericity.

Verification:
- lake env lean GaloisForLFunctions/RHTower/StationaryRecurrenceSupportIntervalLaw.lean passes warning-free.
- targeted lake build module passes; no umbrella build.
- axiom audit of nine load-bearing declarations reports only propext, Classical.choice, Quot.sound.
- module wired into formal/GaloisForLFunctions/RHTower.lean.
- project lint reports unrelated shared-worktree umbrella reachability errors, not this module.
- no stale process from this work.

Research card:
docs/drafts/pipeline/3-formalized/stationary-recurrence-bound-state-mass-law.md

Manuscript integration:
docs/drafts/pipeline/1-in-progress/geometry-complexity-quantum-recurrence/
- main/body/old detailed appendix updated.
- theorem label thm:boundstateedge; equations boundstateedge/boundstatescaling.
- abstract/public summary, position relative, synthesis, proof guide, experimental section updated.
- Added verified Eberlein 1955 reference, DOI 10.1090/S0002-9939-1955-0068030-2.
- Added falsification protocol using independently measured bound-sector population and empirical stationary return edge.
- PDF built at output/pdf/persistent-phase-geometry-of-quantum-recurrence.pdf, 45 A4 pages.
- TeX log has no warning, undefined citation/reference, or overfull/underfull box.
- Visually inspected affected pages 1, 4-6, 17-19, 35-37, 43-45; no overlap/clipping.
- Paper remains standalone: no Lean/HGT/RH/internal-project references.

Literature comparison:
Classical Wiener-Eberlein first moment gives sum w_i^2. New law gives (sum w_i)^2 from full-law support top plus support connectedness. Targeted exact-object search found no prior statement; absence evidence only, not absolute priority claim.