# FZZ neutral conjugate-eigenphase collapse (2026-09-01)

- Source: HJ arXiv:2402.00932v3 (3.26),(3.29)-(3.33) has equal total W+/W- in vacuum/area expansion; corpus conjugate balanced eigenline is `star y`, `|y|=1`.
- New theorem: `y_beta^n (star y_beta)^n = 1` for every depth and positive scale. Neutralized fixed quintic is constant 1; all postprocessing sees only position kernel.
- Killed chain: neutralized fixed-quintic coefficient phase -> divisor eigenphase landing -> Mellin completeness -> RH.
- Survivor: phase must be in position/prime-form kernel or externally charge-compensated imbalance.
- Lean: `RHTower/FZZCigarParityNeutralConjugateEigenphaseCollapseNoGo.lean`; capstone `fzzCigarParity_neutralConjugateEigenphaseCollapse_noGo`; direct/targeted build PASS; axioms `[propext, Classical.choice, Quot.sound]`; umbrella wired.
- Cards: `3-formalized/fzz-neutral-conjugate-eigenphase-collapse.md`, `5-failed/fzz-neutral-fixed-quintic-coefficient-phase.md`.