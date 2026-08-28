# Three-center receiver and joint-sector audit (2026-08-28)

- `HedenmalmCriticalFeatureThreeCenterLatticeQuantum.lean` proves exact three-center Hermitian floor `5` using a 49-coefficient degree-6 Bernstein certificate.
- Global consequence: strict-right packet charge `5/2` in `criticalFeaturePrimeGammaOffLineLatticeBudget`; sufficient 75% ceiling improves from `4/25 N` to `5/16 N`.
- This is genuine receiver-side progress, not the missing arithmetic producer. Corrected budget remains divisor-indexed through critical-line subtraction.
- Tested joint phase coercivity: exact local factor `59/100` exists with a 121-coefficient degree-10 Bernstein certificate. Retired implementation: ~3 minute compile, and local nearest-center selection cannot lift to source-only lattice inequality because omitted holomorphic squares can be negative.
- Positive optimized survivor in `HedenmalmCriticalFeatureThreeCenterHolomorphicSector.lean`: sharp nearest-cell `3/5` coercivity and local holomorphic quantum `689/250`; 140 lines, direct compile 22.6 s. Explicitly local/non-liftable.
- Next legitimate frontier remains pre-divisor pole–Gamma–von-Mangoldt upper bound at relaxed `5/16 N` scale, or source-native grouping whose omitted channels are nonnegative before divisor selection.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Global lint currently fails on unrelated umbrella-unreachable modules from concurrent dirty-worktree additions; target modules pass direct Lean checks and contain no forbidden declarations.