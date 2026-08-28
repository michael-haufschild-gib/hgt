# HC45 HB third-order cokernel quantitative trichotomy (2026-08-28)

Formal module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMThirdOrderCokernelQuantitativeTrichotomy`.
Card: `docs/drafts/pipeline/3-formalized/hb-third-order-cokernel-quantitative-trichotomy.md`.

Corpus-led advance: existing BM/AIME source identity fixes sum of charge-orthogonal stationary, second-harmonic, and direct-third-variation resonant projections to negative exact AIME numerator. New sharp norm law proves their norms sum to at least AIME norm and one channel carries at least `‖AIME‖/3`; aligned equal channels show `1/3` optimal. For nonzero absorbed seed and a left resonant state annihilating the linearized range, selected large channel is also nonexact. This upgrades qualitative cokernel trichotomy to a quantitative, falsifiable source burden.

Audit: direct `lake env lean` passed; target-only build passed 12,749 jobs; all five public theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; wired into RHTower umbrella; global lint has no HC45 error and remains red only on unrelated unreachable modules. Bounded primary-source audit covered arXiv:2112.11168, 2305.19332, 2210.15935, 2401.15516 and found no exact match. Frontier map remained untouched.