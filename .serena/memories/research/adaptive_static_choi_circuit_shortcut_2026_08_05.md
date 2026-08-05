# Adaptive static-Choi circuit-shortcut law (2026-08-05)

Formal module: `formal/GaloisForLFunctions/RHTower/AdaptiveStaticChoiCircuitShortcutActionLaw.lean`
Card: `docs/drafts/pipeline/3-formalized/adaptive-static-choi-circuit-shortcut-action-law.md`

Result: For every nonempty finite spectrum, arbitrary finite dictionary of normalized targets in the full D²-dimensional Choi Hilbert space, adaptive post-time target choice, epsilon < 1/2, replica order n >= 1, and T > 0, Gaussian and centered-uniform capture probabilities are bounded by dictionary cardinality times (sqrt(1-4 epsilon²)^(2n))^-1 times exact replica collision mass plus intrinsic action-resolution leakage. Padded gate words pay exactly |gate|^(s+1). Under maximal projective spectrum, collision mass is exactly replica permutation floor.

Key bridge: choose one captured Choi-orbit anchor per arbitrary full-space target. Triangle inequality makes any other capture 2 epsilon-close to anchor. Pure-state trace identity converts this to phase-twisted microcanonical overlap. No projection of target into diagonal Choi subspace.

Lean audit: direct lake env lean passed; module-only lake build passed; formal lint passed; #print axioms reports only propext, Classical.choice, Quot.sound.

Boundary: finite target dictionary; continuous adjustable gates require a net/entropy theorem. Intrinsic action gap can be tiny. This proves finite-window adaptive circuit-hardness density, not Brown–Susskind pointwise linear-growth onset. Next task: compose with generic ordinary local Hamiltonian and permanent locality–Haar separation.