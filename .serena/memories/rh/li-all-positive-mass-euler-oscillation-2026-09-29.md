# LI actual all-positive-mass Euler-jet oscillation

Goal remains active until unconditional RH proof/falsification fully formalized; auxiliary theorem does not satisfy it.

Verified five wired RHTower leaves: LiEvenCrossCassiniLogMassPole, LiEvenCrossCassiniAllMassPole, LiEvenCrossEulerJetOscillation, LiEvenCrossEulerCurrentBridge, LiEvenCrossRealEulerJetBridge. Named foreground --old Lake builds and exact final `lake env lean <leaf>` passed for every leaf. Scratch #print axioms capstones: only propext, Classical.choice, Quot.sound. No heartbeat overrides/numerical experiments.

New strongest capstone `RHTower.liEvenCrossRealLogMassFirstCurrent_even_deriv_cofinal_both_signs` quantifies over LiEvenCrossPositiveMass={v:Real // 0<v}. Literal g_v(t)=v*exp(t)*liEvenCrossSquareMassAdjacentCurrent(v*exp(t),0), real even iterated derivatives at 0 have strict positive/negative values in every tail. Exact real/complex derivative interface proved; no RH or source positivity premise.

AllMassPole uses Hardy actual real Xi zeros to prove exists_xiSquaredNode_norm_gt B. At node with norm>v^2, reflected mass norm<1, so actual source remains regular there and direct order -3 survives. Canonical finite Taylor radius + finite-prefix Pringsheim excludes eventual coefficient sign. Interior lattice coefficients +/-8 intrinsic multiplicity remain proved in LogMassPole; do not claim arbitrary-node noncancellation at large masses.

Paper/Lean card moved to docs/drafts/pipeline/3-formalized/li-even-euler-jet-oscillation.md; frontier LI row and working loop updated. Whole-tree lint red on unrelated unwired modules; --check-generated additionally found gap/overview freshness drift during concurrent writes. Own leaves absent from errors. Index regenerated once; no full umbrella builds.

Next: LI-CO10 paper card docs/drafts/pipeline/2-fully-proven/li-even-euler-jet-small-mass-crossover.md. Exact mass/exp-pullback jet series requires formal proof before uniform growing-order estimates. Main loop docs/drafts/pipeline/1-in-progress/li-complex-orientation-conjecture-loop-2026-09-29.md.

Rejected crossroutes: weighted TT signed-work dominance equivalent to C9 energy, not new producer; correct theta/Wold Ward reflection exactly negative original. Two arbitrary masses preventing all nonreal pole cancellation also adds no leverage: one interior mass already has no cancellation and strip regularity is RH-strength. Actual source producer for LI orientation remains open.