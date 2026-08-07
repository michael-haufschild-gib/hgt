New module `formal/GaloisForLFunctions/RHTower/RouteRBurnolThetaSameFiberOrientation.lean`, wired into `RHTower.lean`.

Unconditional scientific delta:
- `thetaRootEnergy_neg_of_zero`: source reflection `U_{-z}(-x)=-U_z(x)` plus Haar reflection proves theta root energy even at every theta-source zero.
- `norm_sq_completedXiFirstDividedL2_eq_sameFiberThetaRootEnergy`: removes reflected argument from completed divided-energy landing.
- `thetaXiRankTwoBoundaryFlux_completedXi_sameFiber`: exact division-free comparison `pi * M * B_theta(q) = Im(alpha_q) * ||completedXiFirstDividedL2 q.support||^2`.
- Right-half Xi divisor implies `B_theta<0`, while existing Burnol head current `J_rho>0`; product strictly negative.

Frontier consequence: completed-Xi positive norm and compact-theta boundary port are now on same divisor fibre with fixed normalization and retained nonzero quotient. Remaining Route-R theorem is a coefficient-faithful orientation-reversing handoff from Burnol fixed-window divided atom/current to this completed-Xi/theta port. Positive/isometric same-orientation comparison cannot yield `J<=0`.

Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-r-burnol-theta-same-fibre-orientation.md`.
Verification: `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.RouteRBurnolThetaSameFiberOrientation` passed 10940/10940. All capstones depend only on `[propext, Classical.choice, Quot.sound]`. No forbidden declarations or stale Lean processes.