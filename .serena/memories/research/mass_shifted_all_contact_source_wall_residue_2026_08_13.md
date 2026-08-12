# Exact all-contact arithmetic source-wall residue

At every occupied physical strict shifted-Xi frontier, finite first Padé contact order `d>0` determines exact newborn-norm coefficient
`C_d = (-1)^d * choose(2*(n+2)+d,d) * delta_(2*(n+2)+d) > 0`.
Continuity and strict positivity of preceding admitted adaptive source give
`u^d Wall(y+u) -> R_d = S(y)/(16*C_d) > 0`.
On physical germ this wall is eventually identical to current adaptive mixed completed rational--Gamma-minus-von-Mangoldt source divided by newborn admission norm. Thus prior infinite quadratic residue at flatter contact is only under-renormalization; intrinsic `d`-scaled residue is finite positive for every contact.

Formal module: `formal/GaloisForLFunctions/RHTower/XiShiftedStrictFrontierAllContactSourceWallResidue.lean`.
Umbrella import added. Direct Lean, targeted `lake build GaloisForLFunctions.RHTower.XiShiftedStrictFrontierAllContactSourceWallResidue`, and axiom audit pass; only standard axioms `[propext, Classical.choice, Quot.sound]`. Global lint failure is unrelated missing umbrella imports from concurrent modules; new module is reachable.

Card: `docs/drafts/pipeline/3-formalized/mass-shifted-strict-frontier-all-contact-source-wall-residue.md`.
Report: §9.3 equations (9.3.717)--(9.3.719).

Honest residual: local quotient is closed. RH remains open. Need one source-preserving common cross-degree action/admission law preventing simultaneous escape through growing contact order, shrinking residue, and shrinking physical neighborhoods. Pointwise nonintegrability of distinct wall germs cannot be added without such compatibility.