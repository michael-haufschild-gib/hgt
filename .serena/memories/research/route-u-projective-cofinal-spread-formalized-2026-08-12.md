# Route U projective cofinal spread formalized (2026-08-12)

Created `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionProjectiveCofinalSpread.lean` and imported it from `formal/GaloisForLFunctions/RHTower.lean`.

Formal results: low-edge anchor positivity and shifted-Xi limit 1; exact Gauss-root spread renewal; strict degree increase under finite positive moment form; fixed-prefix beta lower bound; low-edge projective surplus coercivity; eventual degree-uniform harmonic surplus lower bound; cofinal normalized spread divergence along actual shifted-Xi schedules assuming required positive Hankel blocks. Closed audit surface: `routeU_cofinalSpread_and_harmonicWork_closed`.

Verification passed:
- `lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionProjectiveCofinalSpread.lean`
- `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveCofinalSpread`
- `/tmp/RouteUCofinalAudit.lean` prints only `[propext, Classical.choice, Quot.sound]` for four key declarations.
- `.olean` size 1,594,600 bytes.
- no `sorry`, `admit`, declaration `axiom`, `opaque`, or `unsafe` in new module.

Global `scripts/formal_tools.py lint` was run and failed on pre-existing/concurrent unrelated umbrella reachability debt (many Bourgain/Sieve/Suzuki/HTGeometry modules). It did not identify this module as unreachable or forbidden.

Cards/status updated:
- new Stage3 `docs/drafts/pipeline/3-formalized/mass-shifted-projective-low-edge-anchor-cofinal-spread.md`
- Stage2 card and Route U frontier item 76 now point to Lean module and state exact semantic limitation.

Do not overclaim: cofinal-spread theorem remains implication from positive Hankel blocks. It does not prove their positivity, a normalized-flux floor, a cumulative hyperbolic-action budget, or RH. Exact remaining obstruction is degree-reset synchronization in singular reciprocal-mean geometry. Generic ordinary variance/root spread cannot pay resets; next source-specific target is normalized-flux floor or hyperbolic reset-action upper budget. No computation was used.