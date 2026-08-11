# Covariant admission defect-energy producer (2026-08-11)

Created and audited `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionDefectEnergy.lean`, wired at `formal/GaloisForLFunctions/RHTower.lean:6783`.

Exact result: for shifted-Xi moment form `L_y`, current canonical monic admission `P_y`, fixed same-degree monic `A`, defect `D_y=A-P_y`, norm `h_y=L_y(P_y^2)`, coefficient gap `d_y=[X^(n-1)]D_y`, and odd defect energy `J_y=L_y(D_y X D_y)`,
`T_y(P_y,A) = -J_y' - 2 h_y' d_y`.
Raw inverse-Hankel admission velocity cancels identically.

Define covariant source density `S_y=T_y+2h_y'd_y`. At square mass this is the literal rational-Gamma/von Mangoldt arithmetic admission transgression plus canonical norm connection. Lean proves `J_y'=-S_y`, derives continuity on positive compact Hankel chambers from corpus primitives, then proves:
- `∫_[a,b] S_y dy = J_a-J_b`
- `|J_b-J_a| ≤ ∫_[a,b]|S_y|dy`
- uniform `|S_y|≤C` implies `|J_b-J_a|≤C(b-a)`
- for frozen comparator `A=P_a`, `∫_[a,b]S_y dy=-J_b`.

Paper/report addendum: `docs/reports/mass-shifted-spectral-trace-route.md:8980`, equations (9.3.448)–(9.3.456). Formalized card: `docs/drafts/pipeline/3-formalized/mass-shifted-covariant-admission-defect-energy.md`.

Audits: direct `lake env lean` clean; targeted `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionDefectEnergy` passes; forbidden declaration scan and diff check pass; capstone axiom prints only `propext`, `Classical.choice`, `Quot.sound`; no stale Lean process. Whole-corpus lint remains red only due 19 unrelated pre-existing umbrella-unreachable modules; new module is reachable.

Big-picture survivor: canonical admission connection is a gauge term; mixed source curvature is an exact one-form. Remaining mass-shifted spectral-face open core is sign/coercivity or L1 control of terminal odd defect energy along cofinal first-contact schedule. Ordinary `H_(n+2).PosDef` alone does not sign shifted odd form `D↦L_y(D X D)`; do not claim RH. Novelty remains unverified after adjacent Toda/Christoffel/Xi OP audit.