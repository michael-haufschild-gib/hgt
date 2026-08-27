# RBH countable separated-sign rate cone (2026-08-27)

Formalized `GaloisForLFunctions.RHTower.ReflectedBiHeatCountableSeparatedSignRateCone` and wired it into `GaloisForLFunctions.RHTower`.

Exact theorem: for nonnegative countable low/high packets with positive witnesses, positive rates separated pointwise by `lambda_i < kappa ≤ mu_j`, summable low mass, and summable high hyperbolic moments at every positive time, the countable hyperbolic reporter has only its forced wall zero iff its first wall derivative is nonnegative. Stronger oriented equivalence also proved.

New mechanism: no uniform rate gap is needed. Near zero, dominated convergence identifies exact first moment. At infinity, each low atom divided by `sinh(kappa*t)` tends to zero and is dominated by summable `p_i`; Tannery handles low rates accumulating at separator. One positive high atom forces eventual positivity. Endpoint hyperbolic moments give local uniform convergence and continuity, so a negative wall derivative constructs an extra positive root.

Countable real-power aperture factorization and RH-equivalence theorem are included.

Card: `docs/drafts/pipeline/3-formalized/reflected-bi-heat-countable-separated-sign-rate-cone.md`.

Audits passed: direct `lake env lean`, targeted module `lake build`, and `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`). Formal lint has unrelated pre-existing umbrella reachability failures; new module is wired and not flagged. Frontier map remained read-only.