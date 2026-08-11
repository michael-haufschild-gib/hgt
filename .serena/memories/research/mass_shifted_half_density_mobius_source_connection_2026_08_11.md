# Mass-shifted half-density Möbius source connection

Created and formalized `RHTower.XiShiftedHalfDensityMobiusSourceConnection`.

Key theorem: shifted reciprocal moment source forces unique polynomial half-density connection
`K P = X^2 P' + (1/2) X P`. Product compatibility holds iff weight is `1/2`.

Literal completed adaptive arithmetic source:
`Q_w(P) = L_{w^2}((XP)^2) + 2 L_{w^2}((KP)(XP))`,
with amplitude/connection landing before rational–Gamma minus von Mangoldt aggregation and reflection.

Covariant law:
`nabla(XP) - X nabla(P) = -X^2 P`.
Moving odd current:
`I' = 2 <nabla P, XP> - <XP,XP>`.
Source-parallel nonzero amplitude under positive moment form has strict dissipation
`I' = -<XP,XP> < 0`.

Exact effectivity obstruction:
`K(X^n) = (n+1/2) X^(n+1)`; therefore no fixed degree flag is invariant. Finite Hankel faces can observe but not faithfully carry source-parallel flow. Remaining open core is to quantify/sign projection leakage at cofinal first contact.

Files:
- `formal/GaloisForLFunctions/RHTower/XiShiftedHalfDensityMobiusSourceConnection.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`
- `docs/reports/mass-shifted-spectral-trace-route.md` equations 9.3.457–9.3.465
- `docs/drafts/pipeline/3-formalized/mass-shifted-half-density-mobius-source-connection.md`

Verification:
- direct `lake env lean` pass
- targeted module build pass
- axiom audit only `propext`, `Classical.choice`, `Quot.sound`
- formal lint failure is unrelated pre-existing umbrella reachability for 17 modules; new module is wired
- no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, computation, or RH premise.

RH remains unproved.