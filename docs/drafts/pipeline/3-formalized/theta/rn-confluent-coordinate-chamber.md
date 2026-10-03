# RN: actual ordered center chamber for both Schur residuals

Status: formalized, direct leaf audits passed 2026-10-02. No RH premise.

Let k be the actual theta source, H the literal full-tail first-moment
kernel, K=k(0), I=∫₀∞t k'², J₂=∫₀∞t k''², q=p'(0),
β=2I−K²>0, and E=J₂−3qI+qK²>0. For old nodes (0,z), the literal
inverse-Gram coordinate residual is

    B_z(y)=y k(y)−z k(z)[H(0,0)H(z,y)−H(0,z)H(0,y)]/det M.

With T(y)=H_x(0,y), its exact limit as z→0+ is
B_*(y)=y k(y)−KT(y)/β. The proof retains the original inverse entries:
the numerator divided by z tends to H(0,0)T(y), and
det M/z² tends to H(0,0)β. No coefficient-sign hypothesis enters.

## Mixed-row center jet

Schwartz correlation differentiation and half-line integration by parts give

    T(0)=0, T'(0)=β, T''(0)=0, T'''(0)=qK²−2J₂.

The boundary identities are ∫kk'''=qK², ∫k'k''=0 and
∫t k'k'''=−J₂, with k'(0)=0 and k''(0)=−qK.
Consequently B_*(0)=B_*'(0)=B_*''(0)=0 and B_*'''(0)=2KE/β.
Three successive quotient limits prove

    B_*(y)/y³ → KE/(3β)>0             (y→0+).

Combining this with the literal coordinate limit and previously proved
source limit yields the unconditional source theorem

    ∀ᶠ y in 𝓝[>] 0, ∀ᶠ z in 𝓝[>] 0,
      z<y ∧ 0<sourceResidual z y ∧ 0<coordinateResidual z y.

This is a nested center chamber. It does not assert uniformity as y,z
approach zero together or positivity for arbitrary y>0.

## Lean and validation

- `ThetaTailConfluentCoordinatePort.coordinateResidual_limit` (namespace
  `RHTower.ThetaCoordinate`).
- `ThetaTailConfluentCoordinateJets`: `confluentCoordinateResidual_cubic_limit`,
  `eventually_confluentCoordinateResidual_pos`, `eventually_actual_ports_pos`.
- Extended `ThetaTailConfluentCenterLimits` and `ThetaConfluentCoordinateEnergy`
  expose the exact correlation and center integration APIs reused here.

All four changed leaves passed targeted `lake --old build` and final direct
`lake env lean` checks with empty diagnostics. All 26 public theorems in
these leaves were audited by `#print axioms` in /tmp: only propext,
Classical.choice and Quot.sound. Both new leaves are wired into RHTower;
no full or umbrella build was run. Formal lint exited 1 on twelve unrelated
unreachable modules, recorded in the working log; no owned proof violation.

## Remaining hard obligations

Prove global B_*(y)>0 through the actual integrated comparison; establish
the Schur compensation barriers and propagation; extend to arbitrary rank;
discharge the retained RH transfer. Equal diagonals do not identify the
prospective full-tail kernel with the arithmetic off-diagonal kernel.
