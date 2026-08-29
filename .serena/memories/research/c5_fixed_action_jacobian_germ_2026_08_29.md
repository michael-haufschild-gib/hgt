# Direct fixed-action C5 Jacobian ninth germ (2026-08-29)

## Corpus origin
Conjecture was derived using `scripts/formal_tools.py research` from:
- `ThetaCuspFixedActionC5Jacobian`
- `ThetaCuspFixedActionC5JacobianSeamOrientation`
- `PolynomialODEJetC5FixedActionSeamClosure`
- interval Taylor transport pattern in `HTGeometry/StretchedExponentialFiniteDifference.lean`.

## Formal result
New modules:
- `HTGeometry.FixedActionC5JacobianGermClosure`
- `HTGeometry.FixedActionC5JacobianGermAnalyticClosure`
- `RHTower.ThetaCuspFixedActionC5JacobianGermClosure`

Key theorem:
`RHTower.eventually_deriv_thetaCuspReflectedActionC5FixedActionJacobian_center_pos`
proves unconditionally that for some δ>0, every 0<t<δ has
`0 < deriv (fun u => thetaCuspReflectedActionC5FixedActionJacobian u t) 0`.

Exact mechanism:
- division-free germ G equals `(exp(q)-1)^2 * J_u(0,t)` for t>0;
- all G jets below order 9 vanish;
- `G⁽⁹⁾(0)=20160*thetaCuspC5FixedActionSeamLogValue>0`;
- Lagrange Taylor remainder transports this to local strict sign.
The action-partial/velocity term cancels identically from the determinant linearization.

Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
Direct Lean checks and targeted module builds pass.
Card: `docs/drafts/pipeline/3-formalized/theta-cusp-fixed-action-c5-jacobian-germ.md`.

## RH passport and exact open core
local direct-J orientation
→ global direct-J orientation
→ C5 reflection-centre transport
→ reflection-odd rank-four/Ptolemy wall
→ arbitrary finite packets/cofinal no-escape
→ CLG/TTF or Weil positivity
→ `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` or
  `riemannHypothesis_iff_xiWeilPolarization_nonneg`
→ RH.

Next hardest burden: prove global `u>0,t>0` direct-Jacobian orientation from literal theta source, or prove a sharp obstruction and extract its strongest positive survivor. Do not spend effort on more local finite germs or numerical coefficient optimization. Frontier map remains read-only.