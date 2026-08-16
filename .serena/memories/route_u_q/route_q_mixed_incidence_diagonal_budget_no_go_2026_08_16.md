# Route Q mixed-incidence diagonal-budget no-go (2026-08-16)

New formal module: `formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationBoundaryMixedIncidence.lean`.

Define `xiWeilMixedIncidence x y = Re <Jx,y>`. Exact packet fusion: `Q(P.eval+Q.eval)=P.sourceEnergy+Q.sourceEnergy+2*B(P.eval,Q.eval)`. Canonical boundary mixed incidence is exactly `B(b_plus,b_minus)=-E/2`. Every separated reconstruction pair has this same limit.

Unconditional dichotomy: RH, or actual separated prime-Gamma boundary packets have strictly positive diagonal energies tending to zero while mixed incidence tends `-E/2` and eventually exceeds in negative magnitude every fixed `C*sqrt(E_plus*E_minus)`. Capstone: `riemannHypothesis_or_exists_positiveBoundaryPackets_mixedIncidenceDominates`.

Research consequence: every Cauchy-Schwarz-style or diagonal recurrence budget is impossible off RH. Route Q must retain/build independent positive-definite reflection-fixed incidence, equivalently source-first control of `x+Jx`, before diagonalization.

Direct Lean, exact leaf build, and axiom audit passed; standard axioms only. Wired into `RHTower.lean`. Card: `docs/drafts/pipeline/3-formalized/route-q-mixed-incidence-diagonal-budget-no-go.md`.