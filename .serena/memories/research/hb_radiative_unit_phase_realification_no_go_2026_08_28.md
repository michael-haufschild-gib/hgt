HC91 formalized and promoted.

Module: formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMRadiativeSourceFEUnitPhaseRealificationNoGo.lean
Card: docs/drafts/pipeline/3-formalized/hb-radiative-unit-phase-gauge-realification-no-go.md
Umbrella: formal/GaloisForLFunctions/RHTower.lean imports HC91 after HC90.

New result:
- Actual raw nonlinear BM Ward amplitude P(q) defines global bphase(q)=1 if P=0 else P/||P||.
- bphase is nowhere zero and norm one globally; bphase(q)*(||P(q)||:C)=P(q) exactly.
- General radiative diagonal gauged cocycle kappa^b(q)=b(Rq)^-1*kappa_rad(q)*conj(b(q)) and full finite-packet conjugated transport are formalized.
- Off line, exact identity kappa^bphase(q)=(||kappa_rad(q)||:C); hence positive real, nonzero.
- Full phase-gauged packet transport has positive-gain reflected coefficients off line and remains a global anti-linear involution.
- Closed theorem hbXiPhaseSensitiveUnitRadiativeSourceFEUnitPhasePositiveRealBrightCancellation packages these with HC89 bright cancellation.
- This kills reflection-reality as gauge-unqualified selector. Survivor: source/divisor-independent phase reference or common phase rigidity across multiple independent source channels; relative phase holonomy may be first gauge-invariant obstruction.

Audit:
- lake env lean source passed.
- target lake build passed 12020/12020.
- #print axioms main/realification/involution: propext, Classical.choice, Quot.sound only.
- lint only unrelated pre-existing unreachable modules; no HC91 finding.
- /tmp hc91 scratch deleted; no HC90/HC91 Lean processes remain.
- frontier map untouched/read-only.