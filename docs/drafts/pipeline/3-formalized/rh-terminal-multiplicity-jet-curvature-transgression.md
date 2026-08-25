# Xi terminal-multiplicity-jet curvature transgression

- **ID:** RH-TERMINAL-JET-CURVATURE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · nodal/two-cell and Hedenmalm source families
- **Statement:** Finite-cut log norm gain of the nonzero terminal theta-multiplicity jet reconstructs the mixed curvature coefficient and complete second-order arithmetic descent defect.

## Goal

Replace abstract Xi two-cell curvature by one unconditional, source-defined observable without
erasing analytic multiplicity. This is a bridge theorem, not an RH proof: remaining producer must
force terminal-jet holonomy to vanish on every Xi zero fibre.

## Gates

- [x] 0 → 1  in-progress: source-pure terminal jet and fixed arithmetic observation
- [x] 1 → 2  fully-proven: elementary exact proof from terminal-jet norm law and nodal defect law
- [x] 2 → 3  formalized: Lean theorem `xiTerminalMultiplicityJet_curvatureTransgression`; direct check and targeted build green; axioms `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready: independent external novelty review and standalone exposition

## Approach

The terminal jet is nonzero at exact analytic multiplicity. Its cut norm ratio cancels that
nonzero coefficient and equals `exp(x * (2 Re rho - 1) / 2)`. Taking `log` recovers horizontal
modular charge. Multiplication by nonzero vertical Xi phase reconstructs the nodal mixed curvature,
then the existing source-level Bianchi identity reconstructs the full second-order anomaly defect.

## No-go closure

- **Exact killing theorem/mechanism:** `coefficientLiftHigherBirth_closed` shows coarse closure and pentagon coherence do not generally produce a strict fine lift; “closed fibre automatically becomes coherent” is false.
- **Strongest positive survivor:** Xi mixed curvature is exactly terminal-multiplicity-jet holonomy times vertical phase.
- **New insight:** Arithmetic source already measures the RH obstruction. Open theorem must trivialize this specific holonomy; it cannot be generic closure, Bianchi, pentagon, positivity, or multiplicity annihilation.
- **Status:** Paper proof dependency-closed and formalized in `XiTerminalMultiplicityJetCurvatureTransgression.lean`; external novelty preliminary.

## Novelty audit

Curved dg/coring and global curved Koszul-duality literature supplies general language, not this Xi
source identity. Connes--Consani--Moscovici (arXiv:2511.22755) studies self-adjoint finite spectral
approximants; Takook (arXiv:2606.13932) gives a Krein critical-line representation. Neither source
states terminal multiplicity-jet transgression of a second-order Xi descent anomaly. Claim remains
preliminary until broader expert review.

## Log

- 2026-08-24 — exact paper proof, Lean formalization, targeted build, and axiom audit completed
