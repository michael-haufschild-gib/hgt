# Deninger–Meyer full-jet vertical defect

- **ID:** RH-DM-JET-VERTICAL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every finite packet of off-critical Xi supports, closure of full multiplicity-jet observation graph has full vertical fibre, whose dimension is total Xi multiplicity.

## Goal

Distinguish horizontal RH defect from nilpotent multiplicity: off-line exponential character verticalizes entire generalized eigenspace despite polynomial Jordan shear.

## Gates

- [x] 0 → 1: finite source-pure statement; full jet surjectivity + inverse Jordan countertransport + exponential-over-polynomial decay
- [x] 1 → 2: dependency-closed paper proof; no RH or simplicity premise
- [x] 2 → 3: `finrank_deningerMeyerFiniteXiJetGraphVertical_of_offline`; targeted build green; axioms `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4: independent novelty audit and standalone exposition

## Approach

Use fixed finite jet section. Countertransport each support block by inverse centered Jordan flow, lift through section, then apply forward isometric source flow. Output is fixed; source norm is polynomial times `exp (-n (Re ρ - 1/2)^2)` and tends to zero.

## Log

- 2026-08-24 — Meyer already identifies zero order with algebraic multiplicity; new claim is completion-relation defect, not spectral realization.
- 2026-08-24 — formalized in `DeningerMeyerHalfDensityFiniteXiJetVerticalDefect.lean`.
