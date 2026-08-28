# HB AIME/BM global source incompatibility

- **ID:** HB-ABGSI
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB `DYN ORIENT LAND`
- **Statement:** A fixed scalar multiple of the source-derived fundamental AIME cross-branch QNM residue matches the exact unit-seed BM Peierls boundary target on every Xi fibre iff the scalar or absorbed seed vanishes and RH holds.

## Goal

Test first literal nonlinear gravitational source already present in corpus against exact global BM incidence, rather than another abstract carrier. Close AIME-only producer and identify necessity of genuinely new same-pole third-order `++-` dynamics.

## Gates

- [x] 0 → 1 in-progress: mandatory corpus search found AIME support theorem and BM zero-locus but no comparison theorem
- [x] 1 → 2 fully-proven: dependency-closed proof and exact same-pole correction law below
- [x] 2 → 3 formalized: Lean theorem, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone exposition

## Conjecture HC11

For every overtone `n`, normalization `c`, and absorbed seed `a`,

`(∀ q, c · AIMEResidue(a,q) = BMTarget(n,1,q)) ↔ ((c=0 ∨ a=0) ∧ RH)`.

Consequently no nonzero normalization of a nonzero AIME channel realizes global BM incidence.

The full residue has exact pointwise correction law

`Remainder(q) = JostDerivative(q) · BMTarget(q) - AIMENumerator(q)`.

On every critical Xi fibre this specializes to the nonzero forced counterterm
`Remainder(q) = -AIMENumerator(q)` for nonzero seed.

## Proof strategy

Use Hardy's unconditional critical-line Xi copy. BM target vanishes there, while AIME residue is nonzero exactly when seed is nonzero, so equality forces `c=0 ∨ a=0`. Then left side vanishes on every copy, forcing every BM target to vanish and hence RH by exact BM zero-locus. Converse follows from RH and the vanishing source factor.

For arbitrary third-order same-pole remainder, divide full numerator by exact nonzero simple-Jost
derivative and clear denominator. This uniquely solves the incidence equation for the remainder.
At a critical fibre BM target is zero, leaving precisely negative AIME numerator, which is nonzero
iff absorbed seed is nonzero.

## Novelty audit (2026-08-28)

Corpus search found no AIME/BM global comparison. Literature records absorption-induced mode excitation, exact gravitational topological-black-hole QNMs, and QNM conserved-bilinear residue normalization, but no all-Xi comparison with BM Peierls boundary incidence or RH classification. Primary references: Sberna--Bosch--East--Green--Lehner, [Nonlinear effects in the black hole ringdown: Absorption-induced mode excitation](https://arxiv.org/abs/2112.11168); Birmingham--Mokhtari, [Exact Gravitational Quasinormal Frequencies of Topological Black Holes](https://arxiv.org/abs/hep-th/0609028); Green--Hollands--Sberna--Toomani--Zimmerman, [Conserved currents for a Kerr black hole and orthogonality of quasinormal modes](https://arxiv.org/abs/2210.15935).

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEBMGlobalSourceIncompatibility`
- Theorems:
  - `forall_normalizedAIMEResidue_eq_unitBMTarget_iff`
  - `not_exists_nonzero_normalizedAIMEResidue_global_unitBMTarget`
  - `d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_samePoleSource`
  - `d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_forcedCounterterm_of_criticalLine`
  - `d4FullCrossBranch_samePoleSourceRemainder_ne_zero_of_unitBMTarget_of_criticalLine`
- Axioms: only Mathlib foundations `propext`, `Classical.choice`, `Quot.sound`.
- Direct `lake env lean` check and target-specific `lake build` pass; module wired into RHTower umbrella.
- No `sorry`, `admit`, added `axiom`, `opaque`, or `unsafe` declaration. Repository-wide lint reports only unrelated pre-existing unreachable modules.

## Log

- 2026-08-28 — conjectured from source-derived AIME nonvanishing, exact BM target zero-locus, and Hardy critical anchor.
- 2026-08-28 — paper proof closed; Lean source directly checks.
- 2026-08-28 — targeted build, axiom audit, umbrella wiring, and lint-scope audit completed.
