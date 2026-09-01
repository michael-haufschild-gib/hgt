# FZZ fixed-support Abel--Jacobi/Quillen replica no-go

- **ID:** FZZ-FS-AJQ-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/rh-current-frontier-map.md` · FZZ-P source edge
- **Statement:** Fixed-support replica normalization cancels every separated Abel--Jacobi/Quillen term, so no resulting value predicate selects zero radial twist.

## Goal

Kill fixed-support log-circle/Quillen producer for
`FZZLinearReplicaAreaDivisorPassive → Mellin completeness → RH`.

## Gates

- [x] 0 → 1: source-pure conjecture from corpus endpoint and FZZ genus-one formulas
- [x] 1 → 2: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3: Lean module and targeted build PASS; standard axioms only
- [ ] 3 → 4: standalone publication draft

## Approach

Hikida--Schomerus (C.12) makes torus holonomy depend on divisor support; Halder--Jafferis
(3.29)--(3.33) varies winding charge at fixed support. Thus replica deformation fixes Abel--Jacobi
holonomy. Subtraction cancels any separated additive Quillen term; division cancels any separated
group-valued determinant factor. Explicit neutral data realize every complex holonomy, so a constant
normalized response cannot distinguish `Im λ = 0` from `λ = i`.

## No-go closure

- **Exact killing theorem/mechanism:**
  `not_exists_fzzFixedSupportQuillenLogNormalizedResponse_value_selector` and
  `not_exists_fzzFixedSupportQuillenRatioNormalizedResponse_value_selector`.
- **Strongest positive survivor:** viable FZZ-P dynamics must contain a nonseparable mixed
  replica-charge/divisor-support term: support motion or prime-form/OPE branch localization before
  Jacobian integration.
- **New insight:** Quillen normalization choice is not open burden; charge/support separability is
  obstruction.
- **Status:** corpus research found no prior theorem; primary-literature audit through 2026-08-31
  found source formulas but no combined no-go or torus one-point evaluation. Lean module
  `GaloisForLFunctions.RHTower.FZZCigarParityFixedSupportQuillenReplicaNoGo`; direct check and
  targeted build PASS; axioms `[propext, Classical.choice, Quot.sound]`; umbrella wired. Global lint
  remains red only on unrelated pre-existing unreachable modules.

## Log

- 2026-09-01 — `[PROVED HERE]`; formalized and audited.
