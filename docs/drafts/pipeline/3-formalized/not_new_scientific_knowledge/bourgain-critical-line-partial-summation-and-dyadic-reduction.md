# Bourgain critical-line partial summation and dyadic reduction

- **ID:** `bourgain-critical-line-partial-summation-and-dyadic-reduction`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) `[LEAN-PROVED] [BRIDGE]`
- **Source:** Classical Abel summation and dyadic dissection; Bourgain,
  *Decoupling, exponential sums and the Riemann zeta function*, Section 4.
- **Statement:** Uniform bounds for every partial logarithmic phase sum on
  each descending dyadic block of `(0,N]` control the exact critical-line
  Dirichlet polynomial, and hence `ζ(1/2+it)` with the corpus's explicit
  Euler--Maclaurin correction.

## Goal

Close the algebraic and finite-summation interfaces between Bourgain's
unweighted short exponential sums and the canonical corpus zeta carrier.
This is a reusable dependency of the unconditional `13/84` campaign; it does
not assert the missing exponential-sum bounds.

## Gates

- [x] 0 → 1: exact blockwise partial-sum statement and corpus connectors
  identified.
- [x] 1 → 2: finite Abel identity, monotone square-root weight estimate, and
  descending dyadic partition proved on paper.
- [x] 2 → 3: exact Lean theorems compile, axiom audit passes, umbrella wiring
  and formal lint pass.
- [ ] 3 → 4: publication crosswalk after full Bourgain proof is formalized.

## Lean certificate

- `RHTower.sum_Ioc_weight_mul_eq`
- `RHTower.norm_sum_Ioc_invSqrt_mul_le`
- `RHTower.norm_sum_Ioc_critical_cpow_le`
- `RHTower.sum_bourgainDyadicBlocks`
- `RHTower.norm_sum_Ioc_critical_cpow_dyadic_le`
- `RHTower.dirichletPoly_line_eq_critical_cpow_sum`
- `RHTower.norm_dirichletPoly_line_le_dyadic`
- `RHTower.norm_riemannZeta_line_le_dyadic_em`

Modules:

- `formal/GaloisForLFunctions/RHTower/BourgainPartialSummation.lean`
- `formal/GaloisForLFunctions/RHTower/BourgainDyadicDissection.lean`
- `formal/GaloisForLFunctions/RHTower/BourgainZetaReduction.lean`

Verification:

- `lake build GaloisForLFunctions.RHTower.BourgainZetaReduction` passes.
- Representative `#print axioms` output is exactly
  `[propext, Classical.choice, Quot.sound]`.
- `scripts/formal_tools.py lint` passes.

## Scientific status

`[BRIDGE] [LEAN-PROVED] [REDISCOVERED]`. Mathematics is classical and not new.
The formal result removes the previously implicit “partial summation and
dyadic dissection” sentence from Bourgain Section 4. Remaining open cores are
the conductor-length symmetric AFE and the exponential-sum estimates.

## Log

- 2026-07-25 — paper proof closed, formalized, targeted build and axiom audit
  passed, and modules wired into `RHTower.lean`.
