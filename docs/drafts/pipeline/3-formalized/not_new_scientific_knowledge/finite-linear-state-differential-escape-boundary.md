# Finite linear-state differential escape boundary

- **ID:** `finite-linear-state-differential-escape-boundary`
- **Stage:** 3-formalized
- **Type:** EXACT LINEAR PHASE BOUNDARY / CORPUS BRIDGE
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [PARENT DIFFERENTIAL-MODULE THEORY]`
  `[NOT NEW SCIENCE] [NOT AN RH RESULT]`
- **Source:** research programme 5 successor from
  `../../5-failed/operator-presentation-bounded-innovation-stabilization.md`
- **Statement:** An observable in a finite-dimensional linear state preserved by differentiation
  satisfies an explicit nonzero scalar linear differential equation; hence an HT observable cannot
  belong to such a state.

## Exact theorem

Let `F -> E` be a field extension, let `E` carry a derivation `D`, and let `V <= E` be an
`F`-subspace of finite dimension `m`.  Assume

```text
x in V,
D(V) subset V.
```

Then every jet `D^r x` belongs to `V`, so there are coefficients `c_0,...,c_m in F`, not all zero,
with

```text
c_0 x + c_1 D x + ... + c_m D^m x = 0.                  (1)
```

Consequently `x` is differentially algebraic over `F`.  More sharply, `(1)` is the exact linear
or holonomic certificate over `F`.  Its contrapositive is

```text
x hypertranscendental over F
  => x lies in no finite-dimensional F-linear D-invariant state.       (2)
```

## Paper proof

Induct on `r` to obtain `D^r x in V`: the base case is the membership assumption and the successor
case is derivative invariance.  The first `m+1` jets are therefore `m+1` vectors in the
`m`-dimensional space `V`, hence linearly dependent.  The resulting nonzero coefficient vector is
exactly `(1)`.  A nonzero linear differential equation is a nonzero algebraic differential
equation, giving differential algebraicity.  Taking the contrapositive gives `(2)`.  There is no
open core.

## Programme-5 significance

This theorem separates the linear and nonlinear phases which the original programme conflated.
Finite-dimensional **linear** derivative state forces holonomicity; finite-transcendence
derivation-closed field state only forces differential algebraicity.  Neither conclusion follows
from a finite presentation or bounded per-depth increments.

`FiniteObservableKoopmanBoundary.lean` contains a useful constant-coefficient observable model, and
`FiniteDifferentialSystemAlgebraicity.lean` treats coordinates of a presented finite differential
system.  The missing generic interface supplied here is relative to an arbitrary coefficient
field `F` and an arbitrary finite-dimensional `F`-submodule of the ambient field.

## Lean theorem surface

Module: `formal/GaloisForLFunctions/HTGeometry/FiniteLinearStateDifferentialEscape.lean`.

- `DerivationInvariantSubmodule`
- `differentialJet_mem_of_mem_derivationInvariantSubmodule`
- `exists_nonzero_finite_jet_linearCombination_eq_zero_of_mem_derivationInvariantSubmodule`
- `differentialAlgebraicOver_of_mem_derivationInvariantSubmodule`
- `not_mem_derivationInvariantSubmodule_of_hypertranscendentalOver`

## Gates

- [x] 0 -> 1: exact linear replacement isolated
- [x] 1 -> 2: dependency-closed paper proof complete
- [x] existing Lean surface checked before formalization
- [x] novelty and parent-theory verdict assigned
- [x] 2 -> 3: unconditional Lean theorem batch
- [x] targeted touched-file check
- [x] touched-slice formal lint and axiom audit

## Log

- 2026-07-17 -- Extracted as the exact linear positive residue of programme 5 after the general
  stabilization headline was falsified.
- 2026-07-17 -- Promoted to Stage 3 after direct cached compilation.  `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  The project lint reports no proof debt or
  reachability defect for this module; its nonzero repository-wide exit is an unrelated pre-existing
  umbrella-reachability baseline.
