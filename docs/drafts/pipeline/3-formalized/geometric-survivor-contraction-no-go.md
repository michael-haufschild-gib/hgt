# Geometric survivor contraction no-go — Lean certificate

- **ID:** `geometric-survivor-contraction-no-go`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean) / `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `Collatz_as_Pushforward.pdf`, Sections 16–18
- **Statement:** Strict factor-`1/2` decay of a positive geometric weighted observation can coexist with an orbit that never reaches the terminal state.

## Why this is retained

The attached paper's blurred-closure criterion needs an explicit lower-bound faithfulness condition. A strict weighted contraction alone can only force the observed weight toward zero; it does not force finite absorption. The closed countermodel provides a reusable audit guard for every smoothing, readout, or finite-carrier argument in this project.

## Lean certificate

- Module: `formal/GaloisForLFunctions/HTGeometry/GeometricSurvivorContractionNoGo.lean`
- Umbrella: `GaloisForLFunctions.HTGeometry`
- Main theorem: `GaloisForLFunctions.HTGeometry.strict_weight_decay_not_finite_absorption`
- Status: unconditional, closed, axiom-clean; no analytic, Collatz, or numerical premise.

## No-go closure

- **Exact killing mechanism:** a positive geometric observation drops by exactly one half under `n ↦ n + 1`.
- **Strongest positive survivor:** the theorem identifies the exact missing hypothesis: a lower bound that keeps every sharp survivor visible in the chosen norm/readout.
- **New insight:** strict contraction is usable for pointwise termination only after a stated no-loss lower bound links persistent states to nonvanishing observed mass.
- **Status:** Lean formalized. This is standard counterexample infrastructure, not new scientific knowledge.

## Verification

`lake env lean GaloisForLFunctions/HTGeometry/GeometricSurvivorContractionNoGo.lean`

## Log

- 2026-08-17 — formalized after audit of *The Abel–Collatz Resolvent*.
