# Infinite-base Difference Galois for L-functions

## Identity

A standalone Lean 4/mathlib formalization track for the elementary Tier A core of the
infinite-base difference-Galois draft for L-functions. The current product is a truthful formal ledger,
not a proof of RH and not a formalization of the conjectural field.

## Constraints

| Constraint | Rule |
|---|---|
| Zero `sorry` | The Lean tree carries exactly zero `sorry`. Never add one. |
| Axiom-clean | Audited Tier A theorems must depend on exactly `[propext, Classical.choice, Quot.sound]`. |
| Toolchain pinned | Lean + mathlib `v4.30.0`; verify mathlib names with `lake env lean /tmp/probe.lean`. |
| Honest frontier split | Tier B/C draft material is not a Lean theorem unless proved. Do not encode conjectures as axioms. |
| Standalone subtree | Keep private coordination logs and parent-workspace notes out of this publication subtree. |
| No push without go | Do not push or publish without Michael's explicit instruction. |

## Commands

| Command | Purpose |
|---|---|
| `cd formal && lake exe cache get` | Fetch prebuilt mathlib cache. |
| `cd formal && lake build` | Build the Lean library. |
| `bash scripts/check_axioms.sh` | Axiom + `sorry` audit. |
| `cd formal && lake env lean /tmp/probe.lean` | Scratch name checks and axiom probes. |
