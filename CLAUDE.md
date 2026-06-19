# Infinite-base Difference Galois for L-functions

## What this is

A standalone subtree with two parts:

- **Ledger** — a Lean 4 / mathlib library (`formal/`) that machine-checks the elementary,
  finite/multiplicative core of the draft below. It is axiom-clean and carries zero `sorry`.
- **Drafts** — five Markdown research drafts (`docs/drafts/`) founding a nascent field,
  *multi-`q`-difference Galois theory for hypertranscendental L-functions*. They are
  conjectural and air-marked throughout.

The drafts are research toward the Riemann Hypothesis. The Lean tree formalizes only what is
elementary and proved; it is not a proof of RH and contains no conjecture as a theorem or axiom.

## Current invariants (state, not aspiration)

| Invariant | State |
|---|---|
| `sorry` in the Lean tree | zero |
| Axioms of audited theorems | exactly `[propext, Classical.choice, Quot.sound]` (19 theorems) |
| Toolchain | Lean + mathlib `v4.30.0` (pinned in `lean-toolchain`, `lakefile.toml`) |
| Tier coverage in Lean | Tier A only (elementary); Tier B/C live in the drafts |
| Publishing | not pushed or published without Michael's explicit instruction |

## Documentation (auto-loaded)

@docs/architecture.md
@docs/testing.md
@docs/meta/styleguide.md

## Commands

| Command | What it does |
|---|---|
| `cd formal && lake exe cache get` | Fetches the prebuilt mathlib cache. |
| `cd formal && lake build` | Builds the Lean library. |
| `bash scripts/check_axioms.sh` | Runs the axiom + `sorry` audit over the 19 cited theorems. |
| `cd formal && lake env lean /tmp/probe.lean` | Runs a scratch Lean file (e.g. `#print axioms`, name checks). |

`scripts/check_axioms.sh` falls back to `~/.elan/bin` for `lake` if it is not already on `PATH`.
