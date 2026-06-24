# Ihara Quadratic Block Selector Lean Model

- **ID:** ihara-quadratic-block-selector-lean-model
- **Stage:** 3-formalized
- **Type:** PROOF-LAB / NOT-NEW
- **Lean:** `formal/GaloisForLFunctions/IharaBlockSelector.lean`

## Purpose

This card is not a novelty claim about Ihara zeta, Ramanujan graphs, or a new
proof of a known theorem. The point is to build a compact Lean comparison object
for the team:

`functional-equation symmetry + Euler-product-like block`

does not select the critical boundary by itself. A separate spectral/index
selector is needed.

## Model

For a regular-graph Ihara-style quadratic block, define

`P_lambda(u) = 1 - lambda*u + q*u^2`, with `q > 0`.

The critical-circle condition is expressed using squared radius:

`Complex.normSq u = q^(-1)`.

The selector is the discriminant/spectral bound:

`lambda^2 <= 4*q`.

The off-circle index of one block is

`kappa(lambda) = 0` if `lambda^2 <= 4*q`, and `1` otherwise.

## Formalized Claims

The Lean file proves:

1. **Reciprocal identity.**
   For `u != 0`,
   `q*u^2*P_lambda((q*u)^(-1)) = P_lambda(u)`.

2. **One-block selector.**
   For `q > 0`,
   all zeros of `P_lambda` lie on the circle `normSq = q^(-1)` iff
   `lambda^2 <= 4*q`.

3. **Finite product index.**
   A finite family of blocks satisfies the model RH condition iff the sum of
   the block off-circle indices is zero.

4. **FE-only insufficiency.**
   For every `q > 0`, Lean constructs a `lambda` such that the reciprocal
   identity holds but `lambda^2 <= 4*q` fails.

## Why This Is Useful

Bottcher/u0 and Hurwitz are obstruction engines: finite algebraic relations are
broken by monodromy, local orbits, and tail data. This Ihara block model tests a
different RH-relevant shape:

`reciprocity / functional equation -> not enough`

`spectral bound / positivity / index -> selector`

That is the intended lesson for RH-facing work. The exercise is not to learn
Ihara theory by formalizing a mature theorem; it is to have a small verified
object where the missing ingredient is visible in Lean.

## Lean Verification

Targeted checks run:

- `lake env lean GaloisForLFunctions/IharaBlockSelector.lean`
- `lake build GaloisForLFunctions.IharaBlockSelector`
- `/tmp/ihara_axioms.lean` importing the module and printing axioms for:
  - `zerosOnCriticalCircle_iff_spectral_bound`
  - `finiteBlockRH_iff_totalOffCircleIndex_eq_zero`
  - `reciprocal_identity_does_not_force_spectral_bound`

The axiom report contains only standard mathlib foundations:

`propext`, `Classical.choice`, `Quot.sound`.

## Comparison Target

Use this as the third toy axis when the other Lean proofs settle:

| Toy | Engine | RH Lesson |
| --- | --- | --- |
| Bottcher/u0 | unbounded monodromy obstruction | finite algebraic relations cannot absorb infinite branching |
| Hurwitz | local orbit plus tail separation | diagonal monodromy needs external separation data |
| Ihara block | reciprocal FE plus index selector | FE/product symmetry needs positivity or spectral bounds to select the line |

## Status

Formalized. Not new as theorem/proof. Valuable only as an RH-facing proof-shape
comparison object.
