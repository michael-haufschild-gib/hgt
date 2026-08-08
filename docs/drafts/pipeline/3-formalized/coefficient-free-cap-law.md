# Coefficient-free bounds cannot beat the constant sequence

- **ID:** coefficient-free-cap
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** If `B` majorises `Φ g` for every bounded completely multiplicative `g`, and
  `L ≤ Φ(1)`, then `L ≤ B`. If moreover the right-hand side is a function of the moduli alone, then
  `L ≤ B(‖f‖)` for every unimodular completely multiplicative `f`.

## Goal

Three architectures in this corpus turned out to be capped at the trivial size, and the arguments were
the same each time:

* `5-failed/modulus-first-vertical-integral-no-go.md` — the vertical integral of the modulus;
* `5-failed/ghs-prime-saving-master-bound-is-trivial.md` — any coefficient-free majorisation of the two
  GHS sieve mean squares;
* the same card's later section — the unconditional mean-square Cesàro chain, including the improved
  dyadic form.

In each case the bound's right-hand side does not mention the coefficient sequence — because it was
majorised through `‖a_n‖ ≤ A log n`, or because it is built from `‖a_n‖` alone — and the bound holds for
*every* bounded completely multiplicative sequence. Instantiating at the constant sequence `1`, whose
functional value is the trivial size, then bounds the right-hand side from below. Rediscovering that per
route is waste; worse, it invites reading each new estimate as progress.

## The law

`le_of_coefficientFree_bound` makes the test mechanical: to kill a route of this shape, exhibit

1. its bound as a `∀ g` statement whose right-hand side is sequence-free, and
2. a lower bound for the functional at the constant sequence.

Nothing about the analytic estimate enters, so no sharpening of it can evade the conclusion. That is the
substance: the caps are not quantitative accidents.

`le_of_modulusOnly_bound` is the sharper form. A right-hand side depending on the sequence only through
the moduli cannot separate *any* unimodular completely multiplicative sequence from the constant one —
which is the relevant comparison for the Liouville function, whose moduli are identically `1`. (For
Möbius the comparison is with `λ` rather than with `1`, since `‖μ(n)‖` vanishes off the squarefree
integers.)

`trivial_le_cesaro_dyadic_bound_of_law` recovers the Cesàro cap from the law, confirming that the
general test reproduces the hand-made instance.

## Lean

| Statement | Module |
|---|---|
| `le_of_coefficientFree_bound` | `RHTower/Sieve/CoefficientFreeCap.lean` |
| `le_of_modulusOnly_bound` | `RHTower/Sieve/CoefficientFreeCap.lean` |
| `trivial_le_cesaro_dyadic_bound_of_law` | `RHTower/Sieve/CoefficientFreeCap.lean` |

Unconditional: `[propext, Classical.choice, Quot.sound]`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3
- [ ] 3 → 4

## Log
- 2026-08-09 — created in 3-formalized; the mechanism behind three separate no-gos stated once.
