# Continuous integral-lattice rigidity

- **ID:** `continuous-integral-lattice-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `RHTower/ArgumentVariation.lean`
- **Statement:** A continuous real-valued function on a nonempty closed interval whose values lie
  in `δℤ`, for any `δ != 0`, is constant.

## Goal

Replace the duplicated `πℤ` and `2πℤ` interval-rigidity proofs in the argument-variation chain by
one orientation-free lattice law. This is the exact Prop interface needed after a value-reflection
or exponential phase identity has shown that a continuous phase defect is integrally quantized.

## Gates

- [x] 0 → 1  in-progress: exact local and generated APIs searched for a generic lattice law
- [x] 1 → 2  fully-proven: dependency-closed proof recorded below
- [x] 2 → 3  formalized: exact source check, leaf build, and axiom audit passed
- [ ] 3 → 4  publication-ready: use the generic interface in future phase-reflection consumers

## Paper proof

Let `F : [a,b] -> R` be continuous and suppose `F(t) = n_t δ` for some integer `n_t` at every
point, with `δ != 0`. Replacing `δ` by `-δ` and every `n_t` by `-n_t` if necessary, assume
`δ > 0`.

If `F(t) != F(a)`, then `n_t != n_a`; hence

```text
|F(t) - F(a)| = |n_t - n_a| δ >= δ.
```

According to the sign of `F(t)-F(a)`, the intermediate value theorem supplies a point between
`a` and `t` where the value is either `F(a) + δ/2` or `F(t) + δ/2`. But two lattice values cannot
differ by `δ/2`: cancelling `δ` would make an odd integer equal an even integer. This contradiction
proves `F(t)=F(a)` for every `t`.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/ArgumentVariation.lean`.

Principal declaration:

- `continuousOn_int_mul_const` with only `δ != 0`.

Compatibility wrappers:

- `continuousOn_int_mul_two_pi_const`;
- `continuousOn_int_mul_pi_const`.

Both wrappers now invoke the common theorem. Existing winding-number and carrier-phase consumers
retain their original interfaces.

Validation on 2026-07-19:

- exact source check: `lake env lean GaloisForLFunctions/RHTower/ArgumentVariation.lean` — PASS;
- exact leaf build: `lake build GaloisForLFunctions.RHTower.ArgumentVariation` — PASS;
- axiom audit of the general theorem and both wrappers — only
  `[propext, Classical.choice, Quot.sound]`.

## Novelty audit

This is a standard connectedness/discreteness principle, not new scientific knowledge. Its value
is structural: one orientation-free law now closes every interval-valued integral phase interface,
subsumes the separate `πℤ` and `2πℤ` theorems, and removes the need to duplicate an intermediate-
value/parity argument for each future reflection lattice.

## Log

- 2026-07-19 — randomized consolidation draw selected `RHTower/ArgumentVariation.lean`
- 2026-07-19 — corpus search found only the two specialized proofs and no generic local law
- 2026-07-19 — generalized from positive spacing to arbitrary nonzero lattice generator
- 2026-07-19 — exact source check, leaf build, and axiom audit passed; promoted to Stage 3
