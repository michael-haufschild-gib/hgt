# Theorem A as one theorem on a scheme (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **53**.
Continues [[research/scheme_horizon_expansion_2026_08_06]].

## `SchemeTheoremA.lean`

**`scheme_eigenvolume_horizon_theorem`** — one statement, five conjuncts:

1. `ordAt g z = 0 ∨ ordAt g z = −1` — the horizon is a **reduced divisor** (card (2), (5))
2. `ordAt g z ≠ 0 → ordAt g z = −1`
3. `ordAt g z ≠ 0 ↔ ordAt g (F z) ≠ 0` — **total invariance** (3)
4. `ordAt g z = 0 → e z = 1` — **unramified off the horizon** (4)
5. `e z − 1 = e z * boundary (F z) − boundary z` — **`R = f*D − D`** (6)

Hypotheses: pullback law, Jacobian order, eigenvolume condition, surjectivity of the divisor map,
and pointwise expansion on the horizon.

## Dependency status of those hypotheses

- pullback law — proved (`ord_functionFieldMap_eq_mul_ramification`, module 17)
- Jacobian order `e − 1` — proved (`addVal_generator_differentIdeal`, module 50)
- eigenvolume condition — proved from a unit multiple (module 21) and from an invariant coframe
  (module 34)
- surjectivity of the divisor map — supplied
- **ramification along the horizon — the only genuinely external input (Step 4)**

## Gate

`formal_tools.py lint --check-generated` **passed cleanly**.

## Repo note

`pgrep -f "lean --"` showed 1 process; `ps` confirmed it belongs to a **concurrent agent's** session
(different shell snapshot, building `RHTower`).  Always check the snapshot path before concluding a
process is yours.

## Remaining for Theorem A

1. Step 4 globally: ramification along the horizon (`N¹`/int-amplification route).
2. Sheaf of differentials on a scheme (presentation of `K_X = f^*K_X + R_f`).
3. Corollary B: MMP.
