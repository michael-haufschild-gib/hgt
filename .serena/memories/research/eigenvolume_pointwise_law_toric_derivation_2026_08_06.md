# Pointwise local law + toric derivation (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Modules **30 and 31**.
Fixes the interface defect recorded in
[[research/toric_eigenvolume_certificate_2026_08_06]].

## `EigenvolumePointwiseLaw.lean` (30) — interface fix

The packaged laws (`formOrder_pullback_shiftLaw`, `eigenvolume_shiftLaw`) quantify over **all**
prime divisors because they are phrased through `divisorBelow`, which needs
`hwd : ∀ P, (comap φ P.1).height = 1`.  **No concrete instance can supply that**, so those theorems
were unusable in practice.

- **`formOrder_shiftLaw_at`** — same law with `P`, `Q`, `hQ : Q.1 = comap φ P.1` as explicit
  arguments.  Assumes nothing about any other prime divisor.
- **`formOrder_eigen_shiftLaw_at`** — the eigenvolume version.

Lesson for future interfaces here: state local laws pointwise first, and derive the
quantified/packaged version from them — never the other way round.

## `ToricHorizonDerivation.lean` (31) — the machinery exercised

- `prod_X_ne_zero`, `det_jacobian_monomialMap_ne_zero`
- **`toric_shiftLaw`** — the local order law at a coordinate divisor obtained *from the general
  law*, with ramification index (`orderAt_coordDivisor_monomialMap_X`), Jacobian order
  (`orderAt_coordDivisor_det_jacobian`) and eigenvolume condition
  (`eigenvolume_condition_of_unit` + `exists_unit_det_jacobian_mul_prod`) supplied by the monomial
  map.
- **`toric_formOrder_eq_neg_one`** — `c = −1` via `ramificationShift_fixed_eq_neg_one` (Step 4's
  expansion fixed-point argument), needing `1 < e i`.

**Framing**: the same value is computable directly (`formOrder_coordDivisor_log`), so this is a
**test of the general proof**, not a new computation.  Keep saying so.

## Lean traps

- `set φ := …` rewrites the goal but **not** goals produced later by applying lemmas about the
  original term; `rw [h]` then fails to find the pattern.  Use
  `show <original form> ; exact h` instead.
- `simp [orderAt]` does not reach `addVal 0 = ⊤`; spell it
  `simp only [orderAt, map_zero, AddValuation.map_zero]`.
