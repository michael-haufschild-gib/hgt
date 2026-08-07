# The weighted Euler coefficient layers are subspaces, and carry a linear reader

- **ID:** weighted-euler-layers-are-subspaces
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** audit of `RHTower/WeightedEulerCoefficientSpaces` against the reader layer
- **Statement:** The three prime-coefficient layers `T_1 ⊆ M_0 ⊆ M_log` are subspaces, and the signed
  Mertens mean is a linear functional on them that reads the constant coordinate.

## Goal

`WeightedEulerCoefficientSpaces` builds the layers from the seminorm
`marcinkiewiczLogQuotient b X = (1/log X) ∑_{p ≤ X} (log p / p) |b_p|`, proves the chain of inclusions
and exhibits strictness witnesses. What it does not record is that the layers are closed under the
vector-space operations, and it has no *linear* functional on them at all — everything there measures
size. Both gaps are filled here, so the downstream dual-reduction programme can treat the layers as
function spaces.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure
- [x] 1 → 2 fully-proven: complete proof, no open dependency
- [x] 2 → 3 formalized: Lean theorems below, targeted `lake build` green, axiom audit clean
- [ ] 3 → 4 publication-ready: not intended; this is infrastructure

## Internal corpus audit

- `[CORPUS]` `WeightedEulerCoefficientSpaces` — the three layers, the inclusions
  `memVanishingTailLayer_of_memCriticalSummableLayer` and
  `memMarcinkiewiczLogLayer_of_memVanishingTailLayer`, the strictness witnesses, the head/tail
  algebra (`primeLogMass_head_le`, `primeLogMass_head_add_tail`, `primeLogMass_tail_anti`), and the
  two-sided Mertens bounds for the unit field.
- `[CORPUS]` `WeightedEulerDualReduction`, `WeightedEulerRayNormEquivalence` — the consumers.
- `[CORPUS]` No closure property of any layer is stated, and no linear functional exists on them.
- `[NEW]` `RHTower/MertensPrimeMeanReader` supplies both.

## Content `[PROVED HERE]`

**The reader.** `mertensPrimeMean b X = (1/log X) ∑_{p ≤ X} (log p / p) b_p`, the signed companion of
the defining seminorm.

1. `tendsto_mertensPrimeMean_unit` — the constant field has Mertens mean one. This is Mertens' first
   theorem, consumed through the corpus's own two-sided bounds; no arithmetic is re-derived.
2. `abs_mertensPrimeMean_le` — `|mertensPrimeMean b X| ≤ marcinkiewiczLogQuotient b X`, tying the
   linear reader to the seminorm the layers are defined by.
3. `tendsto_mertensPrimeMean_head_zero` — heads are annihilated, because `primeLogMass_head_le` bounds
   a head mass uniformly in the cutoff while the normaliser diverges.
4. `tendsto_mertensPrimeMean_zero_of_vanishingTail` — **`M_0` is annihilated**, by splitting at the
   truncation supplied by `M_0` membership. This is sharp: `M_log` is too big, since the unit field
   lies in it with mean one.
5. `tendsto_mertensPrimeMean_of_vanishingTail` — the reader law on `M_0`. The `T_1` case
   (`tendsto_mertensPrimeMean`) is a one-line corollary through the corpus inclusion.
6. `mertensPrimeMean_const_unique` — the constant is unique, by limit uniqueness alone.
7. `tendsto_mertensPrimeMean_coordinate_zero` — the mean is blind to any single prime.

**The subspace structure.** `primeLogMass_smul`, `primeLogMass_add_le`,
`marcinkiewiczLogQuotient_smul`, `marcinkiewiczLogQuotient_add_le`, and then
`memCriticalSummableLayer_{smul,add}`, `memVanishingTailLayer_{smul,add}`,
`memMarcinkiewiczLogLayer_{smul,add}`. The `M_0` addition case moves both truncations to a common
`max P₁ P₂` using the corpus's `primeLogMass_tail_anti`.

Together: `T_1 ⊆ M_0 ⊆ M_log` is a chain of subspaces, `M_0 + R·1` is a direct sum, and the Mertens
mean is its coordinate.

## Hostile audit

- Unconditional throughout. The only arithmetic input is Mertens' first theorem, already in the
  corpus in prime form, and it enters only through the existing two-sided bounds.
- Not a renaming: the layer file has no linear functional and no closure property, and the sharp
  annihilation statement is on `M_0`, not on the `T_1` the reader was first proved for.
- No claim of RH relevance beyond infrastructure: this equips the weighted Euler dual-reduction
  programme, whose target is the super-source sampling decay `‖H(log p)‖ ≤ C p^{-σ₀}` at `σ₀ = 1`.

## Log

- 2026-08-07 — created in stage 3. `lake build` green (8657 jobs), axioms
  `[propext, Classical.choice, Quot.sound]` on every capstone.
