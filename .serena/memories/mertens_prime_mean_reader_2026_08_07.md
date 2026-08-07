# The signed Mertens mean: a linear reader on the weighted Euler layers (2026-08-07)

Module `RHTower/MertensPrimeMeanReader.lean`, `lake build` green (8657 jobs), axioms
`[propext, Classical.choice, Quot.sound]`, in the RHTower umbrella.

## The gap it fills

`RHTower/WeightedEulerCoefficientSpaces` builds three prime coefficient layers `T_1 ⊆ M_0 ⊆ M_log`
from the SEMINORM `marcinkiewiczLogQuotient b X = (1/log X) ∑_{p≤X} (log p/p)|b_p|`. Everything there
measures size — there was no linear functional on the layers, and no statement that the layers are
subspaces.

`mertensPrimeMean b X = (1/log X) ∑_{p≤X} (log p/p) b_p` is the signed companion, and it is a reader.

## What is proved

- `tendsto_mertensPrimeMean_unit` — the constant field has Mertens mean 1. This IS Mertens' first
  theorem, consumed through the layer file's two-sided bounds `primeLogMass_unit_le` /
  `le_primeLogMass_unit` and its explicit `mertensPrimeConstant`. No arithmetic re-derived.
- `abs_mertensPrimeMean_le` — ties the linear reader to the existing seminorm.
- `tendsto_mertensPrimeMean_head_zero` — heads die because `primeLogMass_head_le` bounds a head mass
  UNIFORMLY in the cutoff while the normaliser diverges.
- `tendsto_mertensPrimeMean_zero_of_vanishingTail` — **`M_0` is annihilated**, via the head/tail split
  at the truncation supplied by `M_0` membership. This is the sharp statement: `M_log` is genuinely
  too big (the unit field lies in it with mean 1).
- `tendsto_mertensPrimeMean_of_vanishingTail` — the reader law on `M_0`;
  `tendsto_mertensPrimeMean` (the `T_1` case) is now a ONE-LINE corollary through the corpus
  inclusion `memVanishingTailLayer_of_memCriticalSummableLayer`.
- `mertensPrimeMean_const_unique` — the constant is unique, by limit uniqueness alone.
- `tendsto_mertensPrimeMean_coordinate_zero` — the mean is blind to any single prime.
- `memVanishingTailLayer_smul`, `memVanishingTailLayer_add`, `primeLogMass_smul`,
  `primeLogMass_add_le`, `marcinkiewiczLogQuotient_smul` — **`M_0` is a subspace**, which the layer
  file never states although it proves the strictness witnesses.

## Why it matters for the reader programme

Second instance of the reading pattern with a genuinely different reference: weight `log p / p`,
normaliser `log X`, constant reference field (Mertens) — versus weight `1/p`, exact unit mass,
escaping supports (Euler sieve, `mem:route_r/euler_sieve_subsumed_by_unit_profile_2026_08_07`). Two
independent instances is what keeps the "universal reading law" from being vocabulary.

It is NOT an instance of `IsCofinalUnitProfile`: Mertens is a HEAD average with asymptotically-unit
mass, not a tail average with exactly-unit mass and escaping support. The only common abstraction
would be "reads the reference to 1 and kills the ideal", which is near-tautological, so the two were
deliberately kept separate.

## Downstream context

`WeightedEulerCoefficientSpaces` is consumed by `WeightedEulerDualReduction` and
`WeightedEulerRayNormEquivalence` (dual reduction for the weighted Euler joint graph, super-source
sampling decay `‖H(log p)‖ ≤ C p^{-σ₀}` at the critical boundary `σ₀ = 1`). The reader and the
subspace facts are available to that programme.
