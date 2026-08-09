# A uniform bound on all Báez-Duarte distances

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## What is proved

`RHTower/UniformDistanceBound.lean`. Every earlier bound was for a single section. Monotonicity of the distance
in the family (`bdDist_mono`) upgrades the best single-generator bound to the whole sequence, because the
discrete section of length `N` contains the modulus `4` as soon as `N ≥ 4`:

**`bdDistDiscrete_sq_le_quarter` — `d_N² ≤ 1 − (log 2)²/(4·((3log 2)/8 − π/32))` for every `N ≥ 4`.**

This is the first statement here that constrains the *entire* sequence rather than one section, and it is
unconditional and symbolic.

## Why this is the ceiling of the method

The value is fixed — it does not improve with `N` — and it cannot be improved much by this route:

* by `SingleGeneratorUseless`, no single modulus gives a gain better than `O((log m)²/m)`, so no other choice of
  one generator beats `m = 4` by more than a constant;
* a bound uniform in `N` that *tended to `0`* would be `d_N → 0`, i.e. the Riemann hypothesis. So the only way
  past a fixed constant is the collective estimate that remains open. There is no unconditional theorem of this
  shape waiting to be found: an upper bound on the collective gain staying away from `1` for all `N` would
  refute RH, and a bound reaching `1` is RH.

The complementary floor is now proved in the same formulation, not only for step vectors:
`DistancePositivity.bdDistDiscrete_ge_factorial_floor` gives `√(1/(N!(N!+1))) ≤ d_N` and hence
`bdDistDiscrete_pos : 0 < d_N` for every `N`, by transporting the arithmetic obstruction through
`bdGen_bdDiscrete_eq_stepVec` and `bdTarget_eq_stepVec`.  So the picture is: each `d_N` is strictly positive,
the whole sequence sits below the constant above from `N = 4` on, and **whether the infimum is `0` is exactly
RH.**

That is where the lane ends unconditionally, and this card is the statement of it.
