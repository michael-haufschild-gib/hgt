# W3: exact extremal blind function

- **ID:** W3-EXACT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0611/obstacles-summary.md`, W3.
- **Statement:** A nonzero real test has `Φ=Ξg`, with `g` holomorphic and zero-free on a strip wider than the critical strip, exact integer blindness, and zero pole–archimedean energy.

## Mathematical boundary

The existing receiver gives rigidity of every Weil-positive system and `RH ↔ PBAP` from this object. The corpus already proves that equivalence unconditionally (`primeBlindPositive_four_tier_equivalence`). The new result supplies the exact optimizer. Positivity of the entire blind program remains separate.

The Carlson growth obstruction includes wider Mellin-strip decay and logarithmic-room integrability hypotheses. These are separate from the strip bounds used in this construction.

## Results

- [Full multiplicity capacity](w3-power-divisor-capacity.md): a nonzero source carrying `Ξ^k` and decaying with double-exponential exponent `b` satisfies `kb≤2`.
- [Theta-square boundary](w3-theta-square-boundary.md): `k=2`, `b=1` is attained by a strictly positive, nonblind source.
- [Positive-real strip](w3-arc-multiplier-positive-strip.md): every arc probability measure gives `Re R(z)>0` on `|Im z|≤501/1000`. The principal square root retains positive spectral decay and introduces no strip zeros.
- [Exact test](w3-single-exact-blind-test.md): the annihilating measure gives `Φ=Ξsqrt(R)`; scalarization preserves its full autocorrelation. `exists_nonzero_xiDivisible_blind_null_test` is unconditional.
- [Sharp blind correlation](w3-exact-blind-correlation-boundary.md): the actual correlation attains exponent one, with every larger exponent excluded by the full squared divisor. `exactExtremalTest_sharp_correlation_tail` formalizes both bounds.

## Lean

All seven modules in `BiScaleUncertainty/ExactExtremal/` passed individual
`lake --old env lean` checks and are imported by `BiScaleUncertainty.lean`.
