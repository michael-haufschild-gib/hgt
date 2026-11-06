# W3: exact extremal blind function

- **ID:** W3-EXACT
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean); sharp-tail extension in progress
- **Source:** `docs/reports/review-0611/obstacles-summary.md`, W3.
- **Statement:** A nonzero real test has `Φ=Ξg`, with `g` holomorphic and zero-free on a strip wider than the critical strip, exact integer blindness, and zero pole–archimedean energy.

## Mathematical boundary

The existing receiver gives rigidity of every Weil-positive system and `RH ↔ PBAP` from this object. The corpus already proves that equivalence unconditionally (`primeBlindPositive_four_tier_equivalence`). The new result supplies the exact optimizer. Positivity of the entire blind program remains separate.

The Carlson growth obstruction includes wider Mellin-strip decay and logarithmic-room integrability hypotheses. These are separate from the strip bounds used in this construction.

## Results

- [Full multiplicity capacity](../3-formalized/w3-power-divisor-capacity.md): a nonzero source carrying `Ξ^k` and decaying with double-exponential exponent `b` satisfies `kb≤2`.
- [Theta-square boundary](../3-formalized/w3-theta-square-boundary.md): `k=2`, `b=1` is attained by a strictly positive, nonblind source.
- [Positive-real strip](../3-formalized/w3-arc-multiplier-positive-strip.md): every arc probability measure gives `Re R(z)>0` on `|Im z|≤501/1000`. The principal square root retains positive spectral decay and introduces no strip zeros.
- [Exact test](../3-formalized/w3-single-exact-blind-test.md): the annihilating measure gives `Φ=Ξsqrt(R)`; scalarization preserves its full autocorrelation. `exists_nonzero_xiDivisible_blind_null_test` is unconditional.
- [Sharp blind correlation](../2-fully-proven/w3-exact-blind-correlation-boundary.md): the actual correlation attains exponent one, with every larger exponent excluded by the full squared divisor. Paper proof complete; Lean assembly pending.

## Completion gates

- [x] Explicit construction with unconditional analytic bounds and all integer moments.
- [x] Full Xi divisibility and real zero-faithfulness.
- [x] Exact receiver hypotheses discharged in Lean.
- [ ] New modules wired into owning umbrella; individual foreground Lean checks.

Exact existence is formalized. Prime-blind positivity remains separate; no RH conclusion is claimed.
