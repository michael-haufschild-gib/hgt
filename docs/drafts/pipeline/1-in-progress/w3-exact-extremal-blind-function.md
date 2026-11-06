# W3: exact extremal blind function

- **ID:** W3-EXACT
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0611/obstacles-summary.md`, W3.
- **Target:** Construct a nonzero strip-holomorphic `Φ = Ξ g`, with `g` zero-free on `ℝ`, whose spectral square has zero cosine moments at every `log n`, `n ≥ 2`; prove every decay and divisibility condition required by `xiDivisibleBlindTest_stripTest`.

## Mathematical boundary

The existing receiver gives rigidity of every Weil-positive system and `RH ↔ PBAP` from this object. Later corpus work already proves that equivalence unconditionally (`primeBlindPositive_four_tier_equivalence`). W3's missing content is the exact optimizer, not a new RH criterion. Existence of the extremal function and positivity of the blind program are distinct obligations.

Known constraints: logarithmic Carlson growth after removing the zeta divisor; double-exponential source-tail bounds from the density of simple critical zeros. Neither supplies the extremal function.

## Conjectures

1. Determine whether the strip-decay formulation itself admits a nonzero positive integer-blind spectral square. Resolve its exact analytic-strip obstruction before imposing the Xi divisor.
2. Construct a positive integer-blind square with the full Xi divisor and no extra real zeros, or identify the additional obstruction and formalize its strongest positive survivor.
3. Full multiplicity capacity: a nonzero double-exponential source carrying `Ξ^k` must satisfy `kb≤2`. `ExactExtremal/PowerDivisorCapacity.lean` passes Lean. For `k=2`, the theta self-convolution attains equality; formalized in `ExactExtremal/ThetaSquareBoundary.lean`. This supplies a boundary model, not integer blindness.
4. Scalar factorization of the existing twisted-arc blind mixture. `twistedArcMinimumPrinciple_holds` supplies an annihilating probability measure; `shiftedGamma_blind_of_twistedArc` supplies nonnegative weights with all required integer cosine moments zero. `arcGammaMultiplier` is holomorphic on a strip and strictly positive on the real spectral axis. Construct one analytic factor with controlled strip growth; do not assume a square root across complex zeros. `TwistedArcNullLaplacePositivity` additionally proves positivity on the imaginary segment `|y|≤3/2`, but not zero-freeness throughout that strip.
5. Positive-real strip: the multiplier has positive real part on `|Im z|≤501/1000`. Paper proof: `2-fully-proven/w3-arc-multiplier-positive-strip.md`. Near the origin the constant term dominates the factorial tail. Outside `|Re z|<7/5`, integral comparison bounds the total change of the normalized quadratic factors by `7/5`, forcing every product's real part positive. Formalize this estimate, then construct the principal square root and discharge the exact receiver.

## Completion gates

- [ ] Explicit construction with unconditional analytic bounds and all integer moments.
- [ ] Full Xi divisibility and real zero-faithfulness.
- [ ] Exact receiver hypotheses discharged in Lean.
- [ ] New modules wired into owning umbrella; individual foreground Lean audits and transitive axiom checks.

No existence claim or RH claim established.
