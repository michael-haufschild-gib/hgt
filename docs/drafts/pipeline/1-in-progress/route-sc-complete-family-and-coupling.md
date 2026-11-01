# SC: complete-family realization and coupling

- **Stage:** 1-in-progress
- **Source:** `docs/reports/review-0111/route-SC.md`.
- **Goal:** Resolve all seven main obligations and four heat obligations with unconditional Lean proofs.

## Completed

**SC1.** One fixed nonnegative smooth unit profile realizes every finite
`ratCorr` Gram as a positive-mass-weighted complete-matrix compression limit
at the same overlap `2·loglog N·(logloglog N)²`. Positivity on the rational
boost-mass-zero hyperplane is equivalent to eventual complete-family
pole-hyperplane positivity at this single multiple. The equivalence uses
compression index at most one and zeta index parity, without assuming exact
moment preservation by the approximating packets.

Proof and exact declarations:
[universal critical overlap](../3-formalized/finite-rational-correlation-grams-at-critical-overlap.md).
The new profile, Gram limit and final direct hyperplane audit pass with only
`propext`, `Classical.choice`, and `Quot.sound`. Both umbrellas are wired.
Actual positivity remains unproved.

**Heat a.** `negIndex_heatArchState_eq_one_of_eighth_le` gives index one for
every `c>0` and `t≥1/8` in `TheHeatDeformedArchimedeanState.lean`.
Its transitive axiom audit and that of
`riemannHypothesis_iff_negIndex_heatArchState_const` pass with only standard
axioms. This supplies the certified upper-time calibration.

## Remaining source obligations

2. Bounded coupling on the natural-exponent cone implies RH when maximal zero width is unattained.
3. Exclude finite nonzero Weil index.
4. Transfer finite-sieve Hodge positivity to the global inter-tower form.
5. Prove an arithmetic finite-index ceiling.
6. Prove a square decomposition for the dilation form itself on a boost-zero two-prime lattice.
7. Prove glued index at most one, equivalently bounded two-prime lattice coupling.

Heat b: `N(t)≤exp(A·t^(−a))`, `a<1`; heat c: a uniform count;
heat d: no index jumps on `(0,1/8]`.

## Cone boundary

The existing double-pole argument requires an attained maximal real part.
Below the supremum its geometric expansion diverges for deeper zeros.
Continuation across the boundary does not isolate residues of an infinite
accumulating pole series.

`le_norm_paperFT_upow` already gives
`(|sinh(Im z)|/‖z‖)^4≤|B̂(z)|`, hence polynomial nonvanishing away from the
critical line. `two_prime_alias_bound_in_Δ` gives joint phase separation

`|Δ log p−2πk₁| log q + |Δ log q−2πk₂| log p ≥ c·min(|Δ|,(2+|Δ|)^(−C))`.

Neither controls residue cancellation while real parts approach an unattained
supremum. A comparison involving the width gap and zero height remains missing.

## Other boundaries

The finite-sieve Hodge theorem concerns the matched prime form after a scalar
subtraction. The Gamma and mixed-term comparison needed for the complete
Weil form is not supplied by that uniform index bound.

`exists_nonrealZeroCount_and_collisionMass_le_twoThirds` bounds the heat count
by `C·R(t)·log(2+3R(t))`, where
`R(t)=max(X₀,2π·exp((2/3+ε)/t))+1`. The `2/3` improves the coefficient of
`1/t`, not its power; it does not provide heat b.
