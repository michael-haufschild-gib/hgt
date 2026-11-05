# Vinogradov–Korobov caps for the window-port flux

- **ID:** vinogradov-korobov-window-caps
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** review-0411 §2.1, A26.

## Target

For every sufficiently high Burnol unit window, replace
`σ_m = 1 − 1/(116 log(m+5))` by
`1 − vkZeroFreeWidth(m+5)/2`, retaining a prefix schedule `C(√m+1)`.
Prove the outer-cap cancellation identity, the resulting vertical-flux exponent,
and transfer the inner-cap stage receivers to this abscissa.

## Proof

Write `w(G)=10⁻⁸(log G)^(−2/3)(loglog G)^(−5/3)`, the corpus's proved VK width.
Eventually `1/log G≤w(G)`. Monotonicity and the xi zero-free theorem give
`Re ρ≤1−w(m+5)` for every xi zero in a sufficiently high Burnol unit window.

At `N≥polySqrtPrefix 1 m`, every theta-prefix zero lies within `1/(16(m+6))`
of an xi zero in the same window. This error is at most `w(m+5)/16`, so the
closed outer rectangle starting at `1−w(m+5)/2` is zero-free. Cauchy's theorem
gives exact cap cancellation and vertical growth `exp((1/2−w(m+5)/2)t)`.

Keep the classical cap on the finitely many lower windows. The resulting inner-cap
reading equals `rightHalfPort` exactly, including its off-line source decomposition.
For degree `k`, use `max(polySqrtPrefix k m, polySqrtPrefix 1 m)`, still a constant
multiple of `√m+1`. The stabilized Fredholm index is independent of the prefix:
integrability at any later stabilized prefix forces index zero at every stabilized
prefix. Thus enlarging the threshold preserves both the fixed-degree corridor
equivalence and the all-polynomial-stage RH equivalence.

## Lean

`ConjugateDiagonalGeometry/WindowPortFlux/VinogradovKorobovCapsAndStageReceivers.lean`:

- `exists_vkWindowCap_zeroFree`, `exists_vkWindowCap_cancellation`.
- `vkInnerCapFlux_eq_rightHalfPort`, `vk_innerCap_source_identity`,
  `vk_integrable_innerCap_iff_offLineSource`.
- `polynomialStage_cofinal_prefix_iff`, `fixedDegree_cofinal_prefix_iff`.
- `vkPolynomialPrefix_eq`, `vk_innerCap_allPolynomialStages_iff_riemannHypothesis`,
  `vk_innerCap_fixedDegree_iff_invPoly_corridor`.

Final direct Lean check passed. Six transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Project imports are acyclic;
CDG umbrella imports the module and was not compiled.

The inner-cap integrability assertion itself remains the separate RH-strength
obstacle B19; the contour and receiver composition does not prove it.
