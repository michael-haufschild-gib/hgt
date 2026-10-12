# Vinogradov–Korobov growth for every σ near 1, and local zero counts near the 1-line

- **ID:** vk-growth-general-sigma
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → Lean
- **Source:** JAS goal loop rows 86, 99, 107–108 (`jas-goal-loop-2026-10-09.md`); the [B] analysis needs unconditional local counts of zeros near Re s = 1
- **Statement:** For τ ≥ exp(exp 30), L = log τ, and w(L) ≤ κ := 1 − σ ≤ 1/(3·2^24): ‖ζ(σ + iτ)‖ ≤ C·L·exp(864·κ^{3/2}·L·log L). Hence, by Jensen, a disc of radius ≍ κ next to 1 + iτ contains O(κ^{3/2} L log L + log L) zeros.

## Goal
Extend the corpus VK growth bound (`norm_riemannZeta_le_vinogradovKorobov`, valid only within the VK width w(L)) to the Richert range κ ≤ κ₀. This is the input for:
1. unconditional local zero counts near the 1-line (Jensen);
2. the "collective spoilers are consistent with every unconditional count" step of row 86, which would then be in Lean;
3. Ford-type density near σ = 1 (B1), together with the corpus Halász–Montgomery machinery.

Non-circular: it uses only the corpus Vinogradov mean-value / dyadic saving and the derivative test.

## Gates
- [x] 0 → 1  in-progress: the corpus blocks adapt verbatim. The dyadic saving δ/4 ≥ ℓ²/(746496 L² log² L) is σ-free. The large-block derivative test saves Y^{−1/(3·2^24)}. κℓ − ℓ³/A ≤ κ^{3/2}√A with √A = 864 L log L.
- [x] 1 → 2  fully-proven: block, initial-segment and assembly bounds (see Approach)
- [x] 2 → 3 (growth part): `RHTower.Sieve.norm_riemannZeta_le_vinogradovKorobov_general` in `RHTower/Sieve/VinogradovZetaGrowthGeneralSigma.lean`; axioms clean; built with `lake build --old`
- [x] 2 → 3 (Jensen local count near the 1-line): `RHTower.zeta_disc_zeroCount_le_near_one_line` in `RHTower/ZetaNearOneLineLocalZeroCount.lean`; axioms clean

## Approach
1. Middle blocks (e^{L^{2/3}} ≤ Y, Y^22 ≤ τ): the prefix bound Pb = 12e^{20}Y^{1−δ/4} + 200Y^{1/2}, with Pb·Y^{−σ} ≤ 12e^{20}exp(κℓ − ℓ³/A) + 200 ≤ 12e^{20}exp(κ^{3/2}√A) + 200.
2. Large blocks (Y^22 > τ): 2560·Y^{κ − 1/(3·2^24)} ≤ 2560 for κ ≤ 1/(3·2^24).
3. Initial segment k ≤ N₀ = ⌈e^{L^{2/3}}⌉: Σ k^{−σ} ≤ N₀^κ(1 + log N₀).
4. Assembly: truncation at X ∈ [τ², 2τ²] as in the corpus; at most 3L + 1 dyadic blocks.

## Log
- 2026-10-12 — created in 1-in-progress from the JAS loop.
- 2026-10-12 — growth part formalized: ‖ζ(σ+iτ)‖ ≤ C·L·exp(κ√κ·864 L log L) for w(L) ≤ κ = 1 − σ ≤ 1/(3·2^24), C = 8 + 4(12e^{20} + 2761). It reuses the corpus `mul_sub_cube_div_le`, `vinogradovKorobovWidth_cube` and the dyadic saving. Next: a Jensen count via `HTGeometry.sum_divisor_le_of_bounds`.
- 2026-10-12 — Jensen count formalized. The zeros of ζ in the disc of radius 5κ/2 around 1 + 2κ + iτ (it contains every zero with Re ρ ≥ 1 − κ/4 and \|Im ρ − τ\| ≤ κ) number at most log(M/m)/log(6/5), with M = (C_VK + C)L*·exp(864κ^{3/2}L* log L*) and m = (2κ)³/(756 log τ). That is O(κ^{3/2}L log L + log L + log(1/κ)). Reading for [B]: covering a unit window by ≍ 1/κ such discs allows ≍ √κ·L log L zeros of depth ≤ κ. So collective spoilers (row 86: ≍ L zeros at constant depth) are consistent with every unconditional local count, now in Lean. Next possible step: Ford-type density via the corpus Halász–Montgomery large values.
- 2026-10-12 — assessment of the next step (Ford-type density N(1−κ,T) ≪ T^{Cκ^{3/2}}(log T)^C). The corpus density towers are Littlewood/argument-variation based (`exists_eventually_zetaLittlewoodZeroCountAbove_le_linearExponent`: exponent (16/5)(1−σ), linear). The κ^{3/2} exponent needs Montgomery's mollified detection, with the growth bound of this card on the detection contour, plus Halász–Montgomery large values (the corpus has the Maynard/Huxley/Jutila large-values modules). This is a large build. Its JAS payoff is the row-88 sliver (VK-hugging chains), so it is parked until it is needed by a route with a bigger payoff.
