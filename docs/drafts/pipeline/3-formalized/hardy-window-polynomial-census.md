# Hardy window pigeonhole: a polynomial critical-line census

**Claim.** Unconditionally, the number of critical-line zeros of `xi` with ordinate in
`(0, T]`, counted with multiplicity, satisfies

    N₀(T) ≥ c · T^{1/16} / (1 + log T)²   for all T ≥ T₁,

with an explicit dyadic-difference form `N₀(2T) − N₀(T) ≥ c · T^{1/16}/(1+log T)²`.

**Status.** [LEAN-PROVED] (stage 3). Axioms: propext, Classical.choice, Quot.sound only.

**Honest assessment.** Relative to external SOTA this is quantitatively subsumed:
Hardy–Littlewood (1921) prove N₀(T) ≫ T, and Selberg/Levinson/Conrey give positive
proportion. So this is **not new scientific knowledge as mathematics**. Relative to the
corpus it is a major frontier move: the strongest previously formalized census was
logarithmic (`exists_log_le_xiPosCriticalZeroCount`, N₀(T) ≥ c log T). This card upgrades
the corpus's unconditional critical-line count from log T to a power of T, and it is (to
our knowledge) the first machine-checked polynomial critical-line zero count in any
proof assistant. [NOVELTY UNVERIFIED] applies only to that formalization-priority claim.

**Mechanism (window pigeonhole).** Partition `[T, 2T]` into `K = ⌊T^{1/8}⌋` windows of
length `H = T/K`. The dyadic second moment `∫ Z² ≥ T/4` forces the heavy windows
(mass ≥ Θ = T/(8K)) to carry ≥ T/8 of the mass, since light windows total ≤ K·Θ = T/8.
Each window's mass is capped by Cauchy–Schwarz: `m_k ≤ √(H · M4)` with M4 the dyadic
fourth-moment bound `(CF+1)·T(1+log T)⁴`, so the number of heavy windows is
≥ (T/8)/√(H·M4) ≈ T^{1/16}/(1+log T)². On each heavy window the first-moment bound
`|∫ Z| ≤ CE·T^{3/4}` loses to the mass cubed (numeric gap: `512·21381376·CE²(CF+1) < T^{1/16}`
for T beyond an explicit 16th power), so the corpus's fourth-moment sign-change detector
places a zeta zero inside the window. Distinct windows give distinct ordinates up to a
factor 2 (shared endpoints), and the ordinates inject into the census difference.

**New Lean modules** (both wired into the RHTower umbrella):
- `GaloisForLFunctions/RHTower/HardyZWindowMean.lean` — window first-moment bound
  `exists_abs_integral_hardyZ_window_le`: one constant C with
  `|∫_a^b Z| ≤ C·√T·√√T` for every `[a,b] ⊆ [T, 2T]`, T ≥ 16 (windowed twist bounds,
  windowed direct-series identity, pointwise tail transfer).
- `GaloisForLFunctions/RHTower/HardyWindowCountTheorem.lean` —
  `exists_heavyFinset` (pigeonhole + per-window sign-change detector),
  `window_fourth_le`, `exists_distinct_ordinates` (fiber-2 selector),
  `numeric_gap` (explicit-constant closure), capstones
  `exists_many_distinct_line_zeros_dyadic`,
  `xiPosCriticalZeroCount_add_card_le`,
  `exists_sixteenthRoot_le_xiPosCriticalZeroCount_sub`,
  `exists_sixteenthRoot_le_xiPosCriticalZeroCount`.

**Inputs consumed (all previously Lean-closed in the corpus):**
`exists_le_integral_hardyZ_sq` (dyadic second moment ≥ T/4),
`exists_integral_hardyZ_pow_four_dyadic_real_le` (dyadic fourth moment ≤ CF·T(1+log T)⁴),
`exists_riemannZeta_line_zero_of_hardyZ_fourth_moment_gap` (sign-change detector),
`HardyZDyadicMean` twist/direct-term machinery, census stack
(`stripFinsetPos`, `xiPosCriticalZeroCount`, `xi_line_eq_zero_iff_hardyZ`,
`xi_order_toNat_ne_zero`).

**Why the exponent is 1/16.** K = T^{1/8} is forced by the first-moment loss: the gap
condition needs `(T^{3/4})²·T(1+log T)⁴ < (T/K)³`, i.e. `K³ < T^{1/2}/polylog`, so
K ≤ T^{1/6−ε}; the heavy count is `√K/polylog`, optimized inside the corpus's mean bound
at K = T^{1/8} giving T^{1/16}. Raising the exponent needs a genuinely better window
first moment (e.g. a windowed second-moment asymptotic — the classical route to ≫ T),
which is the next open layer if this lane is pushed further.
