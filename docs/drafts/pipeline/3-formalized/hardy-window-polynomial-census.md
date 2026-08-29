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

---

## Upgrade: the sixth-root census (same session, second pass)

**Claim.** Unconditionally, `N₀(T) ≥ c · T^{1/6} / (1 + log T)⁶` for all large `T`, with
the dyadic-difference form. [LEAN-PROVED]; axioms propext / Classical.choice / Quot.sound.

**What changed.** The counting step was upgraded from per-window capping to Cauchy–Schwarz
over the heavy set: `(Σ_S m_k)² ≤ |S|·Σ_S m_k²`, with `m_k² ≤ H·m4_k` and the window fourth
moments summing (by interval additivity) to the dyadic fourth moment.  This gives
`(T/8)² ≤ |S|·H·M4`, i.e. a heavy count linear in `K` instead of `√K`.  The sign-change gap
condition `ME²·M4 < (T/8K)³` tolerates `K` up to `T^{1/6}/polylog`, realized as
`K = ⌊T^{1/6}/(D₀(1+log T)²)⌋` with `D₀ = 512(CE²+1)(CF+1)+8` (rpow-based; the nested-sqrt
`T^{1/8}` choice of the first pass was suboptimal).  Exponent `1/6` is the exact ceiling of
this route: the gap forces `K³ < √T/polylog` as long as the window mean is the trivial
`O(T^{3/4})`.  Beating `1/6` requires a windowed second- or fourth-moment asymptotic
(Hardy–Littlewood's mechanism for `N₀ ≫ T`).

**New module** `GaloisForLFunctions/RHTower/HardySixthRootCensus.lean` (umbrella-wired;
the shared lemmas `window_fourth_le`, `exists_distinct_ordinates`,
`one_add_log_pow_four_le_sixteenth` were de-privatized in `HardyWindowCountTheorem.lean`):
`exists_heavyFinset_sq` (Cauchy–Schwarz pigeonhole), `gap_of_key` (K-generic gap),
`nested_four_sqrt_eq_rpow`, `log_sq_le_rpow` (`(1+log T)² ≤ 4624·T^{1/32}`), capstones
`exists_many_distinct_line_zeros_dyadic_sixth`,
`exists_sixthRoot_le_xiPosCriticalZeroCount_sub`,
`exists_sixthRoot_le_xiPosCriticalZeroCount`.

**Honest assessment.** Still quantitatively subsumed by Hardy–Littlewood 1921 (`N₀ ≫ T`) —
not new mathematics.  New-to-corpus; the machine-checked-polynomial-census priority claim
remains [NOVELTY UNVERIFIED].

---

## Upgrade 2: the two-sevenths census via the resonance-graded window mean

**Claim.** Unconditionally, `N₀(T) ≥ c · T^{2/7} / (1 + log T)⁹` for all large `T`, with the
dyadic-difference form. [LEAN-PROVED]; axioms propext / Classical.choice / Quot.sound.

**The new analytic brick** (`HardyZWindowMeanSharp.lean`, ~1300 lines, compiles at default
heartbeats): the sharp window mean
`|∫_a^b Z| ≤ C(T^{1/4}(1+log T) + (b−a)T^{-1/4} + √x + (b−a)T/x)` for every window
`[a,b] ⊆ [T,2T]` and cutoff `1 ≤ x ≤ e^T`.  Mechanism: on a window, the phase rate of the
`m`-th direct term is `log(√(τ/2π)/m) + O(1/T)`; the first-derivative van der Corput test is
graded by the logarithmic distance of `m` to the moving resonance band `[√(a/2π), √(b/2π)]`,
and the near-resonant sums close by a harmonic telescope (`-log(1−u) ≥ u` + `Σ 1/k ≤ 1+log`)
— no dyadic shells.  The `O((b−a)/√T + 1)` crossing terms take the second-derivative test at
`T^{1/4}` each; the far terms keep the graded-by-1 test against the cutoff weight sum `√x`.

**The census step** (`HardyTwoSeventhCensus.lean`, compiles at default heartbeats): at
`x = T^{8/7}` and `K = ⌊T^{2/7}/(D(1+log T)⁵)⌋` windows the per-window mean is
`≤ 6·CS·D·(1+log T)⁵·T^{4/7}`, the gap `512K³ME²(CF+1)L⁴ < T²` closes with a factor `L` to
spare, and the Cauchy–Schwarz heavy count gives `K/(64(CF+1)L⁴)` zeros per dyadic block.
Capstones: `exists_many_distinct_line_zeros_dyadic_twoSeventh`,
`exists_twoSeventhRoot_le_xiPosCriticalZeroCount_sub`,
`exists_twoSeventhRoot_le_xiPosCriticalZeroCount`.

**Ceiling of this pass.** `2/7` is forced by `√x`-vs-`(b−a)T/x` balancing (`x=((b−a)T)^{2/3}`
gives mean `((b−a)T)^{1/3}`, gap `H > T^{5/7}`).  The remaining losses to `N₀ ≫ T`: the
crude `O(T/x)` pointwise dual-edge bound (treating the reflected edge oscillatorily would
allow `x ≈ √T`), and the fourth-moment Cauchy–Schwarz in the counting.  Both are now the
precisely-localized open layers.

**Engineering.** All five Hardy census modules now compile with ZERO `maxHeartbeats`
escalations (user directive): `linarith only`, explicit `mul_le_mul` chains, and
per-block private lemmas replace context-wide `nlinarith`; the sharp module builds in 40 s
against ~570 s for the earlier escalated files.
