# Hardy window pigeonhole: polynomial critical-line census (stage 3)

**Result (final).** Unconditional, premise-free Lean: `N₀(T) ≥ c·T^{1/6}/(1+log T)⁶` with a
dyadic-difference form — upgraded from the first-pass `T^{1/16}/(1+log T)²`, which upgraded
the prior corpus census `c·log T`. Axioms: propext, Classical.choice, Quot.sound.

**Modules** (RHTower namespace, all umbrella-wired):
- `HardyZWindowMean.lean`: `exists_abs_integral_hardyZ_window_le` — one constant C with
  |∫_a^b Z| ≤ C·√T·√√T for every [a,b] ⊆ [T,2T], T ≥ 16.
- `HardyWindowCountTheorem.lean` (848 lines): K-generic `exists_heavyFinset`,
  `window_fourth_le`, `exists_distinct_ordinates` (now public), `numeric_gap`,
  `one_add_log_pow_four_le_sixteenth` (public), sixteenth-root capstones
  (`exists_many_distinct_line_zeros_dyadic`, `xiPosCriticalZeroCount_add_card_le`,
  `exists_sixteenthRoot_le_xiPosCriticalZeroCount[_sub]`).
- `HardySixthRootCensus.lean` (682 lines): `exists_heavyFinset_sq` (Cauchy–Schwarz
  pigeonhole: (T/8)² ≤ |S|·H·M4), `gap_of_key` (K-generic detector gap from
  512K³CE²(CF+1)L⁴ < √T), `nested_four_sqrt_eq_rpow`, `log_sq_le_rpow`
  (L² ≤ 4624·T^{1/32}), capstones `exists_many_distinct_line_zeros_dyadic_sixth`,
  `exists_sixthRoot_le_xiPosCriticalZeroCount[_sub]`.

**Route.** K = ⌊T^{1/6}/(D₀L²)⌋ windows (D₀ = 512(CE²+1)(CF+1)+8; threshold Y^96 device
with Y absorbing all constants, T^{a/96} = (T^{1/96})^a); second moment T/4 vs light cap T/8;
CS over heavy set + per-window m² ≤ H·m4 + interval-additive Σm4 = dyadic fourth ⇒ heavy
count ≥ K/(64(CF+1)L⁴); per-heavy-window zero via fourth-moment sign-change detector (window
mean CE·T^{3/4} loses to mass cubed); fiber-2 ordinate selector; census injection.

**Ceiling.** 1/6 is exact for this route: gap forces K³ < √T/polylog with the trivial
T^{3/4} window mean. Beating it needs a windowed second/fourth-moment asymptotic (HL's
mechanism for N₀ ≫ T) — the next open layer.

**Honest label.** Subsumed by Hardy–Littlewood 1921 (N₀ ≫ T): not new mathematics. New to
corpus; machine-checked-polynomial-census priority claim [NOVELTY UNVERIFIED].

**Lean traps hit** (all resolved): `set` let-bindings + linarith/nlinarith = whnf/isDefEq
timeouts — especially `Y ^ 96` of a let-bound Y, which polynomial-normalizes to degree-96;
fix = `clear_value` after deriving the equational facts, plus `linarith only [...]`
everywhere in giant contexts. `set` folds the goal at set-time (later `rw [← hdef]` on the
goal fails; a fresh `have` statement stays raw). calc of `=` steps against `≤` goal leaves
`X ≤ X` (close via le_of_eq). nlinarith misses D0 ≤ D0³ (hint 0 ≤ D0(D0−1)(D0+1)).
field_simp can fail/close unpredictably — replace with div_mul_cancel₀ calcs. rpow exponent
algebra: `← Real.rpow_natCast` + `← Real.rpow_mul` + `congr 1; norm_num` handles
(T^{1/n})^m = T^{m/n} including the Nat-cast exponent. `Real.log_le_log : 0 < x → x ≤ y → …`;
`not_le.mp` not `lt_of_not_le`; `positivity` fails on opaque set-locals (D0) — explicit
mul_pos chains.

Card: docs/drafts/pipeline/3-formalized/hardy-window-polynomial-census.md
