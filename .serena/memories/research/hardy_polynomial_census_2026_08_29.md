# Hardy window pigeonhole: polynomial critical-line census (stage 3)

**Result.** Unconditional, premise-free Lean: `N₀(T) ≥ c·T^{1/16}/(1+log T)²` with a
dyadic-difference form, upgrading the corpus census from `c·log T`. Axioms: propext,
Classical.choice, Quot.sound.

**Capstones** (RHTower namespace, both modules umbrella-wired):
- `HardyZWindowMean.lean`: `exists_abs_integral_hardyZ_window_le` — one constant C with
  |∫_a^b Z| ≤ C·√T·√√T for every [a,b] ⊆ [T,2T], T ≥ 16.
- `HardyWindowCountTheorem.lean`: `exists_heavyFinset`, `window_fourth_le`,
  `exists_distinct_ordinates`, `numeric_gap`, `exists_many_distinct_line_zeros_dyadic`,
  `xiPosCriticalZeroCount_add_card_le`,
  `exists_sixteenthRoot_le_xiPosCriticalZeroCount_sub`,
  `exists_sixteenthRoot_le_xiPosCriticalZeroCount`.

**Route.** K = ⌊T^{1/8}⌋ windows; second moment T/4 − light-window cap T/8 forces heavy
mass T/8; Cauchy–Schwarz window cap √(H·M4); per-heavy-window zero via the corpus's
fourth-moment sign-change detector (window mean loses to mass cubed); fiber-2 ordinate
selector; injection into `xiPosCriticalZeroCount`. Needs NO windowed second-moment
asymptotic — only the dyadic C/F moments plus the new window mean bound.

**Honest label.** Quantitatively subsumed by Hardy–Littlewood 1921 (N₀ ≫ T): not new
mathematics. New-to-corpus and likely the first machine-checked polynomial critical-line
count ([NOVELTY UNVERIFIED] on that priority claim only).

**Ceiling.** Exponent 1/16 is forced by the T^{3/4} window mean: gap needs K³ < T^{1/2}/polylog,
heavy count = √K/polylog. To beat it: windowed second-moment asymptotic (Hardy–Littlewood's
actual route to ≫ T) — that is the next open layer.

**Lean traps hit** (all resolved): `set` let-bindings + nlinarith = whnf timeouts → replace
nlinarith with explicit mul_le_mul/calc chains and `linarith only [...]` in huge contexts;
`set` folds the goal at set-time, so later `rw [← hsdef]` on the goal fails (already folded)
while a fresh `have` statement stays raw; calc of `=` steps against a `≤` goal leaves `X ≤ X`
(close with le_of_eq); `Real.log_le_log : 0 < x → x ≤ y → ...` current; `not_le.mp` not
`lt_of_not_le`; field_simp may fully close (drop trailing ring); congr 1 + ring replaces
field_simp for a/K = b/K goals.

Card: docs/drafts/pipeline/3-formalized/hardy-window-polynomial-census.md
