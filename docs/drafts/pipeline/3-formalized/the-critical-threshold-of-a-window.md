# The critical threshold of a window

- **ID:** F0311-Q3-4.5c
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0311/fable.md` §4.5(c); loop card `1-in-progress/fable-0311-q3-breakthrough-questions.md`
- **Statement:** For the window `[−A, 0]` let `R₁(A) = inf R*(H)` over window tests with `Q(H) < 0`,
  `R*(H) = 7J(1) M₈(H)/(a_φ |Q(H)|)`, `M₈(H) = ∫ e^{−8y} H²` (`⊤` if there are none). Then `R₁(A)` is
  the exact critical multiple of the window along `c⁸ = R log N`; it is nonincreasing in `A`; it is `⊤`
  iff `Q ≥ 0` on the window, in particular for `A ≤ 2·enlargedWeilFloorAperture` (past `log 2`); `R₁(A) ≥ R₀ = 7J(1)/(a_φ C(8))` and
  `R₁(A) ≥ 7J(1)/(a_φ S(A))` for every `A`; RH holds iff `R₁ ≡ ⊤`.

## What is answered

The report states the properties of `R₁` as derived facts `[D]`; they are now theorems, and `R₁` is
identified with the critical multiple of the whole window:

- for every `0 < R < R₁(A)` the pencil `a_φ Q(H) + (7J(1)/R) M₈(H)` is positive on every nonzero test,
  and every horizon block of the window is eventually positive along `c⁸/log N → R`;
- for every `R > R₁(A)` some window test is eventually negative along the same curve;
- a multiple at which the pencil is positive on all nonzero tests of the window is `≤ R₁(A)`.

The lower bound `max(R₀, 7J(1)/(a_φ S(A)))` holds at every `A`, including every `A` beyond the proved
lengths. The value `R₁(A) = ⊤` at one `A > 2·enlargedWeilFloorAperture` is window positivity at that
length, which is §4.1 and remains open (loop card, ledger rows 5–6).

## Paper proof

1. **Order.** Tests of `[−A, 0]` are tests of `[−B, 0]` for `A ≤ B`; an infimum over a larger set is
   smaller.
2. **Positivity.** An infimum of real numbers over an index set is `⊤` iff the set is empty, i.e. no test
   has `Q(H) < 0`. Windows of length `≤ 181/250`: `Q ≥ 0` on every `C²_c` test of that support length;
   windows of length `≤ 2·enlargedWeilFloorAperture`: the strict floor `Q ≥ ‖H‖²/8000` (ATD).
   RH ⟺ `Q ≥ 0` on every window.
3. **Floors.** If `−Q(H) ≤ F·M₈(H)` on the window with `F > 0`, then `Q(H) < 0` forces `M₈(H) > 0` and
   `R*(H) ≥ 7J(1) M₈/(a_φ F M₈) = 7J(1)/(a_φ F)`. The aperture-independent floor gives `F = C(8)`. The sharp
   floor `Q ≥ −S(A)‖H‖²` with `‖H‖² ≤ M₈(H)` (`e^{−8y} ≥ 1` on `y ≤ 0`) gives `F = S(A) > 0`.
4. **Critical multiple.** A nonzero test has `M₈ > 0`. If `Q(H) ≥ 0` the pencil is `≥ (7J(1)/R)M₈ > 0`; if
   `Q(H) < 0` and `R < R₁(A) ≤ R*(H)` then `a_φ(−Q) R < 7J(1) M₈`, the pencil is positive. Conversely
   positivity of the pencil at a test with `Q < 0` gives `R < R*(H)`. The horizon statements are
   `criticalMultiple_exact` applied to `h = e^{−y/2} H` (half-weight `H`); above `R₁(A)` the infimum
   provides a test with `R*(H) < R`.

## Lean

`formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalThresholdOfAWindow.lean`:
`splineAtom`, `testCriticalMultiple`, **`windowThreshold`**, `apertureIndependentThreshold`,
`windowThreshold_antitone`, `windowThreshold_eq_top_iff`, `windowThreshold_eq_top_of_le`,
**`windowThreshold_eq_top_of_le_enlarged`**,
**`riemannHypothesis_iff_windowThreshold_eq_top`**, `le_windowThreshold_of_floor`,
**`apertureIndependentThreshold_le_windowThreshold`**, **`sharpThreshold_le_windowThreshold`**,
`exponentialMass_pos`, `windowPencil`, `pencil_pos_of_lt_windowThreshold`,
`le_windowThreshold_of_pencil_pos`, **`eventually_pos_of_lt_windowThreshold`**,
**`exists_eventually_neg_of_windowThreshold_lt`**.

Checked with `lake --old env lean`; transitive axioms of the bold theorems and
`windowThreshold_eq_top_of_le`: `propext`, `Classical.choice`, `Quot.sound`. Wired into
`ArithmeticHodgeTheoryOfDegenerations.lean`.

## Log
- 2026-11-04 — formalized
