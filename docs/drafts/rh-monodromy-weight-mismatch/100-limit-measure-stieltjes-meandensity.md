# 100 — The limit valuation measure; its Stieltjes form; the mean-valuation density

The two objects doc 99 §5 named are built.  One new Lean module — `ValLimit.lean` — realises the
monotone limit of the valuation measures, the Stieltjes measure of the valuation content, and the
mean-valuation density.  All typecheck axiom-clean `[propext, Classical.choice, Quot.sound]`;
integrated in `RHTower.lean`.

## 1. The monotone limit measure

- **`valMeasure_mono`** — `T₁ ≤ T₂ → valMeasure T₁ ≤ valMeasure T₂` (as measures): raising the
  height only adds atoms.
- **`valMeasureInf := ⨆ n : ℕ, valMeasure n`** — the limit valuation measure on ℝ; every window
  measure is below it (`valMeasure_le_valMeasureInf`).
- **`valMeasureInf_eq_zero_of_rh`** — under RH the limit measure vanishes (no off-line heights ⟹ no
  atoms ⟹ zero supremum).  The exact RH criterion remains the off-line locus
  `rh_iff_offLineHeights_empty` (the v₂ weights miss odd-order jumps, so vanishing of the *measure* is
  necessary but the *support* is the sharp detector).

## 2. (a) The Stieltjes measure of the valuation content

- **`valMass_mono_real`** — the content `T ↦ (valMass T : ℝ)` is monotone.
- **`valDistribution := valMass_mono_real.stieltjesFunction`** — its Stieltjes function (the
  right-continuous normalisation of the valuation content), via `Monotone.stieltjesFunction`.
- **`valStieltjesMeasure := valDistribution.measure`** and **`valStieltjesMeasure_Ioc`** —
  `valStieltjesMeasure (a, b] = ENNReal.ofReal (valDistribution b − valDistribution a)`: a genuine
  Borel measure on ℝ whose window mass is the enclosed valuation content, its distribution function
  the valuation content profile.

## 3. (b) The mean-valuation density

- **`meanVal T := (valMass T : ℚ) / (#enclosed heights : ℚ)`** — the average 2-adic valuation over
  the enclosed zero heights, a rational line profile.
- **`le_meanVal_of_le_windowDepth`** — `(k:ℕ∞) ≤ windowDepth T → (k:ℚ) ≤ meanVal T` (nonempty
  window): the mean is bounded below by the window depth.
- **`V_one_eq_zero_iff_one_le_windowDepth`** / **`one_le_windowDepth_iff_forall_pos`** — the depth is
  `≥ 1` iff `V 1 T = 0` iff every enclosed jump has positive 2-adic valuation (even order): the
  **level-1 graded rung**.  So `meanVal T ≥ 1` (the density bounded away from `0`) is forced by the
  graded rung.
- **`meanVal_eq_of_filtrationLength_eq`** — the mean is determined by the enclosed filtration
  lengths, each finite-carrier-shadowable (`filtrationLength_eq_finite`): on matching height data the
  whole mean-valuation profile is a decidable finite-carrier datum.

## 4. Status and the line-native ledger

All unconditional over the ξ divisor.  The boundary program is now a family of line-native objects,
each built from the bulk ξ and reduced to the same off-line locus:

| object | type | RH criterion |
|---|---|---|
| off-line locus `offLineHeights` | `Set ℝ` | `= ∅` |
| variation zero-set `badHeightSet k` | closed discrete `Set ℝ` | `= ∅` ∀k |
| valuation profile `valProfile` | `ℝ → ℕ∞` | `≡ ⊤` |
| depth profile `windowDepth` | `ℝ → ℕ∞` | `≡ ⊤` |
| census profile `censusProfile k` | `ℝ → ZMod (2^k)` | flat |
| Stieltjes measure `valStieltjesMeasure` | `Measure ℝ` | mass `0` under RH |
| limit measure `valMeasureInf` | `Measure ℝ` | `0` under RH |
| mean density `meanVal` | `ℝ → ℚ` | `≥ 1` under level-1 rung |

## 5. What this opens

The mean density is a rational profile bounded below by the depth; its **asymptotic behaviour** is the
next object.  Two forward moves: (a) the **liminf mean density** `⨅` over cofinal heights — a single
`ℚ ∪ {∞}` invariant of ξ whose positivity is the level-1 rung on a cofinal window family (hence, via
the producer, a sufficient analytic target), and whose finite-carrier shadow is a decidable liminf on
the completed truncation; (b) the **density–depth defect** `meanVal T − windowDepth T ≥ 0`, the gap
between the average and the minimal valuation, a nonnegative line profile that vanishes exactly when
every enclosed jump shares one valuation (a rigid "equal-order" window) — a new rigidity locus on the
line whose emptiness would collapse the atomic measure to a single-weight counting measure.
