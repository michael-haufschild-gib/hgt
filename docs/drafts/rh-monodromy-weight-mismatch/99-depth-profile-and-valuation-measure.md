# 99 — The depth profile; the valuation atomic measure; the off-line locus

The two objects doc 98 §5 named are built.  One new Lean module — `ValMeasure.lean` — realises the
depth profile as a monotone-decreasing `ℕ∞` step function and the valuation atomic measure as a
genuine finite measure on ℝ.  All typecheck axiom-clean `[propext, Classical.choice, Quot.sound]`;
integrated in `RHTower.lean`.

## 1. (a) The depth profile

- **`windowDepth_antitone`** — `T₁ ≤ T₂ → windowDepth T₂ ≤ windowDepth T₁`: enclosing more zeros can
  only lower the minimal valuation, so the depth profile `T ↦ windowDepth T` is a
  monotone-**decreasing** `ℕ∞`-valued step function.
- **`windowDepth_lt_iff`** — `windowDepth T < n ↔ ∃ z ∈ boxZeros T, filtrationLength z.im < n`: the
  profile descends below level `n` exactly at a low-valuation enclosed height — the **descent
  points are the low-valuation heights**.
- **`windowDepth_eq_top_iff`** — `windowDepth T = ⊤ ↔ boxZeros T = ∅`, and
  **`windowDepth_eq_top_iff_forall_windowCertificate`** — `= ⊤ ↔ ∀ k, WindowCertificate k T`:
  **staying `⊤` past `T` is the full rung tower through `T`**.
- **`discCensusH_eq_zero_of_le_windowDepth`** — `(k:ℕ∞) ≤ windowDepth T → discCensusH k T = 0`: the
  depth is the height to which the census profile stays trivial — a **monotone envelope of the
  census** (`windowDepth_le_filtrationLength` bounds each atom below by the depth).

## 2. (b) The valuation atomic measure

- **`valMass T := ∑ over enclosed heights of filtrationLength t`** — the valuation content, the
  atomic measure's mass on `[0, T)`, refining the doc-97 Stieltjes content by weighting each zero
  height by its 2-adic valuation instead of the jump size mod `2^k`.  Monotone
  (`valMass_mono`); zero on a zero-free window (`valMass_eq_zero_of_windowDepth_top`).
- **`valMeasure T := ∑_t (v₂(discJump t)) • δ_t`** — a genuine `Measure ℝ`, the atomic measure
  weighting each enclosed zero height by its valuation.  **`valMeasure_univ`**: total mass =
  `valMass T`; **`isFiniteMeasure_valMeasure`**: it is a finite measure — a finite Dirac comb on the
  window, its finiteness `windowDepth`-controlled (every atom `≥ windowDepth`).

## 3. The off-line locus

- **`offLineHeights := {t | discJump t ≠ 0}`** — the heights carrying an off-line ξ-zero, equal to
  `{t | valProfile t ≠ ⊤}` (`offLineHeights_eq_valProfile_ne_top`).  The measure's atoms lie here
  (`image_im_subset_offLineHeights`).
- **`rh_iff_offLineHeights_empty`** — `RiemannHypothesis ↔ offLineHeights = ∅`: RH is exactly the
  emptiness of the off-line locus, i.e. no height carries an off-line zero, i.e. the valuation
  measure has no atoms at any level.

## 4. Status and the line-native picture

All unconditional over the ξ divisor.  The depth profile, the census profile, and the valuation
measure are three step-function/measure views of the same jump data on ℝ; the off-line locus is
their common support and the RH target.  The whole boundary program now lives on the line: a
`ℕ∞`-valued depth profile, a `ZMod (2^k)`-valued census profile, an `ℕ`-weighted atomic measure, and
a closed discrete zero-set — all built from the bulk ξ, all reduced to one discrete subset of ℝ being
empty.

## 5. What this opens

The valuation measure is a genuine finite measure, so its **weak-limit behaviour** as `T → ∞` is the
next object: the measures `valMeasure T` increase (as measures) with `T`, so they have a monotone
limit `valMeasure∞ = ∑ over all off-line heights of v₂ · δ_t`, a σ-finite atomic measure on ℝ whose
total mass is finite on every bounded interval and whose being the zero measure is RH.  Two forward
moves: (a) the **restricted measure** `valMeasure∞ ↾ [a,b]` as the window mass functional, a genuine
Stieltjes measure whose distribution function is the valuation content profile `T ↦ valMass T`; (b)
the **normalized atom density** — the ratio `valMass T / (number of enclosed heights)`, the mean
2-adic valuation over a window, a rational-valued line profile whose staying bounded away from `0`
is a graded strengthening of the rung (every enclosed jump carries positive valuation), and whose
finite-carrier shadow is decidable through the transport.
