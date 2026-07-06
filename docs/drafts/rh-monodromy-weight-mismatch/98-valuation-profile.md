# 98 — The 2-adic valuation profile; the filtration length; the window depth

The two objects doc 97 §5 named are built.  One new Lean module — `ValuationProfile.lean` — grades
the whole rung filtration by the 2-adic valuation of the jump divisor.  All typecheck axiom-clean
`[propext, Classical.choice, Quot.sound]`; integrated in `RHTower.lean`.

**Orientation correction (doc 97 §5).**  The filtration `badHeightSet k` is **increasing** in `k`,
not decreasing: `2^{k+1} ∣ n ⟹ 2^k ∣ n` gives `{¬2^k∣n} ⊆ {¬2^{k+1}∣n}`, so `badHeightSet 0 = ∅`
(everything divisible by `2^0 = 1`) and the sets grow.  Hence the meaningful invariant is the *last*
passing level `v₂(discJump t)`, not a "first level at which a height stops failing."

## 1. The 2-adic valuation profile

- **`valProfile t := emultiplicity 2 (discJump t) ∈ ℕ∞`** — the 2-adic valuation of the jump
  divisor, `⊤` where the jump vanishes.
- **`pow_dvd_discJump_iff_le_valProfile`** — `2^k ∣ discJump t ↔ (k:ℕ∞) ≤ valProfile t`.
- **`badHeightSet_eq_valProfile_lt`** — `badHeightSet k = {t | valProfile t < k}`: the variation
  zero-sets are exactly the sub-`k` cuts of the profile — a **graded rung**.  `badHeightSet_subset_succ`
  records the increasing filtration.
- **`valProfile_eq_top_iff`** — `valProfile t = ⊤ ↔ discJump t = 0`.
- **`rh_iff_forall_valProfile_eq_top`** — `RiemannHypothesis ↔ ∀ t, valProfile t = ⊤`: RH is the
  profile being identically `⊤` (every height of infinite 2-adic valuation, i.e. no off-line
  ξ-order).

## 2. The filtration length

- **`filtrationLength t := (discJump t).factorization 2`** — the last level a height passes.
- **`pow_dvd_discJump_iff_le_filtrationLength`** (`discJump t ≠ 0`) — `2^k ∣ discJump t ↔ k ≤
  filtrationLength t`.
- **`valProfile_eq_filtrationLength`** (`discJump t ≠ 0`) — on the zero heights the profile is the
  finite filtration length (ties Objects 1 and 2).
- **`mem_badHeightSet_iff_filtrationLength_lt`** — `t ∈ badHeightSet k ↔ filtrationLength t < k`.

## 3. The window depth — a finite certificate

- **`windowDepth T := inf over box-zero heights below T of (filtrationLength · : ℕ∞)`** (`⊤` for a
  zero-free window).
- **`V_eq_zero_iff_le_windowDepth`** — `V k T = 0 ↔ (k:ℕ∞) ≤ windowDepth T`: the depth is the exact
  rung reach, a **single finite certificate** capturing every level `k` at which the window is
  rung-clean.
- **`windowDepth_lt_top_iff`** — the depth is finite iff the window carries a box ξ-zero.

## 4. The transport shadow

- **`finiteFiltrationLength H mg t := (finiteDiscJump H mg t).factorization 2`** and
  **`filtrationLength_eq_finite`** — where ξ's and the finite carrier's divisibility criteria agree
  at every level (the family of `dvd_discJump_iff_finiteDiscJump`), the two filtration lengths
  coincide.  The length is a decidable finite-carrier datum, and the window depth its shadow.

## 5. Status and what this opens

All unconditional over the ξ divisor; the finite carrier enters only through its zero Finsets and the
per-level divisibility agreement.  The valuation profile is a single line-native `ℕ∞`-valued function
whose entire sub-level filtration is the `badHeightSet` tower and whose being `≡ ⊤` is RH; the window
depth compresses the whole level family into one certificate.

The profile is now a **function on the line valued in `ℕ∞`**, so its analytic shape is the next
object.  Two forward moves: (a) the **depth profile** `T ↦ windowDepth T`, a monotone-decreasing
`ℕ∞`-valued step function of the height (more enclosed zeros can only lower the minimal valuation),
whose descent points are the low-valuation heights and whose staying `= ⊤` past `T` is the rung
through `T` — a monotone envelope of the census profile; (b) the **valuation atomic measure**
`∑_t valProfile-weighted atoms`, refining the Stieltjes content of doc 97: instead of the jump size
mod `2^k`, weight each zero height by its 2-adic valuation, giving a measure whose finiteness on a
window is `windowDepth`-controlled and whose `⊤`-atoms are exactly the RH-forbidden off-line heights.
