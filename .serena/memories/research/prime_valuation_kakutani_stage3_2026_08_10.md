# Prime-valuation Kakutani sector — stage 3 (2026-08-10)

Card `prime-valuation-kakutani-polar-third-completion.md` promoted to `3-formalized`; its Lean gate
("full product-measure/Kakutani formalization") is closed.  Research gates (novelty audit, Xi
conormal normality, RH) stay open by design — it is a retired-route bridge card.

## Mathlib has no Kakutani dichotomy

Only Riesz–Markov–Kakutani.  `Measure.infinitePi` exists (`Mathlib/Probability/ProductMeasure`),
plus `infinitePi_map_restrict`, `infinitePi_pi`, and `iIndepFun_infinitePi`.  Do not look for
likelihood-ratio machinery; there is none.

## The route that works (no martingales)

Separate the twisted product `μ_c` (geometric ratios `p^{-(1-2c)}`) from the critical `μ₀`
(ratios `p⁻¹`) by an **occupancy tail event**, using the corpus
`HTGeometry/ProductOccupancyDichotomy` (both Borel–Cantelli directions, arbitrary local targets):

- `c < 0`: twisted masses `p^{-(1-2c)}` summable, critical masses `p⁻¹` not ⇒ infinite occupancy is
  null for one and full for the other.
- `0 < c < 1/2`: **both diverge**, so plain occupancy cannot separate them, and neither can any
  integer threshold `k ≥ m` (that only works for `c ≥ 1/4`).  The fix is to thin the prime set.

## The thinning lemma (`HTGeometry/DivergentSeriesThinning.lean`)

For positive `y` with `¬Summable y` and `y → 0`, and `0 < s < 1`, there is `T ⊆ ℕ` with
`Summable (y on T)` and `¬Summable (y^s on T)`.  Greedy **two-scale** blocks are the point:
block `j` collects mass `≈ τ_j = 2^{-(j+1)}` out of terms already `≤ δ_j = τ_j^{1/(1-s)}`.  Then
`∑ y^s ≥ δ_j^{s-1} τ_j = 1` per block.  Taking `δ_j = τ_j` instead gives only `τ_j^s`, which
converges — that is the trap.

Lean devices: `sInf` (not `Nat.find`) for the block ends so the definitions stay total;
`Nat.notMem_of_lt_sInf` for greedy minimality; disjointness from `start (j+1) ≥ end j`;
`summable_of_sum_le` plus `Finset.sum_biUnion` for the union bound.  Applied to `y n = 1/(e n)`
for an enumeration `e : ℕ ≃ Nat.Primes` (injective ⇒ `tendsto_cofinite` ⇒ `atTop`).

## Also formalized

`geometricHellingerAffinity a b = √((1-a)(1-b))/(1-√(ab))` with `hasSum_geometricHellinger`, the
rationalized defect `(√a-√b)²/((1-√(ab))((1-√(ab))+√((1-a)(1-b))))`, and `1-H ≥ (√a-√b)²/2`.
So the card's own §4 scalar chain is covered even though the singularity proof takes another route.

## Lean notes

- `summable_subtype_iff_indicator` needs the function as `f ∘ Subtype.val`; supply `(f := …)`
  `(s := …)` explicitly rather than rewriting a lambda goal.
- `Real.sqrt_pow` does not exist; prove `√(x^k) = (√x)^k` via `Real.sqrt_eq_rpow` + `rpow_natCast`.
- `rw [show (1:ℝ) = √1 …]` rewrites *every* `1`, including inside `(1-a)*(1-b)`; use a `calc` with
  `Real.sqrt_le_sqrt`/`Real.sqrt_lt_sqrt` instead.
- `Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular` turns singular + a.c. into `μ = 0`,
  which contradicts `IsProbabilityMeasure` — that is the `iff` capstone.
