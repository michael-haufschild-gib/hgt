# B192: the two ends of the window of ratio three — a packet and its dilate by two are bound

- **ID:** agz-b192-two-ends
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.21 (B192); programme `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ`
- **Statement:** For every `r ≥ 1`, `Q ≥ 2` and every packet `σ` on the blocks of `(2r, 3r]`, the
  neutral part of the window `(2r, 6r]` on `z = σ − U₂σ` (`U₂σ` the refinement of `σ` on the
  dilate `(4r, 6r]`, zero on `(3r, 4r]`) is at least `(1/30) Σ σ_j²`.

## Goal

B192 asks whether the neutral part `N` of `(R, 3R]` has exactly one negative square at every block
size. In the Hodge form of the programme this is: no two wells with disjoint supports are unbound.
The theorem settles the pairs (packet, its dilate by two): `N(σ, U₂σ) ≤ N(σ) − (1/60) Σσ²`, so
`N(σ,U₂σ)² > N(σ) N(U₂σ)` whenever `N(σ) ≤ 0`. It is selective: with the contact of `2` removed
the flat pair is unbound (existing `two_le_hermNegIndex_reweighted_of_ratio_three`). It is not a
proof of B192 (see "What stays open").

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `sum_neutralBlock_twoEnds_ge`, `bilin_neutralWindow_lowerEnd_upperEnd_le`

## Proof

Blocks `a = 2r + j`, `j < r` (end `A`), middle `M = (3r, 4r]`, end `C = (4r, 6r]`; the children of
`a` are `2a, 2a + 1 ∈ C`. `d` = `blockDegree`, `D` = `xLogXDiff`, `J` = `blockJet`.

**1. The two ends (exact).** For packets `σ, τ` on `A` put `z = σ` on `A`, `0` on `M`,
`τ_a/√2` on the two children of `a`. Then

  `N(z) = N_A(σ) + N_A(τ) − √2 ( log 2 · Σ σ_j τ_j + Σ_{j,l} σ_j τ_l K(j,l) )`,

`K(j,l) = J(a_j, 2a_l) + J(a_j, 2a_l + 1)`. Proof: the `C × C` part is `N_A(τ)` by the invariance
of the neutral part under refinement; between `a ∈ A` and `b ∈ C` (`b < 3a`) the neutral part is
`−J(a,b) − [⌊b/2⌋ = a] (log 2)/2`.

**2. Odd sector.** `τ = −σ`: `N(z) = 2 N_A(σ) + √2 log 2 Σσ² + √2 Σ σ_j σ_l K(j,l)`.
`N_A(σ) = W_A(σ) − 2 (Σσ)(Σσ d)` and `W_A ≥ (1/5000) Σσ²` (short windows, ratio `3/2`). Hence

  `N(z) ≥ (1/2500 + √2 log 2) Σσ² − √2 Σ σ_j σ_l k(j,l)`,  `k(j,l) = √2 (d(a_j) + d(a_l)) − K(j,l)`.

**3. `k ≥ 0`.** `D(n) ≤ 2/(2n − 1)` (`n ≥ 2`) gives `K(j,l) ≤ 2/(γ+α) + 2/(γ−α)`, `α = 2a_j + 1`,
`γ = 4 a_l`; `d(a) ≥ 2/(2a+1)` gives `d(a_j) + d(a_l) ≥ 2/α + 4/(γ+2)`. So it suffices that
`g(α) = s(γ+2+2α)(γ²−α²) − 2γα(γ+2) ≥ 0` for `s = √2`, `0 < α ≤ α₁ = (3γ−4)/4` (true since
`α ≤ 6r − 1`, `γ ≥ 8r`). `g` is a cubic in `α` with
`α₁ g(α) = (α₁−α) g(0) + α g(α₁) + α₁ α (α₁−α) s (γ+2+2(α+α₁))`, `g(0) = sγ²(γ+2)`,
`g(α₁) = (γ/32)((35s−48)γ² + (120s−32)γ + 128 − 80s) ≥ 0` for `7/5 ≤ s ≤ 3/2`.

**4. Schur test.** `Σ σ_jσ_l k(j,l) ≤ ½ Σ_j σ_j² Σ_l (k(j,l) + k(l,j))`, and
`Σ_l (k(j,l)+k(l,j)) = 2√2 (r d(a) + log(3/2)) − T/2`, `T = S₁+…+S₆` six sums of consecutive
jets:
`S₁ = Σ_{i<2r} D(6r+j+1+i)`, `S₂ = Σ_{i<2r} D(2r−j+i)`, `S₃ = Σ_{l<r} D(6r+2j+1+l)`,
`S₅ = Σ_{l<r} D(6r+2j+2+l)`, `S₄ = Σ_{l<r} D(2r+2j−l)`, `S₆ = Σ_{l<r} D(2r+2j+1−l)`.
Consecutive jets telescope to steps, and the midpoint enclosure of the step gives
`Σ_{n=p}^{q−1} D(n) ≥ log((2q−1)/(2p−1)) − 1/99` (`q ≥ 3`). With `m = 2j+1`:
`S₁ ≥ log((16r+m)/(12r+m))`, `S₂ ≥ log((8r−m)/(4r−m))`, `S₃, S₅ ≥ log((14r+2m∓1)/(12r+2m∓1))`,
`S₄, S₆ ≥ log((4r+2m∓1)/(2r+2m∓1))`, each minus `1/99`.

Rational bounds: `log(u/v) ≥ 2(u−v)/(u+v)`; `log(u/v) ≤ (u²−v²)/(2uv)`; ratio-two logarithms are
split off as `log 2`. With `ν = m/r`, `ι = 1/r`:

  `T + 6/99 ≥ 3 log 2 − 13/6 + 4/(14+ν) + (32/3)/(16−3ν) + 4/(26+4ν∓2ι) + 2/(4+2ν∓ι) + (1/2)/(2+2ν∓ι)`

(the `∓` terms summed over both signs). Each `1/y` is convex: `1/y ≥ (2y₀ − y)/y₀²` at
`ν₀ = 1/2`, `ι = 0` (`y₀ = 29/2, 29/2, 28, 5, 3`); the `ι` cancel. This gives
`T + 6/99 ≥ 3 log 2 − 13/6 + c₀ − c₁ ν`, `c₀ = 240/841 + 1664/2523 + 30/98 + 24/25 + 4/9`,
`c₁ = 16/841 − 384/2523 + 4/98 + 8/25 + 2/9`.
Trapezoid and chord: `r d(a) ≤ (r/2)(1/a + 1/(a+1)) ≤ (6 − ν)/12`. Numerically
`3 log 2 − 13/6 + c₀ − c₁ν − 6/99 − 4√2((6−ν)/12 + log(3/2)) + 4 log 2 ≥ 0.158 + 0.02 ν`, so
`Σ_l (k(j,l)+k(l,j)) ≤ 2 (log 2 − 1/40)`.

**5.** `N(z) ≥ (1/2500 + √2/40) Σσ² ≥ (1/30) Σσ²`.

## Lean

Module `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/APacketAndItsDilateByTwoAreBoundOnTheWindowOfRatioThree.lean`.

| Step | Declaration |
|---|---|
| 1 the two ends | `twoEnds`, `endJet`, `neutralBlock_add_children`, `sum_neutralBlock_twoEnds` |
| 2 odd sector | `sum_neutralBlock_twoEnds_odd` |
| 3 `k ≥ 0` | `endKernel`, `endJet_le`, `endCoupling_cubic`, `endKernel_nonneg` |
| 4 Schur test, row and column sums | `sum_sum_mul_le_of_nonneg`, `sum_endJet_row`, `sum_endJet_col`, `log_sub_log_le_xLogXStep_sub`, `endSums_real`, `sum_endKernel_add_le` |
| 5 the margin | `sum_neutralBlock_twoEnds_ge` |
| wells | `lowerEnd`, `upperEnd`, `bilin_neutralWindow_upperEnd`, `bilin_neutralWindow_lowerEnd_upperEnd_le`, `not_unbound_lowerEnd_upperEnd` |

## What stays open (B192 itself)

- B192 follows from the positivity of the block matrix of ratio three
  (`hermNegIndex_neutralWindow_le_one_of_nonneg`): Weil positivity at the aperture `½ log 3`,
  beyond the certified ratio `103/50`. Not proved, an estimate only: at infinite block size `N`
  is the compression of `Φ(D)`, `Φ(t) = Re ψ(1/4 + it/2) − log π − √2 log 2 · cos(t log 2)`, to
  `L²[0, log 3]`, and a prolate estimate puts its second eigenvalue near `10⁻³`; an inequality
  with a margin of the size above does not reach it.
- The even sector `τ = σ` holds the bound state. On charge-free `σ` it gives a necessary condition
  for B192: `W_A(σ) ≥ (log 2/√2) Σσ² + (1/√2) Σ σ_jσ_l K(j,l)` on the window of ratio `3/2`.
- Not covered: packets with mass on the middle `(3r, 4r]` or with different values on the two
  children of a block.

## Log
- 2026-11-13 — created in 1-in-progress with the paper proof
- 2026-11-13 — formalized; moved to 3-formalized
