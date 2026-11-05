# The camera reads a near-coincident cluster through its first three moments

- **ID:** zcg-second-order-local-inversion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0411/obstacles-summary_v2.md §2.5.5 (B51) · ZCG README §10 (a)
- **Statement:** Let `Z, Z'` be tempered mimics at aperture `a`, `z₀` a point at height `X`, and
  `0 < r ≤ η`. Suppose every cluster point with height in `[X − R, X + R]` lies in the disc
  `‖z − z₀‖ ≤ r` or at distance `≥ η` from `z₀`, and that these points have count bound `(D, C₀)`
  with `πD < 2a`. Put `ω = γ_{z₀}`, `μ_j = Σ_{‖z − z₀‖ ≤ r} c(z)(γ_z − ω)^j` and
  `N = Σ_{‖z − z₀‖ ≤ r} |c(z)|`. Then for `j = 0, 1, 2`
  `‖μ_j‖ ≤ (N r^{j+1} Lip + Tail_j)/Floor`,
  where `Floor = windowFloor²`, `Lip` is the Lipschitz constant of the pair image on the strip
  (`≍ a² M²`), and `Tail_j ≍ M² e^a (1 + |X|)²/(1 + R)^{2k−2} · S`. In particular `μ₀ = 0` once
  the right side is `< 1`, since `μ₀ ∈ ℤ`.

## Goal
B51 in the form the window method reaches. For a near-coincident pair `c ± w/2` of `Z` against
`c' ± w'/2` of `Z'`: `μ₀ = 0`, `μ₁ = 2(c − c')`, and `μ₂` gives `w² − w'² = O(r³ Lip/Floor)`. So
the image fixes the centre to `O(r²)` and the squared gap to relative precision `O(r Lip/Floor)`.
The sign of `w²` (real pair vs FE pair) is then read from the image (B44 in prime form).

## Proof
Take the isolating windows `F, G` of `isolating_window_of_bump`, blind to the cluster outside the
disc (all at distance `≥ η` from `ω`), and translate to height `X`. Let `Φ(w) = F̂(w) conj Ĝ(conj w)`.
Replace `F` by `annihilate^j F`, whose transform is `(−i(w − ω))^j F̂(w)`; its strip decay costs `j`
orders, so use decay order `k + 2`. Mimicry gives
`0 = Σ_{disc} c(z)(−i(γ_z − ω))^j Φ(γ_z) + Tail_j`.
Write `Φ(γ_z) = Φ(ω) + e_z` with `|e_z| ≤ r Lip`. Lipschitz control of `F̂` on the strip follows
from `|e^{iwu} − e^{iw'u}| ≤ |w − w'| |u| e^{a/2}` and `sup |F| ≤ (2π)^{-1} ∫|F̂| ≤ M/π`. So
`|Φ(ω)| |μ_j| ≤ N r^{j+1} Lip + |Tail_j|`.

## Scale for `ζ`
With `η = exp(−κ log X/(1 + log log X))` the floor is `e^{−O((log X)²)}`, `Lip = e^{O((log X)²)}`,
and decay order `k ≍ log X` makes the tail negligible. So the moments are fixed for clusters of
radius `r ≤ exp(−C (log X)²)`.

## Uniformly in height at polynomial scales
The isolating window `F̂ = sin · b̂² · Π r_k` varies slowly relative to its value at the target:
`|F̂(w) − F̂(w₀)| ≤ (e^{|w − w₀|Λ} − 1)|F̂(w₀)|`, with `Λ` the sum of the log-derivative bounds of
the sine (`|S(w₀)| ≥ ½`), the bump (Cauchy, `|b̂(w₀)| ≥ 1`) and the product
(`|Π q_k − 1| ≤ e^{|w − w₀|Λ_P} − 1`, `Λ_P = 64L(1 + L/η)S₀/H²`). In the moment identity the disc
error is then `6rΛ|Φ(ω)|` per point, so `‖μ_j‖ ≤ N r^{j+1} 6Λ + Tail_j/Floor`. For RvM clusters at
height `T`, aperture `λ · ½ log(T/2π)` and isolation `T^{−M'}`: `6Λ ≤ T^{M' + κ_λ}`,
`κ_λ = πλ/2 + λ + 3`. Decay order `k = ⌈(K + K') log²(T/2π)⌉` makes `Tail/Floor ≤ e^{−K' log³(T/2π)}`.
For a pair `P₁, P₂` against `Q₁, Q₂` this gives centre `4r²T^{M' + κ_λ} + E` and squared gap
`24r³T^{M' + κ_λ} + 4E` for `r ≤ T^{−(M' + κ_λ + 1)}`. For an isolated dipole, `ρ ≤ 2ρ²T^{M' + κ_λ} + E`
forces `ρ ≤ 2E`.

## Lean
`formal/GaloisForLFunctions/ZeroConfigurationGeometry/NearCoincidencesAreReadThroughTheirMoments.lean`:
`norm_discMoment_le` (the statement), `sum_multDiff_eq_zero_of_disc` (`μ₀ = 0`), `pair_moments`
(centre and squared gap from `μ₁, μ₂`), `norm_discMoment_zeta_le` (for `ζ`: for every `K` there are
`C, X₀` with `‖μ_j‖ ≤ N r^{j+1} e^{C (log X)²} + e^{−K (log X)²}` at isolation
`exp(−κ log X/(1 + log log X))`).
`formal/GaloisForLFunctions/ZeroConfigurationGeometry/IsolatingWindowsVarySlowlyAtTheirTarget.lean`:
`core_window_slow`, `isolating_window_slow`, `norm_discMoment_le_slow`, `six_slowRate_le_rpow`,
`camera_tail_budget`, `norm_discMoment_rvm_le`, `pair_centre_and_gap_rvm`, `dipole_collapse_rvm`. Supporting: `exists_local_isolating_pair` (in
`IsolatedPointsAreSeenByTheLocalCamera`), `annihilatePow_props`, `norm_paperFT_sub_le_of_bounded`,
`norm_le_of_paperFT_decay`, `norm_pairImage_sub_le`. Unconditional; axioms `propext`,
`Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 2 → 3  formalized

## Log
- 2026-11-04 — created; formalized
