# The oscillating smooth power shifts its pole off the real abscissa

- **ID:** oscillating-smooth-power-shifted-pole
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/rh-current-frontier-map.md` Route MC (Alternate oscillating-probe receiver)
- **Statement:** For `c_{ε,t}(d) = d^{-ε} cos(t log d)` (`0 < ε ≤ 1/2`, `t ∈ ℝ`, `ρ = 1 − ε + it`):
  (1) when `t ≠ 0`, the real-axis Dirichlet series `C_{ε,t}(σ) = Σ_d c_{ε,t}(d) d^{-σ} = Re ζ(σ + ε − it)` converges to `Re ζ(1 − it)` and is Lipschitz as `σ ↓ 1 − ε` regardless of whether `c_{ε,t}` is paid, because the oscillation shifts the pole from the real abscissa `1 − ε` to `1 − ε ± it`;
  (2) unconditionally, `c_{ε,t}` is unpaid on `(0, 1/2]` at `t = 0`, on a positive sub-half collar `(0, δ(T)]` for `|t| ≤ T`, and across all `t ∈ ℝ` on the Vinogradov–Korobov sub-half strip `0 < ε ≤ min(1/2, min(δ, w_{VK}(max(K_0, |t|) + 1))/4)`, while the paid dampings at any fixed `t` and the paid frequencies on any `[-T, T]` at any fixed `ε ∈ (0, 1/2]` are finite;
  (3) for every critical Wiener kernel `k` (`Σ_j |k(j)| j^{-1/2} < ∞`) and `0 < ε < 1/2`, `k ⋆ c_{ε,t}` is receiver-bounded if and only if `Σ_j k(j) j^{-(1−ε+it)} = 0` or `ζ(1 − ε + it) = 0`.

## Goal

Close the Route MC alternate-receiver question by:
1. Explaining and proving why the real-axis source/Mellin non-admission tools (`APaidReceiverBoundsTheDirichletSeriesUpToItsAbscissa`, `APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa`) cannot refute `ReceiverBounded (oscillatingSmoothPower ε t)` for `t ≠ 0`: the real-axis Dirichlet series `C_{ε,t}(σ)` is regular and Lipschitz across the real abscissa `σ = 1 − ε` for every `t ≠ 0`, because the pole sits off the real axis at `s = 1 − ε ± it`.
2. Establishing the strongest unconditional non-admission and finiteness theorems for `oscillatingSmoothPower ε t` below half damping (`t = 0`, bounded-frequency collars, the global Vinogradov–Korobov sub-half region, and finiteness/isolation of paid sub-half dampings and frequencies).
3. Extending the sub-half hyperplane law (`CriticalWienerPerturbationsOfTheSmoothPowerAreDecidedAtThePole`) from the static smooth power `d^{-ε}` to all oscillating smooth powers `c_{ε,t}`: a critical Wiener convolution `k ⋆ c_{ε,t}` (`0 < ε < 1/2`) is paid iff the complex Dirichlet series of `k` vanishes at the shifted pole `ρ = 1 − ε + it` or `ζ(ρ) = 0`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `TheOscillatingSmoothPowerShiftsItsPoleOffTheRealAbscissa`, `lake --old env lean` exit 0, standard axioms only
- [ ] 3 → 4  publication-ready

## Paper proof `[PROVED HERE]`

### §1. Real-abscissa regularity and off-axis pole shift (`t ≠ 0`)
For `d ≥ 1` and `σ > 1 − ε`, put `w = (σ + ε) − it` (`Re w = σ + ε > 1`). Then
`d^{-(σ+ε)} cos(t log d) = Re(d^{-w})`. Summing over `d ≥ 1` against `Complex.hasSum_nat_cpow` gives
`Σ_{d≥1} c_{ε,t}(d) d^{-σ} = Re ζ((σ + ε) − it)`.
When `t ≠ 0`, the point `w_0 = 1 − it ≠ 1` (`Im w_0 = −t ≠ 0`), so `ζ` is complex-differentiable at `w_0` (`differentiableAt_riemannZeta`). Hence `σ ↦ Re ζ((σ + ε) − it)` is differentiable at `σ = 1 − ε` with value `Re ζ(1 − it)`, so as `σ ↓ 1 − ε` the real-axis Dirichlet series converges to `Re ζ(1 − it)` and satisfies `|C_{ε,t}(σ) − Re ζ(1 − it)| ≤ M(σ − (1 − ε))` on `(1 − ε, 1 − ε + η)` for every `t ≠ 0` and every `ε ∈ ℝ`, paid or unpaid.

### §2. Unconditional zero-free exclusions and finiteness of paid parameters
By `zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower`, for `0 < ε ≤ 1/2` and `t ∈ ℝ`, `ReceiverBounded (oscillatingSmoothPower ε t)` implies `ζ(1 − ε + it) = 0`.
1. At `t = 0`, `0 < 1 − ε < 1`, so `ζ(1 − ε) ≠ 0` (`riemannZeta_ne_zero_of_pos_of_lt_one`), hence `¬ ReceiverBounded (oscillatingSmoothPower ε 0)`.
2. For any `T ≥ 0`, `exists_zero_free_box T` gives `δ > 0` such that `ζ(s) ≠ 0` on `1 − δ ≤ Re s ≤ 1`, `|Im s| ≤ T`, `s ≠ 1`. Thus for `|t| ≤ T` and `0 < ε ≤ min(δ, 1/2)`, `¬ ReceiverBounded (oscillatingSmoothPower ε t)`.
3. By `exists_vk_zero_free_region_abs`, for `|t| ≥ T_0` and `0 < ε < min(1/2, vkHadamardWidth |t|)`, `ζ(1 − ε + it) ≠ 0`, so `¬ ReceiverBounded (oscillatingSmoothPower ε t)`. Globally, `exists_bound_invZeta_vk_uniform` gives `δ > 0` and `K_0 ≥ e^{e^{30}}` such that for all `t ∈ ℝ`, `K ≥ max(K_0, |t|)`, and `0 < ε ≤ min(1/2, min(δ, vkHadamardWidth(K + 1))/4)`, `¬ ReceiverBounded (oscillatingSmoothPower ε t)`.
4. Fix `t ∈ ℝ`. By (2) with `T = |t|`, there is `δ > 0` such that every paid `ε ∈ (0, 1/2]` satisfies `δ ≤ ε ≤ 1/2`. For each `x ∈ [δ, 1/2]`, `z = 1 − x + it ≠ 1`, so `eventually_zetaResidueUnit_ne_zero z` gives an open neighbourhood `U_x` of `x` on which `(1 − ε + it) − 1` and `ζ(1 − ε + it)` are nonzero for all `ε ∈ U_x \ {x}`. By compactness of `[δ, 1/2]`, finitely many `U_x` cover `[δ, 1/2]`, so `{ε ∈ (0, 1/2] | ReceiverBounded (oscillatingSmoothPower ε t)}` is finite.
5. Fix `0 < ε ≤ 1/2` and `T ≥ 0`. For each `t_0 ∈ [−T, T]`, `1 − ε + it_0 ≠ 1`, so `eventually_zetaResidueUnit_ne_zero (1 − ε + it_0)` gives an open neighbourhood `V_{t_0}` containing at most `t_0` among paid frequencies. Compactness of `[−T, T]` yields finiteness of `{t ∈ [−T, T] | ReceiverBounded (oscillatingSmoothPower ε t)}`.

### §3. The shifted-pole hyperplane law for critical Wiener convolutions
Let `k` satisfy `CriticalWiener k` (`Σ_j |k(j)| j^{-1/2} < ∞`), `0 < ε < 1/2`, `t ∈ ℝ`, `ρ = 1 − ε + it`, and `m = Re ζ(2 − ρ)`.
1. By `weightCenteredPrefix_dirichletConv`,
   `A_{k ⋆ c_{ε,t}}(n) = Σ_{1 ≤ j ≤ n} k(j) A_{ε,t}(⌊n/j⌋) + m A_k(n)`.
2. For `1 ≤ j ≤ n`, write `A_{ε,t}(⌊n/j⌋) = Re((ζ(ρ)/ρ) n^ρ j^{-ρ}) + R_{ε,t}(n, j)`. Since `(n/j : ℝ)^ρ = n^ρ j^{-ρ}` (`n, j > 0`), `abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le` at `⌊n/j⌋ ≥ 1` and `norm_cpow_sub_cpow_le` on `[⌊n/j⌋, n/j]` give
   `|R_{ε,t}(n, j)| ≤ (floorSumRate ρ + ‖ζ(ρ)‖) (√(n/j))^{1−ε}`.
   Summing over `j ≤ n ≤ T` against `1/(n(n+1)) ≤ n^{-2}` via `sum_Icc_rpow_neg_one_sub_le` gives
   `pronicNorm (fun n => if j ≤ n then R_{ε,t}(n, j) else 0) T ≤ (floorSumRate ρ + ‖ζ(ρ)‖) √(1 + 1/ε) j^{-1/2}`.
3. Since `1 − ε > 1/2`, `K(ρ) := Σ_{j≥1} (k(j) : ℂ) j^{-ρ}` converges absolutely. For each `j ≥ 1` and `1 ≤ n < j`, `|Re((ζ(ρ)/ρ) n^ρ j^{-ρ})| ≤ ‖ζ(ρ)/ρ‖ n^{1−ε} j^{-(1−ε)}`. By `RHTower.sum_rpow_neg_head_le`,
   `pronicNorm (fun n => if n < j then n^{1−ε} j^{-(1−ε)} else 0) T ≤ √(1 + 1/(1 − 2ε)) j^{-1/2}`.
   Thus replacing the partial sum `Σ_{j≤n} k(j) j^{-ρ}` by `K(ρ)` changes the pronic norm at cutoff `T` by at most `‖ζ(ρ)/ρ‖ √(1 + 1/(1 − 2ε)) Σ_j |k(j)| j^{-1/2}`.
4. Hence `pronicNorm (A_{k ⋆ c_{ε,t}}) T` and `pronicNorm (fun n => Re((K(ρ)ζ(ρ)/ρ) n^ρ)) T` differ by a constant independent of `T`. By the harmonic energy lower bound for `Re(a n^ρ)` (`0 < ε ≤ 1/2`), the latter is bounded in `T` iff `K(ρ)ζ(ρ)/ρ = 0`, i.e. `K(1 − ε + it) = 0 ∨ ζ(1 − ε + it) = 0`.

## No-go closure
- **Exact killing theorem/mechanism:** Direct real-axis Mellin/abscissa non-admission (`not_receiverBounded_of_tendsto_abs_dirichletSeries`, `exists_abs_dirichletSeries_sub_le_mul`) cannot exclude `oscillatingSmoothPower ε t` for `t ≠ 0` because `C_{ε,t}(σ) = Re ζ(σ + ε − it)` is holomorphic across the real abscissa `σ = 1 − ε`: the oscillation shifts the pole to `s = 1 − ε ± it`.
- **Strongest positive survivor:**
  1. `tendsto_dirichletSeries_oscillatingSmoothPower_nhdsGT` and `exists_abs_dirichletSeries_oscillatingSmoothPower_sub_le_mul` (unconditional real-abscissa convergence and Lipschitz regularity for all `t ≠ 0`).
  2. `not_receiverBounded_oscillatingSmoothPower_zero`, `exists_delta_not_receiverBounded_oscillatingSmoothPower_box`, `exists_not_receiverBounded_oscillatingSmoothPower_vk_uniform`, `finite_damping_receiverBounded_oscillatingSmoothPower`, and `finite_freq_receiverBounded_oscillatingSmoothPower` (unconditional zero-free strip exclusions and finiteness of paid sub-half dampings and frequencies).
  3. `receiverBounded_dirichletConv_oscillatingSmoothPower_iff` (the shifted-pole hyperplane law on the critical Wiener algebra: `ReceiverBounded (k ⋆ c_{ε,t}) ↔ K(1 − ε + it) = 0 ∨ ζ(1 − ε + it) = 0` for `0 < ε < 1/2`).
- **New insight:** On the oscillating smooth-power family, the real abscissa `1 − ε` is a regular point of the real-axis Dirichlet series for every `t ≠ 0`; receiver admission is governed instead by the product of the kernel's Dirichlet series and `ζ` at the shifted complex pole `ρ = 1 − ε + it`.
- **Status:** Paper proof complete (`[PROVED HERE]`); formalizing in `GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerShiftsItsPoleOffTheRealAbscissa`.

## Log
- 2026-10-23 — Created in `1-in-progress` with complete paper proof and no-go/positive-salvage closure.
