/-
# q62 — Brolin equidistribution: dominated-convergence reduction of `hConv`

The Brolin keystone `isRieszMeasureOfSmooth_gapAMu_of_greenApprox_integral_tendsto`
(`Q62BrolinEquidistribution.lean`) reduces the unconditional Riesz identity to the single
convergence `hConv : ∫ gₙ·Δφ → ∫ G_c·Δφ`, with `gₙ = greenApprox c · n = (2ⁿ)⁻¹ log‖fⁿ·‖`.

This file replaces the heavy Vitali/`L²`/uniform-integrability route with a **dominated-convergence
split** using the `log⁺` potential `g⁺ₙ = greenApproxPlus c · n = (2ⁿ)⁻¹ log⁺‖fⁿ·‖`:

* `g⁺ₙ → G_c` **everywhere** (`greenApproxPlus_tendsto_greenFunctionDyn`, from the tree's telescoping
  limit `greenApproxPlus_tendsto_greenContinuous` and `greenContinuous = greenFunctionDyn`);
* `g⁺ₙ` is **uniformly bounded on every ball** (`greenApproxPlus_le_ball_const`, telescoped against
  the summable consecutive-difference bound `abs_greenApproxPlus_succ_sub`).

So `∫ g⁺ₙ·Δφ → ∫ G_c·Δφ` by plain dominated convergence (`tendsto_integral_greenApproxPlus_mul`),
with **no** uniform-integrability machinery.  The whole Brolin theorem then reduces to the single
genuinely potential-theoretic input — the vanishing of the negative-log tail

`hTail : (∫ gₙ·Δφ) − (∫ g⁺ₙ·Δφ) → 0`     (i.e. `∫ (2ⁿ)⁻¹ log⁻‖fⁿ·‖·Δφ → 0`),

stated as a difference of integral **values**, so the reduction is pure `Tendsto.add` arithmetic and
needs no `greenApprox` integrability bookkeeping.  `isRieszMeasureOfSmooth_gapAMu_of_tailIntegral_vanish`
is that reduction.

For `c = 0`, `0` is the (exceptional) totally-invariant point, `gₙ ≡ log‖·‖ ↛ G_0` on the disk, and
`hTail` genuinely fails — matching that `c = 0` is excluded from the q62 locus `M ∖ {0, −2}`.
-/
import GaloisForLFunctions.Bottcher.Q62BrolinEquidistribution
import GaloisForLFunctions.Bottcher.GreenContinuity

open Real Filter Topology MeasureTheory Metric Complex Set InnerProductSpace
open scoped Laplacian Real Topology

namespace Bottcher

noncomputable section

/-! ### Uniform-in-`n` upper bound and everywhere-limit for the `log⁺` potentials -/

/-- Telescoped uniform bound: `g⁺_N ≤ g⁺_0 + log(1 + ‖c‖)` for every `N`, because the consecutive
differences of `greenApproxPlus` are summable with total `≤ log(1 + ‖c‖)`. -/
theorem greenApproxPlus_le_zero_add (c z : ℂ) (N : ℕ) :
    greenApproxPlus c z N ≤ greenApproxPlus c z 0 + Real.log (1 + ‖c‖) := by
  have htel : greenApproxPlus c z N
      = greenApproxPlus c z 0 + ∑ n ∈ Finset.range N,
          (greenApproxPlus c z (n + 1) - greenApproxPlus c z n) := by
    rw [Finset.sum_range_sub (fun n => greenApproxPlus c z n) N]; ring
  rw [htel]; gcongr
  calc ∑ n ∈ Finset.range N, (greenApproxPlus c z (n + 1) - greenApproxPlus c z n)
      ≤ ∑ n ∈ Finset.range N, Real.log (1 + ‖c‖) * (1 / 2 : ℝ) ^ (n + 1) := by
        apply Finset.sum_le_sum; intro n _
        exact le_trans (le_abs_self _) (abs_greenApproxPlus_succ_sub c z n)
    _ ≤ ∑' n, Real.log (1 + ‖c‖) * (1 / 2 : ℝ) ^ (n + 1) :=
        (summable_green_diff_bound c).sum_le_tsum _
          (fun n _ => mul_nonneg
            (Real.log_nonneg (le_add_of_nonneg_right (norm_nonneg c))) (by positivity))
    _ = Real.log (1 + ‖c‖) := by
        rw [tsum_mul_left]
        rw [show (∑' n : ℕ, (1/2:ℝ)^(n+1)) = 1 by
          simp_rw [pow_succ']
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num]
        ring

/-- `g⁺_0 = log⁺‖z‖ = log (max ‖z‖ 1)`. -/
theorem greenApproxPlus_zero (c z : ℂ) : greenApproxPlus c z 0 = Real.log (max ‖z‖ 1) := by
  simp [greenApproxPlus]

/-- **Uniform bound on a ball.** `g⁺_N ≤ log(max T 1) + log(1 + ‖c‖)` for all `N` and `‖z‖ ≤ T`. -/
theorem greenApproxPlus_le_ball_const (c z : ℂ) {T : ℝ} (hz : ‖z‖ ≤ T) (N : ℕ) :
    greenApproxPlus c z N ≤ Real.log (max T 1) + Real.log (1 + ‖c‖) := by
  refine le_trans (greenApproxPlus_le_zero_add c z N) ?_
  rw [greenApproxPlus_zero]
  have hlog : Real.log (max ‖z‖ 1) ≤ Real.log (max T 1) :=
    Real.log_le_log (by positivity) (max_le_max hz le_rfl)
  linarith

/-- `g⁺_N → G_c` pointwise, **everywhere** (the tree's telescoping limit lands on
`greenContinuous = greenFunctionDyn`). -/
theorem greenApproxPlus_tendsto_greenFunctionDyn (c z : ℂ) :
    Tendsto (fun N => greenApproxPlus c z N) atTop (𝓝 (greenFunctionDyn c z)) := by
  rw [← greenContinuous_eq_greenFunctionDyn]
  exact greenApproxPlus_tendsto_greenContinuous c z

/-! ### Dominated convergence for the `log⁺` potentials -/

/-- **Dominated convergence for the `log⁺`-potentials.** For any continuous compactly supported `ψ`,
`∫ g⁺ₘ·ψ → ∫ G_c·ψ`: the integrands converge pointwise everywhere and are dominated by
`(log(max T 1) + log(1+‖c‖))·|ψ|`, integrable since `ψ` has compact support. -/
theorem tendsto_integral_greenApproxPlus_mul (c : ℂ) {ψ : ℂ → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun m => ∫ z, greenApproxPlus c z m * ψ z)
      atTop (𝓝 (∫ z, greenFunctionDyn c z * ψ z)) := by
  obtain ⟨T, hT⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set C_B : ℝ := Real.log (max T 1) + Real.log (1 + ‖c‖) with hCB
  refine tendsto_integral_of_dominated_convergence (fun z => C_B * |ψ z|)
    (fun m => ((continuous_greenApproxPlus c m).mul hψ).aestronglyMeasurable)
    ((hψ.integrable_of_hasCompactSupport hψc).norm.const_mul C_B) ?_ ?_
  · intro m
    refine Filter.Eventually.of_forall (fun z => ?_)
    by_cases hz : ψ z = 0
    · simp [hz]
    · have hmem : z ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hz)
      have hzT : ‖z‖ ≤ T := by
        have := hT hmem; rwa [mem_closedBall_zero_iff] at this
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (greenApproxPlus_nonneg c z m)]
      exact mul_le_mul_of_nonneg_right (greenApproxPlus_le_ball_const c z hzT m) (abs_nonneg _)
  · exact Filter.Eventually.of_forall
      (fun z => (greenApproxPlus_tendsto_greenFunctionDyn c z).mul_const (ψ z))

/-! ### `Δφ` is continuous with compact support (reused from the per-level Riesz proof) -/

/-- The Laplacian of a `C²` function is continuous. -/
theorem continuous_laplacian_of_contDiff {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (Δ φ) := by
  have hcont : Continuous (fun x => iteratedFDeriv ℝ 2 φ x) :=
    hφ.continuous_iteratedFDeriv (by norm_num)
  rw [show (Δ φ) = fun x => iteratedFDeriv ℝ 2 φ x ![1, 1] + iteratedFDeriv ℝ 2 φ x ![I, I] from
    laplacian_eq_iteratedFDeriv_complexPlane φ]
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![1,1]).continuous.comp hcont).add
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![I,I]).continuous.comp hcont)

/-- The Laplacian preserves compact support (a local differential operator). -/
theorem hasCompactSupport_laplacian {φ : ℂ → ℝ} (hφc : HasCompactSupport φ) :
    HasCompactSupport (Δ φ) := by
  obtain ⟨R, hR0, hR⟩ := hφc.exists_pos_le_norm
  have hΔloc : ∀ z : ℂ, R < ‖z‖ → Δ φ z = 0 := by
    intro z hz
    have hEZ : φ =ᶠ[𝓝 z] (fun _ => (0:ℝ)) :=
      eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
        (fun x hx => hR x (le_of_lt hx))
    rw [(laplacian_congr_nhds hEZ).eq_of_nhds]; simp
  exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R)
    (fun z hz => by
      rw [Function.mem_support] at hz; rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h; exact hz (hΔloc z (by linarith [not_le.mp h])))

/-! ### The reduction of `hConv` to the negative-log tail -/

/-- **Brolin, reduced to the negative-log tail.**  The unconditional Riesz identity
`IsRieszMeasureOfSmooth (gapAMu c) G_c` follows from the single input `hTail`: for every `C²`
compactly supported `φ`, the difference of the finite-potential integral and its `log⁺` counterpart
tends to `0` along the Brolin subsequence.  Equivalently `∫ (2ⁿ)⁻¹ log⁻‖fⁿ·‖·Δφ → 0` — the genuine
potential-theoretic content of Brolin equidistribution.  Everything else (the `log⁺` dominated
convergence to `∫ G_c·Δφ`) is discharged here. -/
theorem isRieszMeasureOfSmooth_gapAMu_of_tailIntegral_vanish {c : ℂ}
    (hTail : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      Tendsto (fun k => (∫ z, greenApprox c z (brolinLimitSubsequence c k) * Δ φ z)
                      - (∫ z, greenApproxPlus c z (brolinLimitSubsequence c k) * Δ φ z))
        atTop (𝓝 0)) :
    IsRieszMeasureOfSmooth (gapAMu c) (greenFunctionDyn c) := by
  apply isRieszMeasureOfSmooth_gapAMu_of_greenApprox_integral_tendsto
  intro φ hφ hφc
  have hcΔ : Continuous (Δ φ) := continuous_laplacian_of_contDiff hφ
  have hΔc : HasCompactSupport (Δ φ) := hasCompactSupport_laplacian hφc
  have hConvPlus :
      Tendsto (fun k => ∫ z, greenApproxPlus c z (brolinLimitSubsequence c k) * Δ φ z)
        atTop (𝓝 (∫ z, greenFunctionDyn c z * Δ φ z)) :=
    (tendsto_integral_greenApproxPlus_mul c hcΔ hΔc).comp (brolinLimitSubsequence_tendsto_atTop c)
  have hsum := (hTail φ hφ hφc).add hConvPlus
  simpa using hsum

end

end Bottcher
