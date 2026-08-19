import Mathlib
import GaloisForLFunctions.HTGeometry.HardyDiskGutzmer

/-!
# The Hardy space of the unit disk in its coefficient model

`hardy-cyclicity-maximal-ht-field-blindness`, analytic substrate.

`H²(D)` is realized as `ℓ²(ℕ)` — the Taylor coefficients at the origin — with

```text
hardyFun a z = ∑ₙ aₙ zⁿ
```

the associated analytic function on the open unit disk.  The two directions are proved here:

* `diskCoeff_hardyFun` — the Taylor coefficients of `hardyFun a` are `a`;
* `summable_diskCoeff_sq_of_circleAverage_le` — an analytic function on the disk whose circle
  averages are uniformly bounded has square-summable Taylor coefficients, with the same bound.

Together with Gutzmer's identity this is exactly the `H²` norm characterization.
-/

open Complex Filter Metric Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Canonical Taylor coefficients at the origin -/

/-- The `n`-th Taylor coefficient of `f` at the origin. -/
def diskCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / (Nat.factorial n : ℂ)

theorem coeff_eq_diskCoeff {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ENNReal}
    (hf : HasFPowerSeriesOnBall f p 0 R) (n : ℕ) : p.coeff n = diskCoeff f n := by
  have h := hf.factorial_smul (1 : ℂ) n
  rw [show ((p n) fun _ => (1 : ℂ)) = p.coeff n from rfl] at h
  have hiter : (iteratedFDeriv ℂ n f 0) (fun _ => (1 : ℂ)) = iteratedDeriv n f 0 :=
    (iteratedDeriv_eq_iteratedFDeriv).symm
  rw [hiter, nsmul_eq_mul] at h
  have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [diskCoeff, ← h]
  field_simp

/-! ## Gutzmer in terms of the canonical coefficients -/

theorem hasSum_circleAverage_normSq_diskCoeffOn {f : ℂ → ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) {r : ℝ} (hr0 : 0 ≤ r) (hrR : r < R) :
    HasSum (fun k => ‖diskCoeff f k‖ ^ 2 * r ^ (2 * k))
      ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) := by
  set s : ℝ := (R + r) / 2 with hs
  set t : ℝ := (R + 3 * r) / 4 with ht
  have hrt : r < t := by rw [ht]; linarith
  have hts : t < s := by rw [ht, hs]; linarith
  have hsR : s < R := by rw [hs]; linarith
  have hs0 : 0 < s := by rw [hs]; linarith
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hclosed : DifferentiableOn ℂ f (Metric.closedBall 0 (Real.toNNReal s : ℝ)) := by
    refine hf.mono ?_
    rw [Real.coe_toNNReal s (le_of_lt hs0)]
    exact Metric.closedBall_subset_ball hsR
  have hRpos : 0 < Real.toNNReal s := by
    rw [← NNReal.coe_pos, Real.coe_toNNReal s (le_of_lt hs0)]
    exact hs0
  have hp := _root_.DifferentiableOn.hasFPowerSeriesOnBall hclosed hRpos
  have hrt' : r < (Real.toNNReal t : ℝ) := by
    rw [Real.coe_toNNReal t ht0]; exact hrt
  have hts' : ((Real.toNNReal t : NNReal) : ENNReal) < ((Real.toNNReal s : NNReal) : ENNReal) := by
    refine ENNReal.coe_lt_coe.mpr ?_
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal t ht0, Real.coe_toNNReal s (le_of_lt hs0)]
    exact hts
  have hgz := hasSum_circleAverage_normSq hp hr0 hrt' hts'
  refine hgz.congr_fun fun k => ?_
  rw [coeff_eq_diskCoeff hp k]

theorem hasSum_circleAverage_normSq_diskCoeff {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k => ‖diskCoeff f k‖ ^ 2 * r ^ (2 * k))
      ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) :=
  hasSum_circleAverage_normSq_diskCoeffOn hf hr0 hr1

/-! ## Square summability from bounded circle averages -/

/-- **The `H²` criterion.**  If the circle averages of `‖f‖²` are bounded by `K` for every radius
below `1`, then the Taylor coefficients of `f` are square summable with the same bound. -/
theorem summable_diskCoeff_sq_of_circleAverage_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {K r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1)
    (hK : ∀ r : ℝ, r₀ ≤ r → r < 1 →
      (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2 ≤ K) :
    Summable (fun n => ‖diskCoeff f n‖ ^ 2) ∧ ∑' n, ‖diskCoeff f n‖ ^ 2 ≤ K := by
  have hfinite : ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖diskCoeff f n‖ ^ 2 ≤ K := by
    intro N
    have hbound : ∀ r : ℝ, r ∈ Set.Ico r₀ 1 →
        ∑ n ∈ Finset.range N, ‖diskCoeff f n‖ ^ 2 * r ^ (2 * n) ≤ K := by
      rintro r ⟨hr0', hr1⟩
      have hr0 : 0 ≤ r := le_trans hr₀ hr0'
      have hgz := hasSum_circleAverage_normSq_diskCoeff hf hr0 hr1
      have hsum : Summable (fun k => ‖diskCoeff f k‖ ^ 2 * r ^ (2 * k)) := hgz.summable
      have hle := hsum.sum_le_tsum (Finset.range N) (fun n _ => by positivity)
      rw [hgz.tsum_eq] at hle
      exact le_trans hle (hK r hr0' hr1)
    have hcont : ContinuousAt
        (fun r : ℝ => ∑ n ∈ Finset.range N, ‖diskCoeff f n‖ ^ 2 * r ^ (2 * n)) 1 := by
      fun_prop
    have hlim : Tendsto
        (fun r : ℝ => ∑ n ∈ Finset.range N, ‖diskCoeff f n‖ ^ 2 * r ^ (2 * n))
        (nhdsWithin (1:ℝ) (Set.Iio 1))
        (𝓝 (∑ n ∈ Finset.range N, ‖diskCoeff f n‖ ^ 2 * (1:ℝ) ^ (2 * n))) :=
      hcont.continuousWithinAt
    have hIoo : Set.Ioo r₀ 1 ∈ nhdsWithin (1:ℝ) (Set.Iio 1) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Ioi r₀, isOpen_Ioi, hr₀1, fun x hx => ⟨hx.1, hx.2⟩⟩
    have hres := le_of_tendsto hlim
      (Filter.eventually_of_mem hIoo fun r hr => hbound r ⟨le_of_lt hr.1, hr.2⟩)
    simpa using hres
  have hnn : ∀ n : ℕ, 0 ≤ ‖diskCoeff f n‖ ^ 2 := fun n => by positivity
  have hsum : Summable (fun n => ‖diskCoeff f n‖ ^ 2) := summable_of_sum_range_le hnn hfinite
  exact ⟨hsum, tsum_le_of_sum_range_le hnn hfinite⟩

/-! ## The coefficient model of `H²(D)` -/

/-- `H²(D)`, realized as the space of square-summable Taylor coefficients. -/
abbrev HardyDisk := lp (fun _ : ℕ => ℂ) 2

theorem hardyDisk_norm_sq (a : HardyDisk) : ‖a‖ ^ 2 = ∑' n, ‖a n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ => ℂ) (by norm_num) a
  simpa using h

theorem hardyDisk_norm_coord_le (a : HardyDisk) (n : ℕ) : ‖a n‖ ≤ ‖a‖ :=
  lp.norm_apply_le_norm (by norm_num) a n

theorem summable_hardyDisk_terms (a : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => a n * z ^ n) := by
  refine Summable.of_norm_bounded (g := fun n => ‖a‖ * ‖z‖ ^ n) ?_ ?_
  · exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖a‖
  · intro n
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hardyDisk_norm_coord_le a n) (by positivity)

/-- The analytic function on the open unit disk with Taylor coefficients `a`. -/
def hardyFun (a : HardyDisk) (z : ℂ) : ℂ := ∑' n, a n * z ^ n

/-- Its formal power series. -/
def hardySeries (a : HardyDisk) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => a n)

theorem eball_one_eq (x : ℂ) : Metric.eball x (1 : ENNReal) = Metric.ball x 1 := by
  rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp, Metric.eball_ofReal]

theorem hardySeries_coeff (a : HardyDisk) (n : ℕ) : (hardySeries a).coeff n = a n := by
  have h := FormalMultilinearSeries.ofScalars_apply_eq (E := ℂ) (fun m => (a m : ℂ)) (1 : ℂ) n
  rw [FormalMultilinearSeries.coeff, hardySeries,
    show ((1 : Fin n → ℂ)) = (fun _ : Fin n => (1:ℂ)) from rfl, h]
  simp

theorem one_le_hardySeries_radius (a : HardyDisk) : 1 ≤ (hardySeries a).radius := by
  have h := (hardySeries a).le_radius_of_bound ‖a‖ (r := 1) (fun n => ?_)
  · simpa using h
  · rw [hardySeries, FormalMultilinearSeries.ofScalars_norm]
    simpa using hardyDisk_norm_coord_le a n

theorem hasFPowerSeriesOnBall_hardyFun (a : HardyDisk) :
    HasFPowerSeriesOnBall (hardyFun a) (hardySeries a) 0 1 where
  r_le := one_le_hardySeries_radius a
  r_pos := by norm_num
  hasSum := by
    intro y hy
    have hy' : ‖y‖ < 1 := by
      have hb : y ∈ Metric.ball (0 : ℂ) 1 := by rwa [eball_one_eq] at hy
      simpa [Metric.mem_ball, dist_zero_right] using hb
    have hs := (summable_hardyDisk_terms a hy').hasSum
    rw [zero_add]
    refine hs.congr_fun fun n => ?_
    rw [hardySeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

theorem diskCoeff_hardyFun (a : HardyDisk) (n : ℕ) : diskCoeff (hardyFun a) n = a n := by
  rw [← coeff_eq_diskCoeff (hasFPowerSeriesOnBall_hardyFun a) n, hardySeries_coeff]

theorem differentiableOn_hardyFun (a : HardyDisk) :
    DifferentiableOn ℂ (hardyFun a) (Metric.ball 0 1) := by
  intro z hz
  have hball : z ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by rwa [eball_one_eq]
  have hda : DifferentiableAt ℂ (hardyFun a) z :=
    ((hasFPowerSeriesOnBall_hardyFun a).analyticAt_of_mem hball).differentiableAt
  exact hda.differentiableWithinAt

/-- **The `H²` norm bounds every circle average.** -/
theorem circleAverage_hardyFun_le (a : HardyDisk) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖hardyFun a (circleMap 0 r θ)‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have hgz := hasSum_circleAverage_normSq_diskCoeff (differentiableOn_hardyFun a) hr0 hr1
  have hgz' : HasSum (fun k => ‖a k‖ ^ 2 * r ^ (2 * k))
      ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖hardyFun a (circleMap 0 r θ)‖ ^ 2) := by
    refine hgz.congr_fun fun k => ?_
    rw [diskCoeff_hardyFun]
  have hsq : Summable (fun n => ‖a n‖ ^ 2) := by
    have h := (lp.memℓp a)
    rw [memℓp_gen_iff (by norm_num)] at h
    refine h.congr fun n => ?_
    rw [← Real.rpow_natCast ‖a n‖ 2]
    norm_num
  rw [← hgz'.tsum_eq, hardyDisk_norm_sq]
  refine Summable.tsum_le_tsum (fun k => ?_) hgz'.summable hsq
  have hrk : r ^ (2 * k) ≤ 1 := pow_le_one₀ hr0 (le_of_lt hr1)
  nlinarith [sq_nonneg ‖a k‖, hrk, pow_nonneg hr0 (2 * k)]

end GaloisForLFunctions.HTGeometry
