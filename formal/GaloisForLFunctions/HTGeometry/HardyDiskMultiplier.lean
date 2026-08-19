import GaloisForLFunctions.HTGeometry.HardyDiskSpace

/-!
# Bounded analytic multipliers of `H²(D)`

`hardy-cyclicity-maximal-ht-field-blindness`, analytic substrate.

A function `φ` analytic and bounded by `M` on the open unit disk multiplies `H²(D)` boundedly with
operator norm at most `M`.  This is the only analytic input the cyclicity statement needs: an
invertible `H^∞` function gives a topological isomorphism of `H²`, so it carries the dense set of
polynomials onto a dense set, i.e. it is a cyclic vector.
-/

open Complex Filter Metric Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Power series on a fixed inner ball -/

theorem hasFPowerSeriesOnBall_of_ball_one {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 ((Real.toNNReal ρ : NNReal) : ℝ)) 0
      ((Real.toNNReal ρ : NNReal) : ENNReal) := by
  have hcoe : ((Real.toNNReal ρ : NNReal) : ℝ) = ρ := Real.coe_toNNReal ρ (le_of_lt hρ0)
  have hclosed : DifferentiableOn ℂ f (Metric.closedBall 0 ((Real.toNNReal ρ : NNReal) : ℝ)) := by
    refine hf.mono ?_
    rw [hcoe]
    exact Metric.closedBall_subset_ball hρ1
  have hRpos : 0 < Real.toNNReal ρ := by
    rw [← NNReal.coe_pos, hcoe]; exact hρ0
  simpa using _root_.DifferentiableOn.hasFPowerSeriesOnBall hclosed hRpos

/-! ## Linearity of the canonical coefficients -/

theorem diskCoeff_add' {F G : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hG : DifferentiableOn ℂ G (Metric.ball 0 1)) (n : ℕ) :
    diskCoeff (F + G) n = diskCoeff F n + diskCoeff G n := by
  have hpF := hasFPowerSeriesOnBall_of_ball_one hF (ρ := 1/2) (by norm_num) (by norm_num)
  have hpG := hasFPowerSeriesOnBall_of_ball_one hG (ρ := 1/2) (by norm_num) (by norm_num)
  have hsum := hpF.add hpG
  rw [← coeff_eq_diskCoeff hsum n, ← coeff_eq_diskCoeff hpF n, ← coeff_eq_diskCoeff hpG n]
  rfl

theorem diskCoeff_add {F G : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hG : DifferentiableOn ℂ G (Metric.ball 0 1)) (n : ℕ) :
    diskCoeff (fun z => F z + G z) n = diskCoeff F n + diskCoeff G n :=
  diskCoeff_add' hF hG n

theorem diskCoeff_smul' {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1)) (c : ℂ)
    (n : ℕ) : diskCoeff (c • F) n = c * diskCoeff F n := by
  have hpF := hasFPowerSeriesOnBall_of_ball_one hF (ρ := 1/2) (by norm_num) (by norm_num)
  have hsmul := hpF.const_smul (c := c)
  rw [← coeff_eq_diskCoeff hpF n, ← coeff_eq_diskCoeff hsmul n]
  rfl

theorem diskCoeff_smul {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1)) (c : ℂ)
    (n : ℕ) : diskCoeff (fun z => c * F z) n = c * diskCoeff F n :=
  diskCoeff_smul' hF c n

/-! ## Reconstruction -/

theorem hasSum_diskCoeff {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    {z : ℂ} (hz : ‖z‖ < 1) : HasSum (fun n => diskCoeff g n * z ^ n) (g z) := by
  set ρ : ℝ := (‖z‖ + 1) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hzρ : ‖z‖ < ρ := by rw [hρ]; linarith
  have hp := hasFPowerSeriesOnBall_of_ball_one hg hρ0 hρ1
  have hcoe : ((Real.toNNReal ρ : NNReal) : ℝ) = ρ := Real.coe_toNNReal ρ (le_of_lt hρ0)
  have hmem : z ∈ Metric.eball (0 : ℂ) ((Real.toNNReal ρ : NNReal) : ENNReal) := by
    rw [show ((Real.toNNReal ρ : NNReal) : ENNReal) = ENNReal.ofReal ρ from rfl,
      Metric.eball_ofReal]
    simpa [Metric.mem_ball, dist_zero_right] using hzρ
  have hs := hp.hasSum hmem
  rw [zero_add] at hs
  refine hs.congr_fun fun n => ?_
  rw [(cauchyPowerSeries g 0 _).apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm,
    coeff_eq_diskCoeff hp n]

/-- The reconstruction map: an analytic function on the disk with square-summable coefficients is
the `hardyFun` of those coefficients. -/
theorem hardyFun_of_diskCoeff {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hmem : Memℓp (diskCoeff g) 2) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun ⟨diskCoeff g, hmem⟩ z = g z := by
  have hs := hasSum_diskCoeff hg hz
  rw [hardyFun]
  exact hs.tsum_eq

/-! ## Linearity of `hardyFun` -/

theorem hardyFun_add (a b : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun (a + b) z = hardyFun a z + hardyFun b z := by
  rw [hardyFun, hardyFun, hardyFun,
    ← (summable_hardyDisk_terms a hz).tsum_add (summable_hardyDisk_terms b hz)]
  refine tsum_congr fun n => ?_
  have : ((a + b) : HardyDisk) n = a n + b n := rfl
  rw [this, add_mul]

theorem hardyFun_smul (c : ℂ) (a : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun (c • a) z = c * hardyFun a z := by
  rw [hardyFun, hardyFun, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have : ((c • a) : HardyDisk) n = c * a n := rfl
  rw [this, mul_assoc]

/-! ## Locality of the coefficients -/

theorem diskCoeff_congr {F G : ℂ → ℂ} (h : ∀ z ∈ Metric.ball (0:ℂ) 1, F z = G z) (n : ℕ) :
    diskCoeff F n = diskCoeff G n := by
  have hnhds : Metric.ball (0:ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds _ (by norm_num)
  have heq : F =ᶠ[𝓝 (0:ℂ)] G := by
    filter_upwards [hnhds] with z hz using h z hz
  rw [diskCoeff, diskCoeff, heq.iteratedDeriv_eq]

/-- Two `H²` elements with the same analytic function on the disk are equal. -/
theorem hardyDisk_ext {a b : HardyDisk}
    (h : ∀ z : ℂ, ‖z‖ < 1 → hardyFun a z = hardyFun b z) : a = b := by
  refine lp.ext (funext fun n => ?_)
  have ha := diskCoeff_hardyFun a n
  have hb := diskCoeff_hardyFun b n
  have hc : diskCoeff (hardyFun a) n = diskCoeff (hardyFun b) n := by
    refine diskCoeff_congr (fun z hz => ?_) n
    exact h z (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  rw [← ha, ← hb, hc]

/-! ## Bounded analytic multipliers -/

/-- A bounded analytic function on the open unit disk. -/
structure DiskMultiplier where
  fn : ℂ → ℂ
  diff : DifferentiableOn ℂ fn (Metric.ball 0 1)
  bd : ℝ
  bd_nonneg : 0 ≤ bd
  bd_le : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖fn z‖ ≤ bd

theorem continuousOn_circle_of_ball {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (fun θ : ℝ => g (circleMap 0 r θ)) (Set.Icc 0 (2 * π)) := by
  refine hg.continuousOn.comp (continuous_circleMap 0 r).continuousOn (fun θ _ => ?_)
  rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
  exact hr1

theorem intervalIntegrable_normSq_circle {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntervalIntegrable (fun θ : ℝ => ‖g (circleMap 0 r θ)‖ ^ 2) MeasureTheory.volume 0 (2 * π) := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ 2 * π)]
  exact ((continuousOn_circle_of_ball hg hr0 hr1).norm).pow 2

theorem circleAverage_mul_le (φ : DiskMultiplier) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖φ.fn (circleMap 0 r θ) * f (circleMap 0 r θ)‖ ^ 2
      ≤ φ.bd ^ 2 * ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) := by
  have hπ : (0:ℝ) < 2 * π := by positivity
  have hmul : DifferentiableOn ℂ (fun z => φ.fn z * f z) (Metric.ball 0 1) := φ.diff.mul hf
  have hint1 := intervalIntegrable_normSq_circle hmul hr0 hr1
  have hint2 := (intervalIntegrable_normSq_circle hf hr0 hr1).const_mul (φ.bd ^ 2)
  have hpt : ∀ θ ∈ Set.Icc (0:ℝ) (2 * π),
      ‖φ.fn (circleMap 0 r θ) * f (circleMap 0 r θ)‖ ^ 2
        ≤ φ.bd ^ 2 * ‖f (circleMap 0 r θ)‖ ^ 2 := by
    intro θ _
    have hz : circleMap 0 r θ ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
      exact hr1
    have hb := φ.bd_le _ hz
    rw [norm_mul, mul_pow]
    have h1 : ‖φ.fn (circleMap 0 r θ)‖ ^ 2 ≤ φ.bd ^ 2 := by
      have := norm_nonneg (φ.fn (circleMap 0 r θ))
      nlinarith [hb, φ.bd_nonneg]
    nlinarith [h1, sq_nonneg ‖f (circleMap 0 r θ)‖]
  have hmono := intervalIntegral.integral_mono_on (le_of_lt hπ) hint1 hint2 hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have hinv : (0:ℝ) ≤ (2 * π)⁻¹ := by positivity
  calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖φ.fn (circleMap 0 r θ) * f (circleMap 0 r θ)‖ ^ 2
      ≤ (2 * π)⁻¹ * (φ.bd ^ 2 * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono hinv
    _ = φ.bd ^ 2 * ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) := by ring

/-- The coefficient sequence of `φ · f`. -/
def hardyMulCoeff (φ : DiskMultiplier) (a : HardyDisk) : ℕ → ℂ :=
  diskCoeff (fun z => φ.fn z * hardyFun a z)

theorem hardyMulCoeff_bound (φ : DiskMultiplier) (a : HardyDisk) :
    Summable (fun n => ‖hardyMulCoeff φ a n‖ ^ 2) ∧
      ∑' n, ‖hardyMulCoeff φ a n‖ ^ 2 ≤ φ.bd ^ 2 * ‖a‖ ^ 2 := by
  have hmul : DifferentiableOn ℂ (fun z => φ.fn z * hardyFun a z) (Metric.ball 0 1) :=
    φ.diff.mul (differentiableOn_hardyFun a)
  refine summable_diskCoeff_sq_of_circleAverage_le hmul (r₀ := 0) le_rfl (by norm_num)
    (fun r hr0 hr1 => ?_)
  refine le_trans (circleAverage_mul_le φ (differentiableOn_hardyFun a) hr0 hr1) ?_
  have hb := circleAverage_hardyFun_le a hr0 hr1
  have hsq : (0:ℝ) ≤ φ.bd ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hb hsq

theorem memlp_hardyMulCoeff (φ : DiskMultiplier) (a : HardyDisk) :
    Memℓp (hardyMulCoeff φ a) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine ((hardyMulCoeff_bound φ a).1).congr fun n => ?_
  rw [← Real.rpow_natCast ‖hardyMulCoeff φ a n‖ 2]
  norm_num

/-! ## The multiplication operator -/

theorem hardyMulCoeff_add (φ : DiskMultiplier) (a b : HardyDisk) :
    hardyMulCoeff φ (a + b) = hardyMulCoeff φ a + hardyMulCoeff φ b := by
  funext n
  have hda : DifferentiableOn ℂ (fun z => φ.fn z * hardyFun a z) (Metric.ball 0 1) :=
    φ.diff.mul (differentiableOn_hardyFun a)
  have hdb : DifferentiableOn ℂ (fun z => φ.fn z * hardyFun b z) (Metric.ball 0 1) :=
    φ.diff.mul (differentiableOn_hardyFun b)
  have hcong : diskCoeff (fun z => φ.fn z * hardyFun (a + b) z) n
      = diskCoeff (fun z => φ.fn z * hardyFun a z + φ.fn z * hardyFun b z) n := by
    refine diskCoeff_congr (fun z hz => ?_) n
    have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    rw [hardyFun_add a b hz', mul_add]
  rw [hardyMulCoeff, hcong, diskCoeff_add hda hdb]
  rfl

theorem hardyMulCoeff_smul (φ : DiskMultiplier) (c : ℂ) (a : HardyDisk) :
    hardyMulCoeff φ (c • a) = c • hardyMulCoeff φ a := by
  funext n
  have hda : DifferentiableOn ℂ (fun z => φ.fn z * hardyFun a z) (Metric.ball 0 1) :=
    φ.diff.mul (differentiableOn_hardyFun a)
  have hcong : diskCoeff (fun z => φ.fn z * hardyFun (c • a) z) n
      = diskCoeff (fun z => c * (φ.fn z * hardyFun a z)) n := by
    refine diskCoeff_congr (fun z hz => ?_) n
    have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    rw [hardyFun_smul c a hz']
    ring
  rw [hardyMulCoeff, hcong, diskCoeff_smul hda c]
  rfl

/-- **The multiplication operator `M_φ` on `H²(D)`,** of norm at most the sup bound of `φ`. -/
def hardyMul (φ : DiskMultiplier) : HardyDisk →L[ℂ] HardyDisk :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨hardyMulCoeff φ a, memlp_hardyMulCoeff φ a⟩
      map_add' := fun a b => lp.ext (by
        change hardyMulCoeff φ (a + b) = _
        rw [hardyMulCoeff_add]
        rfl)
      map_smul' := fun c a => lp.ext (by
        change hardyMulCoeff φ (c • a) = _
        rw [hardyMulCoeff_smul]
        rfl) }
    φ.bd (fun a => by
      show ‖(⟨hardyMulCoeff φ a, memlp_hardyMulCoeff φ a⟩ : HardyDisk)‖ ≤ φ.bd * ‖a‖
      have hnorm : ‖(⟨hardyMulCoeff φ a, memlp_hardyMulCoeff φ a⟩ : HardyDisk)‖ ^ 2
          ≤ (φ.bd * ‖a‖) ^ 2 := by
        rw [hardyDisk_norm_sq, mul_pow]
        exact (hardyMulCoeff_bound φ a).2
      have h1 : (0:ℝ) ≤ ‖(⟨hardyMulCoeff φ a, memlp_hardyMulCoeff φ a⟩ : HardyDisk)‖ :=
        norm_nonneg _
      have h2 : (0:ℝ) ≤ φ.bd * ‖a‖ := mul_nonneg φ.bd_nonneg (norm_nonneg _)
      nlinarith [hnorm, h1, h2])

@[simp] theorem hardyMul_apply_coeff (φ : DiskMultiplier) (a : HardyDisk) (n : ℕ) :
    (hardyMul φ a) n = hardyMulCoeff φ a n := rfl

theorem hardyFun_hardyMul (φ : DiskMultiplier) (a : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    hardyFun (hardyMul φ a) z = φ.fn z * hardyFun a z := by
  have hmul : DifferentiableOn ℂ (fun w => φ.fn w * hardyFun a w) (Metric.ball 0 1) :=
    φ.diff.mul (differentiableOn_hardyFun a)
  exact hardyFun_of_diskCoeff hmul (memlp_hardyMulCoeff φ a) hz

/-! ## The multiplier algebra -/

/-- Product of two bounded analytic multipliers. -/
def DiskMultiplier.mul (φ ψ : DiskMultiplier) : DiskMultiplier where
  fn := fun z => φ.fn z * ψ.fn z
  diff := φ.diff.mul ψ.diff
  bd := φ.bd * ψ.bd
  bd_nonneg := mul_nonneg φ.bd_nonneg ψ.bd_nonneg
  bd_le := fun z hz => by
    rw [norm_mul]
    exact mul_le_mul (φ.bd_le z hz) (ψ.bd_le z hz) (norm_nonneg _) φ.bd_nonneg

/-- The constant multiplier `1`. -/
def DiskMultiplier.one : DiskMultiplier where
  fn := fun _ => 1
  diff := differentiableOn_const 1
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := fun _ _ => by simp

/-- Multiplication by the coordinate: the unilateral shift. -/
def diskShift : DiskMultiplier where
  fn := fun z => z
  diff := differentiableOn_id
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := fun z hz => by
    have hlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    exact le_of_lt hlt

theorem hardyMul_congr {φ ψ : DiskMultiplier}
    (h : ∀ z ∈ Metric.ball (0:ℂ) 1, φ.fn z = ψ.fn z) (a : HardyDisk) :
    hardyMul φ a = hardyMul ψ a := by
  refine hardyDisk_ext fun z hz => ?_
  have hz' : z ∈ Metric.ball (0:ℂ) 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  rw [hardyFun_hardyMul φ a hz, hardyFun_hardyMul ψ a hz, h z hz']

theorem hardyMul_mul (φ ψ : DiskMultiplier) (a : HardyDisk) :
    hardyMul φ (hardyMul ψ a) = hardyMul (φ.mul ψ) a := by
  refine hardyDisk_ext fun z hz => ?_
  rw [hardyFun_hardyMul φ _ hz, hardyFun_hardyMul ψ a hz, hardyFun_hardyMul (φ.mul ψ) a hz]
  show _ = φ.fn z * ψ.fn z * hardyFun a z
  ring

theorem hardyMul_one (a : HardyDisk) : hardyMul DiskMultiplier.one a = a := by
  refine hardyDisk_ext fun z hz => ?_
  rw [hardyFun_hardyMul DiskMultiplier.one a hz]
  show (1 : ℂ) * hardyFun a z = hardyFun a z
  ring

theorem hardyMul_comm (φ ψ : DiskMultiplier) (a : HardyDisk) :
    hardyMul φ (hardyMul ψ a) = hardyMul ψ (hardyMul φ a) := by
  rw [hardyMul_mul, hardyMul_mul]
  refine hardyMul_congr (fun z _ => ?_) a
  show φ.fn z * ψ.fn z = ψ.fn z * φ.fn z
  ring

end GaloisForLFunctions.HTGeometry
