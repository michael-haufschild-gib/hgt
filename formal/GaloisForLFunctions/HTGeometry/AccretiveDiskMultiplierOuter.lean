import GaloisForLFunctions.HTGeometry.DiskMultiplierAlgebra
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryQuotient

open Complex MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive reciprocal scale used to approximate an accretive multiplier by invertibles. -/
def accretiveEpsilon (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem accretiveEpsilon_pos (n : ℕ) : 0 < accretiveEpsilon n := by
  rw [accretiveEpsilon]
  positivity

theorem tendsto_accretiveEpsilon :
    Tendsto accretiveEpsilon atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0)
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simpa [accretiveEpsilon, one_div] using
    (Tendsto.div_atTop (𝕜 := ℝ) (f := fun _ : ℕ => 1)
      (g := fun n : ℕ => (n : ℝ) + 1) tendsto_const_nhds htop)

theorem norm_le_norm_add_posReal {a : ℂ} {ε : ℝ}
    (ha : 0 ≤ a.re) (hε : 0 ≤ ε) :
    ‖a‖ ≤ ‖a + (ε : ℂ)‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, add_zero]
  nlinarith

/-- Adding a positive real constant to an accretive multiplier gives a uniform lower bound. -/
theorem accretive_add_epsilon_lower
    (φ : DiskMultiplier)
    (hacc : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (φ.fn z).re)
    (n : ℕ) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    accretiveEpsilon n ≤
      ‖(φ.add (DiskMultiplier.const (accretiveEpsilon n))).fn z‖ := by
  have hre : accretiveEpsilon n ≤
      ((φ.add (DiskMultiplier.const (accretiveEpsilon n))).fn z).re := by
    simp only [DiskMultiplier.add_fn, DiskMultiplier.const_fn, Complex.add_re,
      Complex.ofReal_re]
    linarith [hacc z hz]
  exact hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))

/-- Bounded reciprocal of `φ + ε_n`. -/
def accretiveApproxInverse
    (φ : DiskMultiplier)
    (hacc : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (φ.fn z).re)
    (n : ℕ) : DiskMultiplier :=
  (φ.add (DiskMultiplier.const (accretiveEpsilon n))).invOfLowerBound
    (accretiveEpsilon n) (accretiveEpsilon_pos n)
    (accretive_add_epsilon_lower φ hacc n)

/-- Range approximant `φ/(φ+ε_n)`. -/
def accretiveRangeApprox
    (φ : DiskMultiplier)
    (hacc : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (φ.fn z).re)
    (n : ℕ) : DiskMultiplier :=
  φ.mul (accretiveApproxInverse φ hacc n)

theorem norm_accretiveRangeApprox_fn_le_one
    (φ : DiskMultiplier)
    (hacc : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (φ.fn z).re)
    (n : ℕ) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖(accretiveRangeApprox φ hacc n).fn z‖ ≤ 1 := by
  let ε := accretiveEpsilon n
  have hε : 0 < ε := accretiveEpsilon_pos n
  have hden : φ.fn z + (ε : ℂ) ≠ 0 := by
    apply norm_pos_iff.mp
    exact hε.trans_le (accretive_add_epsilon_lower φ hacc n z hz)
  change ‖φ.fn z * (φ.fn z + (ε : ℂ))⁻¹‖ ≤ 1
  rw [norm_mul, norm_inv, ← div_eq_mul_inv]
  exact (div_le_one (norm_pos_iff.mpr hden)).2
    (norm_le_norm_add_posReal (hacc z hz) hε.le)

/-- Safe everywhere representative of the boundary ratio `a/(a+ε_n)`. -/
def accretiveBoundaryApprox (n : ℕ) (a : ℂ) : ℂ :=
  if 0 ≤ a.re then a / (a + (accretiveEpsilon n : ℂ)) else 0

/-- Pointwise limit of the safe accretive ratios. It equals one at every nonzero accretive point. -/
def accretiveBoundaryLimit (a : ℂ) : ℂ :=
  if 0 ≤ a.re ∧ a ≠ 0 then 1 else 0

theorem measurable_accretiveBoundaryApprox (n : ℕ) :
    Measurable (accretiveBoundaryApprox n) := by
  unfold accretiveBoundaryApprox
  apply Measurable.ite
  · exact measurableSet_le measurable_const Complex.measurable_re
  · exact measurable_id.div (measurable_id.add measurable_const)
  · exact measurable_const

theorem measurable_accretiveBoundaryLimit :
    Measurable accretiveBoundaryLimit := by
  change Measurable (fun a : ℂ => if 0 ≤ a.re ∧ a ≠ 0 then 1 else 0)
  apply Measurable.ite
  · exact (measurableSet_le measurable_const Complex.measurable_re).inter
      (measurableSet_singleton 0).compl
  · exact measurable_const
  · exact measurable_const

theorem norm_accretiveBoundaryApprox_le_one (n : ℕ) (a : ℂ) :
    ‖accretiveBoundaryApprox n a‖ ≤ 1 := by
  rw [accretiveBoundaryApprox]
  split_ifs with ha
  · have hε := accretiveEpsilon_pos n
    have hden : a + (accretiveEpsilon n : ℂ) ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hden)).2
      (norm_le_norm_add_posReal ha hε.le)
  · simp

theorem norm_accretiveBoundaryLimit_le_one (a : ℂ) :
    ‖accretiveBoundaryLimit a‖ ≤ 1 := by
  rw [accretiveBoundaryLimit]
  split_ifs <;> simp

theorem tendsto_accretiveBoundaryApprox (a : ℂ) :
    Tendsto (fun n => accretiveBoundaryApprox n a) atTop
      (𝓝 (accretiveBoundaryLimit a)) := by
  unfold accretiveBoundaryApprox accretiveBoundaryLimit
  by_cases hre : 0 ≤ a.re
  · by_cases ha : a = 0
    · subst a
      simp
    · have hden : Tendsto (fun n => a + (accretiveEpsilon n : ℂ)) atTop (𝓝 a) := by
        simpa using tendsto_const_nhds.add
          (Complex.continuous_ofReal.tendsto 0 |>.comp tendsto_accretiveEpsilon)
      have hnum : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
      have hquot := hnum.div hden ha
      change Tendsto (fun n => a / (a + (accretiveEpsilon n : ℂ)))
        atTop (𝓝 (a / a)) at hquot
      simpa [hre, ha, div_self ha] using hquot
  · simp [hre]

theorem ae_re_diskMultiplierBoundaryFun_nonneg
    (φ : DiskMultiplier)
    (hacc : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (φ.fn z).re) :
    ∀ᵐ z ∂circleLebesgue, 0 ≤ (diskMultiplierBoundaryFun φ z).re := by
  obtain ⟨ns, -, hae⟩ := exists_diskMultiplierRadialBoundary_subseq_ae φ
  filter_upwards [hae] with z hz
  have hre : Tendsto
      (fun i => (diskMultiplierRadialBoundaryFun (ns i) φ z).re)
      atTop (𝓝 (diskMultiplierBoundaryFun φ z).re) :=
    (Complex.continuous_re.tendsto _).comp hz
  apply isClosed_Ici.mem_of_tendsto hre
  filter_upwards with i
  apply hacc
  rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_real,
    Real.norm_eq_abs, abs_of_nonneg (hardyDiskAbelRadius_nonneg (ns i)),
    Circle.norm_coe, mul_one]
  exact hardyDiskAbelRadius_lt_one (ns i)

theorem diskMultiplierBoundaryFun_accretiveRangeApprox_ae
    (φ : DiskMultiplier)
    (hacc : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (φ.fn z).re)
    (n : ℕ) :
    diskMultiplierBoundaryFun (accretiveRangeApprox φ hacc n) =ᵐ[circleLebesgue]
      fun z => accretiveBoundaryApprox n (diskMultiplierBoundaryMeasurableRep φ z) := by
  filter_upwards [diskMultiplierBoundaryFun_mul_ae φ
      (accretiveApproxInverse φ hacc n),
    diskMultiplierBoundaryFun_invOfLowerBound_ae
      (φ.add (DiskMultiplier.const (accretiveEpsilon n : ℂ)))
      (accretiveEpsilon n) (accretiveEpsilon_pos n)
      (accretive_add_epsilon_lower φ hacc n),
    diskMultiplierBoundaryFun_add_ae φ
      (DiskMultiplier.const (accretiveEpsilon n : ℂ)),
    diskMultiplierBoundaryFun_const_ae (accretiveEpsilon n : ℂ),
    diskMultiplierBoundaryMeasurableRep_ae φ,
    ae_re_diskMultiplierBoundaryFun_nonneg φ hacc]
      with z hmul hinv hadd hconst hrep hre
  change diskMultiplierBoundaryFun (accretiveApproxInverse φ hacc n) z = _ at hinv
  change diskMultiplierBoundaryFun
      (φ.mul (accretiveApproxInverse φ hacc n)) z = _
  rw [hmul, hinv]
  rw [hadd, hconst, hrep]
  simp only [accretiveBoundaryApprox, if_pos hre, div_eq_mul_inv]

theorem ae_accretiveBoundaryLimit_eq_one
    (φ : DiskMultiplier)
    (hacc : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (φ.fn z).re)
    (hne : ∃ z ∈ Metric.ball (0 : ℂ) 1, φ.fn z ≠ 0) :
    (fun z => accretiveBoundaryLimit (diskMultiplierBoundaryMeasurableRep φ z))
      =ᵐ[circleLebesgue] fun _ => 1 := by
  filter_upwards [diskMultiplierBoundaryMeasurableRep_ae φ,
    ae_re_diskMultiplierBoundaryFun_nonneg φ hacc,
    diskMultiplierBoundary_ne_zero_ae φ hne] with z hrep hre hz
  rw [hrep, accretiveBoundaryLimit, if_pos ⟨hre, hz⟩]

theorem tendsto_hardyMul_accretiveRangeApprox
    (φ : DiskMultiplier)
    (hacc : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (φ.fn z).re)
    (hne : ∃ z ∈ Metric.ball (0 : ℂ) 1, φ.fn z ≠ 0)
    (f : HardyDisk) :
    Tendsto (fun n => hardyMul (accretiveRangeApprox φ hacc n) f)
      atTop (𝓝 f) := by
  let a : Circle → ℂ := diskMultiplierBoundaryMeasurableRep φ
  let q : ℕ → Circle → ℂ := fun n z => accretiveBoundaryApprox n (a z)
  let qLimit : Circle → ℂ := fun z => accretiveBoundaryLimit (a z)
  have hqmeas : ∀ n, Measurable (q n) := by
    intro n
    change Measurable (fun z => accretiveBoundaryApprox n (a z))
    exact (measurable_accretiveBoundaryApprox n).comp
      (measurable_diskMultiplierBoundaryMeasurableRep φ)
  have hqLimitMeas : Measurable qLimit := by
    change Measurable (fun z => accretiveBoundaryLimit (a z))
    exact measurable_accretiveBoundaryLimit.comp
      (measurable_diskMultiplierBoundaryMeasurableRep φ)
  have hqbd : ∀ n z, ‖q n z‖ ≤ 1 := fun n z =>
    norm_accretiveBoundaryApprox_le_one n (a z)
  have hqLimitBd : ∀ z, ‖qLimit z‖ ≤ 1 := fun z =>
    norm_accretiveBoundaryLimit_le_one (a z)
  have hqpt : ∀ z, Tendsto (fun n => q n z) atTop (𝓝 (qLimit z)) := fun z =>
    tendsto_accretiveBoundaryApprox (a z)
  have hmul := tendsto_lpBoundedMulCLM_apply hqmeas hqLimitMeas zero_le_one
    hqbd hqLimitBd hqpt (hardyDiskBoundary f)
  have hleft : ∀ n,
      lpBoundedMulCLM (p := 2) (μ := circleLebesgue) (hqmeas n) zero_le_one
          (hqbd n) (hardyDiskBoundary f) =
        hardyDiskBoundary (hardyMul (accretiveRangeApprox φ hacc n) f) := by
    intro n
    rw [← diskMultiplierBoundaryMul_apply]
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := circleLebesgue)
        (hqmeas n) zero_le_one (hqbd n) (hardyDiskBoundary f),
      diskMultiplierBoundaryMul_coeFn (accretiveRangeApprox φ hacc n)
        (hardyDiskBoundary f),
      diskMultiplierBoundaryFun_accretiveRangeApprox_ae φ hacc n]
        with z hq hχ hboundary
    rw [hq, hχ, hboundary]
  have hright :
      lpBoundedMulCLM (p := 2) (μ := circleLebesgue) hqLimitMeas zero_le_one
          hqLimitBd (hardyDiskBoundary f) = hardyDiskBoundary f := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := circleLebesgue)
        hqLimitMeas zero_le_one hqLimitBd (hardyDiskBoundary f),
      ae_accretiveBoundaryLimit_eq_one φ hacc hne] with z hmulz hone
    rw [hmulz]
    change accretiveBoundaryLimit (diskMultiplierBoundaryMeasurableRep φ z) * _ = _
    rw [hone, one_mul]
  rw [show (fun n => lpBoundedMulCLM (p := 2) (μ := circleLebesgue)
      (hqmeas n) zero_le_one (hqbd n) (hardyDiskBoundary f)) =
      fun n => hardyDiskBoundary (hardyMul (accretiveRangeApprox φ hacc n) f) by
        funext n; exact hleft n,
    hright] at hmul
  rw [Metric.tendsto_atTop] at hmul ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hmul ε hε
  exact ⟨N, fun n hn => by
    have hb := hN n hn
    simpa only [dist_eq_norm, ← hardyDiskBoundary.norm_map,
      map_sub] using hb⟩

/-- Every nonzero accretive bounded analytic multiplier is outer. -/
theorem isOuterDiskMultiplier_of_re_nonneg
    (φ : DiskMultiplier)
    (hacc : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (φ.fn z).re)
    (hne : ∃ z ∈ Metric.ball (0 : ℂ) 1, φ.fn z ≠ 0) :
    IsOuterDiskMultiplier φ := by
  rw [isOuterDiskMultiplier_iff_denseRange, denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro f _
  apply isClosed_closure.mem_of_tendsto
    (tendsto_hardyMul_accretiveRangeApprox φ hacc hne f)
  filter_upwards with n
  apply subset_closure
  refine ⟨hardyMul (accretiveApproxInverse φ hacc n) f, ?_⟩
  exact hardyMul_mul φ (accretiveApproxInverse φ hacc n) f

/-- Strictly accretive bounded analytic multipliers are outer. -/
theorem isOuterDiskMultiplier_of_re_pos
    (φ : DiskMultiplier)
    (hacc : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (φ.fn z).re) :
    IsOuterDiskMultiplier φ := by
  apply isOuterDiskMultiplier_of_re_nonneg φ (fun z hz => (hacc z hz).le)
  exact ⟨0, Metric.mem_ball_self zero_lt_one,
    fun hzero => by
      have hre := congrArg Complex.re hzero
      simp at hre
      exact (ne_of_gt (hacc 0 (Metric.mem_ball_self zero_lt_one))) hre⟩

end

end GaloisForLFunctions.HTGeometry
