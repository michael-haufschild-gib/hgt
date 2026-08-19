import GaloisForLFunctions.HTGeometry.HardyDiskBlaschke

/-!
# The range of a Blaschke multiplication and its model space

`hardy-cyclicity-maximal-ht-field-blindness`, equation `(16)` and the codimension statement.

The reproducing kernel of `H²(D)` at a point `a` of the disk is the geometric coefficient sequence
`k_a(n) = conj(a)ⁿ`, and `⟪k_a, x⟫ = (hardyFun x)(a)`.  For a single Blaschke factor,

```text
range M_{b_a} = { x : (hardyFun x)(a) = 0 } = (ℂ ∙ k_a)ᗮ,
```

so the model space `H² ⊖ b_a H²` is the line `ℂ ∙ k_a`.  Multiplication by a finite Blaschke
product is an isometry, hence a closed embedding, so cyclic subspaces transport:
`[B·O] = B·[O] = B·H²`.
-/

open Complex Filter Metric Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The reproducing kernel -/

/-- The coefficient sequence of the Szegő kernel at `a`. -/
def hardyKernelCoeff (a : ℂ) : ℕ → ℂ := fun n => ((starRingEnd ℂ) a) ^ n

theorem memlp_hardyKernel {a : ℂ} (ha : ‖a‖ < 1) : Memℓp (hardyKernelCoeff a) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hsum : Summable (fun n : ℕ => (‖a‖ ^ 2) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith [norm_nonneg a])
  refine hsum.congr fun n => ?_
  rw [hardyKernelCoeff, norm_pow, RCLike.norm_conj]
  rw [show ((2 : ENNReal).toReal) = ((2:ℕ) : ℝ) by norm_num,
    Real.rpow_natCast (‖a‖ ^ n) 2]
  ring

/-- The Szegő reproducing kernel at `a`, as an element of `H²(D)`. -/
def hardyKernel {a : ℂ} (ha : ‖a‖ < 1) : HardyDisk := ⟨hardyKernelCoeff a, memlp_hardyKernel ha⟩

theorem hardyKernel_ne_zero {a : ℂ} (ha : ‖a‖ < 1) : hardyKernel ha ≠ 0 := by
  intro h
  have h0 : (hardyKernel ha) 0 = 0 := by rw [h]; rfl
  rw [show (hardyKernel ha) 0 = hardyKernelCoeff a 0 from rfl, hardyKernelCoeff, pow_zero] at h0
  exact one_ne_zero h0

/-- **The reproducing property.** -/
theorem inner_hardyKernel {a : ℂ} (ha : ‖a‖ < 1) (x : HardyDisk) :
    (inner ℂ (hardyKernel ha) x : ℂ) = hardyFun x a := by
  rw [lp.inner_eq_tsum, hardyFun]
  refine tsum_congr fun n => ?_
  rw [RCLike.inner_apply,
    show (hardyKernel ha) n = hardyKernelCoeff a n from rfl, hardyKernelCoeff, ← map_pow,
    Complex.conj_conj]

theorem mem_orthogonal_kernel_iff {a : ℂ} (ha : ‖a‖ < 1) (x : HardyDisk) :
    x ∈ (ℂ ∙ hardyKernel ha)ᗮ ↔ hardyFun x a = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  constructor
  · intro h
    have h2 : (inner ℂ (hardyKernel ha) x : ℂ) = 0 := by
      rw [← inner_conj_symm, h, map_zero]
    rwa [inner_hardyKernel ha x] at h2
  · intro h
    have h2 : (inner ℂ (hardyKernel ha) x : ℂ) = 0 := by rw [inner_hardyKernel ha x, h]
    rw [← inner_conj_symm, h2, map_zero]

/-! ## The single Blaschke factor -/

/-- One Blaschke factor as finite Blaschke data. -/
def singleBlaschke {a : ℂ} (ha : ‖a‖ < 1) : FiniteBlaschke where
  deg := 1
  zeros := fun _ => a
  bound := ‖a‖
  bound_nonneg := norm_nonneg a
  bound_lt := ha
  zeros_le := fun _ => le_rfl

theorem singleBlaschke_fn {a : ℂ} (ha : ‖a‖ < 1) (z : ℂ) :
    (singleBlaschke ha).fn z = blaschkeFactor a z := by
  rw [FiniteBlaschke.fn, blaschkeProd]
  simp [singleBlaschke]

theorem blaschkeFactor_self {a : ℂ} (ha : ‖a‖ < 1) : blaschkeFactor a a = 0 := by
  rw [blaschkeFactor, sub_self, zero_div]

/-! ## The range of a single Blaschke multiplication -/

theorem hardyFun_eq_zero_of_mem_range {a : ℂ} (ha : ‖a‖ < 1) {x : HardyDisk}
    (hx : x ∈ LinearMap.range ((hardyMul (singleBlaschke ha).toMultiplier :
      HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk)) :
    hardyFun x a = 0 := by
  obtain ⟨y, rfl⟩ := hx
  have h := hardyFun_hardyMul (singleBlaschke ha).toMultiplier y (z := a) ha
  rw [show ((hardyMul (singleBlaschke ha).toMultiplier :
      HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) y
      = hardyMul (singleBlaschke ha).toMultiplier y from rfl, h]
  show (singleBlaschke ha).fn a * hardyFun y a = 0
  rw [singleBlaschke_fn, blaschkeFactor_self ha, zero_mul]

theorem mem_range_of_hardyFun_eq_zero {a : ℂ} (ha : ‖a‖ < 1) {x : HardyDisk}
    (hx : hardyFun x a = 0) :
    x ∈ LinearMap.range ((hardyMul (singleBlaschke ha).toMultiplier :
      HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) := by
  classical
  have hane : ‖a‖ < 1 := ha
  have hamem : a ∈ Metric.ball (0:ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using ha
  have hball : Metric.ball (0:ℂ) 1 ∈ 𝓝 a := Metric.isOpen_ball.mem_nhds hamem
  set f : ℂ → ℂ := hardyFun x with hf
  have hfdiff : DifferentiableOn ℂ f (Metric.ball 0 1) := differentiableOn_hardyFun x
  have hd : DifferentiableOn ℂ (dslope f a) (Metric.ball 0 1) :=
    (differentiableOn_dslope hball).mpr hfdiff
  set g : ℂ → ℂ := fun z => dslope f a z * (1 - (starRingEnd ℂ) a * z) with hg
  have hgdiff : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    refine hd.mul ?_
    fun_prop
  -- pointwise factorization
  have hkey : ∀ z ∈ Metric.ball (0:ℂ) 1, blaschkeFactor a z * g z = f z := by
    intro z hz
    have hzn : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 := by
      refine blaschke_denom_ne_zero ?_
      nlinarith [norm_nonneg a, norm_nonneg z, hzn, ha]
    by_cases hza : z = a
    · subst hza
      rw [blaschkeFactor_self ha, zero_mul]
      exact hx.symm
    · have hne : z ≠ a := hza
      have hzsub : z - a ≠ 0 := sub_ne_zero.mpr hne
      have hds : dslope f a z = (z - a)⁻¹ * f z := by
        rw [dslope_of_ne f hne, slope_def_field, hx, sub_zero, div_eq_inv_mul]
      rw [hg]
      simp only
      have hden' : (1 : ℂ) - z * (starRingEnd ℂ) a ≠ 0 := by
        rw [mul_comm]; exact hden
      rw [hds, blaschkeFactor]
      field_simp
  -- the quotient is in `H²`
  set r₀ : ℝ := (1 + ‖a‖) / 2 with hr₀
  have hr₀0 : 0 ≤ r₀ := by rw [hr₀]; positivity
  have hr₀1 : r₀ < 1 := by rw [hr₀]; linarith
  have hr₀a : ‖a‖ < r₀ := by rw [hr₀]; linarith
  set C : ℝ := 4 / (1 - ‖a‖) with hC
  have hCpos : 0 < C := by rw [hC]; have := norm_nonneg a; positivity
  have hbound : ∀ r : ℝ, r₀ ≤ r → r < 1 →
      (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖g (circleMap 0 r θ)‖ ^ 2
        ≤ C ^ 2 * ‖x‖ ^ 2 := by
    intro r hr hr1
    have hr0 : 0 ≤ r := le_trans hr₀0 hr
    have hpt : ∀ θ ∈ Set.Icc (0:ℝ) (2 * π),
        ‖g (circleMap 0 r θ)‖ ^ 2 ≤ C ^ 2 * ‖f (circleMap 0 r θ)‖ ^ 2 := by
      intro θ _
      set z : ℂ := circleMap 0 r θ with hz
      have hzn : ‖z‖ = r := by rw [hz, norm_circleMap_zero, abs_of_nonneg hr0]
      have hzne : z ≠ a := by
        intro h
        rw [h] at hzn
        linarith [hr₀a, hr]
      have hzsub : ‖z - a‖ ≥ r - ‖a‖ := by
        have := norm_sub_norm_le z a
        rw [hzn] at this
        linarith
      have hrpos : 0 < r - ‖a‖ := by linarith [hr₀a, hr]
      have hds : ‖dslope f a z‖ = ‖f z‖ / ‖z - a‖ := by
        rw [dslope_of_ne f hzne, slope_def_field, hx, sub_zero, norm_div]
      have hnum : ‖(1 : ℂ) - (starRingEnd ℂ) a * z‖ ≤ 2 := by
        have h1 : ‖(starRingEnd ℂ) a * z‖ = ‖a‖ * r := by
          rw [norm_mul, RCLike.norm_conj, hzn]
        have h2 : ‖(1 : ℂ) - (starRingEnd ℂ) a * z‖ ≤ 1 + ‖a‖ * r := by
          have := norm_sub_le (1 : ℂ) ((starRingEnd ℂ) a * z)
          rw [norm_one, h1] at this
          exact this
        nlinarith [h2, norm_nonneg a, hr1, hr0, ha]
      have hgz : ‖g z‖ ≤ C * ‖f z‖ := by
        rw [hg]
        simp only
        rw [norm_mul, hds]
        have hfz : (0:ℝ) ≤ ‖f z‖ := norm_nonneg _
        have hzs : (0:ℝ) < ‖z - a‖ := lt_of_lt_of_le hrpos hzsub
        have hstep : ‖f z‖ / ‖z - a‖ ≤ ‖f z‖ / (r - ‖a‖) :=
          div_le_div_of_nonneg_left hfz hrpos hzsub
        have hstep2 : ‖f z‖ / (r - ‖a‖) ≤ ‖f z‖ / ((1 - ‖a‖) / 2) := by
          refine div_le_div_of_nonneg_left hfz (by linarith) ?_
          rw [hr₀] at hr
          linarith
        have hC' : ‖f z‖ / ((1 - ‖a‖) / 2) * 2 = C * ‖f z‖ := by
          rw [hC]
          field_simp
          ring
        have hq : (0:ℝ) ≤ ‖f z‖ / ‖z - a‖ := div_nonneg hfz (le_of_lt hzs)
        calc ‖f z‖ / ‖z - a‖ * ‖1 - (starRingEnd ℂ) a * z‖
            ≤ ‖f z‖ / ‖z - a‖ * 2 := mul_le_mul_of_nonneg_left hnum hq
          _ ≤ ‖f z‖ / ((1 - ‖a‖) / 2) * 2 :=
              mul_le_mul_of_nonneg_right (le_trans hstep hstep2) (by norm_num)
          _ = C * ‖f z‖ := hC'
      have hgnn : (0:ℝ) ≤ ‖g z‖ := norm_nonneg _
      have hfnn : (0:ℝ) ≤ ‖f z‖ := norm_nonneg _
      nlinarith [hgz, hgnn, hfnn, hCpos.le]
    have hint1 := intervalIntegrable_normSq_circle hgdiff hr0 hr1
    have hint2 := (intervalIntegrable_normSq_circle hfdiff hr0 hr1).const_mul (C ^ 2)
    have hπ : (0:ℝ) < 2 * π := by positivity
    have hmono := intervalIntegral.integral_mono_on (le_of_lt hπ) hint1 hint2 hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    have hinv : (0:ℝ) ≤ (2 * π)⁻¹ := by positivity
    have hstep := mul_le_mul_of_nonneg_left hmono hinv
    have hfb := circleAverage_hardyFun_le x hr0 hr1
    have hC2 : (0:ℝ) ≤ C ^ 2 := by positivity
    calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖g (circleMap 0 r θ)‖ ^ 2
        ≤ (2 * π)⁻¹ * (C ^ 2 * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) := hstep
      _ = C ^ 2 * ((2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) := by ring
      _ ≤ C ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left hfb hC2
  obtain ⟨hsum, -⟩ := summable_diskCoeff_sq_of_circleAverage_le hgdiff hr₀0 hr₀1 hbound
  have hmem : Memℓp (diskCoeff g) 2 := by
    rw [memℓp_gen_iff (by norm_num)]
    refine hsum.congr fun n => ?_
    rw [← Real.rpow_natCast ‖diskCoeff g n‖ 2]
    norm_num
  refine ⟨⟨diskCoeff g, hmem⟩, ?_⟩
  show hardyMul (singleBlaschke ha).toMultiplier ⟨diskCoeff g, hmem⟩ = x
  refine hardyDisk_ext fun z hz => ?_
  have hzb : z ∈ Metric.ball (0:ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  rw [hardyFun_hardyMul _ _ hz, hardyFun_of_diskCoeff hgdiff hmem hz]
  show (singleBlaschke ha).fn z * g z = hardyFun x z
  rw [singleBlaschke_fn]
  exact hkey z hzb

/-- **The range of one Blaschke multiplication is the kernel of the point evaluation.** -/
theorem range_hardyMul_singleBlaschke {a : ℂ} (ha : ‖a‖ < 1) :
    LinearMap.range ((hardyMul (singleBlaschke ha).toMultiplier :
        HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk)
      = (ℂ ∙ hardyKernel ha)ᗮ := by
  ext x
  rw [mem_orthogonal_kernel_iff ha x]
  exact ⟨fun hx => hardyFun_eq_zero_of_mem_range ha hx,
    fun hx => mem_range_of_hardyFun_eq_zero ha hx⟩

/-- **The model space of a single Blaschke factor is a line.** -/
theorem finrank_orthogonal_range_singleBlaschke {a : ℂ} (ha : ‖a‖ < 1) :
    Module.finrank ℂ ((LinearMap.range ((hardyMul (singleBlaschke ha).toMultiplier :
      HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))ᗮ) = 1 := by
  rw [range_hardyMul_singleBlaschke ha]
  haveI : FiniteDimensional ℂ (ℂ ∙ hardyKernel ha) :=
    FiniteDimensional.span_singleton ℂ (hardyKernel ha)
  rw [Submodule.orthogonal_orthogonal]
  exact finrank_span_singleton (hardyKernel_ne_zero ha)

/-! ## Cyclic subspaces transport across a Blaschke isometry -/

theorem isometry_hardyMul_blaschke (B : FiniteBlaschke) :
    Isometry (hardyMul B.toMultiplier) :=
  AddMonoidHomClass.isometry_of_norm _ (fun x => norm_hardyMul_blaschke B x)

/-- **Equation (16).**  If `x` is a cyclic vector then the cyclic subspace of `B·x` is exactly
`B · H²(D)`. -/
theorem cyclicSubspace_blaschke_mul (B : FiniteBlaschke) {x : HardyDisk}
    (hx : cyclicSubspace x = ⊤) :
    cyclicSubspace (hardyMul B.toMultiplier x)
      = LinearMap.range ((hardyMul B.toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) := by
  have hemb : IsClosedEmbedding (hardyMul B.toMultiplier) :=
    (isometry_hardyMul_blaschke B).isClosedEmbedding
  have hclosureV : closure ((polyMultiples x : Submodule ℂ HardyDisk) : Set HardyDisk)
      = Set.univ := by
    have hc := hx
    rw [cyclicSubspace] at hc
    have hcoe := congrArg (fun W : Submodule ℂ HardyDisk => (W : Set HardyDisk)) hc
    rwa [Submodule.topologicalClosure_coe, Submodule.top_coe] at hcoe
  refine SetLike.ext' ?_
  rw [cyclicSubspace, polyMultiples_map, Submodule.topologicalClosure_coe, Submodule.map_coe]
  simp only [ContinuousLinearMap.coe_coe]
  rw [hemb.closure_image_eq, hclosureV, Set.image_univ]
  rfl

end GaloisForLFunctions.HTGeometry
