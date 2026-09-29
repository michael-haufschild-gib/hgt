import GaloisForLFunctions.HTGeometry.SzegoOuterCyclic
import GaloisForLFunctions.HTGeometry.OuterMultiplierUniqueness
import GaloisForLFunctions.HTGeometry.HardyBoundaryCayleyIdentification

/-!
# Szegő outer multipliers of bounded weights

For a measurable, positive, bounded, `2π`-periodic weight `w` whose logarithm is integrable, the
Szegő function `D_w = exp((1/4π) ∫ -H(e^{iθ}, ·) log w(θ) dθ)` is a bounded analytic multiplier:

* `|D_w(re^{iθ})|² → w(θ)` as `r → 1` for almost every `θ`, and the `L²` boundary of `D_w` has
  squared modulus `w` almost everywhere on the circle;
* `D_w(0) = exp((1/4π)∫₀^{2π} log w) > 0` and `D_w` has no zeros;
* `D_w` is outer, so multiplication by `D_w` on `H²` is injective with dense range;
* if `1/w` is not integrable, the range of multiplication by `D_w` is not closed;
* `D_w` is the unique outer multiplier with boundary modulus `√w` and positive value at `0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A bounded Szegő weight on the circle. -/
structure SzegoWeight where
  w : ℝ → ℝ
  meas : Measurable w
  pos : ∀ θ, 0 < w θ
  bound : ℝ
  le_bound : ∀ θ, w θ ≤ bound
  periodic : Function.Periodic w (2 * π)
  logInt : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π)

/-! ## Radial and circle boundary values -/

/-- A `2π`-periodic function is unchanged by reduction of the angle to `(-π, π]`. -/
theorem periodic_apply_arg_circleMap {L : ℝ → ℝ} (hL : Function.Periodic L (2 * π)) (t : ℝ) :
    L (Complex.arg (circleMap 0 1 t)) = L t := by
  rw [show circleMap 0 1 t = Complex.exp (t * Complex.I) by simp [circleMap],
    Complex.arg_exp_mul_I, ← self_sub_toIocDiv_zsmul, hL.sub_zsmul_eq]

/-- Radial limits of `‖φ‖²` determine the squared modulus of the `L²` boundary of `φ`. -/
theorem ae_norm_sq_diskMultiplierBoundaryFun_eq_of_radial (φ : DiskMultiplier) {L : ℝ → ℝ}
    (hLm : Measurable L) (hLper : Function.Periodic L (2 * π))
    (hrad : ∀ᵐ θ ∂volume, Tendsto (fun r => ‖φ.fn (circleMap 0 r θ)‖ ^ (2 : ℕ)) (𝓝[<] 1)
      (𝓝 (L θ))) :
    ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun φ z‖ ^ (2 : ℕ) = L (Complex.arg (z : ℂ)) := by
  obtain ⟨ns, hns, hboundary⟩ := exists_diskMultiplierRadialBoundary_subseq_ae φ
  have hscale : Measure.QuasiMeasurePreserving
      (fun a : ℝ => (2 * Real.pi) • a) volume volume :=
    Measure.quasiMeasurePreserving_smul volume
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hradScaled : ∀ᵐ a ∂volume,
      Tendsto (fun r => ‖φ.fn (circleMap 0 r ((2 * Real.pi) • a))‖ ^ (2 : ℕ)) (𝓝[<] 1)
        (𝓝 (L ((2 * Real.pi) • a))) :=
    hscale.ae hrad
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hvh : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  let circleHomeo := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hhomeo : MeasurePreserving circleHomeo volume circleLebesgue := by
    refine ⟨circleHomeo.continuous.measurable, ?_⟩
    rw [circleLebesgue, hvh]
  have hcircle : MeasurePreserving (circleHomeo ∘ QuotientAddGroup.mk)
      (volume.restrict (Set.Ioc (0 : ℝ) (0 + 1))) circleLebesgue :=
    hhomeo.comp (AddCircle.measurePreserving_mk (1 : ℝ) 0)
  have hboundaryPull : ∀ᵐ a ∂volume.restrict (Set.Ioc (0 : ℝ) (0 + 1)),
      Tendsto (fun i => diskMultiplierRadialBoundaryFun (ns i) φ
          (circleHomeo (QuotientAddGroup.mk a))) atTop
        (𝓝 (diskMultiplierBoundaryFun φ (circleHomeo (QuotientAddGroup.mk a)))) :=
    hcircle.quasiMeasurePreserving.ae hboundary
  have hrepPull : ∀ᵐ a ∂volume.restrict (Set.Ioc (0 : ℝ) (0 + 1)),
      diskMultiplierBoundaryMeasurableRep φ (circleHomeo (QuotientAddGroup.mk a)) =
        diskMultiplierBoundaryFun φ (circleHomeo (QuotientAddGroup.mk a)) :=
    hcircle.quasiMeasurePreserving.ae (diskMultiplierBoundaryMeasurableRep_ae φ)
  have hradPull : ∀ᵐ a ∂volume.restrict (Set.Ioc (0 : ℝ) (0 + 1)),
      Tendsto (fun r => ‖φ.fn (circleMap 0 r ((2 * Real.pi) • a))‖ ^ (2 : ℕ)) (𝓝[<] 1)
        (𝓝 (L ((2 * Real.pi) • a))) :=
    hradScaled.filter_mono (ae_mono Measure.restrict_le_self)
  have hang : ∀ a : ℝ, angularCircle ((2 * Real.pi) • a) =
      circleHomeo (QuotientAddGroup.mk a) := fun a => by
    simpa only [smul_eq_mul, circleHomeo, AddCircle.homeomorphCircle_apply] using
      angularCircle_two_pi_mul a
  have htarget : ∀ a : ℝ, L ((2 * Real.pi) • a)
      = L (Complex.arg ((circleHomeo (QuotientAddGroup.mk a) : Circle) : ℂ)) := fun a => by
    rw [← hang, coe_angularCircle, periodic_apply_arg_circleMap hLper]
  have hsource : ∀ᵐ a ∂volume.restrict (Set.Ioc (0 : ℝ) (0 + 1)),
      ‖diskMultiplierBoundaryMeasurableRep φ (circleHomeo (QuotientAddGroup.mk a))‖ ^ (2 : ℕ) =
        L (Complex.arg ((circleHomeo (QuotientAddGroup.mk a) : Circle) : ℂ)) := by
    filter_upwards [hboundaryPull, hrepPull, hradPull] with a hba hrep hsa
    have hradius : Tendsto (fun i => hardyDiskAbelRadius (ns i)) atTop (𝓝[<] (1 : ℝ)) :=
      tendsto_hardyDiskAbelRadius.comp hns.tendsto_atTop
    have hsseq := hsa.comp hradius
    have hbnorm : Tendsto
        (fun i => ‖diskMultiplierRadialBoundaryFun (ns i) φ
          (circleHomeo (QuotientAddGroup.mk a))‖ ^ (2 : ℕ)) atTop
        (𝓝 (‖diskMultiplierBoundaryFun φ (circleHomeo (QuotientAddGroup.mk a))‖ ^ (2 : ℕ))) :=
      ((continuous_norm.pow 2).tendsto _).comp hba
    have hsame : (fun i => ‖φ.fn (circleMap 0 (hardyDiskAbelRadius (ns i))
          ((2 * Real.pi) • a))‖ ^ (2 : ℕ)) =
        fun i => ‖diskMultiplierRadialBoundaryFun (ns i) φ
          (circleHomeo (QuotientAddGroup.mk a))‖ ^ (2 : ℕ) := by
      funext i
      rw [diskMultiplierRadialBoundaryFun, circleMap_eq_radius_mul_angularCircle, hang]
    change Tendsto (fun i => ‖φ.fn (circleMap 0 (hardyDiskAbelRadius (ns i))
        ((2 * Real.pi) • a))‖ ^ (2 : ℕ)) atTop (𝓝 (L ((2 * Real.pi) • a))) at hsseq
    rw [hsame] at hsseq
    have hlimit := tendsto_nhds_unique hbnorm hsseq
    rw [← hrep, htarget] at hlimit
    exact hlimit
  have hmeasSet : MeasurableSet {z : Circle |
      ‖diskMultiplierBoundaryMeasurableRep φ z‖ ^ (2 : ℕ) = L (Complex.arg (z : ℂ))} :=
    measurableSet_eq_fun ((measurable_diskMultiplierBoundaryMeasurableRep φ).norm.pow_const 2)
      (hLm.comp (Complex.measurable_arg.comp
        (show Measurable (fun z : Circle => (z : ℂ)) from Continuous.measurable (by fun_prop))))
  have hmeasMap : AEMeasurable (circleHomeo ∘ QuotientAddGroup.mk)
      (volume.restrict (Set.Ioc (0 : ℝ) (0 + 1))) :=
    hcircle.measurable.aemeasurable
  have hrepTarget : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryMeasurableRep φ z‖ ^ (2 : ℕ) = L (Complex.arg (z : ℂ)) := by
    rw [← hcircle.map_eq]
    exact (ae_map_iff hmeasMap hmeasSet).2 hsource
  filter_upwards [hrepTarget, diskMultiplierBoundaryMeasurableRep_ae φ] with z hz hrep
  rwa [hrep] at hz

/-- Circle-almost-everywhere statements pull back to almost every angle in `(0, 2π]`. -/
theorem ae_angularCircle_of_ae_circle {P : Circle → Prop} (hP : ∀ᵐ z ∂circleLebesgue, P z) :
    ∀ᵐ θ ∂volume, θ ∈ Set.Ioc 0 (2 * Real.pi) → P (angularCircle θ) := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hvh : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  let circleHomeo := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hhomeo : MeasurePreserving circleHomeo volume circleLebesgue := by
    refine ⟨circleHomeo.continuous.measurable, ?_⟩
    rw [circleLebesgue, hvh]
  have hcircle : MeasurePreserving (circleHomeo ∘ QuotientAddGroup.mk)
      (volume.restrict (Set.Ioc (0 : ℝ) (0 + 1))) circleLebesgue :=
    hhomeo.comp (AddCircle.measurePreserving_mk (1 : ℝ) 0)
  have hpull : ∀ᵐ a ∂volume, a ∈ Set.Ioc (0 : ℝ) 1 →
      P (circleHomeo (QuotientAddGroup.mk a)) := by
    have h := hcircle.quasiMeasurePreserving.ae hP
    rw [zero_add] at h
    exact (ae_restrict_iff' measurableSet_Ioc).mp h
  have hscale : Measure.QuasiMeasurePreserving
      (fun θ : ℝ => (2 * Real.pi)⁻¹ • θ) volume volume :=
    Measure.quasiMeasurePreserving_smul volume
      (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  filter_upwards [hscale.ae hpull] with θ hθ hmem
  have h2π : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have ha : (2 * Real.pi)⁻¹ • θ ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [smul_eq_mul]
    exact ⟨mul_pos (inv_pos.mpr h2π) hmem.1,
      by rw [inv_mul_le_iff₀ h2π, mul_one]; exact hmem.2⟩
  have heq : angularCircle θ = circleHomeo (QuotientAddGroup.mk ((2 * Real.pi)⁻¹ • θ)) := by
    have h := angularCircle_two_pi_mul ((2 * Real.pi)⁻¹ • θ)
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ h2π.ne', one_mul] at h
    rw [h]
    simp only [circleHomeo, AddCircle.homeomorphCircle_apply, smul_eq_mul]
  rw [heq]
  exact hθ ha

/-! ## The Szegő outer multiplier -/

namespace SzegoWeight

variable (W : SzegoWeight)

theorem bound_pos : 0 < W.bound := (W.pos 0).trans_le (W.le_bound 0)

theorem logPeriodic : Function.Periodic (fun θ => Real.log (W.w θ)) (2 * π) := fun θ => by
  simp only [W.periodic θ]

theorem logIntervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun θ => Real.log (W.w θ)) volume a b := by
  have hbase : IntervalIntegrable (fun θ => Real.log (W.w θ)) volume 0 (0 + 2 * π) := by
    simpa using W.logInt
  exact W.logPeriodic.intervalIntegrable Real.two_pi_pos.ne' hbase a b

theorem logLocallyIntegrable : LocallyIntegrable (fun θ => Real.log (W.w θ)) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hkR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hk.isBounded
  have hIcc := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by linarith [abs_nonneg R])).mp (W.logIntervalIntegrable (-|R|) |R|)
  exact hIcc.mono_set fun y hy => by
    have hyR : |y| ≤ R := by simpa [Metric.mem_closedBall, Real.dist_eq] using hkR hy
    exact abs_le.mp (hyR.trans (le_abs_self R))

/-- The Szegő outer multiplier `D_w`, bounded by `√(sup w)`. -/
def outer : DiskMultiplier where
  fn := szegoOuter W.w
  diff := (analyticOnNhd_szegoOuter W.logInt).differentiableOn
  bd := Real.sqrt W.bound
  bd_nonneg := Real.sqrt_nonneg _
  bd_le := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have hsq := normSq_szegoOuter_le_from_weight_bound W.bound_pos W.logInt W.pos W.le_bound
      (norm_nonneg z) hz1 z.arg
    rw [circleMap_norm_arg] at hsq
    rw [← abs_norm]
    exact Real.abs_le_sqrt hsq

theorem outer_fn : W.outer.fn = szegoOuter W.w := rfl

/-- `D_w` has no zeros. -/
theorem outer_ne_zero (z : ℂ) : W.outer.fn z ≠ 0 := szegoOuter_ne_zero _ _

/-- `D_w(0) = exp((1/4π) ∫₀^{2π} log w) > 0`. -/
theorem outer_zero : W.outer.fn 0 = ((Real.exp ((1 / (4 * Real.pi)) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log (W.w θ)) : ℝ) : ℂ) :=
  szegoOuter_zero_eq_real_exp _

/-- `|D_w(re^{iθ})|² → w(θ)` for almost every `θ`. -/
theorem tendsto_normSq_outer : ∀ᵐ θ ∂volume,
    Tendsto (fun r => ‖W.outer.fn (circleMap 0 r θ)‖ ^ (2 : ℕ)) (𝓝[<] 1) (𝓝 (W.w θ)) :=
  tendsto_normSq_szegoOuter_ae W.logLocallyIntegrable W.logInt W.logPeriodic W.pos

/-- The `L²` boundary of `D_w` has squared modulus `w`. -/
theorem ae_norm_sq_boundary_outer : ∀ᵐ z ∂circleLebesgue,
    ‖diskMultiplierBoundaryFun W.outer z‖ ^ (2 : ℕ) = W.w (Complex.arg (z : ℂ)) :=
  ae_norm_sq_diskMultiplierBoundaryFun_eq_of_radial W.outer W.meas W.periodic
    W.tendsto_normSq_outer

theorem outer_exists_ne : ∃ z ∈ Metric.ball (0 : ℂ) 1, W.outer.fn z ≠ 0 :=
  ⟨0, by simp, W.outer_ne_zero 0⟩

/-- `D_w` coincides with the canonical outer factor of itself. -/
theorem diskMultiplierOuterFactor_outer_fn :
    (diskMultiplierOuterFactor W.outer W.outer_exists_ne).fn = W.outer.fn := by
  funext z
  show szegoOuter (diskMultiplierOuterWeight W.outer) z = szegoOuter W.w z
  unfold szegoOuter
  congr 2
  refine intervalIntegral.integral_congr_ae ?_
  have hsafe : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundarySafe W.outer z‖ ^ (2 : ℕ) = W.w (Complex.arg (z : ℂ)) := by
    filter_upwards [diskMultiplierBoundarySafe_ae W.outer W.outer_exists_ne,
      W.ae_norm_sq_boundary_outer] with z h1 h2
    rw [h1, h2]
  filter_upwards [ae_angularCircle_of_ae_circle hsafe] with θ hθ hmem
  rw [uIoc_of_le Real.two_pi_pos.le] at hmem
  have h := hθ hmem
  rw [coe_angularCircle, periodic_apply_arg_circleMap W.periodic] at h
  rw [diskMultiplierOuterWeight, h]

/-- **Outerness.**  `D_w` is an outer multiplier. -/
theorem isOuter : IsOuterDiskMultiplier W.outer := by
  have h := isOuterDiskMultiplier_diskMultiplierOuterFactor W.outer W.outer_exists_ne
  unfold IsOuterDiskMultiplier at h ⊢
  rwa [hardyOf_congr (fun z _ => congrFun W.diskMultiplierOuterFactor_outer_fn z)] at h

/-- Multiplication by the zero-free `D_w` is injective on `H²`. -/
theorem hardyMul_outer_injective : Function.Injective (hardyMul W.outer) := by
  intro f g hfg
  apply hardyDisk_ext
  intro z hz
  have h := congrArg (fun a => hardyFun a z) hfg
  simp only [hardyFun_hardyMul W.outer _ hz] at h
  exact mul_left_cancel₀ (W.outer_ne_zero z) h

/-- Multiplication by the outer `D_w` has dense range in `H²`. -/
theorem denseRange_hardyMul_outer : DenseRange (hardyMul W.outer) := by
  have h := W.isOuter
  unfold IsOuterDiskMultiplier at h
  rw [cyclicSubspace, hardyOf, polyMultiples_map] at h
  have hle : (polyMultiples hardyOne).map
      ((hardyMul W.outer : HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) ≤
        LinearMap.range ((hardyMul W.outer : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) := LinearMap.map_le_range
  have htop : (LinearMap.range ((hardyMul W.outer : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk)).topologicalClosure = ⊤ :=
    top_unique (h ▸ Submodule.topologicalClosure_mono hle)
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr htop
  exact hd.mono fun x hx => LinearMap.mem_range.mp hx

theorem apply_arg_angularCircle (θ : ℝ) :
    W.w (Complex.arg ((angularCircle θ : Circle) : ℂ)) = W.w θ := by
  rw [coe_angularCircle, periodic_apply_arg_circleMap W.periodic]

/-- **Nonclosed range.**  If `1/w` is not integrable, multiplication by `D_w` does not have closed
range: surjectivity would give `g ∈ H²` with `D_w g = 1`, whose boundary has squared modulus
`1/w`. -/
theorem not_isClosed_range_hardyMul_outer
    (hinv : ¬IntervalIntegrable (fun θ => (W.w θ)⁻¹) volume 0 (2 * π)) :
    ¬IsClosed (Set.range (hardyMul W.outer)) := by
  intro hcl
  have hone : hardyOne ∈ Set.range (hardyMul W.outer) := by
    have hcr := W.denseRange_hardyMul_outer.closure_range
    rw [hcl.closure_eq] at hcr
    rw [hcr]
    trivial
  obtain ⟨g, hg⟩ := hone
  have hb := diskMultiplierBoundaryMul_apply W.outer g
  rw [hg, hardyOne, hardyDiskBoundary_single] at hb
  have hprod : ∀ᵐ z ∂circleLebesgue,
      diskMultiplierBoundaryFun W.outer z * (hardyDiskBoundary g : Circle → ℂ) z = 1 := by
    filter_upwards [diskMultiplierBoundaryMul_coeFn W.outer (hardyDiskBoundary g),
      circleMonomialLp_coeFn_ae circleLebesgue 0] with z h1 h2
    rw [← h1, hb, h2, pow_zero]
  have hsq : ∀ᵐ z ∂circleLebesgue,
      ‖(hardyDiskBoundary g : Circle → ℂ) z‖ ^ (2 : ℕ) = (W.w (Complex.arg (z : ℂ)))⁻¹ := by
    filter_upwards [hprod, W.ae_norm_sq_boundary_outer] with z h1 h2
    have hn := congrArg (fun u : ℂ => ‖u‖ ^ (2 : ℕ)) h1
    simp only [norm_mul, mul_pow, norm_one, one_pow] at hn
    rw [h2] at hn
    exact eq_inv_of_mul_eq_one_right hn
  have hmem := Lp.memLp (hardyDiskBoundary g)
  have hint : Integrable (fun z : Circle => (W.w (Complex.arg (z : ℂ)))⁻¹) circleLebesgue :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp hmem).congr hsq
  have hmeas : Measurable (fun z : Circle => (W.w (Complex.arg (z : ℂ)))⁻¹) :=
    (W.meas.comp (Complex.measurable_arg.comp
      (show Measurable (fun z : Circle => (z : ℂ)) from Continuous.measurable (by fun_prop)))).inv
  have hII := intervalIntegrable_angularCircle_of_integrable_circleLebesgue _ hmeas hint
  apply hinv
  refine hII.congr fun θ _ => ?_
  have h := angularCircle_two_pi_mul (θ / (2 * Real.pi))
  rw [mul_div_cancel₀ _ Real.two_pi_pos.ne'] at h
  show (W.w (Complex.arg ((AddCircle.toCircle (↑(θ / (2 * Real.pi)) : AddCircle (1 : ℝ)) :
    Circle) : ℂ)))⁻¹ = (W.w θ)⁻¹
  rw [← h, W.apply_arg_angularCircle]

/-- **Uniqueness.**  An outer multiplier with boundary modulus `√w` and positive value at the
origin is `D_w`. -/
theorem eq_outer_of_isOuter (ψ : DiskMultiplier) (hψ : IsOuterDiskMultiplier ψ)
    (hmod : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun ψ z‖ ^ (2 : ℕ) = W.w (Complex.arg (z : ℂ)))
    {s : ℝ} (hs : 0 < s) (hψ0 : ψ.fn 0 = s) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ψ.fn z = W.outer.fn z := by
  have hmod' : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun ψ z‖ = ‖diskMultiplierBoundaryFun W.outer z‖ := by
    filter_upwards [hmod, W.ae_norm_sq_boundary_outer] with z h1 h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (h1.trans h2.symm)
  obtain ⟨c, hc, hcz⟩ := outerDiskMultiplier_unique_up_to_unimodular ψ W.outer hmod' hψ W.isOuter
  set R := Real.exp ((1 / (4 * Real.pi)) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log (W.w θ))
  have hR : 0 < R := Real.exp_pos _
  have h0 := hcz 0 (by simp)
  rw [hψ0, W.outer_zero] at h0
  have hcval : c = ((s / R : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hR.ne')]
    exact h0.symm
  have hc1 : c = 1 := by
    rw [hcval] at hc ⊢
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hs hR)] at hc
    rw [hc, Complex.ofReal_one]
  intro z hz
  rw [hcz z hz, hc1, one_mul]

end SzegoWeight

end

end GaloisForLFunctions.HTGeometry
