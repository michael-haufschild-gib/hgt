import GaloisForLFunctions.RHTower.SelbergMaassPeriodCurrentRigidity
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Complete original current is continuous in height through common zeros

A differentiable real-parameter vector source has only countably many zeros
with nonzero derivative. Applying this fact twice shows that original
horizontal second derivatives vanish at almost every common zero on a fixed
height. Away from nodes the signed acceleration quotient is continuous; at
nodes with zero acceleration its source majorant tends to zero. Compact
original C² bounds therefore justify dominated convergence in height.

The complete current-period limit is continuous at every positive height.
A second dominated-convergence argument removes the regulator after height
integration, retaining the entire horizontal current over each compact
rectangle. Positive line current yields a source-dependent positive band
and a fixed positive rectangle bound for all sufficiently small regulators.
Zero limiting band mass is equivalent to vanishing at every height in the
band. Original nonflat nodes supply one concrete positivity trigger.

No node is excluded, no pointwise current-density limit is integrated, and
no nodal measure formula or analyticity is assumed. The band and its bound
are source-dependent. No uniform quotient-area quarter inequality, full-Xi
spectral occurrence, or Riemann hypothesis is asserted.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory ModularGroup
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCurrentHeightContinuity
noncomputable section

/-- A differentiable one-dimensional source has only countably many zeros with nonzero derivative. -/
theorem countable_nonflat_zeros {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : ℝ → E} (h : ∀ x, HasDerivAt F (G x) x) :
    {x | F x = 0 ∧ G x ≠ 0}.Countable := by
  apply (countable_setOf_isolated_right_within (s := {x | F x = 0})).mono
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hn := ((h x).eventually_ne (c := 0) hx.2).filter_mono
    (nhdsWithin_mono x (show {z | F z = 0} ∩ Ioi x ⊆ {x}ᶜ from
      fun z hz => by simpa using hz.2.ne'))
  have hz : ∀ᶠ z in 𝓝[{z | F z = 0} ∩ Ioi x] x, F z = 0 :=
    by filter_upwards [self_mem_nhdsWithin] with z hz; exact hz.1
  exact eventually_false_iff_eq_bot.mp ((hn.and hz).mono (fun _ hz => hz.1 hz.2))

/-- Two successive derivatives vanish almost everywhere on the original zero set. -/
theorem ae_flat_second_zeros {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G H : ℝ → E} (h : ∀ x, HasDerivAt F (G x) x)
    (h' : ∀ x, HasDerivAt G (H x) x) :
    ∀ᵐ x : ℝ, F x = 0 → G x = 0 ∧ H x = 0 := by
  have hc := (countable_nonflat_zeros h).union (countable_nonflat_zeros h')
  have ha : ∀ᵐ x : ℝ, x ∉ {x | F x = 0 ∧ G x ≠ 0} ∪ {x | G x = 0 ∧ H x ≠ 0} := by
    exact (measure_eq_zero_iff_ae_notMem).mp (hc.measure_zero volume)
  filter_upwards [ha] with x hx hf
  simp only [mem_union,mem_setOf_eq,not_or] at hx
  have hg : G x = 0 := by by_contra hn; exact hx.1 ⟨hf,hn⟩
  exact ⟨hg, by by_contra hn; exact hx.2 ⟨hg,hn⟩⟩

open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceEnergy
open SelbergMaassSourceCurrents SelbergMaassTraceRegularized SelbergMaassRegulatorMass
open SelbergMaassChordEnergy SelbergMaassUnipotentPaths SelbergMaassTraceDirection
open SelbergMaassPeriodResistance SelbergMaassTraceRadial SelbergMaassCongruenceAverage
open SelbergMaassPeriodCurrentLimit SelbergMaassPeriodCurrentRigidity
variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Original acceleration is continuous throughout the open upper half-plane. -/
theorem accelerationBound_continuousOn :
    ContinuousOn (accelerationBound N f) {z : ℂ | 0 < z.im} := by
  apply continuousOn_finsetSum Finset.univ
  intro q _
  exact (dir_contDiffOn (dir_contDiffOn (quotientForm N f q).2.2.1.1
    (m:=1) (by norm_num) 1) (m:=0) (by norm_num) 1).continuousOn.norm

/-- The original acceleration pairing is jointly continuous. -/
theorem accelerationPair_continuousOn :
    ContinuousOn (accelerationPair N f) {z : ℂ | 0 < z.im} := by
  apply continuousOn_finsetSum Finset.univ
  intro q _
  exact Complex.reCLM.continuous.comp_continuousOn
    ((dir_contDiffOn (dir_contDiffOn (quotientForm N f q).2.2.1.1
      (m:=1) (by norm_num) 1) (m:=0) (by norm_num) 1).continuousOn.mul
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).continuous.comp_continuousOn
      (quotientForm N f q).2.2.1.1.continuousOn))

/-- At almost every common zero on any horizontal line, all original horizontal accelerations vanish. -/
theorem ae_acceleration_zero_at_nodes {y : ℝ} (hy : 0 < y) :
    ∀ᵐ x : ℝ, density N f (ofComplex (point x y)) = 0 →
      accelerationBound N f (point x y) = 0 := by
  have hF (q : Deck N) : ContDiffOn ℝ 2 (field N f q) {z : ℂ | 0 < z.im} :=
    (quotientForm N f q).2.2.1.1
  have hq (q : Deck N) : ∀ᵐ x : ℝ, field N f q (point x y)=0 →
      dir 1 (field N f q) (point x y)=0 ∧ dir 1 (dir 1 (field N f q)) (point x y)=0 := by
    apply ae_flat_second_zeros
    · intro x
      have hp : 0 < (point x y).im := by simpa [point] using hy
      have hd := ((hF q).contDiffAt
        (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt (by norm_num)
      simpa only [dir,Function.comp_def] using hd.hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)
    · intro x
      have hp : 0 < (point x y).im := by simpa [point] using hy
      have hd := ((dir_contDiffOn (hF q)
        (m:=1) (by norm_num) 1).contDiffAt
        (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt (by norm_num)
      simpa only [dir,Function.comp_def] using hd.hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)
  have hall := (ae_all_iff).mpr hq
  filter_upwards [hall] with x hx hz
  apply Finset.sum_eq_zero
  intro q _
  have hnorm := field_norm_le_amplitude N f q (point x y)
  rw [hz,Real.sqrt_zero] at hnorm
  have hf : field N f q (point x y)=0 := norm_le_zero_iff.mp hnorm
  simp only [(hx q hf).2,norm_zero]

/-- The signed source quotient is jointly continuous away from nodes and at nodes with zero acceleration. -/
theorem sourceAccelerationDensity_continuousAt_of_regular_or_flat (z : ℂ)
    (hz : 0 < z.im) (hflat : density N f (ofComplex z)=0 → accelerationBound N f z=0) :
    ContinuousAt (sourceAccelerationDensity N f) z := by
  have hn := isOpen_upperHalfPlaneSet.mem_nhds hz
  by_cases hd : density N f (ofComplex z)=0
  · have hb := (accelerationBound_continuousOn N f).continuousAt hn
    change Tendsto (accelerationBound N f) (𝓝 z) (𝓝 (accelerationBound N f z)) at hb
    rw [hflat hd] at hb
    change Tendsto (sourceAccelerationDensity N f) (𝓝 z) (𝓝 (sourceAccelerationDensity N f z))
    rw [show sourceAccelerationDensity N f z=0 by simp [sourceAccelerationDensity,hd]]
    exact squeeze_zero_norm (sourceAccelerationDensity_bound N f) hb
  · exact ((accelerationPair_continuousOn N f).continuousAt hn).div
      ((density_contDiffOn N f).continuousOn.continuousAt hn).sqrt
      (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (density_nonneg N f _) (Ne.symm hd)))

/-- Height continuity holds for almost every horizontal coordinate, even on a nodal height. -/
theorem ae_sourceAccelerationDensity_height_continuousAt {y : ℝ} (hy : 0 < y) :
    ∀ᵐ x : ℝ, ContinuousAt (fun t => sourceAccelerationDensity N f (point x t)) y := by
  filter_upwards [ae_acceleration_zero_at_nodes N f hy] with x hx
  exact (sourceAccelerationDensity_continuousAt_of_regular_or_flat N f (point x y)
    (by simpa [point] using hy) hx).comp (point_vertical x y).continuousAt

/-- A compact rectangle supplies one source-derived bound for all its heights. -/
theorem exists_acceleration_rectangle_bound {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc a b,
      accelerationBound N f (point x y) ≤ C := by
  have hc : ContinuousOn (fun xy : ℝ × ℝ => accelerationBound N f (point xy.1 xy.2))
      (Icc 0 1 ×ˢ Icc a b) := by
    apply (accelerationBound_continuousOn N f).comp
      (show Continuous (fun xy : ℝ × ℝ => point xy.1 xy.2) by unfold point; fun_prop).continuousOn
    intro xy hxy
    simpa [point] using ha.trans_le hxy.2.1
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨C,fun x hx y hy => ?_⟩
  exact (le_abs_self _).trans (hC (x,y) ⟨hx,hy⟩)

/-- The complete current-period limit is continuous at every positive height, including common-zero heights. -/
theorem periodCurrentLimit_continuousAt {y : ℝ} (hy : 0 < y) :
    ContinuousAt (periodCurrentLimit N f) y := by
  obtain ⟨C,hC⟩ := exists_acceleration_rectangle_bound N f (b:=y+1) (a:=y/2) (by linarith)
  have hn : Ioo (y/2) (y+1) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have h := intervalIntegral.continuousAt_of_dominated_interval
    (μ:=volume) (F:=fun t x => sourceAccelerationDensity N f (point x t))
    (x₀:=y) (a:=0) (b:=1) (bound:=fun _ => C)
    (by filter_upwards [hn] with t ht
        exact (sourceAccelerationDensity_measurable N f (by linarith [ht.1])).aestronglyMeasurable.restrict)
    (by filter_upwards [hn] with t ht
        exact Eventually.of_forall (fun x hx => (sourceAccelerationDensity_bound N f (point x t)).trans
          (hC x (by simpa using Ioc_subset_Icc_self hx)
            t ⟨ht.1.le,ht.2.le⟩)))
    intervalIntegrable_const
    (by filter_upwards [ae_sourceAccelerationDensity_height_continuousAt N f hy] with x hx
        exact fun _ => hx)
  exact h.neg

/-- Complete original current is continuous on the whole positive-height domain. -/
theorem periodCurrentLimit_continuousOn : ContinuousOn (periodCurrentLimit N f) (Ioi 0) :=
  fun _ hy => (periodCurrentLimit_continuousAt N f hy).continuousWithinAt

/-- Regulated signed acceleration is jointly continuous in the original upper half-plane. -/
theorem accelerationDensity_continuousOn (e : Ioi (0:ℝ)) :
    ContinuousOn (accelerationDensity N f e) {z : ℂ | 0 < z.im} :=
  (accelerationPair_continuousOn N f).div (radius_contDiffOn N f e).continuousOn
    (fun z _ => (radius_pos N f e z).ne')

/-- Every full regulated current-period integral is continuous in height. -/
theorem periodCurrentEnergy_continuousAt (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (periodCurrentEnergy N f e) y := by
  obtain ⟨C,hC⟩ := exists_acceleration_rectangle_bound N f (b:=y+1) (a:=y/2) (by linarith)
  have hn : Ioo (y/2) (y+1) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have h := intervalIntegral.continuousAt_of_dominated_interval
    (μ:=volume) (F:=fun t x => accelerationDensity N f e (point x t))
    (x₀:=y) (a:=0) (b:=1) (bound:=fun _ => C)
    (by filter_upwards [hn] with t ht
        exact (accelerationDensity_continuous N f e (by linarith [ht.1])).aestronglyMeasurable)
    (by filter_upwards [hn] with t ht
        exact Eventually.of_forall (fun x hx => (accelerationDensity_bound N f e (point x t)).trans
          (hC x (by simpa using Ioc_subset_Icc_self hx) t ⟨ht.1.le,ht.2.le⟩)))
    intervalIntegrable_const
    (Eventually.of_forall (fun x _ =>
      ((accelerationDensity_continuousOn N f e).continuousAt
        (isOpen_upperHalfPlaneSet.mem_nhds (by simpa [point] using hy))).comp
        (point_vertical x y).continuousAt))
  have he : periodCurrentEnergy N f e =ᶠ[𝓝 y]
      (fun t => -(∫ x in (0:ℝ)..1, accelerationDensity N f e (point x t))) := by
    filter_upwards [hn] with t ht
    exact periodCurrentEnergy_eq_acceleration N f e (by linarith [ht.1])
  exact h.neg.congr_of_eventuallyEq he

/-- Actual acceleration bounds control its full horizontal integral on the whole rectangle. -/
theorem acceleration_integral_le_rectangle_bound {a b C : ℝ} (ha : 0 < a)
    (hC : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc a b, accelerationBound N f (point x y) ≤ C)
    {y : ℝ} (hy : y ∈ Icc a b) :
    (∫ x in (0:ℝ)..1, accelerationBound N f (point x y)) ≤ C := by
  have h := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ)≤1)
    ((accelerationBound_continuous N f (ha.trans_le hy.1)).intervalIntegrable 0 1)
    (intervalIntegrable_const (c:=C)) (fun x hx => hC x hx y hy)
  simpa using h

/-- The complete limiting current is integrable on every compact positive-height interval. -/
theorem periodCurrentLimit_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (periodCurrentLimit N f) volume a b :=
  (periodCurrentLimit_continuousOn N f |>.mono (fun _ hx => ha.trans_le hx.1)).intervalIntegrable_of_Icc hab

/-- Every regulated complete current is integrable over each compact positive-height interval. -/
theorem periodCurrentEnergy_intervalIntegrable (e : Ioi (0:ℝ)) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (periodCurrentEnergy N f e) volume a b := by
  have hc : ContinuousOn (periodCurrentEnergy N f e) (Icc a b) :=
    fun _ hy => (periodCurrentEnergy_continuousAt N f e (ha.trans_le hy.1)).continuousWithinAt
  exact hc.intervalIntegrable_of_Icc hab

/-- Full original current mass over a compact rectangle converges, retaining all nodal concentration. -/
theorem periodCurrentEnergy_band_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun e : Ioi (0:ℝ) => ∫ y in a..b, periodCurrentEnergy N f e y)
      regulatorAtZero (𝓝 (∫ y in a..b, periodCurrentLimit N f y)) := by
  letI : regulatorAtZero.IsCountablyGenerated := by unfold regulatorAtZero; infer_instance
  obtain ⟨C,hC⟩ := exists_acceleration_rectangle_bound N f (b:=b) ha
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · exact Eventually.of_forall (fun e => (periodCurrentEnergy_intervalIntegrable N f e ha hab).aestronglyMeasurable_restrict_uIoc)
  · apply Eventually.of_forall
    intro e
    apply Eventually.of_forall
    intro y hy
    have hy' : y ∈ Icc a b := by rw [uIoc_of_le hab] at hy; exact Ioc_subset_Icc_self hy
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ periodCurrentEnergy N f e y from
      pathEnergy_nonneg N f e y (by norm_num : (0:ℝ)≤1))]
    exact (periodCurrentEnergy_le_accelerationBound N f e (ha.trans_le hy'.1)).trans
      (acceleration_integral_le_rectangle_bound N f ha hC hy')
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun y hy => periodCurrentEnergy_tendsto N f
      (ha.trans (by rw [uIoc_of_le hab] at hy; exact hy.1)))

/-- Strict positivity at one height persists with a quantitative source-dependent floor on a closed band. -/
theorem exists_positive_current_band {y : ℝ} (hy : 0 < y)
    (hE : 0 < periodCurrentLimit N f y) :
    ∃ a b : ℝ, 0 < a ∧ a < y ∧ y < b ∧
      ∀ t ∈ Icc a b, periodCurrentLimit N f y / 2 ≤ periodCurrentLimit N f t := by
  have he := (periodCurrentLimit_continuousAt N f hy).eventually
    (Ioi_mem_nhds (show periodCurrentLimit N f y / 2 < periodCurrentLimit N f y by linarith))
  have hn : {t : ℝ | 0 < t ∧ periodCurrentLimit N f y / 2 < periodCurrentLimit N f t} ∈ 𝓝 y :=
    by filter_upwards [Ioi_mem_nhds hy,he] with t ht htE; exact ⟨ht,htE⟩
  obtain ⟨l,u,⟨hl,hu⟩,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  refine ⟨(l+y)/2,(y+u)/2,?_,by linarith,by linarith,?_⟩
  · exact (hs ⟨by linarith,by linarith⟩).1
  · intro t ht
    exact (hs ⟨by linarith [ht.1],by linarith [ht.2]⟩).2.le

/-- A positive current height gives a positive complete limiting rectangle mass. -/
theorem exists_positive_current_band_mass {y : ℝ} (hy : 0 < y)
    (hE : 0 < periodCurrentLimit N f y) :
    ∃ a b : ℝ, 0 < a ∧ a < y ∧ y < b ∧
      0 < ∫ t in a..b, periodCurrentLimit N f t := by
  obtain ⟨a,b,ha,hay,hyb,hfloor⟩ := exists_positive_current_band N f hy hE
  refine ⟨a,b,ha,hay,hyb,?_⟩
  have hab : a < b := hay.trans hyb
  have h := intervalIntegral.integral_mono_on (μ:=volume) hab.le
    (intervalIntegrable_const (c:=periodCurrentLimit N f y/2))
    (periodCurrentLimit_intervalIntegrable N f ha hab.le) hfloor
  have hp : 0 < (b-a)*(periodCurrentLimit N f y/2) := mul_pos (sub_pos.mpr hab) (by linarith)
  exact hp.trans_le (by simpa [mul_div_assoc] using h)

/-- Positive limiting rectangle mass survives uniformly for all sufficiently small regulators. -/
theorem exists_eventually_positive_current_band {y : ℝ} (hy : 0 < y)
    (hE : 0 < periodCurrentLimit N f y) :
    ∃ a b c : ℝ, 0 < a ∧ a < y ∧ y < b ∧ 0 < c ∧
      ∀ᶠ e : Ioi (0:ℝ) in regulatorAtZero,
        c ≤ ∫ t in a..b, periodCurrentEnergy N f e t := by
  obtain ⟨a,b,ha,hay,hyb,hM⟩ := exists_positive_current_band_mass N f hy hE
  refine ⟨a,b,(∫ t in a..b, periodCurrentLimit N f t)/2,ha,hay,hyb,by linarith,?_⟩
  have h := (periodCurrentEnergy_band_tendsto N f ha (hay.trans hyb).le).eventually
    (Ioi_mem_nhds (show (∫ t in a..b, periodCurrentLimit N f t)/2 <
      ∫ t in a..b, periodCurrentLimit N f t by linarith))
  exact h.mono (fun _ ht => ht.le)

/-- Actual iterated horizontal-current integration equals integration of the complete period energy. -/
theorem horizontalCurrent_rectangle_eq_periods (e : Ioi (0:ℝ)) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b, ∫ x in (0:ℝ)..1, horizontalCurrentDensity N f e (point x y)) =
      ∫ y in a..b, periodCurrentEnergy N f e y := by
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ∈ Icc a b := by simpa only [uIcc_of_le hab] using hy
  exact (pathEnergy_eq_current_integral N f e (ha.trans_le hy'.1) 0 1).symm

/-- Regulator removal commutes with integration of the full original horizontal current over a compact rectangle. -/
theorem horizontalCurrent_rectangle_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun e : Ioi (0:ℝ) =>
      ∫ y in a..b, ∫ x in (0:ℝ)..1, horizontalCurrentDensity N f e (point x y))
      regulatorAtZero (𝓝 (∫ y in a..b, periodCurrentLimit N f y)) := by
  simp_rw [horizontalCurrent_rectangle_eq_periods N f _ ha hab]
  exact periodCurrentEnergy_band_tendsto N f ha hab

/-- A positive complete line current yields a fixed positive lower bound for actual rectangle currents at all small regulators. -/
theorem exists_eventually_positive_horizontal_rectangle {y : ℝ} (hy : 0 < y)
    (hE : 0 < periodCurrentLimit N f y) :
    ∃ a b c : ℝ, 0 < a ∧ a < y ∧ y < b ∧ 0 < c ∧
      ∀ᶠ e : Ioi (0:ℝ) in regulatorAtZero,
        c ≤ ∫ t in a..b, ∫ x in (0:ℝ)..1, horizontalCurrentDensity N f e (point x t) := by
  obtain ⟨a,b,c,ha,hay,hyb,hc,h⟩ := exists_eventually_positive_current_band N f hy hE
  refine ⟨a,b,c,ha,hay,hyb,hc,?_⟩
  simpa only [horizontalCurrent_rectangle_eq_periods N f _ ha (hay.trans hyb).le] using h

/-- Zero complete mass on a nondegenerate band is equivalent to zero current at every height in that band. -/
theorem current_band_mass_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ y in a..b, periodCurrentLimit N f y)=0 ↔
      ∀ y ∈ Icc a b, periodCurrentLimit N f y=0 := by
  constructor
  · intro h y hy
    have hp := periodCurrentLimit_nonneg N f (ha.trans_le hy.1)
    by_contra hn
    have hpos := intervalIntegral.integral_pos hab
      ((periodCurrentLimit_continuousOn N f).mono (fun _ hx => ha.trans_le hx.1))
      (fun t ht => periodCurrentLimit_nonneg N f (ha.trans ht.1))
      ⟨y,hy,lt_of_le_of_ne hp (Ne.symm hn)⟩
    simp only [h,lt_self_iff_false] at hpos
  · intro h
    calc
      _ = ∫ _ in a..b, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact h y (by simpa only [uIcc_of_le hab.le] using hy)
      _ = 0 := by simp

/-- A nonflat original common node forces positive current mass on a genuine surrounding height band. -/
theorem nonflat_node_positive_horizontal_rectangle (z : ℍ) (hz : density N f z=0)
    (hG : 0 < directionalEnergy N f 1 z) :
    ∃ a b c : ℝ, 0 < a ∧ a < z.im ∧ z.im < b ∧ 0 < c ∧
      ∀ᶠ e : Ioi (0:ℝ) in regulatorAtZero,
        c ≤ ∫ t in a..b, ∫ x in (0:ℝ)..1, horizontalCurrentDensity N f e (point x t) :=
  exists_eventually_positive_horizontal_rectangle N f z.im_pos
    (periodCurrentLimit_pos_of_nonflat_node N f z hz hG)

end
end GaloisForLFunctions.RHTower.SelbergMaassCurrentHeightContinuity
