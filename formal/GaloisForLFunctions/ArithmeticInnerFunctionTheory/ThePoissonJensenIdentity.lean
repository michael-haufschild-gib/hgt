import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenEquality
import GaloisForLFunctions.RHTower.ZetaPoissonJensenInequality

/-!
# The Poisson–Jensen identity on the half-plane

Let `E` be entire of quadratic growth on `Re s ≥ ½`, `Re w > ½`, `E(w) ≠ 0`, and let `E` be bounded
away from zero far along the horizontal ray through `w`. Then the boundary logarithm is integrable
against the Poisson kernel `P_w` of the half-plane and

`∫ log |E(½ + iτ)| P_w(τ) dτ − log |E(w)| = Σ_ρ m_ρ log (|ρ + w̄ − 1| / |ρ − w|)`,

the sum running over the zeros of `E` in `Re s > ½`, with multiplicity, and converging. So the inner
factor of `E` on the half-plane is exactly the Blaschke product of its zeros: there is no singular
part (`hasSum_poissonJensen`).

The proof pulls `E` back to the disc through the automorphism of the half-plane sending `1` to `w`,
applies Jensen on the circles of radius `r < 1`, and passes to the limit `r → 1` with the radial
theorem `tendsto_integral_log_norm_circleMap_nhdsLT_one`. The lower bound on the ray is what excludes
a singular mass at the boundary point `∞`. Positivity of the finite Jensen sums gives the summability.
-/

open Complex Metric Filter Topology MeasureTheory Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-! ### The identity on the disc -/

/-- A disc datum: holomorphic off the boundary point `1`, nonzero at the centre, of polynomial growth
at `1`, and bounded below on a radius ending at `1`. -/
structure IsDiscDatum (Φ : ℂ → ℂ) : Prop where
  diff : DifferentiableOn ℂ Φ {1}ᶜ
  meas : Measurable Φ
  ne0 : Φ 0 ≠ 0
  up : ∃ A : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 → Real.log ‖Φ w‖ ≤ A - 2 * Real.log ‖1 - w‖
  low : ∃ c x₀ : ℝ, 0 < c ∧ 1 / 2 ≤ x₀ ∧ x₀ < 1 ∧ ∀ x : ℝ, x₀ ≤ x → x < 1 → c ≤ ‖Φ x‖

namespace IsDiscDatum

variable {Φ : ℂ → ℂ} (h : IsDiscDatum Φ)

include h

theorem analyticAt {w : ℂ} (hw : w ≠ 1) : AnalyticAt ℂ Φ w :=
  h.diff.analyticAt (isOpen_compl_singleton.mem_nhds hw)

theorem analyticOnNhd_ball : AnalyticOnNhd ℂ Φ (ball (0 : ℂ) 1) := fun u hu =>
  h.analyticAt (by rintro rfl; simp at hu)

theorem analyticOnNhd_closedBall {r : ℝ} (hr : r < 1) : AnalyticOnNhd ℂ Φ (closedBall (0 : ℂ) r) :=
  fun u hu => h.analyticAt (by
    rintro rfl
    simp only [mem_closedBall, dist_zero_right, norm_one] at hu
    linarith)

theorem circleIntegrable : CircleIntegrable (fun w => Real.log ‖Φ w‖) 0 1 := by
  obtain ⟨A, hA⟩ := h.up
  exact (circleIntegrable_and_sum_log_add_le_circleAverage h.diff h.meas h.ne0 ⟨A, hA⟩
    (U := ∅) (by simp)).1

theorem tendsto_circleAverage :
    Tendsto (fun r => Real.circleAverage (fun w => Real.log ‖Φ w‖) 0 r) (𝓝[<] 1)
      (𝓝 (Real.circleAverage (fun w => Real.log ‖Φ w‖) 0 1)) := by
  obtain ⟨A, hA⟩ := h.up
  obtain ⟨c, x₀, hc, hx₀, hx₀1, hlow⟩ := h.low
  have ht := tendsto_integral_log_norm_circleMap_nhdsLT_one h.diff h.meas h.ne0 hA hc hx₀ hx₀1 hlow
  simp only [Real.circleAverage_def, smul_eq_mul]
  exact ht.const_mul _

/-- The Jensen sums converge to the boundary average minus the value at the centre. -/
theorem tendsto_jensenSum :
    Tendsto (fun r : ℝ => ∑ᶠ u, (MeromorphicOn.divisor Φ (closedBall (0 : ℂ) |r|) u : ℝ) *
        Real.log (r * ‖u‖⁻¹)) (𝓝[<] 1)
      (𝓝 (Real.circleAverage (fun w => Real.log ‖Φ w‖) 0 1 - Real.log ‖Φ 0‖)) := by
  refine (h.tendsto_circleAverage.sub_const _).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have han : AnalyticOnNhd ℂ Φ (closedBall 0 |r|) := by
    rw [abs_of_pos hr.1]; exact h.analyticOnNhd_closedBall hr.2
  rw [han.circleAverage_log_norm hr.1.ne' h.ne0]
  simp only [zero_sub, norm_neg, add_sub_cancel_right]

end IsDiscDatum

/-- The multiplicity of `Φ` on the open disc. -/
def discMult (Φ : ℂ → ℂ) := MeromorphicOn.divisor Φ (ball (0 : ℂ) 1)

/-- The Green weight of a point of the disc. -/
def discWeight (Φ : ℂ → ℂ) (u : ℂ) : ℝ := (discMult Φ u : ℝ) * Real.log ‖u‖⁻¹

/-- The Jensen weight at radius `r`. -/
def radialWeight (Φ : ℂ → ℂ) (r : ℝ) (u : ℂ) : ℝ :=
  (MeromorphicOn.divisor Φ (closedBall (0 : ℂ) |r|) u : ℝ) * Real.log (r * ‖u‖⁻¹)

namespace IsDiscDatum

variable {Φ : ℂ → ℂ} (h : IsDiscDatum Φ)

include h

private theorem discMult_nonneg (u : ℂ) : 0 ≤ discMult Φ u :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg h.analyticOnNhd_ball u

private theorem discWeight_nonneg (u : ℂ) : 0 ≤ discWeight Φ u := by
  by_cases hu : u ∈ ball (0 : ℂ) 1
  · rcases eq_or_ne u 0 with rfl | hu0
    · simp [discWeight]
    · apply mul_nonneg (by exact_mod_cast h.discMult_nonneg u)
      apply Real.log_nonneg
      rw [one_le_inv₀ (norm_pos_iff.mpr hu0)]
      exact (mem_ball_zero_iff.mp hu).le
  · simp [discWeight, discMult, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

omit h in
private theorem radial_finite (r : ℝ) : Function.HasFiniteSupport (radialWeight Φ r) := by
  apply (MeromorphicOn.divisor Φ (closedBall (0 : ℂ) |r|)).finiteSupport
    (isCompact_closedBall 0 |r|) |>.subset
  intro u hu
  contrapose! hu
  simp_all [Function.mem_support, radialWeight]

private theorem radial_nonneg {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (u : ℂ) :
    0 ≤ radialWeight Φ r u := by
  have ha : AnalyticOnNhd ℂ Φ (closedBall 0 |r|) := by
    rw [abs_of_pos hr.1]; exact h.analyticOnNhd_closedBall hr.2
  by_cases hu : u ∈ closedBall (0 : ℂ) |r|
  · apply mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha u)
    rcases eq_or_ne u 0 with rfl | hu0
    · simp
    · apply Real.log_nonneg
      rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.mpr hu0)]
      simpa [mem_closedBall, dist_zero_right, abs_of_pos hr.1] using hu
  · simp [radialWeight, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

private theorem radial_eq {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) {u : ℂ} (hu : ‖u‖ ≤ r) :
    radialWeight Φ r u = (discMult Φ u : ℝ) * Real.log (r * ‖u‖⁻¹) := by
  have ha : AnalyticOnNhd ℂ Φ (closedBall 0 |r|) := by
    rw [abs_of_pos hr.1]; exact h.analyticOnNhd_closedBall hr.2
  have hc : u ∈ closedBall (0 : ℂ) |r| := by
    simpa [mem_closedBall, dist_zero_right, abs_of_pos hr.1] using hu
  have hb : u ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hu.trans_lt hr.2)
  simp only [radialWeight, discMult, MeromorphicOn.divisor_apply ha.meromorphicOn hc,
    MeromorphicOn.divisor_apply h.analyticOnNhd_ball.meromorphicOn hb]

private theorem radial_le {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (u : ℂ) :
    radialWeight Φ r u ≤ discWeight Φ u := by
  by_cases hu : ‖u‖ ≤ r
  · rw [h.radial_eq hr hu]
    apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast h.discMult_nonneg u)
    rcases eq_or_ne u 0 with rfl | hu0
    · simp
    · apply Real.log_le_log (mul_pos hr.1 (inv_pos.mpr (norm_pos_iff.mpr hu0)))
      exact mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg u)) hr.2.le
  · have hc : u ∉ closedBall (0 : ℂ) |r| := by
      simpa [mem_closedBall, dist_zero_right, abs_of_pos hr.1] using hu
    simpa [radialWeight, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc]
      using h.discWeight_nonneg u

private theorem tendsto_radial (u : ℂ) :
    Tendsto (fun r => radialWeight Φ r u) (𝓝[<] (1 : ℝ)) (𝓝 (discWeight Φ u)) := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [radialWeight, discWeight]
  by_cases hu : ‖u‖ < 1
  · have ht : Tendsto (fun r : ℝ => (discMult Φ u : ℝ) * Real.log (r * ‖u‖⁻¹))
        (𝓝[<] 1) (𝓝 (discWeight Φ u)) := by
      have h' := ((tendsto_nhdsWithin_of_tendsto_nhds (s := Iio (1 : ℝ))
        (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 1) (𝓝 1))).mul_const ‖u‖⁻¹).log
        (by simpa using inv_ne_zero (norm_ne_zero_iff.mpr hu0))
      simpa [discWeight] using h'.const_mul (discMult Φ u : ℝ)
    apply ht.congr'
    filter_upwards [Ioo_mem_nhdsLT hu] with r hr
    exact (h.radial_eq ⟨(norm_nonneg u).trans_lt hr.1, hr.2⟩ hr.1.le).symm
  · have hb : u ∉ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using hu
    have hw : discWeight Φ u = 0 := by
      simp [discWeight, discMult, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb]
    rw [hw]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hc : u ∉ closedBall (0 : ℂ) |r| := by
      simp only [mem_closedBall, dist_zero_right, abs_of_pos hr.1]
      exact not_le.mpr (hr.2.trans_le (not_lt.mp hu))
    simp [radialWeight, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc]

private theorem weight_sum_le (s : Finset ℂ) :
    ∑ u ∈ s, discWeight Φ u ≤
      Real.circleAverage (fun w => Real.log ‖Φ w‖) 0 1 - Real.log ‖Φ 0‖ := by
  apply le_of_tendsto_of_tendsto (tendsto_finsetSum s (fun u _ => h.tendsto_radial u))
    h.tendsto_jensenSum
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hrw : (∑ᶠ u, (MeromorphicOn.divisor Φ (closedBall (0 : ℂ) |r|) u : ℝ) *
      Real.log (r * ‖u‖⁻¹)) = ∑' u, radialWeight Φ r u :=
    (tsum_eq_finsum (L := SummationFilter.unconditional ℂ) (radial_finite r)).symm
  rw [hrw]
  exact (summable_of_hasFiniteSupport (radial_finite r)).sum_le_tsum s
    (fun u _ => h.radial_nonneg hr u)

private theorem summable_weight : Summable (discWeight Φ) :=
  summable_of_sum_le h.discWeight_nonneg h.weight_sum_le

private theorem tsum_weight_eq :
    ∑' u, discWeight Φ u =
      Real.circleAverage (fun w => Real.log ‖Φ w‖) 0 1 - Real.log ‖Φ 0‖ := by
  apply le_antisymm (h.summable_weight.tsum_le_of_sum_le h.weight_sum_le)
  apply le_of_tendsto h.tendsto_jensenSum
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hrw : (∑ᶠ u, (MeromorphicOn.divisor Φ (closedBall (0 : ℂ) |r|) u : ℝ) *
      Real.log (r * ‖u‖⁻¹)) = ∑' u, radialWeight Φ r u :=
    (tsum_eq_finsum (L := SummationFilter.unconditional ℂ) (radial_finite r)).symm
  rw [hrw]
  exact (summable_of_hasFiniteSupport (radial_finite r)).tsum_le_tsum
    (h.radial_le hr) h.summable_weight

/-- **The disc identity.** The Green weights of the zeros in the open disc sum to the boundary
average minus the logarithm of the value at the centre. -/
theorem hasSum_discWeight :
    HasSum (discWeight Φ) (Real.circleAverage (fun w => Real.log ‖Φ w‖) 0 1 - Real.log ‖Φ 0‖) := by
  have hs := h.summable_weight.hasSum
  rwa [h.tsum_weight_eq] at hs

theorem discMult_eq_natOrder {u : ℂ} (hu : ‖u‖ < 1) :
    discMult Φ u = (analyticOrderNatAt Φ u : ℤ) := by
  rw [discMult, MeromorphicOn.AnalyticOnNhd.divisor_apply h.analyticOnNhd_ball
    (mem_ball_zero_iff.mpr hu)]
  have hne : analyticOrderAt Φ u ≠ ⊤ := by
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
    have hu' : u ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hu
    refine h.analyticOnNhd_ball.analyticOrderAt_ne_top_of_isPreconnected
      (convex_ball _ _).isPreconnected h0 hu' ?_
    rw [(h.analyticOnNhd_ball 0 h0).analyticOrderAt_eq_zero.mpr h.ne0]
    exact ENat.zero_ne_top
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  simp [analyticOrderNatAt, ← hm]

end IsDiscDatum

/-! ### The half-plane -/

/-- `T(s) − w = (2σ − 1)(s − 1)` for the automorphism `T` sending `1` to `w`. -/
theorem halfPlaneShift_sub (w s : ℂ) :
    halfPlaneShift w s - w = ((2 * w.re - 1 : ℝ) : ℂ) * (s - 1) := by
  apply Complex.ext
  · simp [halfPlaneShift]; ring
  · simp [halfPlaneShift]

/-- `T(s) + w̄ − 1 = (2σ − 1) s`. -/
theorem halfPlaneShift_add_conj (w s : ℂ) :
    halfPlaneShift w s + conj w - 1 = ((2 * w.re - 1 : ℝ) : ℂ) * s := by
  apply Complex.ext
  · simp [halfPlaneShift]; ring
  · simp [halfPlaneShift]

/-- The Blaschke coordinate of the centre `w`. -/
def blaschkeCoord (w ρ : ℂ) : ℂ := (ρ - w) / (ρ + conj w - 1)

theorem ne_zero_of_half_lt_re {w ρ : ℂ} (hw : 1 / 2 < w.re) (hρ : 1 / 2 < ρ.re) :
    ρ + conj w - 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- The strict Blaschke inequality `|ρ − w| < |ρ + w̄ − 1|` on the half-plane. -/
theorem norm_sub_lt_norm_add_conj {w ρ : ℂ} (hw : 1 / 2 < w.re) (hρ : 1 / 2 < ρ.re) :
    ‖ρ - w‖ < ‖ρ + conj w - 1‖ := by
  have h1 : ‖ρ - w‖ ^ 2 < ‖ρ + conj w - 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

theorem norm_blaschkeCoord_lt_one {w ρ : ℂ} (hw : 1 / 2 < w.re) (hρ : 1 / 2 < ρ.re) :
    ‖blaschkeCoord w ρ‖ < 1 := by
  rw [blaschkeCoord, norm_div, div_lt_one (norm_pos_iff.mpr (ne_zero_of_half_lt_re hw hρ))]
  exact norm_sub_lt_norm_add_conj hw hρ

/-- The Green kernel of the half-plane: `G(w, ρ) = log (|ρ + w̄ − 1| / |ρ − w|)`. -/
def greenKernel (w ρ : ℂ) : ℝ := Real.log (‖ρ + conj w - 1‖ / ‖ρ - w‖)

theorem greenKernel_eq_log_inv_blaschke (w ρ : ℂ) :
    greenKernel w ρ = Real.log ‖blaschkeCoord w ρ‖⁻¹ := by
  rw [greenKernel, blaschkeCoord, norm_div, inv_div]

theorem greenKernel_pos {w ρ : ℂ} (hw : 1 / 2 < w.re) (hρ : 1 / 2 < ρ.re) (hne : ρ ≠ w) :
    0 < greenKernel w ρ := by
  have hpos : 0 < ‖ρ - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  exact Real.log_pos (by rw [one_lt_div hpos]; exact norm_sub_lt_norm_add_conj hw hρ)

/-- The composite chart `u ↦ T(1/(1 − u))`. -/
def discChart (w u : ℂ) : ℂ := halfPlaneShift w (halfPlaneOfDisc u)

theorem blaschkeCoord_discChart {w : ℂ} (hw : 1 / 2 < w.re) {u : ℂ} (hu : u ≠ 1) :
    blaschkeCoord w (discChart w u) = u := by
  have hne : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hlam : ((2 * w.re - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * w.re - 1) ≠ 0 by linarith)
  have hs : halfPlaneOfDisc u ≠ 0 := inv_ne_zero hne
  rw [blaschkeCoord, discChart, halfPlaneShift_sub, halfPlaneShift_add_conj,
    mul_div_mul_left _ _ hlam, halfPlaneOfDisc]
  field_simp
  ring

theorem discChart_blaschkeCoord {w ρ : ℂ} (hw : 1 / 2 < w.re) (hρ : 1 / 2 < ρ.re) :
    discChart w (blaschkeCoord w ρ) = ρ := by
  set q : ℂ := ρ + conj w - 1 with hq
  have hq0 : q ≠ 0 := ne_zero_of_half_lt_re hw hρ
  have hlam : ((2 * w.re - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * w.re - 1) ≠ 0 by linarith)
  have hone : 1 - (ρ - w) / q = ((2 * w.re - 1 : ℝ) : ℂ) / q := by
    rw [eq_div_iff hq0, sub_mul, div_mul_cancel₀ _ hq0, one_mul, hq]
    push_cast
    have h := Complex.add_conj w
    push_cast at h
    linear_combination h
  rw [discChart, blaschkeCoord, ← hq, halfPlaneOfDisc, hone, inv_div]
  unfold halfPlaneShift
  rw [hq]
  field_simp
  apply Complex.ext <;> simp <;> ring

theorem re_discChart_gt {w u : ℂ} (hw : 1 / 2 < w.re) (hu : ‖u‖ < 1) :
    1 / 2 < (discChart w u).re := by
  rw [discChart, re_halfPlaneShift]
  have := re_halfPlaneOfDisc_gt hu
  nlinarith

/-- An entire function of quadratic growth on the closed half-plane. -/
structure IsHalfPlaneDatum (E : ℂ → ℂ) : Prop where
  diff : Differentiable ℂ E
  growth : ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → ‖E s‖ ≤ K * (‖s‖ + 2) ^ 2

/-- A centre: a nonzero point with `E` bounded below far along its horizontal ray. -/
structure IsCentre (E : ℂ → ℂ) (w : ℂ) : Prop where
  re_gt : 1 / 2 < w.re
  ne0 : E w ≠ 0
  ray : ∃ c σ₁ : ℝ, 0 < c ∧ ∀ σ : ℝ, σ₁ ≤ σ → c ≤ ‖E ((σ : ℂ) + (w.im : ℂ) * I)‖

variable {E : ℂ → ℂ}

theorem isDiscDatum_comp (hE : IsHalfPlaneDatum E) {w : ℂ} (hw : IsCentre E w) :
    IsDiscDatum (fun u => E (discChart w u)) := by
  have hs0 := hw.re_gt
  have hlam : 0 < 2 * w.re - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have hne : (1 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have h1 : DifferentiableWithinAt ℂ halfPlaneOfDisc {1}ᶜ u :=
      (((differentiableAt_const _).sub differentiableAt_id).inv hne).differentiableWithinAt
    have h2 : Differentiable ℂ (halfPlaneShift w) := by
      unfold halfPlaneShift; fun_prop
    exact (hE.diff _).comp_differentiableWithinAt u ((h2 _).comp_differentiableWithinAt u h1)
  · have h2 : Continuous (halfPlaneShift w) := by unfold halfPlaneShift; fun_prop
    exact hE.diff.continuous.measurable.comp
      (h2.measurable.comp ((measurable_const.sub measurable_id).inv))
  · simpa [discChart, halfPlaneOfDisc, halfPlaneShift_one] using hw.ne0
  · obtain ⟨K, hK1, hK⟩ := hE.growth
    set C : ℝ := 2 * w.re + 2 + ‖w‖ with hC
    have hC1 : 1 ≤ C := by have := norm_nonneg w; rw [hC]; linarith
    refine ⟨Real.log (K * C ^ 2) + 2 * Real.log 5, fun u hu hu1 => ?_⟩
    have hne : (1 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
    have hn0 : 0 < ‖1 - u‖ := norm_pos_iff.mpr hne
    have hn2 : ‖1 - u‖ ≤ 2 := by
      calc ‖1 - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have hs : ‖halfPlaneOfDisc u‖ = 1 / ‖1 - u‖ := by
      rw [halfPlaneOfDisc, norm_inv, one_div]
    have hbound : ‖halfPlaneOfDisc u‖ + 2 ≤ 5 / ‖1 - u‖ := by
      rw [hs, div_add' _ _ _ hn0.ne', div_le_div_iff_of_pos_right hn0]
      nlinarith
    have hre : 1 / 2 ≤ (halfPlaneShift w (halfPlaneOfDisc u)).re := by
      rw [re_halfPlaneShift]
      have := re_halfPlaneOfDisc_ge hu hu1
      nlinarith
    have hG := hK _ hre
    have hT := norm_halfPlaneShift_add_two_le hs0 (halfPlaneOfDisc u)
    have hKC : 1 ≤ K * C ^ 2 := by nlinarith
    have hlog0 : 0 ≤ Real.log (K * C ^ 2) := Real.log_nonneg hKC
    have hlog5 : 2 * Real.log ‖1 - u‖ ≤ 2 * Real.log 5 := by
      have := Real.log_le_log hn0 (by linarith : ‖1 - u‖ ≤ 5)
      linarith
    change Real.log ‖E (discChart w u)‖ ≤ _
    rcases eq_or_ne (E (discChart w u)) 0 with h0 | h0
    · rw [h0, norm_zero, Real.log_zero]
      linarith
    · have hpos : 0 < ‖E (discChart w u)‖ := norm_pos_iff.mpr h0
      have h1 : ‖E (discChart w u)‖ ≤ K * C ^ 2 * (5 / ‖1 - u‖) ^ 2 := by
        calc ‖E (discChart w u)‖ ≤ K * (‖halfPlaneShift w (halfPlaneOfDisc u)‖ + 2) ^ 2 := hG
          _ ≤ K * (C * (‖halfPlaneOfDisc u‖ + 2)) ^ 2 := by gcongr
          _ = K * C ^ 2 * (‖halfPlaneOfDisc u‖ + 2) ^ 2 := by ring
          _ ≤ K * C ^ 2 * (5 / ‖1 - u‖) ^ 2 := by gcongr
      have h2 := Real.log_le_log hpos h1
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_div (by norm_num)
        hn0.ne'] at h2
      push_cast at h2
      linarith
  · obtain ⟨c, σ₁, hc, hray⟩ := hw.ray
    -- the radius `x ↦ T(1/(1−x))` runs along the horizontal ray through `w`
    set σ₂ : ℝ := max 2 (((σ₁ - 1 / 2) / (2 * w.re - 1)) + 1 / 2) with hσ₂
    have hσ₂2 : 2 ≤ σ₂ := le_max_left _ _
    have hσ₂σ : ((σ₁ - 1 / 2) / (2 * w.re - 1)) + 1 / 2 ≤ σ₂ := le_max_right _ _
    refine ⟨c, 1 - σ₂⁻¹, hc, ?_, ?_, fun x hx hx1 => ?_⟩
    · have : σ₂⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hσ₂2
      norm_num at this ⊢
      linarith
    · have : 0 < σ₂⁻¹ := inv_pos.mpr (by linarith)
      linarith
    · have h1x : 0 < 1 - x := by linarith
      have hσx : σ₂ ≤ (1 - x)⁻¹ := by
        rw [le_inv_comm₀ (by linarith) h1x]
        linarith
      set σ : ℝ := (1 - x)⁻¹ with hσ
      have hchart : discChart w x = ((((2 * w.re - 1) * (σ - 1 / 2) + 1 / 2 : ℝ)) : ℂ) +
          (w.im : ℂ) * I := by
        have hs : halfPlaneOfDisc (x : ℂ) = (σ : ℂ) := by
          simp only [halfPlaneOfDisc, hσ]; push_cast; rfl
        rw [discChart, hs]
        unfold halfPlaneShift
        push_cast
        ring
      change c ≤ ‖E (discChart w x)‖
      rw [hchart]
      apply hray
      have h3 : (σ₁ - 1 / 2) / (2 * w.re - 1) ≤ σ - 1 / 2 := by linarith
      rw [div_le_iff₀ hlam] at h3
      nlinarith

/-- The multiplicity transported by the chart: `T ∘ (u ↦ 1/(1−u))` is a local biholomorphism. -/
theorem analyticOrderAt_comp_discChart {w u : ℂ} (hw : 1 / 2 < w.re) (hu : u ≠ 1) :
    analyticOrderAt (fun v => E (discChart w v)) u = analyticOrderAt E (discChart w u) := by
  have hne : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hl : (2 * w.re - 1) ≠ 0 := by linarith
  have hlC : ((2 * w.re - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl
  have hd : HasDerivAt (discChart w) (((2 * w.re - 1 : ℝ) : ℂ) * ((1 - u) ^ 2)⁻¹) u := by
    have h1 : HasDerivAt (fun v : ℂ => (1 - v)⁻¹) (((1 - u) ^ 2)⁻¹) u := by
      convert ((hasDerivAt_id u).const_sub (1 : ℂ)).inv hne using 1 <;> first | rfl | norm_num
    have h2 := (h1.sub_const (1 / 2 : ℂ)).const_mul ((2 * w.re - 1 : ℝ) : ℂ)
    have h3 := (h2.add_const (1 / 2 : ℂ)).add_const ((w.im : ℂ) * I)
    exact h3
  have han : AnalyticAt ℂ (discChart w) u := by
    have : AnalyticAt ℂ (fun v : ℂ => ((2 * w.re - 1 : ℝ) : ℂ) * ((1 - v)⁻¹ - 1 / 2) + 1 / 2 +
        (w.im : ℂ) * I) u := by
      have h0 : AnalyticAt ℂ (fun v : ℂ => (1 - v)⁻¹) u :=
        (analyticAt_const.sub analyticAt_id).inv hne
      exact (analyticAt_const.mul (h0.sub analyticAt_const)).add analyticAt_const |>.add
        analyticAt_const
    exact this
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := E) han
    (by rw [hd.deriv]; exact mul_ne_zero hlC (inv_ne_zero (pow_ne_zero 2 hne)))
  simpa [Function.comp_def] using h

/-- The zeros of `E` in the open half-plane. -/
abbrev RightZeros (E : ℂ → ℂ) := {ρ : ℂ // E ρ = 0 ∧ 1 / 2 < ρ.re}

/-- **The Poisson–Jensen identity.** The inner factor of `E` is the Blaschke product of its zeros:
the boundary logarithm is `P_w`-integrable and the Green potential of the zeros at `w`, with
multiplicity, converges to `∫ log|E| P_w − log|E(w)|`. -/
theorem hasSum_poissonJensen (hE : IsHalfPlaneDatum E) {w : ℂ} (hw : IsCentre E w) :
    Integrable (fun τ : ℝ => Real.log ‖E (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) ∧
      HasSum (fun ρ : RightZeros E => (analyticOrderNatAt E ρ : ℝ) * greenKernel w ρ)
        ((∫ τ : ℝ, Real.log ‖E (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) - Real.log ‖E w‖) := by
  have hs0 := hw.re_gt
  have hD := isDiscDatum_comp hE hw
  set Φ : ℂ → ℂ := fun u => E (discChart w u) with hΦ
  set F : ℝ → ℝ := fun τ => Real.log ‖E (1 / 2 + τ * I)‖ with hF
  have hcrit : ∀ t : ℝ, discChart w (circleMap 0 1 (criticalLineAngle t))
      = 1 / 2 + (((2 * w.re - 1) * t + w.im : ℝ) : ℂ) * I := by
    intro t
    rw [discChart, halfPlaneOfDisc_circleMap_criticalLineAngle, halfPlaneShift_criticalLine]
  obtain ⟨hiff, heq⟩ := circleAverage_shift_eq_poisson hs0 F
    (fun u => Real.log ‖Φ u‖) (fun t => by simp only [hΦ, hF, hcrit])
  have hint := hiff.mp hD.circleIntegrable
  refine ⟨hint, ?_⟩
  have hΦ0 : Φ 0 = E w := by simp [hΦ, discChart, halfPlaneOfDisc, halfPlaneShift_one]
  have hsum := hD.hasSum_discWeight
  rw [heq, hΦ0] at hsum
  -- transport from the disc to the zeros in the half-plane
  have hsupp : Function.support (discWeight Φ) ⊆ {u : ℂ | Φ u = 0 ∧ ‖u‖ < 1} := by
    intro u hu
    by_contra hz
    apply hu
    by_cases hb : ‖u‖ < 1
    · have hu0 : Φ u ≠ 0 := fun h0 => hz ⟨h0, hb⟩
      have hord : analyticOrderAt Φ u = 0 :=
        (hD.analyticAt (by rintro rfl; simp at hb)).analyticOrderAt_eq_zero.mpr hu0
      rw [discWeight, hD.discMult_eq_natOrder hb, analyticOrderNatAt, hord]
      simp
    · have hb' : u ∉ ball (0 : ℂ) 1 := by simpa [mem_ball_zero_iff] using hb
      simp [discWeight, discMult, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb']
  have hsub := (hasSum_subtype_iff_of_support_subset hsupp).mpr hsum
  let e : {u : ℂ | Φ u = 0 ∧ ‖u‖ < 1} ≃ RightZeros E :=
    { toFun := fun u => ⟨discChart w u, u.2.1, re_discChart_gt hs0 u.2.2⟩
      invFun := fun ρ => ⟨blaschkeCoord w ρ, by
        constructor
        · change E (discChart w (blaschkeCoord w ρ)) = 0
          rw [discChart_blaschkeCoord hs0 ρ.2.2]
          exact ρ.2.1
        · exact norm_blaschkeCoord_lt_one hs0 ρ.2.2⟩
      left_inv := fun u => by
        apply Subtype.ext
        exact blaschkeCoord_discChart hs0 (by rintro h; have := u.2.2; simp [h] at this)
      right_inv := fun ρ => by
        apply Subtype.ext
        exact discChart_blaschkeCoord hs0 ρ.2.2 }
  have ht := e.symm.hasSum_iff.mpr hsub
  have hfun : (((discWeight Φ) ∘ ((↑) : {u : ℂ | Φ u = 0 ∧ ‖u‖ < 1} → ℂ)) ∘ e.symm) =
      fun ρ : RightZeros E => (analyticOrderNatAt E ρ : ℝ) * greenKernel w ρ := by
    funext ρ
    have hb := norm_blaschkeCoord_lt_one hs0 ρ.2.2
    have hu1 : blaschkeCoord w ρ ≠ 1 := by
      intro h1
      rw [h1] at hb
      simp at hb
    change discWeight Φ (blaschkeCoord w ρ) = _
    rw [discWeight, hD.discMult_eq_natOrder hb, greenKernel_eq_log_inv_blaschke]
    have hord := analyticOrderAt_comp_discChart (E := E) hs0 hu1
    rw [discChart_blaschkeCoord hs0 ρ.2.2] at hord
    have hnat : analyticOrderNatAt Φ (blaschkeCoord w ρ) = analyticOrderNatAt E ρ := by
      simp only [analyticOrderNatAt, hΦ, hord]
    rw [hnat]
    push_cast
    rfl
  rw [hfun] at ht
  exact ht

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
