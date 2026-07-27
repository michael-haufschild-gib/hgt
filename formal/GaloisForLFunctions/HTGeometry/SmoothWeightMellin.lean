import GaloisForLFunctions.HTGeometry.SmoothWeight
import Mathlib.Analysis.MellinTransform

/-!
# The Mellin transform of the smooth cutoff

The cutoff vanishes beyond `N + H` and is bounded by one, so its Mellin integrand is dominated by
`x^{σ-1}` on `(0, N+H]` and vanishes past that.  Hence the Mellin transform converges for every
`σ > 0` — in particular on both the initial line `Re s = c > 1` and the shifted line
`Re s = Θ + ε`, which is what makes the contour shift meaningful.
-/

open Complex MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The Mellin integrand of the cutoff is continuous on the positive ray. -/
theorem continuousOn_mellin_smoothWeight (N H : ℝ) (s : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
  · refine ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const ?_
    left
    simpa using hx0
  · exact (Complex.continuous_ofReal.comp
      (smoothWeight_contDiff N H (n := 0)).continuous).continuousAt

/-- Beyond `N + H` the integrand vanishes. -/
theorem mellin_smoothWeight_eq_zero_of_le {N H : ℝ} (hH : 0 < H) {x : ℝ} (hx : N + H ≤ x) (s : ℂ) :
    (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ) = 0 := by
  rw [smoothWeight_eq_zero hH hx]
  simp

/-- **Convergence of the Mellin transform of the cutoff** on every half-plane `Re s > 0`. -/
theorem integrableOn_mellin_smoothWeight {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) {s : ℂ}
    (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)) (Ioi 0) := by
  have hNH : (0 : ℝ) ≤ N + H := by linarith
  have hsplit : Ioc (0 : ℝ) (N + H) ∪ Ioi (N + H) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi hNH
  rw [← hsplit]
  refine IntegrableOn.union ?_ ?_
  · -- dominated by `x ^ (σ - 1)`, integrable near the origin
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
        (volume.restrict (Ioc (0 : ℝ) (N + H))) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact (continuousOn_mellin_smoothWeight N H s).mono Ioc_subset_Ioi_self
    have hdom : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Ioc (0 : ℝ) (N + H)) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hNH]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    refine Integrable.mono' hdom hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (smoothWeight_nonneg N H x)]
    have hpow : (0 : ℝ) < x ^ (s.re - 1) := Real.rpow_pos_of_pos hx0 _
    have h1 : smoothWeight N H x ≤ 1 := smoothWeight_le_one N H x
    nlinarith [hpow, h1, smoothWeight_nonneg N H x]
  · -- the integrand vanishes there
    refine (integrableOn_zero (μ := volume) (s := Ioi (N + H))).congr_fun ?_ measurableSet_Ioi
    intro x hx
    exact (mellin_smoothWeight_eq_zero_of_le hH (le_of_lt hx) s).symm

/-- The Mellin transform of the cutoff, as an integral over `(0, ∞)`. -/
theorem mellin_smoothWeight_eq {N H : ℝ} (s : ℂ) :
    mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s
      = ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ) := by
  rw [mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [smul_eq_mul]

/-- **Integration by parts for the cutoff's Mellin integral, on a finite interval.**  The boundary
term at `N + H` vanishes because the cutoff does; the one at `δ` is `δ^s / s` because the cutoff is
still `1` there. -/
theorem intervalIntegral_mellin_smoothWeight_byParts {N H : ℝ} (hH : 0 < H)
    {s : ℂ} (hs : s ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδN : δ ≤ N) :
    (∫ x in δ..(N + H), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
      = -((δ : ℂ) ^ s / s)
        - ∫ x in δ..(N + H), ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s) := by
  have hδM : δ ≤ N + H := by linarith
  have huIcc : Set.uIcc δ (N + H) = Set.Icc δ (N + H) := Set.uIcc_of_le hδM
  have hne : ∀ x ∈ Set.uIcc δ (N + H), x ≠ 0 := by
    intro x hx
    rw [huIcc] at hx
    exact ne_of_gt (lt_of_lt_of_le hδ hx.1)
  have hsm1 : s - 1 ≠ -1 := by
    intro h
    exact hs (by linear_combination h)
  have hu : ∀ x ∈ Set.uIcc δ (N + H),
      HasDerivAt (fun y : ℝ => ((smoothWeight N H y : ℝ) : ℂ))
        (((deriv (smoothWeight N H) x : ℝ) : ℂ)) x := by
    intro x _
    exact HasDerivAt.ofReal_comp
      (((smoothWeight_contDiff N H (n := 1)).differentiable (by norm_num)) x).hasDerivAt
  have hv : ∀ x ∈ Set.uIcc δ (N + H),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ s / s) ((x : ℂ) ^ (s - 1)) x := by
    intro x hx
    have h := hasDerivAt_ofReal_cpow_const' (x := x) (r := s - 1) (hne x hx) hsm1
    simpa using h
  have hu' : IntervalIntegrable
      (fun x : ℝ => ((deriv (smoothWeight N H) x : ℝ) : ℂ)) MeasureTheory.volume δ (N + H) := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact Complex.continuous_ofReal.comp
      ((smoothWeight_contDiff N H (n := 2)).continuous_deriv (by norm_num))
  have hv' : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (s - 1)) MeasureTheory.volume δ (N + H) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const ?_
    left
    simpa using lt_of_lt_of_le hδ hx.1
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hzero : smoothWeight N H (N + H) = 0 := smoothWeight_eq_zero hH le_rfl
  have hone : smoothWeight N H δ = 1 := smoothWeight_eq_one hH hδN
  rw [hzero, hone] at key
  have hcomm : (∫ x in δ..(N + H), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
      = ∫ x in δ..(N + H), ((smoothWeight N H x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [hcomm, key]
  push_cast
  ring

/-- The Mellin integrand of the cutoff contributes `O(δ^σ)` near the origin. -/
theorem norm_integral_Ioc_zero_le {N H : ℝ} {s : ℂ} (hs : 0 < s.re) {δ : ℝ} (hδ : 0 < δ) :
    ‖∫ x in Ioc (0 : ℝ) δ, (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)‖
      ≤ δ ^ s.re / s.re := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Ioc (0 : ℝ) δ) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hb : ∀ x ∈ Ioc (0 : ℝ) δ,
      ‖(x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)‖ ≤ x ^ (s.re - 1) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (smoothWeight_nonneg N H x)]
    have hpow : (0 : ℝ) < x ^ (s.re - 1) := Real.rpow_pos_of_pos hx0 _
    nlinarith [smoothWeight_le_one N H x, smoothWeight_nonneg N H x, hpow]
  have hnormint : IntegrableOn
      (fun x : ℝ => ‖(x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)‖) (Ioc (0 : ℝ) δ) := by
    refine Integrable.mono' hint ?_ ?_
    · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc).norm
      exact (continuousOn_mellin_smoothWeight N H s).mono Ioc_subset_Ioi_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hb x hx
  have hval : ∫ x in Ioc (0 : ℝ) δ, x ^ (s.re - 1) = δ ^ s.re / s.re := by
    rw [← intervalIntegral.integral_of_le hδ.le, integral_rpow (Or.inl (by linarith))]
    rw [Real.zero_rpow (by linarith)]
    have : s.re - 1 + 1 = s.re := by ring
    rw [this]
    ring
  calc ‖∫ x in Ioc (0 : ℝ) δ, (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)‖
      ≤ ∫ x in Ioc (0 : ℝ) δ, ‖(x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioc (0 : ℝ) δ, x ^ (s.re - 1) :=
        setIntegral_mono_on hnormint hint measurableSet_Ioc hb
    _ = δ ^ s.re / s.re := hval

/-- Splitting the Mellin integral of the cutoff at a positive cut. -/
theorem integral_Ioi_split {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) {s : ℂ} (hs : 0 < s.re)
    {δ : ℝ} (hδ : 0 < δ) (hδM : δ ≤ N + H) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
      = (∫ x in Ioc (0 : ℝ) δ, (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
        + ∫ x in Ioc δ (N + H), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ) := by
  have hall := integrableOn_mellin_smoothWeight hN hH hs
  have htail : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
      = ∫ x in Ioc (0 : ℝ) (N + H), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ) := by
    have hsplit : Ioc (0 : ℝ) (N + H) ∪ Ioi (N + H) = Ioi (0 : ℝ) :=
      Ioc_union_Ioi_eq_Ioi (by linarith)
    rw [← hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hall.mono_set (by rw [← hsplit]; exact subset_union_left))
      (hall.mono_set (by rw [← hsplit]; exact subset_union_right))]
    have hzero : ∫ x in Ioi (N + H), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      exact mellin_smoothWeight_eq_zero_of_le hH (le_of_lt hx) s
    rw [hzero, add_zero]
  rw [htail]
  have hsplit2 : Ioc (0 : ℝ) δ ∪ Ioc δ (N + H) = Ioc (0 : ℝ) (N + H) :=
    Ioc_union_Ioc_eq_Ioc hδ.le hδM
  rw [← hsplit2]
  refine setIntegral_union ?_ measurableSet_Ioc ?_ ?_
  · rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.mpr hx'.1)
  · exact hall.mono_set (fun x hx => hx.1)
  · exact hall.mono_set (fun x hx => lt_trans hδ hx.1)

/-- The cutoff's derivative vanishes to the left of `N`. -/
theorem deriv_smoothWeight_eq_zero_of_lt {N H : ℝ} (hH : 0 < H) {x : ℝ} (hx : x < N) :
    deriv (smoothWeight N H) x = 0 := by
  have heq : smoothWeight N H =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact smoothWeight_eq_one hH (le_of_lt hy)
  rw [heq.deriv_eq, deriv_const]

/-- The cutoff's derivative vanishes to the right of `N + H`. -/
theorem deriv_smoothWeight_eq_zero_of_gt {N H : ℝ} (hH : 0 < H) {x : ℝ} (hx : N + H < x) :
    deriv (smoothWeight N H) x = 0 := by
  have heq : smoothWeight N H =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact smoothWeight_eq_zero hH (le_of_lt hy)
  rw [heq.deriv_eq, deriv_const]

/-- The derivative integrand is continuous on the positive ray. -/
theorem continuousOn_deriv_integrand (N H : ℝ) {s : ℂ} (hs : s ≠ 0) :
    ContinuousOn (fun x : ℝ => ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s))
      (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ (ContinuousAt.div ?_ ?_ hs))
  · exact (Complex.continuous_ofReal.comp
      ((smoothWeight_contDiff N H (n := 2)).continuous_deriv (by norm_num))).continuousAt
  · exact ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
      (Or.inl (by simpa using hx0))
  · exact continuousAt_const

/-- The derivative integrand vanishes off `[N, N+H]`. -/
theorem deriv_integrand_eq_zero_right {N H : ℝ} (hH : 0 < H) {x : ℝ} (hx : N + H < x) (s : ℂ) :
    ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s) = 0 := by
  rw [deriv_smoothWeight_eq_zero_of_gt hH hx]
  simp

/-- The derivative integrand contributes nothing below `N`. -/
theorem deriv_integrand_eq_zero_left {N H : ℝ} (hH : 0 < H) {x : ℝ} (hx : x < N) (s : ℂ) :
    ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s) = 0 := by
  rw [deriv_smoothWeight_eq_zero_of_lt hH hx]
  simp

/-- The derivative integrand is integrable on the positive ray: it is continuous and supported in
the compact interval `[N, N+H]`, which is bounded away from the origin. -/
theorem integrableOn_deriv_integrand {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {s : ℂ} (hs : s ≠ 0) :
    IntegrableOn (fun x : ℝ => ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s))
      (Ioi 0) := by
  have hsplit : Ioc (0 : ℝ) (N + H) ∪ Ioi (N + H) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi (by linarith)
  rw [← hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hsplit2 : Ioc (0 : ℝ) (N / 2) ∪ Ioc (N / 2) (N + H) = Ioc (0 : ℝ) (N + H) :=
      Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
    rw [← hsplit2]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_zero (μ := volume) (s := Ioc (0 : ℝ) (N / 2))).congr_fun ?_
        measurableSet_Ioc
      intro x hx
      exact (deriv_integrand_eq_zero_left hH (by linarith [hx.2]) s).symm
    · refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
      refine ContinuousOn.integrableOn_Icc ?_
      refine (continuousOn_deriv_integrand N H hs).mono ?_
      intro x hx
      exact lt_of_lt_of_le (by linarith) hx.1
  · refine (integrableOn_zero (μ := volume) (s := Ioi (N + H))).congr_fun ?_ measurableSet_Ioi
    intro x hx
    exact (deriv_integrand_eq_zero_right hH hx s).symm

/-- Below `N` the derivative integral is empty, above `N+H` it is too. -/
theorem integral_deriv_integrand_eq {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {s : ℂ} (hs : s ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hδN : δ < N) :
    (∫ x in Ioi (0 : ℝ), ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s))
      = ∫ x in Ioc δ (N + H), ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s) := by
  have hall := integrableOn_deriv_integrand hN hH hs
  have hsplit : Ioc (0 : ℝ) δ ∪ Ioi δ = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hδ.le
  rw [← hsplit, setIntegral_union (by
      rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.mpr hx'))
    measurableSet_Ioi (hall.mono_set (fun x hx => hx.1))
    (hall.mono_set (fun x hx => lt_trans hδ hx))]
  have hzero : ∫ x in Ioc (0 : ℝ) δ,
      ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact deriv_integrand_eq_zero_left hH (lt_of_le_of_lt hx.2 hδN) s
  rw [hzero, zero_add]
  have hsplit2 : Ioc δ (N + H) ∪ Ioi (N + H) = Ioi δ :=
    Ioc_union_Ioi_eq_Ioi (by linarith)
  rw [← hsplit2, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hall.mono_set (fun x hx => lt_trans hδ hx.1))
    (hall.mono_set (fun x hx => lt_trans hδ (lt_trans (by linarith) hx)))]
  have hzero2 : ∫ x in Ioi (N + H),
      ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact deriv_integrand_eq_zero_right hH hx s
  rw [hzero2, add_zero]

/-- **Integration by parts for the cutoff's Mellin transform, on `(0,∞)`.**  The boundary term at
the origin vanishes for every `Re s > 0`. -/
theorem mellin_smoothWeight_byParts {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
      = - ∫ x in Ioi (0 : ℝ), ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s) := by
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hsnorm : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr hsne
  have hkey : ∀ δ : ℝ, 0 < δ → δ < N →
      ‖(∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
        + ∫ x in Ioi (0 : ℝ), ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s)‖
      ≤ δ ^ s.re / s.re + δ ^ s.re / ‖s‖ := by
    intro δ hδ hδN
    have hδM : δ ≤ N + H := by linarith
    have hF := integral_Ioi_split hN.le hH hs hδ hδM
    have hG := integral_deriv_integrand_eq hN hH hsne hδ hδN
    have hIBP := intervalIntegral_mellin_smoothWeight_byParts hH hsne hδ hδN.le
    rw [intervalIntegral.integral_of_le hδM, intervalIntegral.integral_of_le hδM] at hIBP
    rw [hF, hIBP, hG]
    have hsimp : ((∫ x in Ioc (0 : ℝ) δ, (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
        + (-((δ : ℂ) ^ s / s)
          - ∫ x in Ioc δ (N + H),
              ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s)))
        + (∫ x in Ioc δ (N + H), ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s))
        = (∫ x in Ioc (0 : ℝ) δ, (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
          - ((δ : ℂ) ^ s / s) := by ring
    rw [hsimp]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_integral_Ioc_zero_le (N := N) (H := H) hs hδ
    have h2 : ‖((δ : ℂ) ^ s / s)‖ = δ ^ s.re / ‖s‖ := by
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hδ]
    rw [h2]
    linarith [h1]
  have hle : ‖(∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ))
      + ∫ x in Ioi (0 : ℝ), ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s)‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hCpos : (0 : ℝ) < 1 / s.re + 1 / ‖s‖ := by positivity
    have hrpos : (0 : ℝ) < ε / (1 / s.re + 1 / ‖s‖) := by positivity
    refine le_trans (hkey (min (N / 2) ((ε / (1 / s.re + 1 / ‖s‖)) ^ (1 / s.re)))
      (lt_min (by linarith) (Real.rpow_pos_of_pos hrpos _))
      (lt_of_le_of_lt (min_le_left _ _) (by linarith))) ?_
    set δ : ℝ := min (N / 2) ((ε / (1 / s.re + 1 / ‖s‖)) ^ (1 / s.re)) with hδdef
    have hδpos : (0 : ℝ) < δ :=
      lt_min (by linarith) (Real.rpow_pos_of_pos hrpos _)
    have hpow : δ ^ s.re ≤ ε / (1 / s.re + 1 / ‖s‖) := by
      have h1 : δ ≤ (ε / (1 / s.re + 1 / ‖s‖)) ^ (1 / s.re) := min_le_right _ _
      have h2 : δ ^ s.re ≤ ((ε / (1 / s.re + 1 / ‖s‖)) ^ (1 / s.re)) ^ s.re :=
        Real.rpow_le_rpow hδpos.le h1 hs.le
      rw [← Real.rpow_mul hrpos.le] at h2
      rw [show (1 / s.re) * s.re = 1 by field_simp] at h2
      rwa [Real.rpow_one] at h2
    have hcollect : δ ^ s.re / s.re + δ ^ s.re / ‖s‖ = δ ^ s.re * (1 / s.re + 1 / ‖s‖) := by
      field_simp
    rw [hcollect, zero_add]
    calc δ ^ s.re * (1 / s.re + 1 / ‖s‖)
        ≤ (ε / (1 / s.re + 1 / ‖s‖)) * (1 / s.re + 1 / ‖s‖) :=
          mul_le_mul_of_nonneg_right hpow hCpos.le
      _ = ε := by field_simp
  have hzero := norm_le_zero_iff.mp hle
  linear_combination hzero

/-- **Integration by parts with vanishing boundary values.**  This is the step that iterates: after
one integration by parts the integrand carries `w'`, which vanishes at both ends of any interval
containing its support, so every further step is boundary-term free. -/
theorem intervalIntegral_byParts_of_vanishing {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hv : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) v) (hva : v a = 0) (hvb : v b = 0)
    {s : ℂ} (hs : s ≠ 0) :
    (∫ x in a..b, ((v x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))
      = - ∫ x in a..b, ((deriv v x : ℝ) : ℂ) * ((x : ℂ) ^ s / s) := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hne : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    rw [huIcc] at hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hsm1 : s - 1 ≠ -1 := by
    intro h
    exact hs (by linear_combination h)
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => ((v y : ℝ) : ℂ)) (((deriv v x : ℝ) : ℂ)) x := by
    intro x _
    exact HasDerivAt.ofReal_comp ((hv.differentiable (by norm_num) x).hasDerivAt)
  have hvd : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ s / s) ((x : ℂ) ^ (s - 1)) x := by
    intro x hx
    have h := hasDerivAt_ofReal_cpow_const' (x := x) (r := s - 1) (hne x hx) hsm1
    simpa using h
  have hu' : IntervalIntegrable (fun x : ℝ => ((deriv v x : ℝ) : ℂ)) MeasureTheory.volume a b := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact Complex.continuous_ofReal.comp (hv.continuous_deriv (by norm_num))
  have hv' : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (s - 1)) MeasureTheory.volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const ?_
    left
    simpa using lt_of_lt_of_le ha hx.1
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hvd hu' hv'
  rw [hva, hvb] at key
  simpa using key

/-- Iterated derivatives of a smooth function are smooth. -/
theorem contDiff_top_iteratedDeriv {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv j v) := by
  induction j with
  | zero => simpa [iteratedDeriv_zero] using hv
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact ContDiff.deriv' ih

/-- **`j`-fold integration by parts.**  For a smooth function all of whose derivatives vanish at
both endpoints, the Mellin-type integral gains a factor `(s(s+1)⋯(s+j-1))^{-1}` and passes to the
`j`-th derivative. -/
theorem intervalIntegral_byParts_iterate {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvan : ∀ i : ℕ, iteratedDeriv i v a = 0 ∧ iteratedDeriv i v b = 0)
    {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    (∫ x in a..b, ((v x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))
      = (-1) ^ j / (∏ i ∈ Finset.range j, (s + (i : ℂ))) *
        ∫ x in a..b, ((iteratedDeriv j v x : ℝ) : ℂ) * (x : ℂ) ^ (s + (j : ℂ) - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hsj : s + (j : ℂ) ≠ 0 := by
        intro h
        have hre : (s + (j : ℂ)).re = 0 := by rw [h]; simp
        rw [Complex.add_re, Complex.natCast_re] at hre
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have hstep := intervalIntegral_byParts_of_vanishing (v := iteratedDeriv j v) hab ha
        ((contDiff_top_iteratedDeriv hv j).of_le (WithTop.coe_le_coe.mpr le_top)) (hvan j).1 (hvan j).2
        (s := s + (j : ℂ)) hsj
      have hexp : ∀ x : ℝ, (x : ℂ) ^ (s + (j : ℂ) - 1) = (x : ℂ) ^ (s + (j : ℂ) - 1) := fun _ => rfl
      rw [ih, hstep]
      have hsucc : (iteratedDeriv (j + 1) v) = deriv (iteratedDeriv j v) := iteratedDeriv_succ
      have hcast : ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) := by push_cast; ring
      have hprod : (∏ i ∈ Finset.range (j + 1), (s + (i : ℂ)))
          = (∏ i ∈ Finset.range j, (s + (i : ℂ))) * (s + (j : ℂ)) := Finset.prod_range_succ _ _
      rw [hprod, hsucc]
      have hpow : ∀ x : ℝ, (x : ℂ) ^ (s + (j : ℂ)) = (x : ℂ) ^ (s + ((j + 1 : ℕ) : ℂ) - 1) := by
        intro x
        congr 1
        push_cast
        ring
      rw [intervalIntegral.integral_congr (g := fun x : ℝ =>
        (((deriv (iteratedDeriv j v) x : ℝ) : ℂ) * ((x : ℂ) ^ (s + ((j + 1 : ℕ) : ℂ) - 1)))
          / (s + (j : ℂ))) (fun x _ => by rw [hpow x]; ring)]
      rw [intervalIntegral.integral_div]
      field_simp
      ring

/-- Every derivative of positive order of the cutoff vanishes to the left of `N`. -/
theorem iteratedDeriv_smoothWeight_eq_zero_of_lt {N H : ℝ} (hH : 0 < H) {i : ℕ} (hi : i ≠ 0)
    {x : ℝ} (hx : x < N) : iteratedDeriv i (smoothWeight N H) x = 0 := by
  have heq : smoothWeight N H =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact smoothWeight_eq_one hH (le_of_lt hy)
  rw [heq.iteratedDeriv_eq i, iteratedDeriv_const, if_neg hi]

/-- Every derivative of positive order of the cutoff vanishes to the right of `N + H`. -/
theorem iteratedDeriv_smoothWeight_eq_zero_of_gt {N H : ℝ} (hH : 0 < H) {i : ℕ} (hi : i ≠ 0)
    {x : ℝ} (hx : N + H < x) : iteratedDeriv i (smoothWeight N H) x = 0 := by
  have heq : smoothWeight N H =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact smoothWeight_eq_zero hH (le_of_lt hy)
  rw [heq.iteratedDeriv_eq i, iteratedDeriv_const, if_neg hi]

/-- All derivatives of `w'` vanish at any pair of endpoints straddling the support. -/
theorem iteratedDeriv_deriv_smoothWeight_vanishing {N H : ℝ} (hH : 0 < H) {a b : ℝ}
    (ha : a < N) (hb : N + H < b) (i : ℕ) :
    iteratedDeriv i (deriv (smoothWeight N H)) a = 0 ∧
      iteratedDeriv i (deriv (smoothWeight N H)) b = 0 := by
  rw [← iteratedDeriv_succ']
  exact ⟨iteratedDeriv_smoothWeight_eq_zero_of_lt hH (Nat.succ_ne_zero i) ha,
    iteratedDeriv_smoothWeight_eq_zero_of_gt hH (Nat.succ_ne_zero i) hb⟩

/-- The cutoff's derivative is smooth. -/
theorem contDiff_deriv_smoothWeight (N H : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv (smoothWeight N H)) :=
  ContDiff.deriv' (smoothWeight_contDiff N H (n := ⊤))

/-- The derivative integral, over an interval straddling the support. -/
theorem integral_deriv_integrand_eq' {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {s : ℂ} (hs : s ≠ 0)
    {b : ℝ} (hb : N + H < b) :
    (∫ x in Ioi (0 : ℝ), ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s))
      = ∫ x in (N / 2)..b, ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s) := by
  have hall := integrableOn_deriv_integrand hN hH hs
  have hbase := integral_deriv_integrand_eq hN hH hs (δ := N / 2) (by linarith) (by linarith)
  rw [hbase, intervalIntegral.integral_of_le (by linarith : N / 2 ≤ b)]
  have hsplit : Ioc (N / 2) (N + H) ∪ Ioc (N + H) b = Ioc (N / 2) b :=
    Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  rw [← hsplit, setIntegral_union (by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.mpr hx'.1))
    measurableSet_Ioc
    (hall.mono_set (fun x hx => lt_trans (by linarith : (0 : ℝ) < N / 2) hx.1))
    (hall.mono_set (fun x hx => lt_trans (by linarith : (0 : ℝ) < N + H) hx.1))]
  have hzero : ∫ x in Ioc (N + H) b,
      ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact deriv_integrand_eq_zero_right hH hx.1 s
  rw [hzero, add_zero]

/-- **The `j`-fold form of the cutoff's Mellin transform.**  Taking norms, the factor
`‖s‖ ∏_{i<j} ‖s+1+i‖` is exactly what the iterated integration by parts produces. -/
theorem norm_mellin_smoothWeight_mul_eq {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {s : ℂ}
    (hs : 0 < s.re) (j : ℕ) :
    ‖s‖ * (∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) *
        ‖∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)‖
      = ‖∫ x in (N / 2)..(N + H + 1),
          ((iteratedDeriv j (deriv (smoothWeight N H)) x : ℝ) : ℂ) *
            (x : ℂ) ^ (s + 1 + (j : ℂ) - 1)‖ := by
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hb : N + H < N + H + 1 := by linarith
  have hstep1 := mellin_smoothWeight_byParts hN hH hs
  have hstep2 := integral_deriv_integrand_eq' hN hH hsne hb
  -- pull the constant `1/s` out of the interval integral
  have hpull : (∫ x in (N / 2)..(N + H + 1),
      ((deriv (smoothWeight N H) x : ℝ) : ℂ) * ((x : ℂ) ^ s / s))
      = (∫ x in (N / 2)..(N + H + 1),
          ((deriv (smoothWeight N H) x : ℝ) : ℂ) * (x : ℂ) ^ (s + 1 - 1)) / s := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have : s + 1 - 1 = s := by ring
    rw [this]
    ring
  have hiter := intervalIntegral_byParts_iterate (v := deriv (smoothWeight N H))
    (a := N / 2) (b := N + H + 1) (by linarith) (by linarith)
    (contDiff_deriv_smoothWeight N H)
    (iteratedDeriv_deriv_smoothWeight_vanishing hH (by linarith) hb)
    (s := s + 1) (by simpa using by linarith [hs] : (0 : ℝ) < (s + 1).re) j
  rw [hstep1, hstep2, hpull, hiter]
  rw [norm_neg, norm_div, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow]
  have hprodnorm : ‖∏ i ∈ Finset.range j, (s + 1 + (i : ℂ))‖
      = ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖ := norm_prod _ _
  rw [hprodnorm]
  have hsnorm : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr hsne
  have hprodpos : (0 : ℝ) < ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖ := by
    refine Finset.prod_pos fun i _ => ?_
    refine norm_pos_iff.mpr ?_
    intro h
    have hre : (s + 1 + (i : ℂ)).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.add_re, Complex.one_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  field_simp

/-- **Decay of the cutoff's Mellin transform.**  For every order `j` there is a constant with
`‖s‖ (∏_{i<j} ‖s+1+i‖) ‖W(s)‖ ≤ C` on the strip `0 < Re s ≤ σmax`; since the product is at least
`|t|^j`, this is decay of order `j+1` in `|t|`. -/
theorem exists_bound_mellin_smoothWeight {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ) (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 < s.re → s.re ≤ σmax →
      ‖s‖ * (∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) *
        ‖∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ((smoothWeight N H x : ℝ) : ℂ)‖ ≤ C := by
  obtain ⟨Cj, hCj, hbound⟩ := exists_bound_iteratedDeriv_smoothWeight hH N (j + 1)
  have hb1 : (1 : ℝ) ≤ N + H + 1 := by linarith
  have hb0 : (0 : ℝ) < N + H + 1 := by linarith
  set M : ℝ := Cj / H ^ (j + 1) * (N + H + 1) ^ (σmax + (j : ℝ)) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : (0 : ℝ) ≤ Cj / H ^ (j + 1) := by positivity
    positivity
  refine ⟨M * |N + H + 1 - N / 2|, by positivity, fun s hs hsmax => ?_⟩
  rw [norm_mellin_smoothWeight_mul_eq hN hH hs j]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  have hxmem : x ∈ Set.Ioc (N / 2) (N + H + 1) := by
    rw [Set.uIoc_of_le (by linarith)] at hx
    exact hx
  have hx0 : (0 : ℝ) < x := lt_trans (by linarith : (0 : ℝ) < N / 2) hxmem.1
  have hxb : x ≤ N + H + 1 := hxmem.2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hre : (s + 1 + (j : ℂ) - 1).re = s.re + (j : ℝ) := by
    simp
    ring
  rw [hre]
  have hderiv : |iteratedDeriv j (deriv (smoothWeight N H)) x| ≤ Cj / H ^ (j + 1) := by
    rw [← iteratedDeriv_succ']
    exact hbound x
  have hexp1 : x ^ (s.re + (j : ℝ)) ≤ (N + H + 1) ^ (s.re + (j : ℝ)) := by
    refine Real.rpow_le_rpow hx0.le hxb ?_
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hexp2 : (N + H + 1) ^ (s.re + (j : ℝ)) ≤ (N + H + 1) ^ (σmax + (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  have hpowpos : (0 : ℝ) < x ^ (s.re + (j : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hCjH : (0 : ℝ) ≤ Cj / H ^ (j + 1) := by positivity
  calc |iteratedDeriv j (deriv (smoothWeight N H)) x| * x ^ (s.re + (j : ℝ))
      ≤ (Cj / H ^ (j + 1)) * x ^ (s.re + (j : ℝ)) :=
        mul_le_mul_of_nonneg_right hderiv hpowpos.le
    _ ≤ (Cj / H ^ (j + 1)) * (N + H + 1) ^ (σmax + (j : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_trans hexp1 hexp2) hCjH
    _ = M := by rw [hM]

end GaloisForLFunctions.HTGeometry
