import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralComplexGamma
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralDeficientAsymptotics

/-!
# The sectorial projective limit

At complex time `z = R w` with `Re w > 0` the transported finite part of a smooth chart, normalized
by `R^a`, converges to the rotated terminal residue:

`R^a · η_a(e^{-Rw·} h) → c Γ(a) w^{-a} h(0)`,  `−1 < a < 0`.

The chart splits by Hadamard's lemma into its value at the origin, whose contribution rescales to
the rotated regularized Gamma integral, and a remainder, whose contribution is `O(1/R)`.  Along the
ray `w = e^{iθ}` the residue carries the phase `e^{-iaθ}`, whose angular slope is `−a`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology Complex

noncomputable section

variable {a : ℝ}

/-- The transported finite part at complex time. -/
def ctransportedFinitePart (c a : ℝ) (z : ℂ) (h : ℝ → ℝ) : ℂ :=
  (c : ℂ) * ((∫ s in Ioo (0 : ℝ) 1,
      (Complex.exp (-(z * s)) * (h s : ℂ) - (h 0 : ℂ)) * ((s ^ (a - 1) : ℝ) : ℂ)) +
    (h 0 : ℂ) / (a : ℂ))

/-- The cut integral at complex time. -/
def ccutIntegral (a : ℝ) (z : ℂ) : ℂ := ∫ s in Ioo (0 : ℝ) 1, cgammaDefect a z s

/-- The Hadamard remainder contribution at complex time. -/
def cremainderIntegral (a : ℝ) (z : ℂ) (r : ℝ → ℝ) : ℂ :=
  ∫ s in Ioo (0 : ℝ) 1, Complex.exp (-(z * s)) * (r s : ℂ) * ((s ^ a : ℝ) : ℂ)

/-! ## The Hadamard split -/

theorem csplit_integrand {h r : ℝ → ℝ} (hr : ∀ s, h s = h 0 + s * r s) {s : ℝ} (hs : 0 < s)
    (z : ℂ) (a : ℝ) :
    (Complex.exp (-(z * s)) * (h s : ℂ) - (h 0 : ℂ)) * ((s ^ (a - 1) : ℝ) : ℂ) =
      (h 0 : ℂ) * cgammaDefect a z s +
        Complex.exp (-(z * s)) * (r s : ℂ) * ((s ^ a : ℝ) : ℂ) := by
  have hsplit : ((s ^ a : ℝ) : ℂ) = (s : ℂ) * ((s ^ (a - 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, rpow_succ_split hs a]
  rw [hr s, cgammaDefect, hsplit]
  push_cast
  ring

theorem norm_cremainder_integrand (z : ℂ) (r : ℝ → ℝ) (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ‖Complex.exp (-(z * s)) * (r s : ℂ) * ((s ^ a : ℝ) : ℂ)‖ =
      Real.exp (-(z.re * s)) * |r s| * s ^ a := by
  have hre : (-(z * (s : ℂ))).re = -(z.re * s) := by simp
  have hpos : (0 : ℝ) < s ^ a := Real.rpow_pos_of_pos hs _
  rw [norm_mul, norm_mul, Complex.norm_exp, hre, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]

theorem integrableOn_cremainder (ha : -1 < a) {z : ℂ} (hz : 0 ≤ z.re) {r : ℝ → ℝ}
    (hrc : Continuous r) {B : ℝ} (hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B) :
    IntegrableOn (fun s : ℝ => Complex.exp (-(z * s)) * (r s : ℂ) * ((s ^ a : ℝ) : ℂ))
      (Ioo 0 1) := by
  refine Integrable.mono' (g := fun s : ℝ => B * s ^ a)
    ((integrableOn_rpow_of_neg_one_lt ha).const_mul _) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine ContinuousOn.mul (ContinuousOn.mul ?_ (by fun_prop)) ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
    · refine Complex.continuous_ofReal.continuousOn.comp ?_ (mapsTo_univ _ _)
      exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx.1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have hpos : (0 : ℝ) < s ^ a := Real.rpow_pos_of_pos hs0 _
    rw [norm_cremainder_integrand z r a hs0]
    have hexp1 : Real.exp (-(z.re * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hexp0 : (0 : ℝ) < Real.exp (-(z.re * s)) := Real.exp_pos _
    have hrb : |r s| ≤ B := hB s hs
    have hstep : Real.exp (-(z.re * s)) * |r s| ≤ B := by
      nlinarith [abs_nonneg (r s)]
    exact mul_le_mul_of_nonneg_right hstep hpos.le

theorem ctransportedFinitePart_split (c : ℝ) (ha : -1 < a) (ha0 : a < 0) {z : ℂ}
    (hz : 0 < z.re) {h r : ℝ → ℝ} (hr : ∀ s, h s = h 0 + s * r s) (hrc : Continuous r) {B : ℝ}
    (hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B) :
    ctransportedFinitePart c a z h =
      (c : ℂ) * ((h 0 : ℂ) * (ccutIntegral a z + 1 / (a : ℂ)) + cremainderIntegral a z r) := by
  have hint1 : IntegrableOn (fun s : ℝ => (h 0 : ℂ) * cgammaDefect a z s) (Ioo 0 1) :=
    (((integrableOn_cgammaDefect ha ha0 hz).mono_set Ioo_subset_Ioi_self)).const_mul _
  have hint2 := integrableOn_cremainder ha hz.le hrc hB
  have hcongr : (∫ s in Ioo (0 : ℝ) 1,
        (Complex.exp (-(z * s)) * (h s : ℂ) - (h 0 : ℂ)) * ((s ^ (a - 1) : ℝ) : ℂ)) =
      ∫ s in Ioo (0 : ℝ) 1, ((h 0 : ℂ) * cgammaDefect a z s +
        Complex.exp (-(z * s)) * (r s : ℂ) * ((s ^ a : ℝ) : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    exact csplit_integrand hr hs.1 z a
  rw [ctransportedFinitePart, hcongr, integral_add hint1 hint2, integral_const_mul]
  rw [show (∫ s in Ioo (0 : ℝ) 1, cgammaDefect a z s) = ccutIntegral a z from rfl,
    show (∫ s in Ioo (0 : ℝ) 1, Complex.exp (-(z * s)) * (r s : ℂ) * ((s ^ a : ℝ) : ℂ)) =
      cremainderIntegral a z r from rfl]
  ring

/-! ## Rescaling the cut integral -/

theorem ccutIntegral_eq_interval (a : ℝ) (z : ℂ) :
    ccutIntegral a z = ∫ s in (0 : ℝ)..1, cgammaDefect a z s := by
  rw [ccutIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

theorem cgammaDefect_scaling {R : ℝ} (hR : 0 < R) (w : ℂ) (a : ℝ) {s : ℝ} (hs : 0 < s) :
    cgammaDefect a ((R : ℂ) * w) s =
      (((R ^ (a - 1) : ℝ)⁻¹ : ℝ) : ℂ) * cgammaDefect a w (R * s) := by
  have hprod : ((R * s) ^ (a - 1) : ℝ) = R ^ (a - 1) * s ^ (a - 1) :=
    Real.mul_rpow hR.le hs.le
  have hne : (R ^ (a - 1) : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR _)
  have harg : -((R : ℂ) * w * (s : ℂ)) = -(w * ((R * s : ℝ) : ℂ)) := by push_cast; ring
  have hneC : ((R ^ (a - 1) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hne
  rw [cgammaDefect, cgammaDefect, harg, hprod]
  push_cast
  field_simp

/-- The rescaled cut integral is the truncated rotated Gamma integral. -/
theorem rpow_mul_ccutIntegral {R : ℝ} (hR : 0 < R) (w : ℂ) (a : ℝ) :
    ((R ^ a : ℝ) : ℂ) * ccutIntegral a ((R : ℂ) * w) =
      ∫ t in (0 : ℝ)..R, cgammaDefect a w t := by
  have hne : R ≠ 0 := ne_of_gt hR
  have hcongr : (∫ s in (0 : ℝ)..1, cgammaDefect a ((R : ℂ) * w) s) =
      ∫ s in (0 : ℝ)..1, (((R ^ (a - 1) : ℝ)⁻¹ : ℝ) : ℂ) * cgammaDefect a w (R * s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · simp only [cgammaDefect, ← h]
      norm_num
    · exact cgammaDefect_scaling hR w a h
  have hsub : (∫ s in (0 : ℝ)..1, cgammaDefect a w (R * s)) =
      R⁻¹ • ∫ t in (R * 0)..(R * 1), cgammaDefect a w t :=
    intervalIntegral.integral_comp_mul_left _ hne
  rw [mul_zero, mul_one, Complex.real_smul] at hsub
  rw [ccutIntegral_eq_interval, hcongr, intervalIntegral.integral_const_mul, hsub]
  have hcollapse : ((R ^ a : ℝ) : ℂ) * ((((R ^ (a - 1) : ℝ)⁻¹ : ℝ) : ℂ) * ((R⁻¹ : ℝ) : ℂ)) = 1 := by
    have hcoe : ((R ^ a : ℝ) : ℂ) * ((((R ^ (a - 1) : ℝ)⁻¹ : ℝ) : ℂ) * ((R⁻¹ : ℝ) : ℂ)) =
        ((R ^ a * ((R ^ (a - 1))⁻¹ * R⁻¹) : ℝ) : ℂ) := by push_cast; ring
    rw [hcoe]
    have hreal : (R ^ a * ((R ^ (a - 1))⁻¹ * R⁻¹) : ℝ) = 1 := by
      rw [← Real.rpow_neg_one R, ← Real.rpow_neg hR.le, ← Real.rpow_add hR, ← Real.rpow_add hR]
      have hz : a + (-(a - 1) + -1) = 0 := by ring
      rw [hz, Real.rpow_zero]
    rw [hreal, Complex.ofReal_one]
  calc ((R ^ a : ℝ) : ℂ) * ((((R ^ (a - 1) : ℝ)⁻¹ : ℝ) : ℂ) *
        (((R⁻¹ : ℝ) : ℂ) * ∫ t in (0 : ℝ)..R, cgammaDefect a w t))
      = (((R ^ a : ℝ) : ℂ) * ((((R ^ (a - 1) : ℝ)⁻¹ : ℝ) : ℂ) * ((R⁻¹ : ℝ) : ℂ))) *
          ∫ t in (0 : ℝ)..R, cgammaDefect a w t := by ring
    _ = ∫ t in (0 : ℝ)..R, cgammaDefect a w t := by rw [hcollapse, one_mul]

/-! ## The remainder is negligible -/

theorem norm_cremainderIntegral_le (ha : -1 < a) {z : ℂ} (hz : 0 < z.re) {r : ℝ → ℝ}
    (hrc : Continuous r) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B) :
    ‖cremainderIntegral a z r‖ ≤ B * (z.re ^ (-(a + 1)) * Real.Gamma (a + 1)) := by
  have hint := integrableOn_cremainder ha hz.le hrc hB
  have hstep : ‖cremainderIntegral a z r‖ ≤
      ∫ s in Ioo (0 : ℝ) 1, B * (Real.exp (-(z.re * s)) * s ^ a) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on hint.norm ?_ measurableSet_Ioo fun s hs => ?_
    · exact ((integrableOn_expScaled ha hz).mono_set Ioo_subset_Ioi_self).const_mul B
    · have hs0 : (0 : ℝ) < s := hs.1
      have hpos : (0 : ℝ) < s ^ a := Real.rpow_pos_of_pos hs0 _
      have hexp0 : (0 : ℝ) < Real.exp (-(z.re * s)) := Real.exp_pos _
      rw [norm_cremainder_integrand z r a hs0]
      have hrb : |r s| ≤ B := hB s hs
      calc Real.exp (-(z.re * s)) * |r s| * s ^ a
          ≤ Real.exp (-(z.re * s)) * B * s ^ a :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrb hexp0.le) hpos.le
        _ = B * (Real.exp (-(z.re * s)) * s ^ a) := by ring
  have hsub : (∫ s in Ioo (0 : ℝ) 1, B * (Real.exp (-(z.re * s)) * s ^ a)) ≤
      B * (z.re ^ (-(a + 1)) * Real.Gamma (a + 1)) := by
    rw [integral_const_mul, ← integral_expScaled ha hz]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    refine setIntegral_mono_set (integrableOn_expScaled ha hz) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0 : ℝ) < s := hs
      positivity
    · exact (Ioo_subset_Ioi_self : (Ioo (0 : ℝ) 1) ≤ Ioi 0).eventuallyLE
  linarith

theorem tendsto_normalized_cremainder (ha : -1 < a) {w : ℂ} (hw : 0 < w.re) {r : ℝ → ℝ}
    (hrc : Continuous r) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B) :
    Tendsto (fun R : ℝ => ((R ^ a : ℝ) : ℂ) * cremainderIntegral a ((R : ℂ) * w) r) atTop
      (𝓝 0) := by
  set C : ℝ := B * (w.re ^ (-(a + 1)) * Real.Gamma (a + 1)) with hCdef
  have hlim : Tendsto (fun R : ℝ => C / R) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hzre : ((R : ℂ) * w).re = R * w.re := by simp
  have hz : 0 < ((R : ℂ) * w).re := by rw [hzre]; positivity
  have hRa : (0 : ℝ) < R ^ a := Real.rpow_pos_of_pos hR _
  have hbound := norm_cremainderIntegral_le ha hz hrc hB0 hB
  rw [hzre] at hbound
  have hsplit : (R * w.re) ^ (-(a + 1)) = R ^ (-(a + 1)) * w.re ^ (-(a + 1)) :=
    Real.mul_rpow hR.le hw.le
  rw [hsplit] at hbound
  have hcollapse : R ^ a * R ^ (-(a + 1)) = R⁻¹ := by
    rw [← Real.rpow_add hR, ← Real.rpow_neg_one R]
    congr 1
    ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRa]
  calc R ^ a * ‖cremainderIntegral a ((R : ℂ) * w) r‖
      ≤ R ^ a * (B * (R ^ (-(a + 1)) * w.re ^ (-(a + 1)) * Real.Gamma (a + 1))) :=
        mul_le_mul_of_nonneg_left hbound hRa.le
    _ = C * (R ^ a * R ^ (-(a + 1))) := by rw [hCdef]; ring
    _ = C / R := by rw [hcollapse]; ring

/-! ## The sectorial limit -/

theorem tendsto_rpow_ofReal_atTop (ha0 : a < 0) :
    Tendsto (fun R : ℝ => ((R ^ a : ℝ) : ℂ)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun R : ℝ => R ^ a) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := -a) (by linarith)
    simpa using h
  have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  simp only [Function.comp_def, Complex.ofReal_zero] at h2
  exact h2

/-- **The sectorial projective limit.**  Along every ray of the right half-plane the normalized
transported finite part converges to the rotated terminal residue. -/
theorem tendsto_ctransportedFinitePart (c : ℝ) (ha : -1 < a) (ha0 : a < 0) {w : ℂ}
    (hw : 0 < w.re) {h : ℝ → ℝ} (hh : IsSmoothReal h) :
    Tendsto (fun R : ℝ => ((R ^ a : ℝ) : ℂ) * ctransportedFinitePart c a ((R : ℂ) * w) h) atTop
      (𝓝 ((c : ℂ) * ((Real.Gamma a : ℂ) * w ^ ((-a : ℝ) : ℂ) * (h 0 : ℂ)))) := by
  set r : ℝ → ℝ := hadamardAvg 0 (deriv h) with hrdef
  have hrS : IsSmoothReal r := isSmoothReal_hadamardAvg 0 hh.derivSmooth
  have hrc : Continuous r := hrS.continuous
  have hr : ∀ s, h s = h 0 + s * r s := hadamard_eq hh
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hrc.continuousOn
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B := fun s hs =>
    le_trans (hB₀ s ⟨hs.1.le, hs.2.le⟩) (le_max_left _ _)
  have hcut : Tendsto (fun R : ℝ => ((R ^ a : ℝ) : ℂ) *
      (ccutIntegral a ((R : ℂ) * w) + 1 / (a : ℂ))) atTop (𝓝 (cgammaIntegral a w)) := by
    have htrunc : Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, cgammaDefect a w t) atTop
        (𝓝 (cgammaIntegral a w)) :=
      intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_cgammaDefect ha ha0 hw)
        tendsto_id
    have htail : Tendsto (fun R : ℝ => ((R ^ a : ℝ) : ℂ) * (1 / (a : ℂ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_ofReal_atTop ha0).mul_const (1 / (a : ℂ))
    have hsum := htrunc.add htail
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [← rpow_mul_ccutIntegral hR w a]
    ring
  have hrem := tendsto_normalized_cremainder ha hw hrc hB0 hB
  have hmain : Tendsto (fun R : ℝ => (c : ℂ) * ((h 0 : ℂ) * (((R ^ a : ℝ) : ℂ) *
      (ccutIntegral a ((R : ℂ) * w) + 1 / (a : ℂ))) +
      ((R ^ a : ℝ) : ℂ) * cremainderIntegral a ((R : ℂ) * w) r)) atTop
      (𝓝 ((c : ℂ) * ((h 0 : ℂ) * cgammaIntegral a w + 0))) :=
    Tendsto.const_mul _ ((hcut.const_mul (h 0 : ℂ)).add hrem)
  rw [add_zero, cgammaIntegral_eq ha ha0 hw] at hmain
  have hval : (c : ℂ) * ((h 0 : ℂ) * ((Real.Gamma a : ℂ) * w ^ ((-a : ℝ) : ℂ))) =
      (c : ℂ) * ((Real.Gamma a : ℂ) * w ^ ((-a : ℝ) : ℂ) * (h 0 : ℂ)) := by ring
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hz : 0 < ((R : ℂ) * w).re := by
    have : ((R : ℂ) * w).re = R * w.re := by simp
    rw [this]
    positivity
  rw [ctransportedFinitePart_split c ha ha0 hz hr hrc hB]
  ring

/-! ## The angular phase -/

theorem cpow_exp_mul_I (a : ℝ) {θ : ℝ} (hθ1 : -Real.pi < θ) (hθ2 : θ ≤ Real.pi) :
    (Complex.exp ((θ : ℂ) * Complex.I)) ^ ((-a : ℝ) : ℂ) =
      Complex.exp (((-(a * θ) : ℝ) : ℂ) * Complex.I) := by
  have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have him : ((θ : ℂ) * Complex.I).im = θ := by simp
  rw [Complex.cpow_def_of_ne_zero hne, Complex.log_exp (by rw [him]; exact hθ1)
    (by rw [him]; exact hθ2)]
  congr 1
  push_cast
  ring

theorem arg_terminal_phase {u : ℝ} (h1 : -Real.pi < u) (h2 : u ≤ Real.pi) :
    Complex.arg (Complex.exp ((u : ℂ) * Complex.I)) = u := by
  rw [Complex.arg_exp_mul_I]
  exact (toIocMod_eq_self Real.two_pi_pos).2 ⟨h1, by linarith⟩

/-- **The angular phase slope of the terminal residue is `−a`.** -/
theorem hasDerivAt_terminal_phase (a : ℝ) {θ : ℝ} (hθ : |θ| < Real.pi)
    (haθ : |a * θ| < Real.pi) :
    HasDerivAt (fun u : ℝ =>
      Complex.arg ((Complex.exp ((u : ℂ) * Complex.I)) ^ ((-a : ℝ) : ℂ))) (-a) θ := by
  have h0 : HasDerivAt (fun u : ℝ => a * u) a θ := by
    simpa using (hasDerivAt_id θ).const_mul a
  have hbase : HasDerivAt (fun u : ℝ => -(a * u)) (-a) θ := h0.neg
  refine hbase.congr_of_eventuallyEq ?_
  have hopen : IsOpen {u : ℝ | |u| < Real.pi ∧ |a * u| < Real.pi} := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt (continuous_abs) continuous_const
    · exact isOpen_lt (continuous_abs.comp (continuous_const.mul continuous_id)) continuous_const
  have hmem : θ ∈ {u : ℝ | |u| < Real.pi ∧ |a * u| < Real.pi} := ⟨hθ, haθ⟩
  filter_upwards [hopen.mem_nhds hmem] with u hu
  obtain ⟨hu1, hu2⟩ := hu
  have hu1' := abs_lt.1 hu1
  have hu2' := abs_lt.1 hu2
  rw [cpow_exp_mul_I a hu1'.1 hu1'.2.le,
    arg_terminal_phase (u := -(a * u)) (by linarith [hu2'.2]) (by linarith [hu2'.1])]

/-- Below the cut the phase slope is the remaining distance to the death cut. -/
theorem phase_slope_eq_deathCut_sub {β ρ : ℝ} (hobs : ρ ∈ observerLine β) (ha : ρ + β < 0) :
    deathCut β = -β ∧ -(ρ + β) = deathCut β - ρ := by
  have hobs' : 0 < 2 * ρ + β := (mem_observerLine_iff β ρ).1 hobs
  have hβ : β < 0 := by linarith
  have hcut : deathCut β = -β := by
    rw [deathCut, max_eq_right]
    linarith
  exact ⟨hcut, by rw [hcut]; ring⟩

/-- **The terminal residue along the ray `w = e^{iθ}` carries the phase `e^{-iaθ}`.** -/
theorem tendsto_ctransportedFinitePart_ray (c : ℝ) (ha : -1 < a) (ha0 : a < 0) {θ : ℝ}
    (hθ1 : -(Real.pi / 2) < θ) (hθ2 : θ < Real.pi / 2) {h : ℝ → ℝ} (hh : IsSmoothReal h) :
    Tendsto (fun R : ℝ => ((R ^ a : ℝ) : ℂ) *
        ctransportedFinitePart c a ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) h) atTop
      (𝓝 ((c : ℂ) * ((Real.Gamma a : ℂ) *
        Complex.exp (((-(a * θ) : ℝ) : ℂ) * Complex.I) * (h 0 : ℂ)))) := by
  have hre : (Complex.exp ((θ : ℂ) * Complex.I)).re = Real.cos θ := by
    rw [Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have hw : 0 < (Complex.exp ((θ : ℂ) * Complex.I)).re := by
    rw [hre]
    exact Real.cos_pos_of_mem_Ioo ⟨hθ1, hθ2⟩
  have hmain := tendsto_ctransportedFinitePart c ha ha0 hw hh
  rwa [cpow_exp_mul_I a (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at hmain

end

end GaloisForLFunctions.HTGeometry.Interfinity
