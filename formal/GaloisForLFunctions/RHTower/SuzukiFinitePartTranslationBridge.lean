import GaloisForLFunctions.RHTower.SuzukiRestrictedWeilFinitePart
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Suzuki finite part as a translation-difference energy

Suzuki's equation (2.6) requires identifying the interval Hadamard finite part with a
full-line logarithmic Fourier multiplier.  This module proves the geometric half of that
identification.  For a source intrinsically supported in `(-a,a)`, the finite-part energy is

`(1/2) ∫₀^{2a} h⁻¹ ∫ℝ |u(x)-u(x+h)|² dx dh - log(2a) ∫ℝ |u|²`.

The proof does not split a conditionally convergent kernel.  It first symmetrizes the full-line
translation energy.  At each `x`, the two resulting divided differences are regular at `h = 0`;
their exterior pieces are then the elementary logarithmic boundary tails.  This makes every
Fubini interchange absolutely integrable.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Full-line real translation-difference energy. -/
def suzukiRealTranslationDifferenceEnergy (u : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ x : ℝ, (u x - u (x + h)) ^ 2

private def suzukiSymmetricDividedKernel (u : ℝ → ℝ) (h x : ℝ) : ℝ :=
  u x * ((2 * u x - u (x + h) - u (x - h)) / h)

private theorem core_eq_zero_of_not_mem_aperture {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) {x : ℝ} (hx : x ∉ Ioo (-a) a) : u x = 0 := by
  by_contra hux
  exact hx (u.support_subset_aperture hux)

private theorem core_square_integrable {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Integrable (fun x : ℝ => u x ^ 2) := by
  have hsupp : Function.support (fun x : ℝ => u x ^ 2) ⊆
      Icc (-u.supportRadius) u.supportRadius := by
    intro x hx
    exact u.support_subset (fun hzero => hx (by simp [hzero]))
  exact (u.continuous.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)

private theorem core_cross_integrable {a : ℝ} (u : SuzukiRestrictedWeilCore a) (h : ℝ) :
    Integrable (fun x : ℝ => u x * u (x + h)) := by
  have hsupp : HasCompactSupport (fun x : ℝ => u x * u (x + h)) :=
    u.hasCompactSupport.mul_right
  exact (u.continuous.mul (u.continuous.comp (continuous_id.add continuous_const)))
    |>.integrable_of_hasCompactSupport hsupp

private theorem core_cross_sub_integrable {a : ℝ} (u : SuzukiRestrictedWeilCore a) (h : ℝ) :
    Integrable (fun x : ℝ => u x * u (x - h)) := by
  have hsupp : HasCompactSupport (fun x : ℝ => u x * u (x - h)) :=
    u.hasCompactSupport.mul_right
  exact (u.continuous.mul (u.continuous.comp (continuous_id.sub continuous_const)))
    |>.integrable_of_hasCompactSupport hsupp

private theorem core_shift_square_integrable {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) (h : ℝ) :
    Integrable (fun x : ℝ => u (x + h) ^ 2) :=
  (core_square_integrable u).comp_add_right h

private theorem core_mass_interval_eq {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    (∫ x in (-a)..a, u x ^ 2) = ∫ x : ℝ, u x ^ 2 := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hux : u x ≠ 0 := fun hzero => hx (by simp [hzero])
  have hxa := u.support_subset_aperture hux
  exact ⟨hxa.1, hxa.2.le⟩

private theorem translationDifferenceEnergy_eq_symmetric_integral {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) (h : ℝ) :
    suzukiRealTranslationDifferenceEnergy u h =
      ∫ x in (-a)..a, u x * (2 * u x - u (x + h) - u (x - h)) := by
  have hu2 := core_square_integrable u
  have hu2shift := core_shift_square_integrable u h
  have hcross := core_cross_integrable u h
  have hcrossSub := core_cross_sub_integrable u h
  have hshiftSq : (∫ x : ℝ, u (x + h) ^ 2) = ∫ x : ℝ, u x ^ 2 := by
    simpa using integral_add_right_eq_self (μ := volume) (fun x : ℝ => u x ^ 2) h
  have hcrossShift : (∫ x : ℝ, u x * u (x - h)) =
      ∫ x : ℝ, u x * u (x + h) := by
    have hs := integral_sub_right_eq_self (μ := volume)
      (fun x : ℝ => u (x + h) * u x) h
    simpa [sub_add_cancel, mul_comm] using hs
  have hdiff : suzukiRealTranslationDifferenceEnergy u h =
      2 * (∫ x : ℝ, u x ^ 2) - 2 * (∫ x : ℝ, u x * u (x + h)) := by
    unfold suzukiRealTranslationDifferenceEnergy
    calc
      (∫ x : ℝ, (u x - u (x + h)) ^ 2) =
          ∫ x : ℝ, (u x ^ 2 + u (x + h) ^ 2) - 2 * (u x * u (x + h)) := by
            refine integral_congr_ae (ae_of_all _ fun x => by ring)
      _ = ((∫ x : ℝ, u x ^ 2) + ∫ x : ℝ, u (x + h) ^ 2) -
          2 * (∫ x : ℝ, u x * u (x + h)) := by
            calc
              (∫ x : ℝ, (u x ^ 2 + u (x + h) ^ 2) -
                  2 * (u x * u (x + h))) =
                  (∫ x : ℝ, u x ^ 2 + u (x + h) ^ 2) -
                    ∫ x : ℝ, 2 * (u x * u (x + h)) :=
                      integral_sub (hu2.add hu2shift) (hcross.const_mul 2)
              _ = ((∫ x : ℝ, u x ^ 2) + ∫ x : ℝ, u (x + h) ^ 2) -
                  2 * (∫ x : ℝ, u x * u (x + h)) := by
                    rw [integral_add hu2 hu2shift,
                      MeasureTheory.integral_const_mul]
      _ = 2 * (∫ x : ℝ, u x ^ 2) - 2 * (∫ x : ℝ, u x * u (x + h)) := by
            rw [hshiftSq]
            ring
  rw [hdiff]
  have hsupp : Function.support
      (fun x : ℝ => u x * (2 * u x - u (x + h) - u (x - h))) ⊆ Ioc (-a) a := by
    intro x hx
    have hux : u x ≠ 0 := by
      intro hzero
      exact hx (by simp [hzero])
    have hxa := u.support_subset_aperture hux
    exact ⟨hxa.1, hxa.2.le⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  have hreprInt : (∫ x : ℝ,
      u x * (2 * u x - u (x + h) - u (x - h))) =
          (∫ x : ℝ, 2 * (u x ^ 2)) - (∫ x : ℝ, u x * u (x + h)) -
            ∫ x : ℝ, u x * u (x - h) := by
    calc
      (∫ x : ℝ, u x * (2 * u x - u (x + h) - u (x - h))) =
          ∫ x : ℝ, (2 * u x ^ 2 - u x * u (x + h)) - u x * u (x - h) := by
            refine integral_congr_ae (ae_of_all _ fun x => by ring)
      _ = (∫ x : ℝ, 2 * u x ^ 2 - u x * u (x + h)) -
          ∫ x : ℝ, u x * u (x - h) :=
            integral_sub ((hu2.const_mul 2).sub hcross) hcrossSub
      _ = ((∫ x : ℝ, 2 * u x ^ 2) - ∫ x : ℝ, u x * u (x + h)) -
          ∫ x : ℝ, u x * u (x - h) := by
            rw [integral_sub (hu2.const_mul 2) hcross]
  rw [hreprInt, hcrossShift, MeasureTheory.integral_const_mul]
  ring

private theorem exists_core_joint_bounds {a : ℝ} (_ha : 0 < a)
    (u : SuzukiRestrictedWeilCore a) :
    ∃ U D : ℝ, 0 ≤ U ∧ 0 ≤ D ∧
      (∀ x ∈ Icc (-a) a, |u x| ≤ U) ∧
      (∀ x ∈ Icc (-3 * a) (3 * a), ∀ y ∈ Icc (-3 * a) (3 * a),
        |u y - u x| ≤ D * |y - x|) := by
  obtain ⟨U0, hU0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    u.continuous.continuousOn
  let U := max U0 0
  have hU : ∀ x ∈ Icc (-a) a, |u x| ≤ U := by
    intro x hx
    have hxU : |u x| ≤ U0 := by simpa [Real.norm_eq_abs] using hU0 x hx
    exact hxU.trans (le_max_left _ _)
  have hud : Continuous (deriv u) := (contDiff_infty_iff_deriv.mp u.smooth).2.continuous
  obtain ⟨D0, hD0⟩ := isCompact_Icc.exists_bound_of_continuousOn hud.continuousOn
  let D := max D0 0
  have hD0' : 0 ≤ D := le_max_right _ _
  have hderiv : ∀ z ∈ Icc (-3 * a) (3 * a), ‖deriv u z‖ ≤ D := by
    intro z hz
    exact (hD0 z hz).trans (le_max_left _ _)
  refine ⟨U, D, le_max_right _ _, hD0', hU, ?_⟩
  intro x hx y hy
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (u.smooth.differentiable (by simp)).differentiableAt) hderiv
      (convex_Icc (-3 * a) (3 * a)) hx hy
  simpa [Real.norm_eq_abs] using hmv

private theorem integrableOn_symmetricDividedKernel_prod {a : ℝ} (ha : 0 < a)
    (u : SuzukiRestrictedWeilCore a) :
    IntegrableOn (Function.uncurry (suzukiSymmetricDividedKernel u))
      (Ioc 0 (2 * a) ×ˢ Ioc (-a) a) volume := by
  obtain ⟨U, D, hU0, hD0, hU, hlip⟩ := exists_core_joint_bounds ha u
  have hmeas : Measurable (Function.uncurry (suzukiSymmetricDividedKernel u)) := by
    unfold suzukiSymmetricDividedKernel
    have hu : Measurable fun p : ℝ × ℝ => u p.2 :=
      u.continuous.measurable.comp measurable_snd
    have hnum : Measurable fun p : ℝ × ℝ =>
        2 * u p.2 - u (p.2 + p.1) - u (p.2 - p.1) :=
      ((measurable_const.mul hu).sub
        (u.continuous.measurable.comp (measurable_snd.add measurable_fst))).sub
        (u.continuous.measurable.comp (measurable_snd.sub measurable_fst))
    exact hu.mul (hnum.div measurable_fst)
  have hfinite : volume (Ioc 0 (2 * a) ×ˢ Ioc (-a) a) ≠ ⊤ := by
    refine (lt_of_le_of_lt
      (measure_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := U * (2 * D)) hfinite
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  rcases p with ⟨h, x⟩
  have hh : h ∈ Ioc 0 (2 * a) := hp.1
  have hx : x ∈ Ioc (-a) a := hp.2
  have hxA : x ∈ Icc (-a) a := Ioc_subset_Icc_self hx
  have hxp : x + h ∈ Icc (-3 * a) (3 * a) := by constructor <;> linarith [hx.1, hx.2, hh.1, hh.2]
  have hxm : x - h ∈ Icc (-3 * a) (3 * a) := by constructor <;> linarith [hx.1, hx.2, hh.1, hh.2]
  have hx3 : x ∈ Icc (-3 * a) (3 * a) := by constructor <;> linarith [hx.1, hx.2, ha]
  have hpBound := hlip x hx3 (x + h) hxp
  have hmBound := hlip x hx3 (x - h) hxm
  have habsh : |h| = h := abs_of_pos hh.1
  have hp' : |u x - u (x + h)| ≤ D * h := by
    rw [abs_sub_comm]
    calc
      |u (x + h) - u x| ≤ D * |x + h - x| := hpBound
      _ = D * h := by rw [show x + h - x = h by ring, habsh]
  have hm' : |u x - u (x - h)| ≤ D * h := by
    rw [abs_sub_comm]
    calc
      |u (x - h) - u x| ≤ D * |x - h - x| := hmBound
      _ = D * h := by rw [show x - h - x = -h by ring, abs_neg, habsh]
  have hnum : |2 * u x - u (x + h) - u (x - h)| ≤ 2 * D * h := by
    calc
      |2 * u x - u (x + h) - u (x - h)| =
          |(u x - u (x + h)) + (u x - u (x - h))| := by ring_nf
      _ ≤ |u x - u (x + h)| + |u x - u (x - h)| := abs_add_le _ _
      _ ≤ D * h + D * h := add_le_add hp' hm'
      _ = 2 * D * h := by ring
  have hquot : |(2 * u x - u (x + h) - u (x - h)) / h| ≤ 2 * D := by
    rw [abs_div, habsh]
    exact (div_le_iff₀ hh.1).2 (by nlinarith)
  unfold Function.uncurry suzukiSymmetricDividedKernel
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hU x hxA) hquot (abs_nonneg _) hU0

private theorem integral_symmetricDividedKernel_swap {a : ℝ} (ha : 0 < a)
    (u : SuzukiRestrictedWeilCore a) :
    (∫ h in (0 : ℝ)..(2 * a), ∫ x in (-a)..a,
        suzukiSymmetricDividedKernel u h x) =
      ∫ x in (-a)..a, ∫ h in (0 : ℝ)..(2 * a),
        suzukiSymmetricDividedKernel u h x := by
  have hint := integrableOn_symmetricDividedKernel_prod ha u
  have hprod : Integrable (Function.uncurry (suzukiSymmetricDividedKernel u))
      ((volume.restrict (Ioc 0 (2 * a))).prod (volume.restrict (Ioc (-a) a))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← IntegrableOn]
    exact hint
  have hswap := integral_integral_swap hprod
  simpa [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * a by linarith),
    intervalIntegral.integral_of_le (show -a ≤ a by linarith)] using hswap

private theorem continuous_dslope_core {a x : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Continuous (dslope (u : ℝ → ℝ) x) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = x
  · subst y
    exact continuousAt_dslope_same.mpr
      (u.smooth.differentiable (by simp)).differentiableAt
  · exact (continuousAt_dslope_of_ne hy).mpr u.continuous.continuousAt

private theorem right_divided_intervalIntegrable {a x b : ℝ} (hb : 0 ≤ b)
    (u : SuzukiRestrictedWeilCore a) :
    IntervalIntegrable (fun h : ℝ => (u x - u (x + h)) / h) volume 0 b := by
  have hc : Continuous (fun h : ℝ => -dslope (u : ℝ → ℝ) x (x + h)) :=
    (continuous_dslope_core u).comp (continuous_const.add continuous_id) |>.neg
  refine (hc.intervalIntegrable 0 b).congr ?_
  intro h hh
  rw [uIoc_of_le hb] at hh
  have hh0 : h ≠ 0 := hh.1.ne'
  have hne : x + h ≠ x := by
    intro heq
    apply hh0
    linarith
  dsimp
  rw [dslope_of_ne _ hne, slope_def_field,
    show x + h - x = h by ring]
  field_simp [hh0]
  ring

private theorem left_divided_intervalIntegrable {a x b : ℝ} (hb : 0 ≤ b)
    (u : SuzukiRestrictedWeilCore a) :
    IntervalIntegrable (fun h : ℝ => (u x - u (x - h)) / h) volume 0 b := by
  have hc : Continuous (fun h : ℝ => dslope (u : ℝ → ℝ) x (x - h)) :=
    (continuous_dslope_core u).comp (continuous_const.sub continuous_id)
  refine (hc.intervalIntegrable 0 b).congr ?_
  intro h hh
  rw [uIoc_of_le hb] at hh
  have hh0 : h ≠ 0 := hh.1.ne'
  have hne : x - h ≠ x := by
    intro heq
    apply hh0
    linarith
  dsimp
  rw [dslope_of_ne _ hne, slope_def_field,
    show x - h - x = -h by ring]
  field_simp [hh0]
  ring

private theorem right_divided_integral_eq {a x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (-a) a)
    (u : SuzukiRestrictedWeilCore a) :
    (∫ h in (0 : ℝ)..(2 * a), (u x - u (x + h)) / h) =
      (∫ y in x..a, (u x - u y) / (y - x)) +
        u x * (Real.log (2 * a) - Real.log (a - x)) := by
  have hb : 0 ≤ 2 * a := by linarith
  have hcut : 0 ≤ a - x := by linarith [hx.2]
  have hcutle : a - x ≤ 2 * a := by linarith [hx.1]
  have hall := right_divided_intervalIntegrable hb u (x := x)
  have hfirst := hall.mono_set (by
    rw [uIcc_of_le hcut, uIcc_of_le hb]
    intro h hh
    exact ⟨hh.1, hh.2.trans hcutle⟩)
  have htail := hall.mono_set (by
    rw [uIcc_of_le (show a - x ≤ 2 * a by exact hcutle), uIcc_of_le hb]
    intro h hh
    exact ⟨hcut.trans hh.1, hh.2⟩)
  have hsplit := integral_add_adjacent_intervals hfirst htail
  rw [← hsplit]
  have hchange : (∫ h in (0 : ℝ)..(a - x), (u x - u (x + h)) / h) =
      ∫ y in x..a, (u x - u y) / (y - x) := by
    have hc := intervalIntegral.integral_comp_add_right
      (fun y : ℝ => (u x - u y) / (y - x)) x
      (a := (0 : ℝ)) (b := a - x)
    simpa [add_sub_cancel_left, add_comm] using hc
  rw [hchange]
  have htailPoint : (∫ h in (a - x)..(2 * a), (u x - u (x + h)) / h) =
      ∫ h in (a - x)..(2 * a), u x * (1 / h) := by
    refine intervalIntegral.integral_congr fun h hh => ?_
    have hh' : a - x ≤ h := by
      have := (mem_uIcc.mp hh)
      rcases this with h | h <;> linarith
    have hzero : u (x + h) = 0 := core_eq_zero_of_not_mem_aperture u (by
      intro hmem
      linarith [hmem.2])
    rw [hzero]
    ring
  rw [htailPoint, intervalIntegral.integral_const_mul]
  have hzero : 0 ∉ uIcc (a - x) (2 * a) := by
    rw [uIcc_of_le hcutle]
    intro hz
    simp only [mem_Icc] at hz
    linarith [hx.2]
  rw [integral_one_div hzero, Real.log_div (by positivity) (by linarith [hx.2])]

private theorem left_divided_integral_eq {a x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (-a) a)
    (u : SuzukiRestrictedWeilCore a) :
    (∫ h in (0 : ℝ)..(2 * a), (u x - u (x - h)) / h) =
      (∫ y in (-a)..x, (u x - u y) / (x - y)) +
        u x * (Real.log (2 * a) - Real.log (a + x)) := by
  have hb : 0 ≤ 2 * a := by linarith
  have hcut : 0 ≤ a + x := by linarith [hx.1]
  have hcutle : a + x ≤ 2 * a := by linarith [hx.2]
  have hall := left_divided_intervalIntegrable hb u (x := x)
  have hfirst := hall.mono_set (by
    rw [uIcc_of_le hcut, uIcc_of_le hb]
    intro h hh
    exact ⟨hh.1, hh.2.trans hcutle⟩)
  have htail := hall.mono_set (by
    rw [uIcc_of_le hcutle, uIcc_of_le hb]
    intro h hh
    exact ⟨hcut.trans hh.1, hh.2⟩)
  have hsplit := integral_add_adjacent_intervals hfirst htail
  rw [← hsplit]
  have hchange : (∫ h in (0 : ℝ)..(a + x), (u x - u (x - h)) / h) =
      ∫ y in (-a)..x, (u x - u y) / (x - y) := by
    have hc := intervalIntegral.integral_comp_sub_left
      (fun y : ℝ => (u x - u y) / (x - y)) x
      (a := (0 : ℝ)) (b := a + x)
    simpa using hc
  rw [hchange]
  have htailPoint : (∫ h in (a + x)..(2 * a), (u x - u (x - h)) / h) =
      ∫ h in (a + x)..(2 * a), u x * (1 / h) := by
    refine intervalIntegral.integral_congr fun h hh => ?_
    have hh' : a + x ≤ h := by
      have := (mem_uIcc.mp hh)
      rcases this with h | h <;> linarith
    have hzero : u (x - h) = 0 := core_eq_zero_of_not_mem_aperture u (by
      intro hmem
      linarith [hmem.1])
    rw [hzero]
    ring
  rw [htailPoint, intervalIntegral.integral_const_mul]
  have hzero : 0 ∉ uIcc (a + x) (2 * a) := by
    rw [uIcc_of_le hcutle]
    intro hz
    simp only [mem_Icc] at hz
    linarith [hx.1]
  rw [integral_one_div hzero, Real.log_div (by positivity) (by linarith [hx.1])]

private theorem integral_symmetricDividedKernel_slice {a x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo (-a) a) (u : SuzukiRestrictedWeilCore a) :
    (∫ h in (0 : ℝ)..(2 * a), suzukiSymmetricDividedKernel u h x) =
      -(((∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) +
          ∫ y in x..a, (u y - u x) * (y - x)⁻¹) * u x) +
        (2 * Real.log (2 * a) - Real.log (a ^ 2 - x ^ 2)) * u x ^ 2 := by
  have hb : 0 ≤ 2 * a := by linarith
  have hr := right_divided_integral_eq ha hx u
  have hl := left_divided_integral_eq ha hx u
  have hri := right_divided_intervalIntegrable hb u (x := x)
  have hli := left_divided_intervalIntegrable hb u (x := x)
  unfold suzukiSymmetricDividedKernel
  have hpoint : (fun h : ℝ => u x * ((2 * u x - u (x + h) - u (x - h)) / h)) =
      fun h => u x * (((u x - u (x + h)) / h) + ((u x - u (x - h)) / h)) := by
    funext h
    ring
  rw [hpoint, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hri hli, hr, hl]
  have hrSource : (∫ y in x..a, (u x - u y) / (y - x)) =
      -(∫ y in x..a, (u y - u x) * (y - x)⁻¹) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ => by
      simp only [div_eq_mul_inv]
      ring
  have hlSource : (∫ y in (-a)..x, (u x - u y) / (x - y)) =
      -(∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ => by
      simp only [div_eq_mul_inv]
      ring
  rw [hrSource, hlSource]
  have hlog : Real.log (a ^ 2 - x ^ 2) = Real.log (a - x) + Real.log (a + x) := by
    rw [show a ^ 2 - x ^ 2 = (a - x) * (a + x) by ring,
      Real.log_mul (by linarith [hx.2]) (by linarith [hx.1])]
  rw [hlog]
  ring

private theorem integrated_symmetricDividedKernel_eq {a : ℝ} (ha : 0 < a)
    (u : SuzukiRestrictedWeilCore a) :
    (∫ h in (0 : ℝ)..(2 * a), ∫ x in (-a)..a,
        suzukiSymmetricDividedKernel u h x) =
      (1 / 2 : ℝ) * suzukiFinitePartDifferenceEnergy a u +
        2 * Real.log (2 * a) * (∫ x in (-a)..a, u x ^ 2) -
          suzukiFinitePartLogPotential a u := by
  rw [integral_symmetricDividedKernel_swap ha u]
  let S : ℝ → ℝ := fun x =>
    ((∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) +
      ∫ y in x..a, (u y - u x) * (y - x)⁻¹) * u x
  have hsymm := suzukiFinitePartDividedDifference_symmetrization ha u.smooth
  have hlog := suzukiFinitePartLogPotential_integrable_upper ha
    u.supportRadius_nonneg u.supportRadius_lt_aperture u.continuous u.support_subset
  have hmass : IntervalIntegrable (fun x : ℝ => u x ^ 2) volume (-a) a :=
    (u.continuous.pow 2).intervalIntegrable _ _
  have hSint : IntervalIntegrable S volume (-a) a := by
    simpa [S] using hsymm.1
  have hSval : (∫ x in (-a)..a, S x) =
      -(1 / 2 : ℝ) * suzukiFinitePartDifferenceEnergy a u := by
    simpa [S, suzukiFinitePartDifferenceEnergy] using hsymm.2.1
  have htail : IntervalIntegrable
      (fun x : ℝ => (2 * Real.log (2 * a) - Real.log (a ^ 2 - x ^ 2)) * u x ^ 2)
      volume (-a) a := by
    have hrepr : (fun x : ℝ =>
        (2 * Real.log (2 * a) - Real.log (a ^ 2 - x ^ 2)) * u x ^ 2) =
      (fun x => 2 * Real.log (2 * a) * u x ^ 2) -
        (fun x => Real.log (a ^ 2 - x ^ 2) * u x ^ 2) := by
      funext x
      dsimp
      ring
    rw [hrepr]
    exact (hmass.const_mul _).sub hlog.1
  have hslice : (∫ x in (-a)..a, ∫ h in (0 : ℝ)..(2 * a),
      suzukiSymmetricDividedKernel u h x) =
      ∫ x in (-a)..a, -S x +
        (2 * Real.log (2 * a) - Real.log (a ^ 2 - x ^ 2)) * u x ^ 2 := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    by_cases hux : u x = 0
    · have hpoint : ∀ h : ℝ, suzukiSymmetricDividedKernel u h x = 0 := by
        intro h
        simp [suzukiSymmetricDividedKernel, hux]
      simp [hpoint, S, hux]
    · have hxa := u.support_subset_aperture hux
      simpa [S] using integral_symmetricDividedKernel_slice ha hxa u
  rw [hslice]
  have htailEval : (∫ x in (-a)..a,
      (2 * Real.log (2 * a) - Real.log (a ^ 2 - x ^ 2)) * u x ^ 2) =
      2 * Real.log (2 * a) * (∫ x in (-a)..a, u x ^ 2) -
        suzukiFinitePartLogPotential a u := by
    unfold suzukiFinitePartLogPotential
    rw [show (∫ x in (-a)..a,
        (2 * Real.log (2 * a) - Real.log (a ^ 2 - x ^ 2)) * u x ^ 2) =
      (∫ x in (-a)..a, 2 * Real.log (2 * a) * u x ^ 2) -
        ∫ x in (-a)..a, Real.log (a ^ 2 - x ^ 2) * u x ^ 2 by
      rw [← intervalIntegral.integral_sub (hmass.const_mul _) hlog.1]
      refine intervalIntegral.integral_congr fun x _ => by ring,
      intervalIntegral.integral_const_mul]
  have hsum := intervalIntegral.integral_add hSint.neg htail
  have hsum' : (∫ x in (-a)..a, -S x +
      (2 * Real.log (2 * a) - Real.log (a ^ 2 - x ^ 2)) * u x ^ 2) =
      (∫ x in (-a)..a, -S x) +
        ∫ x in (-a)..a,
          (2 * Real.log (2 * a) - Real.log (a ^ 2 - x ^ 2)) * u x ^ 2 := by
    simpa only [Pi.neg_apply, Pi.add_apply] using hsum
  rw [hsum', intervalIntegral.integral_neg, hSval, htailEval]
  unfold suzukiFinitePartDifferenceEnergy
  ring

/-- The truncated real translation quotient is absolutely integrable. -/
theorem suzukiRealTranslationDifferenceQuotient_intervalIntegrable
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    IntervalIntegrable
      (fun h : ℝ => suzukiRealTranslationDifferenceEnergy u h / h)
      volume 0 (2 * a.1) := by
  have hint := integrableOn_symmetricDividedKernel_prod a.property u
  have hprod : Integrable (Function.uncurry (suzukiSymmetricDividedKernel u))
      ((volume.restrict (Ioc 0 (2 * a.1))).prod
        (volume.restrict (Ioc (-a.1) a.1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← IntegrableOn]
    exact hint
  have hout := hprod.integral_prod_left
  have hma : -a.1 ≤ a.1 := by linarith [a.property]
  have hout' : IntegrableOn
      (fun h : ℝ => ∫ x in (-a.1)..a.1, suzukiSymmetricDividedKernel u h x)
      (Ioc 0 (2 * a.1)) := by
    change Integrable
      (fun h : ℝ => ∫ x in (-a.1)..a.1, suzukiSymmetricDividedKernel u h x)
      (volume.restrict (Ioc 0 (2 * a.1)))
    apply hout.congr
    filter_upwards with h
    rw [intervalIntegral.integral_of_le hma]
    rfl
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 2 * a.1 by linarith [a.property])]
  exact hout'.congr_fun (fun h _ => by
    change (∫ x in (-a.1)..a.1, suzukiSymmetricDividedKernel u h x) =
      suzukiRealTranslationDifferenceEnergy u h / h
    rw [translationDifferenceEnergy_eq_symmetric_integral]
    unfold suzukiSymmetricDividedKernel
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x _ => by ring) measurableSet_Ioc

/-- Beyond twice the aperture, the two compact supports are disjoint and the translation
difference energy is exactly twice the mass. -/
theorem suzukiRealTranslationDifferenceEnergy_eq_two_mass_of_two_aperture_le
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1)
    {h : ℝ} (hh : 2 * a.1 ≤ h) :
    suzukiRealTranslationDifferenceEnergy u h = 2 * ∫ x : ℝ, u x ^ 2 := by
  rw [translationDifferenceEnergy_eq_symmetric_integral]
  have hpoint : (∫ x in (-a.1)..a.1,
      u x * (2 * u x - u (x + h) - u (x - h))) =
      ∫ x in (-a.1)..a.1, 2 * u x ^ 2 := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (show -a.1 ≤ a.1 by linarith [a.property])] at hx
    have hbounds : -a.1 ≤ x ∧ x ≤ a.1 := hx
    have hplus : u (x + h) = 0 := core_eq_zero_of_not_mem_aperture u (by
      intro hm
      linarith [hm.2])
    have hminus : u (x - h) = 0 := core_eq_zero_of_not_mem_aperture u (by
      intro hm
      linarith [hm.1])
    rw [hplus, hminus]
    ring
  rw [hpoint, intervalIntegral.integral_const_mul, core_mass_interval_eq]

/-- Exact spatial identity behind Suzuki's equation (2.6).  Positivity, smoothness, and strict
aperture support are intrinsic in the two structured arguments. -/
theorem suzukiFinitePartEnergy_eq_translationDifference
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    suzukiFinitePartEnergy a.1 u =
      (1 / 2 : ℝ) * (∫ h in (0 : ℝ)..(2 * a.1),
        suzukiRealTranslationDifferenceEnergy u h / h) -
          Real.log (2 * a.1) * (∫ x : ℝ, u x ^ 2) := by
  have hkernel : (∫ h in (0 : ℝ)..(2 * a.1),
      suzukiRealTranslationDifferenceEnergy u h / h) =
      ∫ h in (0 : ℝ)..(2 * a.1), ∫ x in (-a.1)..a.1,
        suzukiSymmetricDividedKernel u h x := by
    refine intervalIntegral.integral_congr fun h _ => ?_
    rw [translationDifferenceEnergy_eq_symmetric_integral]
    unfold suzukiSymmetricDividedKernel
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x _ => by ring
  rw [hkernel, integrated_symmetricDividedKernel_eq a.property u, ← core_mass_interval_eq u]
  unfold suzukiFinitePartEnergy
  ring

end GaloisForLFunctions.RHTower
