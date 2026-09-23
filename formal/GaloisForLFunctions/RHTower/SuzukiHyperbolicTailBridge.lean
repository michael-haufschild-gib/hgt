import GaloisForLFunctions.RHTower.SuzukiOriginRemainderFirstJet
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Suzuki endpoint finite part and the global archimedean tail

The restricted Suzuki form contains an endpoint logarithm while the global Weil distribution
contains an infinite hyperbolic tail.  Their equality is controlled by the exact primitive

`d/dh (log (tanh (h/2))) = 1 / sinh h`.

This module proves the two improper identities, including the removable origin cancellation,
needed to identify those presentations without a cutoff premise.
-/

open Filter MeasureTheory Set Topology

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

/-- Logarithmic hyperbolic primitive on the positive ray. -/
def suzukiHyperbolicPrimitive (h : ℝ) : ℝ :=
  Real.log (Real.sinh (h / 2)) - Real.log (Real.cosh (h / 2))

/-- The derivative of the hyperbolic primitive is `csch`. -/
theorem hasDerivAt_suzukiHyperbolicPrimitive {h : ℝ} (hh : 0 < h) :
    HasDerivAt suzukiHyperbolicPrimitive (1 / Real.sinh h) h := by
  have hhhalf : 0 < h / 2 := by linarith
  have hsinh : Real.sinh (h / 2) ≠ 0 := (Real.sinh_ne_zero).2 hhhalf.ne'
  have hcosh : Real.cosh (h / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hhalf : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) h := by
    simpa using (hasDerivAt_id' h).div_const 2
  have hraw := (hhalf.sinh.log hsinh).sub (hhalf.cosh.log hcosh)
  have hsinhH : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh.ne'
  have hderiv : Real.cosh (h / 2) * (1 / 2 : ℝ) / Real.sinh (h / 2) -
      Real.sinh (h / 2) * (1 / 2 : ℝ) / Real.cosh (h / 2) =
        1 / Real.sinh h := by
    rw [show h = 2 * (h / 2) by ring, Real.sinh_two_mul]
    field_simp [hsinh, hcosh, hsinhH]
    nlinarith [Real.cosh_sq_sub_sinh_sq (h / 2)]
  change HasDerivAt (fun y : ℝ =>
    Real.log (Real.sinh (y / 2)) - Real.log (Real.cosh (y / 2)))
      (1 / Real.sinh h) h
  rw [← hderiv]
  exact hraw

private theorem tendsto_sinh_half_div_self_nhdsGT_zero :
    Tendsto (fun h : ℝ => Real.sinh (h / 2) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have hhalf : HasDerivAt (fun h : ℝ => h / 2) (1 / 2 : ℝ) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).div_const 2
  have hsinh : HasDerivAt (fun h : ℝ => Real.sinh (h / 2)) (1 / 2 : ℝ) 0 := by
    convert hhalf.sinh using 1 <;> norm_num
  have hslope := hsinh.tendsto_slope_zero_right
  convert hslope using 1
  funext h
  simp [slope, div_eq_mul_inv]
  ring

private theorem tendsto_exp_half_sub_one_div_self_nhdsGT_zero :
    Tendsto (fun h : ℝ => (Real.exp (h / 2) - 1) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  have hhalf : HasDerivAt (fun h : ℝ => h / 2) (1 / 2 : ℝ) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).div_const 2
  have hexp : HasDerivAt (fun h : ℝ => Real.exp (h / 2)) (1 / 2 : ℝ) 0 := by
    convert hhalf.exp using 1 <;> norm_num
  have hsub : HasDerivAt (fun h : ℝ => Real.exp (h / 2) - 1) (1 / 2 : ℝ) 0 :=
    hexp.sub_const 1
  have hslope := hsub.tendsto_slope_zero_right
  convert hslope using 1
  funext h
  simp [slope, div_eq_mul_inv]
  ring

/-- The primitive minus `log h` has the exact removable endpoint value `-log 2`. -/
theorem tendsto_suzukiHyperbolicPrimitive_sub_log_nhdsGT_zero :
    Tendsto (fun h : ℝ => suzukiHyperbolicPrimitive h - Real.log h)
      (𝓝[>] (0 : ℝ)) (𝓝 (-Real.log 2)) := by
  have hcosh : Tendsto (fun h : ℝ => Real.cosh (h / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun h : ℝ => Real.cosh (h / 2)) := by fun_prop
    have ht := tendsto_nhdsWithin_of_tendsto_nhds
      (s := Ioi (0 : ℝ)) (hc.continuousAt :
        Tendsto (fun h : ℝ => Real.cosh (h / 2)) (𝓝 0)
          (𝓝 (Real.cosh (0 / 2))))
    simpa using ht
  have hratio : Tendsto (fun h : ℝ =>
      (Real.sinh (h / 2) / h) / Real.cosh (h / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    have ht := tendsto_sinh_half_div_self_nhdsGT_zero.div hcosh (by norm_num)
    convert ht using 1
    · funext h
      rfl
    · norm_num
  have hlog := (Real.continuousAt_log (by norm_num : (1 / 2 : ℝ) ≠ 0)).tendsto.comp hratio
  have heq : (fun h : ℝ => suzukiHyperbolicPrimitive h - Real.log h) =ᶠ[𝓝[>] 0]
      fun h => Real.log ((Real.sinh (h / 2) / h) / Real.cosh (h / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := hh.ne'
    have hsinh : Real.sinh (h / 2) ≠ 0 :=
      (Real.sinh_ne_zero).2 (div_ne_zero hh0 (by norm_num))
    have hcosh0 : Real.cosh (h / 2) ≠ 0 := (Real.cosh_pos _).ne'
    unfold suzukiHyperbolicPrimitive
    rw [← Real.log_div hsinh hcosh0,
      ← Real.log_div (div_ne_zero hsinh hcosh0) hh0]
    congr 1
    field_simp [hh0, hcosh0]
  have hlog' : Tendsto (fun h =>
      Real.log ((Real.sinh (h / 2) / h) / Real.cosh (h / 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (1 / 2))) := by
    simpa only [Function.comp_def] using hlog
  apply Tendsto.congr' heq.symm
  convert hlog' using 1
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]

/-- The hyperbolic primitive vanishes at positive infinity. -/
theorem tendsto_suzukiHyperbolicPrimitive_atTop :
    Tendsto suzukiHyperbolicPrimitive atTop (𝓝 0) := by
  have hneg : Tendsto (fun h : ℝ => Real.exp (-h)) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have htanh : Tendsto (fun h : ℝ => Real.tanh (h / 2)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hquot := (hone.sub hneg).div
      (hone.add hneg) (by norm_num : (1 + 0 : ℝ) ≠ 0)
    convert hquot using 1
    · funext h
      rw [Real.tanh_eq]
      change (Real.exp (h / 2) - Real.exp (-(h / 2))) /
          (Real.exp (h / 2) + Real.exp (-(h / 2))) =
        (1 - Real.exp (-h)) / (1 + Real.exp (-h))
      have he : Real.exp (h / 2) ≠ 0 := (Real.exp_pos _).ne'
      have hden : 1 + Real.exp (-h) ≠ 0 := by positivity
      field_simp [he, hden]
      rw [show -h = -(h / 2) + -(h / 2) by ring, Real.exp_add]
      have heprod : Real.exp (h / 2) * Real.exp (-(h / 2)) = 1 := by
        rw [← Real.exp_add]
        norm_num
      have heprod' :
          Real.exp (h * (1 / 2)) * Real.exp (h * (-1 / 2)) = 1 := by
        convert heprod using 1 <;> ring
      have habb :
          Real.exp (h * (1 / 2)) * Real.exp (h * (-1 / 2)) ^ (2 : ℕ) =
            Real.exp (h * (-1 / 2)) := by
        calc
          _ = (Real.exp (h * (1 / 2)) * Real.exp (h * (-1 / 2))) *
                Real.exp (h * (-1 / 2)) := by ring
          _ = _ := by rw [heprod', one_mul]
      ring_nf
      rw [habb]
      ring
    · norm_num
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp htanh
  have heq : suzukiHyperbolicPrimitive =ᶠ[atTop]
      fun h => Real.log (Real.tanh (h / 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with h hh
    have hsinh : Real.sinh (h / 2) ≠ 0 :=
      (Real.sinh_ne_zero).2 (by linarith : h / 2 ≠ 0)
    have hcosh : Real.cosh (h / 2) ≠ 0 := (Real.cosh_pos _).ne'
    unfold suzukiHyperbolicPrimitive
    rw [← Real.log_div hsinh hcosh, ← Real.tanh_eq_sinh_div_cosh]
  simpa using hlog.congr' heq.symm

/-- Continuous extension of `(exp(h/2)-1)/sinh h` at the origin. -/
def suzukiHalfExponentialSinhRatio (h : ℝ) : ℝ :=
  if h = 0 then 1 / 2 else (Real.exp (h / 2) - 1) / Real.sinh h

theorem continuous_suzukiHalfExponentialSinhRatio :
    Continuous suzukiHalfExponentialSinhRatio := by
  rw [continuous_iff_continuousAt]
  intro h
  by_cases hh : h = 0
  · subst h
    rw [continuousAt_iff_punctured_nhds]
    have hsinhRatio : Tendsto (fun h : ℝ => h / Real.sinh h)
        (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      have hsinh : HasDerivAt Real.sinh 1 0 := by simpa using Real.hasDerivAt_sinh 0
      have hslope := hsinh.tendsto_slope
      have hinv := hslope.inv₀ one_ne_zero
      convert hinv using 1
      · funext h
        simp [slope, div_eq_mul_inv]
        ring
      · norm_num
    have hexp : Tendsto (fun h : ℝ => (Real.exp (h / 2) - 1) / h)
        (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
      have hhalf : HasDerivAt (fun h : ℝ => h / 2) (1 / 2 : ℝ) 0 := by
        simpa using (hasDerivAt_id' (0 : ℝ)).div_const 2
      have he : HasDerivAt (fun h : ℝ => Real.exp (h / 2) - 1) (1 / 2 : ℝ) 0 := by
        convert hhalf.exp.sub (hasDerivAt_const (0 : ℝ) (1 : ℝ)) using 1
        all_goals first | rfl | norm_num | ring
      convert he.tendsto_slope using 1
      funext h
      simp [slope, div_eq_mul_inv]
      ring
    have hprod := hexp.mul hsinhRatio
    rw [show suzukiHalfExponentialSinhRatio 0 = (1 / 2 : ℝ) by
      simp [suzukiHalfExponentialSinhRatio]]
    convert hprod.congr' ?_ using 1 <;> norm_num
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := by simpa using hh
    have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh0
    simp only [suzukiHalfExponentialSinhRatio, if_neg hh0]
    field_simp [hh0, hsinh]
  · have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh
    apply ContinuousAt.congr_of_eventuallyEq
      ((by fun_prop : ContinuousAt
        (fun x : ℝ => (Real.exp (x / 2) - 1) / Real.sinh x) h))
    filter_upwards [eventually_ne_nhds hh] with x hx
    simp [suzukiHalfExponentialSinhRatio, hx]

/-- Continuous origin extension of `csch h - 1/h`.  Suzuki's continuous remainder curvature
supplies one cancellation; the half-exponential ratio supplies the other. -/
def suzukiCschMinusInvExtension (h : ℝ) : ℝ :=
  2 * suzukiOriginRemainderCurvature h + 4 * Real.cosh (h / 2) -
    suzukiHalfExponentialSinhRatio h

theorem continuous_suzukiCschMinusInvExtension :
    Continuous suzukiCschMinusInvExtension := by
  unfold suzukiCschMinusInvExtension
  exact (((continuous_suzukiOriginRemainderCurvature.const_mul 2).add
    ((Real.continuous_cosh.comp (continuous_id.div_const 2)).const_mul 4)).sub
      continuous_suzukiHalfExponentialSinhRatio)

theorem suzukiCschMinusInvExtension_of_pos {h : ℝ} (hh : 0 < h) :
    suzukiCschMinusInvExtension h = 1 / Real.sinh h - 1 / h := by
  have hh0 : h ≠ 0 := hh.ne'
  have hden : 1 - Real.exp (-(2 * h)) ≠ 0 :=
    (one_sub_exp_neg_two_mul_pos hh).ne'
  have hden' : 1 - Real.exp (-(h * 2)) ≠ 0 := by
    convert hden using 1 <;> ring
  have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh0
  have hdiff : Real.exp h - Real.exp (-h) ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_exp.mpr (by linarith)))
  have htail :
      Real.exp (-(h / 2)) / (1 - Real.exp (-(2 * h))) =
        Real.exp (h / 2) / (2 * Real.sinh h) := by
    rw [Real.sinh_eq]
    field_simp [hden', hdiff]
    rw [mul_sub, sub_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> ring
  rw [suzukiCschMinusInvExtension,
    suzukiOriginRemainderCurvature_of_ne hh0, abs_of_pos hh,
    screwRegularKernel_eq_tailForm hh,
    suzukiHalfExponentialSinhRatio, if_neg hh0, htail]
  rw [Real.cosh_eq]
  field_simp [hsinh, hh0]
  ring

/-- Exact finite endpoint compensation. -/
theorem integral_suzukiCschMinusInvExtension
    {R : ℝ} (hR : 0 < R) :
    (∫ h in (0 : ℝ)..R, suzukiCschMinusInvExtension h) =
      suzukiHyperbolicPrimitive R - Real.log R + Real.log 2 := by
  let P : ℝ → ℝ := fun h => suzukiHyperbolicPrimitive h - Real.log h
  have hderiv : ∀ h ∈ Ioo (0 : ℝ) R,
      HasDerivAt P (suzukiCschMinusInvExtension h) h := by
    intro h hh
    have hraw := (hasDerivAt_suzukiHyperbolicPrimitive hh.1).sub
      (Real.hasDerivAt_log hh.1.ne')
    dsimp only [P]
    rw [suzukiCschMinusInvExtension_of_pos hh.1]
    convert hraw using 1
    all_goals first | rfl | ring
  have hint : IntervalIntegrable suzukiCschMinusInvExtension volume 0 R :=
    continuous_suzukiCschMinusInvExtension.intervalIntegrable 0 R
  have hleft : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 (-Real.log 2)) :=
    tendsto_suzukiHyperbolicPrimitive_sub_log_nhdsGT_zero
  have hright : Tendsto P (𝓝[<] R)
      (𝓝 (suzukiHyperbolicPrimitive R - Real.log R)) := by
    have hcont : ContinuousAt P R := by
      dsimp only [P]
      exact (hasDerivAt_suzukiHyperbolicPrimitive hR).continuousAt.sub
        (Real.continuousAt_log hR.ne')
    exact hcont.tendsto.mono_left inf_le_left
  simpa only [P, sub_neg_eq_add] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hR hderiv hint hleft hright

private theorem inv_sinh_eq_two_mul_exp_neg_div {h : ℝ} (hh : 0 < h) :
    1 / Real.sinh h = 2 * Real.exp (-h) / (1 - Real.exp (-(2 * h))) := by
  have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh.ne'
  have hden : 1 - Real.exp (-(2 * h)) ≠ 0 :=
    (one_sub_exp_neg_two_mul_pos hh).ne'
  have hden' : 1 - Real.exp (-(h * 2)) ≠ 0 := by
    convert hden using 1 <;> ring
  have hdiff : Real.exp h - Real.exp (-h) ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_exp.mpr (by linarith)))
  rw [Real.sinh_eq]
  field_simp [hdiff, hden']
  rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
  congr 1
  · rw [show -h + h = 0 by ring, Real.exp_zero]
  · ring

theorem integrableOn_inv_sinh_Ioi {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun h : ℝ => 1 / Real.sinh h) (Ioi R) := by
  let d : ℝ := 1 - Real.exp (-(2 * R))
  have hd : 0 < d := one_sub_exp_neg_two_mul_pos hR
  have hdom : IntegrableOn (fun h : ℝ => (2 / d) * Real.exp (-h)) (Ioi R) := by
    change Integrable (fun h : ℝ => (2 / d) * Real.exp (-h))
      (volume.restrict (Ioi R))
    simpa only [one_mul, neg_mul] using
      (exp_neg_integrableOn_Ioi R (b := 1) zero_lt_one).const_mul (2 / d)
  refine hdom.mono' ?_ ?_
  · exact ((Real.measurable_sinh.inv.const_mul 1).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hhR : R < h := hh
    have hhpos : 0 < h := hR.trans hh
    have hdenpos : 0 < 1 - Real.exp (-(2 * h)) :=
      one_sub_exp_neg_two_mul_pos hhpos
    have hdenle : d ≤ 1 - Real.exp (-(2 * h)) := by
      dsimp only [d]
      have he : Real.exp (-(2 * h)) ≤ Real.exp (-(2 * R)) :=
        Real.exp_le_exp.mpr (by nlinarith [hhR])
      linarith
    rw [inv_sinh_eq_two_mul_exp_neg_div hhpos, Real.norm_eq_abs,
      abs_of_pos (div_pos (mul_pos (by norm_num) (Real.exp_pos _)) hdenpos)]
    have hn : 0 ≤ 2 * Real.exp (-h) := by positivity
    calc
      2 * Real.exp (-h) / (1 - Real.exp (-(2 * h))) ≤
          2 * Real.exp (-h) / d :=
        div_le_div_of_nonneg_left hn hd hdenle
      _ = (2 / d) * Real.exp (-h) := by ring

/-- Exact global tail of the archimedean finite-part distribution. -/
theorem integral_Ioi_inv_sinh
    {R : ℝ} (hR : 0 < R) :
    (∫ h in Ioi R, 1 / Real.sinh h) = -suzukiHyperbolicPrimitive R := by
  have hcont : ContinuousWithinAt suzukiHyperbolicPrimitive (Ici R) R :=
    (hasDerivAt_suzukiHyperbolicPrimitive hR).continuousAt.continuousWithinAt
  have hderiv : ∀ h ∈ Ioi R,
      HasDerivAt suzukiHyperbolicPrimitive (1 / Real.sinh h) h := by
    intro h hh
    exact hasDerivAt_suzukiHyperbolicPrimitive (hR.trans hh)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_inv_sinh_Ioi hR) tendsto_suzukiHyperbolicPrimitive_atTop]
  ring

end RHTower
