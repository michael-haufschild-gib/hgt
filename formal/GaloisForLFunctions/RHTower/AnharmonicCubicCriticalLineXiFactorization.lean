import GaloisForLFunctions.RHTower.AnharmonicChebyshevMovingFiber
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap

open Complex

namespace RHTower

noncomputable section

def chebyshevCriticalLinePoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * I

def chebyshevCriticalLineXiWeight (t : ℝ) : ℝ :=
  ‖xi (chebyshevAnharmonicW (chebyshevCriticalLinePoint t))‖ ^ 2

private theorem criticalLinePoint_conj (t : ℝ) :
    (starRingEnd ℂ) (chebyshevCriticalLinePoint t) =
      1 - chebyshevCriticalLinePoint t := by
  simp [chebyshevCriticalLinePoint, Complex.ext_iff]
  ring

private theorem criticalLinePoint_ne_zero (t : ℝ) :
    chebyshevCriticalLinePoint t ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp [chebyshevCriticalLinePoint] at hr

private theorem criticalLineWTwo_eq (t : ℝ) :
    chebyshevAnharmonicWTwo (chebyshevCriticalLinePoint t) =
      (starRingEnd ℂ)
        (1 - chebyshevAnharmonicW (chebyshevCriticalLinePoint t)) := by
  let s := chebyshevCriticalLinePoint t
  have hs0 : s ≠ 0 := criticalLinePoint_ne_zero t
  have hrecip : 1 - chebyshevAnharmonicW s = 1 / s := by
    simp only [chebyshevAnharmonicW]
    field_simp [hs0]
    ring
  calc
    chebyshevAnharmonicWTwo s = 1 / (1 - s) := rfl
    _ = 1 / (starRingEnd ℂ s) := by rw [criticalLinePoint_conj]
    _ = (starRingEnd ℂ) (1 / s) := by simp
    _ = (starRingEnd ℂ) (1 - chebyshevAnharmonicW s) := by rw [hrecip]

theorem chebyshevCriticalLineW_norm (t : ℝ) :
    ‖chebyshevAnharmonicW (chebyshevCriticalLinePoint t)‖ = 1 := by
  let s := chebyshevCriticalLinePoint t
  have hs0 : s ≠ 0 := criticalLinePoint_ne_zero t
  have hnum : s - 1 = -((starRingEnd ℂ) s) := by
    rw [criticalLinePoint_conj]
    ring
  rw [chebyshevAnharmonicW, hnum, norm_div, norm_neg, norm_conj,
    div_self (norm_ne_zero_iff.mpr hs0)]

/-- The two noncentral Xi factors form a conjugate pair on the critical line. -/
theorem chebyshevXiCyclicOrbitProduct_criticalLine (t : ℝ) :
    chebyshevXiCyclicOrbitProduct (chebyshevCriticalLinePoint t) =
      xi (chebyshevCriticalLinePoint t) *
        (chebyshevCriticalLineXiWeight t : ℂ) := by
  let s := chebyshevCriticalLinePoint t
  have hxi : xi (chebyshevAnharmonicWTwo s) =
      (starRingEnd ℂ) (xi (chebyshevAnharmonicW s)) := by
    rw [criticalLineWTwo_eq, xi_conj, xi_one_sub]
  change chebyshevXiCyclicOrbitProduct s =
    xi s * ((‖xi (chebyshevAnharmonicW s)‖ ^ 2 : ℝ) : ℂ)
  unfold chebyshevXiCyclicOrbitProduct
  rw [hxi]
  calc
    xi s * xi (chebyshevAnharmonicW s) *
        (starRingEnd ℂ) (xi (chebyshevAnharmonicW s)) =
      xi s * (xi (chebyshevAnharmonicW s) *
        (starRingEnd ℂ) (xi (chebyshevAnharmonicW s))) := by ring
    _ = _ := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The weight is positive because the orbit point lies on the unit circle,
inside the corpus's Xi zero-free band. -/
theorem chebyshevCriticalLineXiWeight_pos (t : ℝ) :
    0 < chebyshevCriticalLineXiWeight t := by
  have him :
      |(chebyshevAnharmonicW (chebyshevCriticalLinePoint t)).im| ≤ 1 :=
    (Complex.abs_im_le_norm _).trans_eq (chebyshevCriticalLineW_norm t)
  have hxi : xi (chebyshevAnharmonicW (chebyshevCriticalLinePoint t)) ≠ 0 :=
    xi_ne_zero_of_abs_im_le_one him
  exact sq_pos_of_pos (norm_pos_iff.mpr hxi)

theorem chebyshevXiCyclicOrbitProduct_criticalLine_eq_zero_iff (t : ℝ) :
    chebyshevXiCyclicOrbitProduct (chebyshevCriticalLinePoint t) = 0 ↔
      xi (chebyshevCriticalLinePoint t) = 0 := by
  rw [chebyshevXiCyclicOrbitProduct_criticalLine]
  have hw : (chebyshevCriticalLineXiWeight t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (chebyshevCriticalLineXiWeight_pos t))
  simp [hw]

theorem chebyshevXiCyclicOrbitProduct_criticalLine_re_pos_iff (t : ℝ) :
    0 < (chebyshevXiCyclicOrbitProduct (chebyshevCriticalLinePoint t)).re ↔
      0 < (xi (chebyshevCriticalLinePoint t)).re := by
  rw [chebyshevXiCyclicOrbitProduct_criticalLine]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact mul_pos_iff_of_pos_right (chebyshevCriticalLineXiWeight_pos t)

theorem chebyshevCriticalLineXiWeight_tendsto_atTop :
    Filter.Tendsto chebyshevCriticalLineXiWeight Filter.atTop
      (nhds (1 / 4 : ℝ)) := by
  have hnorm_le (t : ℝ) : t ≤ ‖chebyshevCriticalLinePoint t‖ := by
    have him : (chebyshevCriticalLinePoint t).im = t := by
      simp [chebyshevCriticalLinePoint]
    calc
      t ≤ |t| := le_abs_self t
      _ = |(chebyshevCriticalLinePoint t).im| := by rw [him]
      _ ≤ ‖chebyshevCriticalLinePoint t‖ := Complex.abs_im_le_norm _
  have hnorm_top : Filter.Tendsto
      (fun t : ℝ => ‖chebyshevCriticalLinePoint t‖)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with t ht
    exact ht.trans (hnorm_le t)
  have hinvnorm : Filter.Tendsto
      (fun t : ℝ => (‖chebyshevCriticalLinePoint t‖)⁻¹)
      Filter.atTop (nhds (0 : ℝ)) := hnorm_top.inv_tendsto_atTop
  have hinv : Filter.Tendsto
      (fun t : ℝ => (chebyshevCriticalLinePoint t)⁻¹)
      Filter.atTop (nhds (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_inv] using hinvnorm
  have hWfun (t : ℝ) :
      chebyshevAnharmonicW (chebyshevCriticalLinePoint t) =
        1 - (chebyshevCriticalLinePoint t)⁻¹ := by
    unfold chebyshevAnharmonicW
    field_simp [criticalLinePoint_ne_zero t]
  have hW : Filter.Tendsto
      (fun t : ℝ => chebyshevAnharmonicW (chebyshevCriticalLinePoint t))
      Filter.atTop (nhds (1 : ℂ)) := by
    have hfun :
        (fun t : ℝ => chebyshevAnharmonicW (chebyshevCriticalLinePoint t)) =
          (fun t : ℝ => 1 - (chebyshevCriticalLinePoint t)⁻¹) := by
      funext t
      exact hWfun t
    rw [hfun]
    simpa using (tendsto_const_nhds.sub hinv)
  have hxi : Filter.Tendsto
      (fun t : ℝ => xi (chebyshevAnharmonicW (chebyshevCriticalLinePoint t)))
      Filter.atTop (nhds (xi 1)) :=
    xi_differentiable.continuous.continuousAt.tendsto.comp hW
  have hval : ‖xi (1 : ℂ)‖ ^ 2 = (1 / 4 : ℝ) := by
    rw [xi_one]
    norm_num
  change Filter.Tendsto
    (fun t : ℝ => ‖xi (chebyshevAnharmonicW (chebyshevCriticalLinePoint t))‖ ^ 2)
    Filter.atTop (nhds (1 / 4 : ℝ))
  rw [← hval]
  exact hxi.norm.pow 2

private theorem criticalLinePoint_neg (t : ℝ) :
    chebyshevCriticalLinePoint (-t) =
      (starRingEnd ℂ) (chebyshevCriticalLinePoint t) := by
  simp [chebyshevCriticalLinePoint, Complex.ext_iff]

private theorem criticalLineW_conj (s : ℂ) :
    chebyshevAnharmonicW ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (chebyshevAnharmonicW s) := by
  simp [chebyshevAnharmonicW]

theorem chebyshevCriticalLineXiWeight_even (t : ℝ) :
    chebyshevCriticalLineXiWeight (-t) =
      chebyshevCriticalLineXiWeight t := by
  simp only [chebyshevCriticalLineXiWeight]
  rw [criticalLinePoint_neg, criticalLineW_conj, xi_conj]
  simp

theorem chebyshevCriticalLineXiWeight_tendsto_atBot :
    Filter.Tendsto chebyshevCriticalLineXiWeight Filter.atBot
      (nhds (1 / 4 : ℝ)) := by
  have h := chebyshevCriticalLineXiWeight_tendsto_atTop.comp
    Filter.tendsto_neg_atBot_atTop
  simpa only [Function.comp_def, chebyshevCriticalLineXiWeight_even] using h

end

end RHTower
