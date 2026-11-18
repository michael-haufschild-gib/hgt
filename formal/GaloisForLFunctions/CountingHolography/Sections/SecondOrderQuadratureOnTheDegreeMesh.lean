import GaloisForLFunctions.CountingHolography.Sections.UniformQuadratureForPrimeContacts
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSecondOrderSynthesis
import GaloisForLFunctions.RHTower.Sieve.UnitBlockFrequencyBounds

/-!
# Second-order quadrature for harmonic degree samples

The density in the degree coordinate is G(log x)/x. Its second derivative
has an integrable x⁻³ envelope even as the conductor window grows.
The zero endpoint values turn the original sum into the trapezoid rule.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology MeasureTheory AbsoluteGeometryOfSpecZ SpacingScaleHarmonicAnalysis

private theorem derivative_zero_left {f g : ℝ → ℝ} {b : ℝ}
    (h : ∀ x, HasDerivAt f (g x) x) (hz : ∀ x < b, f x = 0) :
    ∀ x < b, g x = 0 := by
  intro x hx
  have he : f =ᶠ[𝓝 x] fun _ => (0:ℝ) := (gt_mem_nhds hx).mono hz
  exact (h x).unique ((hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he)

private theorem density_derivative {f g : ℝ → ℝ} {y : ℝ}
    (h : ∀ x, HasDerivAt f (g x) x) (hy : 0 < y) (q : ℕ) :
    HasDerivAt (fun x : ℝ => f (Real.log x)/x^q)
      ((g (Real.log y)-q*f (Real.log y))/y^(q+1)) y := by
  have hh := ((h _).comp y (Real.hasDerivAt_log hy.ne')).div ((hasDerivAt_id' y).pow q) (pow_ne_zero _ hy.ne')
  apply hh.congr_deriv
  cases q with
  | zero => simp [div_eq_mul_inv]
  | succ q =>
    simp only [Pi.pow_apply,Function.comp_apply,Nat.cast_succ,Nat.add_one_sub_one,pow_succ,mul_one]
    field_simp [hy.ne',pow_ne_zero _ hy.ne']

/-- On any degree window the harmonic quadrature error is at most a constant
times r⁻², with constants from the first two derivatives and the function. -/
theorem degreeSum_second_order {G G₁ G₂ : ℝ → ℝ} (hG : ∀ u, HasDerivAt G (G₁ u) u)
    (hG₁ : ∀ u, HasDerivAt G₁ (G₂ u) u) (hc₂ : Continuous G₂)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ u, |G u| ≤ A ∧ |G₁ u| ≤ A ∧ |G₂ u| ≤ A)
    (hz : ∀ u < Real.log 2, G u = 0) (L : ℕ) {r : ℕ} (hr : 0 < r)
    (hend : G (Real.log (1+(L:ℝ))) = 0) :
    |(∑ j ∈ Ioc r (r+L*r), G (Real.log ((j:ℝ)/r))/j) -
      ∫ u in (0:ℝ)..Real.log (1+(L:ℝ)), G u| ≤ 8*A/(r:ℝ)^2 := by
  let F := fun x : ℝ => G (Real.log (max x 1))/max x 1
  let F₁ := fun x : ℝ => (G₁ (Real.log (max x 1))-G (Real.log (max x 1)))/(max x 1)^2
  let F₂ := fun x : ℝ => (G₂ (Real.log (max x 1))-3*G₁ (Real.log (max x 1))+2*G (Real.log (max x 1)))/(max x 1)^3
  have hz₁ := derivative_zero_left hG hz
  have hz₂ := derivative_zero_left hG₁ hz₁
  have hlog {x : ℝ} (hx : x < 2) : Real.log (max x 1) < Real.log 2 :=
    Real.log_lt_log (zero_lt_one.trans_le (le_max_right _ _)) (max_lt hx (by norm_num))
  have hF (x) : HasDerivAt F (F₁ x) x := by
    by_cases hx : 1 < x
    · have h := density_derivative hG (zero_lt_one.trans hx) 1
      change HasDerivAt F ((G₁ (Real.log (max x 1))-G (Real.log (max x 1)))/(max x 1)^2) x
      rw [max_eq_left hx.le]
      apply (show HasDerivAt (fun y : ℝ => G (Real.log y)/y)
        ((G₁ (Real.log x)-G (Real.log x))/x^2) x by simpa only [pow_one,Nat.cast_one,one_mul] using h).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds hx] with y hy
      simp only [F,max_eq_left hy.le]
    · have hx' : x < 2 := (le_of_not_gt hx).trans_lt (by norm_num)
      have hconst := hasDerivAt_const x (0:ℝ)
      simp only [F₁,hz₁ _ (hlog hx'),hz _ (hlog hx'),sub_self,zero_div]
      apply hconst.congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds hx'] with y hy
      simp only [F,hz _ (hlog hy),zero_div]
  have hF₁ (x) : HasDerivAt F₁ (F₂ x) x := by
    by_cases hx : 1 < x
    · have h := density_derivative (fun u => (hG₁ u).sub (hG u)) (zero_lt_one.trans hx) 2
      change HasDerivAt F₁ ((G₂ (Real.log (max x 1))-3*G₁ (Real.log (max x 1))+2*G (Real.log (max x 1)))/(max x 1)^3) x
      rw [max_eq_left hx.le]
      apply (h.congr_deriv (by simp only [Pi.sub_apply,Nat.cast_ofNat]; ring)).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds hx] with y hy
      simp only [F₁,max_eq_left hy.le,Pi.sub_apply]
    · have hx' : x < 2 := (le_of_not_gt hx).trans_lt (by norm_num)
      simp only [F₂,hz₂ _ (hlog hx'),hz₁ _ (hlog hx'),hz _ (hlog hx'),mul_zero,sub_zero,add_zero,zero_div]
      apply (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds hx'] with y hy
      simp only [F₁,hz₁ _ (hlog hy),hz _ (hlog hy),sub_self,zero_div]
  have hc : Continuous G := continuous_iff_continuousAt.mpr fun x => (hG x).continuousAt
  have hc₁ : Continuous G₁ := continuous_iff_continuousAt.mpr fun x => (hG₁ x).continuousAt
  have hcF₂ : Continuous F₂ :=
    (((hc₂.comp continuous_log_max_one).sub (continuous_const.mul (hc₁.comp continuous_log_max_one))).add
      (continuous_const.mul (hc.comp continuous_log_max_one))).div
      ((continuous_id.max continuous_const).pow 3) (fun x => pow_ne_zero _ (max_one_ne_zero x))
  let T := 1+(L:ℝ)
  have hT : 1 ≤ T := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hcurv : ∫ x in (1:ℝ)..T, |F₂ x| ≤ 6*A := by
    have hh : ContinuousOn (fun x : ℝ => 1/x^2) (Set.uIcc 1 T) :=
      continuousOn_const.div (continuous_id.pow 2).continuousOn fun x hx =>
        pow_ne_zero _ (zero_lt_one.trans_le ((Set.uIcc_of_le hT ▸ hx : x ∈ Set.Icc 1 T).1)).ne'
    calc _ ≤ ∫ x in (1:ℝ)..T, (6*A)*(1/x^2) := by
           apply intervalIntegral.integral_mono_on hT (hcF₂.abs.intervalIntegrable _ _)
             ((continuousOn_const.mul hh).intervalIntegrable)
           intro x hx
           have hx₁ := hx.1
           have hx₀ := zero_lt_one.trans_le hx₁
           obtain ⟨hb₀,hb₁,hb₂⟩ := hb (Real.log x)
           have hnum : |G₂ (Real.log x)-3*G₁ (Real.log x)+2*G (Real.log x)| ≤ 6*A := by
             rw [abs_le] at hb₀ hb₁ hb₂ ⊢
             constructor <;> linarith only [hb₀.1,hb₀.2,hb₁.1,hb₁.2,hb₂.1,hb₂.2]
           rw [show |F₂ x| = |G₂ (Real.log x)-3*G₁ (Real.log x)+2*G (Real.log x)|/x^3 by
             simp only [F₂,max_eq_left hx₁,abs_div,abs_of_nonneg (pow_nonneg hx₀.le 3)]]
           change _ ≤ (6*A)*(1/x^2)
           rw [mul_one_div]
           exact div_le_div₀ (by positivity) hnum (sq_pos_of_pos hx₀)
             (by simpa only [pow_succ x 2] using le_mul_of_one_le_right (sq_nonneg x) hx₁)
      _ = (6*A)*∫ x in (1:ℝ)..T, 1/x^2 := intervalIntegral.integral_const_mul ..
      _ ≤ _ := by simpa only [div_one,mul_one] using mul_le_mul_of_nonneg_left
                    (_root_.RHTower.Sieve.intervalIntegral_one_div_sq_le one_pos hT) (by positivity : 0 ≤ 6*A)
  let nodes := fun i : ℕ => 1+(i:ℝ)/r
  let J := L*r
  have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hstep (i : ℕ) : nodes (i+1)-nodes i=1/(r:ℝ) := by dsimp only [nodes]; push_cast; ring
  have h0 : nodes 0=1 := by simp [nodes]
  have hJ : nodes J=T := by simp only [nodes,J,T,Nat.cast_mul,mul_div_cancel_right₀ _ hr'.ne']
  have hmono : Monotone nodes := fun i j hij =>
    add_le_add_right (div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) hr'.le) _
  have ht := abs_trapRule_sub_le_two hmono (J := J) (fun i _ => (hstep i).le) hF hF₁ hcF₂
  rw [h0,hJ,integral_comp_log_div hc hT] at ht
  have hF₀ : F (nodes 0) = 0 := by
    rw [h0]; simp [F,hz 0 (Real.log_pos (by norm_num))]
  have hFend : F (nodes J) = 0 := by simp only [hJ,F,max_eq_left hT,T,hend,zero_div]
  have htel := sum_range_sub (fun i => F (nodes i)) J
  rw [sum_sub_distrib,hF₀,hFend,sub_zero,sub_eq_zero] at htel
  have htrap : trapRule F nodes J = (1/(r:ℝ))*∑ i ∈ range J, F (nodes (i+1)) := by
    unfold trapRule
    simp_rw [hstep]
    rw [← mul_sum]
    congr 1
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul,sum_add_distrib,htel]
    ring
  have hmesh : (∑ j ∈ Ioc r (r+L*r), G (Real.log ((j:ℝ)/r))/j) = trapRule F nodes J := by
    rw [htrap,sum_Ioc_add_eq_sum_range,mul_sum]
    refine sum_congr rfl fun j _ => ?_
    unfold F nodes
    rw [cast_add_succ_div hr j,cast_add_succ_eq hr j,Nat.cast_succ,max_eq_left (one_le_one_add_div r j)]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hmesh]
  exact ht.trans ((mul_le_mul_of_nonneg_left hcurv (by positivity)).trans (by
    rw [div_pow,one_pow]; field_simp [hr'.ne']; linarith only [hA]))

#print axioms degreeSum_second_order

end GaloisForLFunctions.CountingHolography.Sections
