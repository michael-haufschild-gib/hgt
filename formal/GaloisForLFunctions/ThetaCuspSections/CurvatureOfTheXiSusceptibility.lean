import GaloisForLFunctions.ThetaCuspSections.GibbsResponse
import GaloisForLFunctions.RHTower.XiMagnetizationGHSConcavity

/-!
# Quantitative susceptibility of the real Xi tilt

Moving the digamma argument by an arbitrary number of unit steps exposes
a sum of simple poles. The remaining magnetization is positive and concave
on the far ray. Its first two derivative inequalities telescope to inverse
linear and inverse quadratic bounds. In particular every positive tilt has
strictly negative third cumulant and its scale heat capacity grows unboundedly.
-/

open Set Finset Filter Topology RHTower

namespace ThetaCuspSections

noncomputable section

private def poleShift (j : ℕ) : ℝ := 33/2 + 2*j

private def remainder (n : ℕ) (w : ℝ) := xiRealLogDeriv w + ∑ j ∈ range n, (w+poleShift j)⁻¹

private theorem shift_pos {w : ℝ} (hw : 0 < w) (j : ℕ) : 0 < w+poleShift j := by
  dsimp [poleShift]
  positivity

private theorem concave_remainder (n : ℕ) : ConcaveOn ℝ (Ici (17/2)) (remainder n) := by
  let g (y : ℝ) := (Complex.digamma ((y : ℝ) : ℂ)).re
  have hg : ConcaveOn ℝ (Ioi 0) (fun y : ℝ => g (y+n)) :=
    (concaveOn_re_digamma.translate_left (n : ℝ)).subset
      (fun y hy => show 0 < y+n from add_pos_of_pos_of_nonneg hy (Nat.cast_nonneg n)) (convex_Ioi 0)
  have hc := (((concaveOn_ghsFinitePart.add
    (concaveOn_const (𝕜 := ℝ) (-(Real.log Real.pi / 2)) (convex_Ici (9 : ℝ)))).add
    (concaveOn_half_comp_affine hg)).add (concaveOn_re_logDeriv_riemannZeta.subset
      (fun x (hx : 9 ≤ x) => show 1 < x by linarith) (convex_Ici 9))).translate_right (1/2 : ℝ)
  apply (hc.subset (fun w (hw : (17:ℝ)/2 ≤ w) => show 9 ≤ 1/2+w by linarith)
    (convex_Ici _)).congr
  intro w hw
  let x := 1/2+w
  have hpos : 0 < x/2+8 := by dsimp [x]; change (17:ℝ)/2 ≤ w at hw; linarith
  have hshift := re_digamma_shift hpos n
  have hsum : (∑ j ∈ range n, 1/(x/2+8+(j : ℝ)))/2 = ∑ j ∈ range n, (w+poleShift j)⁻¹ := by
    rw [Finset.sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [div_div, one_div, show (x/2+8+j)*2 = w+poleShift j by dsimp [x,poleShift]; ring]
  simp only [Function.comp_apply, Pi.add_apply]
  rw [remainder, xiRealLogDeriv_eq_ghsGammaPrimeForm (by change (17:ℝ)/2 ≤ w at hw; linarith)]
  change ghsFinitePart x + - (Real.log Real.pi / 2) + g (x/2+8+n)/2 +
    (logDeriv riemannZeta (x : ℂ)).re = ghsGammaPrimeForm x + _
  unfold ghsGammaPrimeForm g
  linarith only [hshift, hsum]

private def poleSlope (n : ℕ) (w : ℝ) := ∑ j ∈ range n, -((w+poleShift j)^2)⁻¹

private theorem rem_deriv (n : ℕ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (remainder n) (deriv xiRealLogDeriv w + poleSlope n w) w :=
  (hasDerivAt_xiRealLogDeriv w).differentiableAt.hasDerivAt.add
    (HasDerivAt.fun_sum (u := range n) (A := fun j (y : ℝ) => (y+poleShift j)⁻¹)
      fun j _ => hasDerivAt_inv_add (shift_pos hw j).ne')

private theorem rem_second (n : ℕ) {w : ℝ} (hw : 0 < w) :
    deriv (deriv (remainder n)) w = deriv (deriv xiRealLogDeriv) w +
      ∑ j ∈ range n, 2*((w+poleShift j)^3)⁻¹ := by
  have he : deriv (remainder n) =ᶠ[𝓝 w] fun x => deriv xiRealLogDeriv x + poleSlope n x := by
    filter_upwards [Ioi_mem_nhds hw] with x hx using (rem_deriv n hx).deriv
  rw [he.deriv_eq]
  exact ((hasDerivAt_deriv_xiRealLogDeriv hw).differentiableAt.hasDerivAt.add
    (HasDerivAt.fun_sum (u := range n) (A := fun j (y : ℝ) => -((y+poleShift j)^2)⁻¹)
      fun j _ => hasDerivAt_neg_inv_sq_add (shift_pos hw j).ne')).deriv

private theorem rem_nonneg (n : ℕ) {w : ℝ} (hw : 0 < w) : 0 ≤ remainder n w := by
  apply add_nonneg _ (sum_nonneg fun j _ => inv_nonneg.mpr (shift_pos hw j).le)
  rw [xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment hw]
  exact (mul_pos hw (re_xiShiftedReciprocalMoment_pos (pow_pos hw 2) (by norm_num))).le

private theorem finite_slope (n : ℕ) {w : ℝ} (hw : 17/2 ≤ w) :
    ∑ j ∈ range n, ((w+poleShift j)^2)⁻¹ ≤ deriv xiRealLogDeriv w := by
  have hw' : 0 < w := by linarith
  have hd := rem_deriv n hw'
  let v := deriv xiRealLogDeriv w + poleSlope n w
  have hv : 0 ≤ v := by
    by_contra! hn
    let t := (remainder n w+1)/(-v)
    have ht : 0 < t := div_pos (by linarith only [rem_nonneg n hw']) (neg_pos.mpr hn)
    have hs := (concave_remainder n).slope_le_of_hasDerivAt hw (by change 17/2 ≤ w+t; linarith)
      (lt_add_of_pos_right w ht) hd
    rw [slope_def_field, add_sub_cancel_left, div_le_iff₀ ht] at hs
    have ht' : (-v)*t = remainder n w+1 := by dsimp [t]; field_simp [hn.ne]
    have hp := rem_nonneg n (add_pos hw' ht)
    change remainder n (w+t)-remainder n w ≤ v*t at hs
    linarith only [ht', hs, hp]
  dsimp [v,poleSlope] at hv
  rw [sum_neg_distrib] at hv
  linarith only [hv]

private theorem finite_curvature (n : ℕ) {w : ℝ} (hw : 17/2 < w) :
    deriv (deriv xiRealLogDeriv) w + ∑ j ∈ range n, 2*((w+poleShift j)^3)⁻¹ ≤ 0 := by
  have ha := (concave_remainder n).antitoneOn_deriv
    (fun x (hx : 17/2 ≤ x) => (rem_deriv n (by linarith : 0 < x)).differentiableAt)
  have he := ha.derivWithin_nonpos (x := w)
  rwa [derivWithin_of_mem_nhds (Ici_mem_nhds hw), rem_second n (by linarith : 0 < w)] at he

private theorem sum_poles_lower {w : ℝ} (hw : 0 < w) (n : ℕ) :
    ((w+poleShift 0)⁻¹-(w+poleShift n)⁻¹)/2 ≤ ∑ j ∈ range n, ((w+poleShift j)^2)⁻¹ ∧
    (((w+poleShift 0)^2)⁻¹-((w+poleShift n)^2)⁻¹)/2 ≤
      ∑ j ∈ range n, 2*((w+poleShift j)^3)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    let y := w+poleShift n
    have hy : 0 < y := shift_pos hw n
    have hs : w+poleShift (n+1) = y+2 := by simp [y,poleShift]; ring
    have h₁ : (y⁻¹-(y+2)⁻¹)/2 ≤ (y^2)⁻¹ := by
      field_simp
      nlinarith only [hy, sq_nonneg y]
    have h₂ : ((y^2)⁻¹-((y+2)^2)⁻¹)/2 ≤ 2*(y^3)⁻¹ := by
      field_simp
      nlinarith only [hy, sq_nonneg y, pow_nonneg hy.le 3, pow_nonneg hy.le 4]
    rw [sum_range_succ, sum_range_succ, hs]
    exact ⟨by linarith only [ih.1,h₁], by linarith only [ih.2,h₂]⟩

private theorem tendsto_inv_shift (w : ℝ) :
    Tendsto (fun n : ℕ => (w+poleShift n)⁻¹) atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  refine tendsto_atTop_mono' _ ?_ tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop ⌈|w|⌉₊] with n hn
  have h := (Nat.le_ceil |w|).trans (Nat.cast_le.mpr hn)
  dsimp [poleShift]
  linarith only [h,neg_abs_le w]

/-- The variance is bounded below by the reciprocal field on the entire far ray. -/
theorem xi_susceptibility_lower {w : ℝ} (hw : 17/2 ≤ w) :
    1/(2*(w+33/2)) ≤ deriv xiRealLogDeriv w := by
  have hw' : 0 < w := by linarith
  have ht := ((tendsto_const_nhds (x := (w+poleShift 0)⁻¹)).sub (tendsto_inv_shift w)).div_const 2
  have h := le_of_tendsto ht (Eventually.of_forall fun n =>
    (sum_poles_lower hw' n).1.trans (finite_slope n hw))
  simpa [poleShift,one_div,mul_inv_rev,div_eq_mul_inv] using h

/-- The negative third cumulant has an explicit inverse-square lower bound in magnitude. -/
theorem xi_third_cumulant_upper {w : ℝ} (hw : 17/2 < w) :
    deriv (deriv xiRealLogDeriv) w ≤ -(1/(2*(w+33/2)^2)) := by
  have hw' : 0 < w := by linarith
  have ht := ((tendsto_const_nhds (x := ((w+poleShift 0)^2)⁻¹)).sub
    ((tendsto_inv_shift w).pow 2)).div_const 2
  have h := le_of_tendsto ht (b := -deriv (deriv xiRealLogDeriv) w) (Eventually.of_forall fun n => by
    rw [← inv_pow]
    linarith only [(sum_poles_lower hw' n).2, finite_curvature n hw])
  simp [poleShift,one_div,mul_inv_rev,div_eq_mul_inv] at h ⊢
  linarith only [h]

/-- Strict pointwise GHS on every positive field, including the transition between the two bounds. -/
theorem xi_third_cumulant_negative (w : {x : ℝ // 0 < x}) :
    deriv (deriv xiRealLogDeriv) w.val < 0 := by
  by_cases h : w.val ≤ 9
  · apply deriv2_xiRealLogDeriv_neg w.property
    nlinarith only [mul_self_le_mul_self w.property.le h]
  · exact (xi_third_cumulant_upper (by linarith : 17/2 < w.val)).trans_lt (by positivity)

/-- Under pure scale control the heat capacity is at least linear in the field asymptotically. -/
theorem tiltCapacity_lower (u v : ℝ) (h : 17/2 ≤ Real.exp (u-v)) :
    Real.exp (u-v)^2/(2*(Real.exp (u-v)+33/2)) ≤ tiltCapacity u v := by
  rw [tiltCapacity_eq_xi_susceptibility, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (xi_susceptibility_lower h) (sq_nonneg _)

#print axioms xi_susceptibility_lower
#print axioms xi_third_cumulant_upper
#print axioms xi_third_cumulant_negative
#print axioms tiltCapacity_lower

end

end ThetaCuspSections
