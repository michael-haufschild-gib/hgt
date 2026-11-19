import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
# Cosine loss on a vertical strip

Projecting an absolutely summable complex measure from a strip onto the
imaginary axis preserves the first-order reflected translation loss.
Only the bounded real parts enter the domination estimate.
-/

noncomputable section
open Filter Complex Topology
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry

/-- Product of the two reflected translation differences. -/
def exponentialLoss (z t : ℂ) := (1-cexp (z*t))*(1-cexp (-z*t))
private abbrev axis (z : ℂ) := (z.im : ℂ)*I

private theorem exponentialLoss_expand (z t : ℂ) :
    exponentialLoss z t = 2-cexp (z*t)-cexp (-z*t) := by
  have he : cexp (z*t)*cexp (-z*t) = 1 := by
    rw [← Complex.exp_add,neg_mul,add_neg_cancel,Complex.exp_zero]
  unfold exponentialLoss
  linear_combination he

private theorem exponentialLoss_axis (z : ℂ) (h : ℝ) :
    exponentialLoss (axis z) h = ((2*(1-Real.cos (h*z.im)) : ℝ) : ℂ) := by
  let p : ℂ := cexp (axis z * h)
  have hc : cexp (-axis z * h) = conj p := by
    simp only [p,axis,← Complex.exp_conj,map_mul,Complex.conj_I,Complex.conj_ofReal]
    congr 1
    ring
  change (1-p)*(1-cexp (-axis z*h)) = _
  rw [hc,← (show conj (1-p) = 1-conj p by simp)]
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
  apply congrArg Complex.ofReal
  have he : axis z*(h:ℂ) = ((h*z.im : ℝ):ℂ)*I := by dsimp only [axis]; push_cast; ring
  rw [show p = cexp (((h*z.im : ℝ):ℂ)*I) by rw [← he]]
  rw [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
    Complex.one_im,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
  linear_combination Real.sin_sq_add_cos_sq (h*z.im)

private theorem exponentialLoss_hasDerivAt (z : ℂ) : HasDerivAt (exponentialLoss z) 0 0 := by
  have hd (w : ℂ) := (hasDerivAt_const (0:ℂ) (1:ℂ)).sub
    ((hasDerivAt_const_mul (x := (0:ℂ)) w).cexp)
  simpa [exponentialLoss] using (hd z).mul (hd (-z))

private theorem exp_axis_bound {z : ℂ} (hz : |z.re| ≤ 1) {h : ℝ} (hh : 0 ≤ h) (h₁ : h ≤ 1) :
    ‖cexp (z*h) - cexp (axis z*h)‖ ≤ 2*h := by
  have he : z*h = ((z.re*h : ℝ):ℂ) + axis z*h := by
    rw [Complex.ofReal_mul,← add_mul,Complex.re_add_im]
  have hb : |z.re*h| ≤ h := by
    rw [abs_mul,abs_of_nonneg hh]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hz hh
  have hn : ‖cexp (axis z*h)‖ = 1 := by
    simp [axis,Complex.norm_exp,Complex.mul_re]
  rw [he,Complex.exp_add,← sub_one_mul,norm_mul,hn,mul_one,← Complex.ofReal_exp,
    ← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  linarith only [Real.abs_exp_sub_one_le (hb.trans h₁),hb]

private theorem exponentialLoss_error_bound {z : ℂ} (hz : |z.re| ≤ 1)
    {h : ℝ} (hh : 0 ≤ h) (h₁ : h ≤ 1) :
    ‖exponentialLoss z h-exponentialLoss (axis z) h‖ ≤ 4*h := by
  have hneg : axis (-z) = -axis z := by simp [axis]
  have hb := exp_axis_bound (z := -z) (by simpa using hz) hh h₁
  rw [hneg] at hb
  have he : exponentialLoss z h-exponentialLoss (axis z) h =
      -(cexp (z*h)-cexp (axis z*h)) - (cexp (-z*h)-cexp (-axis z*h)) := by
    rw [exponentialLoss_expand,exponentialLoss_expand]; ring
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_neg]
  linarith only [exp_axis_bound hz hh h₁,hb]

/-- Moving each ordinate horizontally to the critical line changes the first-order
cosine loss by zero. The strip width bounds the error uniformly in the ordinate. -/
theorem tendsto_strip_cosine_projection_error {ι : Type*} (z : ι → ℂ)
    (hz : ∀ q, |(z q).re| ≤ 1) {A : ι → ℂ} (hA : Summable fun q => ‖A q‖) :
    Tendsto (fun h : ℝ => ∑' q : ι, h⁻¹ •
      ((exponentialLoss (z q) h-((2*(1-Real.cos (h*(z q).im)) : ℝ):ℂ))*A q))
      (𝓝[>] 0) (𝓝 0) := by
  simp_rw [← exponentialLoss_axis]
  have hlim (q : ι) :=
    (((exponentialLoss_hasDerivAt (z q)).sub
      (exponentialLoss_hasDerivAt (axis (z q)))).mul_const (A q)).comp_ofReal.tendsto_slope_zero_right
  have hp : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have h₁ : ∀ᶠ h : ℝ in 𝓝[>] 0, h ≤ 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_le_const (by norm_num : (0:ℝ)<1)
  have he : (∑' _ : ι, (0 : ℂ)) = 0 := tsum_zero
  rw [← he]
  apply tendsto_tsum_of_dominated_convergence (hA.mul_left 4)
  · intro q
    simpa [exponentialLoss] using hlim q
  · filter_upwards [hp,h₁] with h hh h₁' q
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hh.le),norm_mul,← div_eq_inv_mul,
      div_le_iff₀ hh]
    have hb := exponentialLoss_error_bound
      (hz q) hh.le h₁'
    linarith only [mul_le_mul_of_nonneg_right hb (norm_nonneg (A q))]

#print axioms tendsto_strip_cosine_projection_error

end GaloisForLFunctions.HTGeometry
