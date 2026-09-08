import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceParameterHolomorphy
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles
import Mathlib.Analysis.Meromorphic.Complex

/-! Continuation of the original dressed BM radial solutions and connection factor. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The nonconstant physical horizon dressing is entire in its exponent. -/
theorem power_exponent_entire {z : ℝ} (hz : 0 < z) :
    Differentiable ℂ (fun a => power a z) := by
  unfold power
  exact differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))

/-- The original ingoing solution is holomorphic in frequency off the real axis,
with the physical radial power retained. -/
theorem horizon_frequency_analyticAt (w chi : ℂ) (hw : w.im ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo 0 1) : AnalyticAt ℂ (fun u => horizon u chi z) w := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have he : ∀ᶠ u : ℂ in 𝓝 w, u.im ≠ 0 := Complex.continuous_im.continuousAt.eventually_ne hw
  filter_upwards [he] with u hu
  have hpow := (power_exponent_entire hz.1).differentiableAt.comp u
    (show DifferentiableAt ℂ (fun v : ℂ => v/2) u by fun_prop)
  have hgauss := horizonGauss_frequency_differentiableAt u chi (z:ℂ) hu
    (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz.1] using hz.2)
  exact hpow.mul hgauss

/-- The original normalizable solution is entire in frequency in the physical interior. -/
theorem normalizable_frequency_entire (chi : ℂ) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    Differentiable ℂ (fun w => normalizable w chi z) := by
  intro w
  have hpow := (power_exponent_entire hz.1).differentiableAt.comp w
    (show DifferentiableAt ℂ (fun v : ℂ => v/2) w by fun_prop)
  have hnorm : ‖((1-z:ℝ):ℂ)‖ < 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith [hz.2])]
    linarith [hz.1]
  have hg := outerGauss_frequency_differentiableAt w chi ((1-z:ℝ):ℂ) hnorm
  simpa only [normalizable,dress,outerFactor,Complex.ofReal_sub,Complex.ofReal_one] using!
    hpow.mul (hg.const_mul (power (1/2) (1-z)))

/-- Gamma-pole cancellation is kept through the entire reciprocal Gamma factors.
The actual connection is analytic off the real frequency axis, including its QNM zeros. -/
theorem connection_frequency_analyticAt (w chi : ℂ) (hw : w.im ≠ 0) :
    AnalyticAt ℂ (fun u => connection u chi) w := by
  have hc : ∀ n : ℕ, gaussC w ≠ -(n:ℂ) := by
    intro n hn
    apply hw
    have hh := congrArg Complex.im hn
    simpa only [gaussC,Complex.add_im,Complex.one_im,Complex.neg_im,Complex.natCast_im,
      neg_zero,zero_add] using hh
  have hg := (_root_.HTGeometry.analyticAt_Gamma_off_poles hc).comp
    (show AnalyticAt ℂ gaussC w by unfold gaussC; fun_prop)
  have hi := Complex.differentiable_one_div_Gamma
  have ha : AnalyticAt ℂ (fun u => (Complex.Gamma (gaussC u-gaussA u chi))⁻¹) w :=
    (hi.analyticAt _).comp (show AnalyticAt ℂ (fun u => gaussC u-gaussA u chi) w by
      unfold gaussC gaussA; fun_prop)
  have hb : AnalyticAt ℂ (fun u => (Complex.Gamma (gaussC u-gaussB u chi))⁻¹) w :=
    (hi.analyticAt _).comp (show AnalyticAt ℂ (fun u => gaussC u-gaussB u chi) w by
      unfold gaussC gaussB; fun_prop)
  have hk : AnalyticAt ℂ (fun _ : ℂ => Complex.Gamma (1/2:ℂ)) w := analyticAt_const
  have hp := ((hg.mul hk).mul ha).mul hb
  simpa only [connection,Function.comp_def,Pi.mul_def,div_eq_mul_inv,mul_inv_rev,
    mul_assoc,mul_comm,mul_left_comm] using! hp

/-- The original radial Green numerator divided by its full Wronskian normalization
is meromorphic in frequency. This statement concerns the kernel, before endpoint integration. -/
theorem greenKernel_frequency_meromorphicAt (w chi : ℂ) (hw : w.im ≠ 0)
    {z t : ℝ} (hz : z ∈ Ioo 0 1) (ht : t ∈ Ioo 0 1) :
    MeromorphicAt (fun u => horizon u chi (min z t)*normalizable u chi (max z t)/(-connection u chi)) w := by
  have hmin : min z t ∈ Ioo (0:ℝ) 1 := ⟨lt_min hz.1 ht.1,(min_le_left _ _).trans_lt hz.2⟩
  have hmax : max z t ∈ Ioo (0:ℝ) 1 := ⟨hz.1.trans_le (le_max_left _ _),max_lt hz.2 ht.2⟩
  exact ((horizon_frequency_analyticAt w chi hw hmin).meromorphicAt.mul
    ((normalizable_frequency_entire chi hmax).analyticAt w).meromorphicAt).div
      (connection_frequency_analyticAt w chi hw).meromorphicAt.neg

end
end RHTower.D4BMLaplaceRadial
