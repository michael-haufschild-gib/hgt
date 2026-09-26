import GaloisForLFunctions.RHTower.JacobiThetaBoundaryLimits
import Mathlib.Analysis.Complex.Liouville

/-!
# All-order flatness at the odd Jacobi theta cusp

The modular odd-cusp exponential estimate dominates every polynomial order in
an upper-half-plane cone. Shrinking Cauchy disks give the same flatness for
all complex derivatives. These estimates supply the differentiated endpoint
control required by the literal theta source's imaginary-axis arc charges.
-/

open Complex Filter Topology Set
noncomputable section
namespace RHTower.ThetaImaginaryArc


def oddTheta (w : ℂ) : ℂ := jacobiTheta (1+w)

private theorem exp_neg_div_le {a r : ℝ} (ha : 0<a) (hr : 0<r) (n : ℕ) :
    Real.exp (-a/r) ≤ (n.factorial:ℝ)/a^n*r^n := by
  have hx : 0 < a/r := div_pos ha hr
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hh := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (a/r) hx.le n)
  have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(a/r))).le
  have he : Real.exp (a/r)*Real.exp (-(a/r)) = 1 := by rw [← Real.exp_add]; simp
  have hk : Real.exp (-(a/r)) ≤ (n.factorial:ℝ)/(a/r)^n := by
    apply (le_div_iff₀ (pow_pos hx n)).mpr
    calc
      Real.exp (-(a/r))*(a/r)^n = (a/r)^n*Real.exp (-(a/r)) := mul_comm _ _
      _ ≤ Real.exp (a/r)*(n.factorial:ℝ)*Real.exp (-(a/r)) := hm
      _ = n.factorial := by rw [mul_right_comm, he, one_mul]
  convert hk using 1
  · congr 1
    ring
  · rw [div_pow]
    field_simp

/-- Every polynomial order is dominated at the odd cusp inside a fixed cone. -/
theorem oddTheta_power_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 < w.im → ‖w‖ ≤ 1/20 → ‖w‖ ≤ 5*w.im →
      ‖oddTheta w‖ ≤ C*‖w‖^n := by
  let a : ℝ := Real.pi/20
  let C : ℝ := 2*jacobiThetaTailConstant*((n+1).factorial:ℝ)/a^(n+1)
  have ha : 0<a := by dsimp [a]; positivity
  have hK : 0<jacobiThetaTailConstant := jacobiThetaTailConstant_pos
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro w hw hr1 hcone
  have hr : 0<‖w‖ := norm_pos_iff.mpr (ne_zero_of_im_pos hw)
  have hsq : Complex.normSq w = ‖w‖^2 := Complex.normSq_eq_norm_sq w
  have hM : 4 ≤ w.im/Complex.normSq w := by
    rw [hsq, le_div_iff₀ (pow_pos hr 2)]
    nlinarith [mul_le_mul_of_nonneg_left hr1 hr.le]
  have hinv : 1/(5*‖w‖) ≤ w.im/Complex.normSq w := by
    rw [hsq, div_le_div_iff₀ (by positivity : 0<5*‖w‖) (pow_pos hr 2)]
    nlinarith [mul_le_mul_of_nonneg_left hcone hr.le]
  have he : Real.exp (-Real.pi*(w.im/Complex.normSq w)/4) ≤ Real.exp (-a/‖w‖) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hinv (by positivity : 0≤Real.pi/4)
    have heq : (Real.pi/4)*(1/(5*‖w‖)) = a/‖w‖ := by dsimp [a]; ring
    rw [heq] at hh
    calc
      -Real.pi*(w.im/Complex.normSq w)/4 = -(Real.pi/4*(w.im/Complex.normSq w)) := by ring
      _ ≤ -(a/‖w‖) := neg_le_neg hh
      _ = -a/‖w‖ := by ring
  have hp : ‖w‖^(-(1/2):ℝ) ≤ ‖w‖⁻¹ := by
    have hh := Real.rpow_le_rpow_of_exponent_ge hr (by linarith : ‖w‖≤1)
      (by norm_num : (-1:ℝ) ≤ -(1/2))
    simpa only [Real.rpow_neg_one] using hh
  calc
    ‖oddTheta w‖ ≤ ‖w‖^(-(1/2):ℝ)*(2*jacobiThetaTailConstant*
        Real.exp (-Real.pi*(w.im/Complex.normSq w)/4)) := norm_jacobiTheta_one_add_le hw hM
    _ ≤ ‖w‖⁻¹*(2*jacobiThetaTailConstant*Real.exp (-a/‖w‖)) := by
      exact mul_le_mul hp (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity) (by positivity)
    _ ≤ ‖w‖⁻¹*(2*jacobiThetaTailConstant*((((n+1).factorial:ℝ)/a^(n+1))*‖w‖^(n+1))) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr.le)
      exact mul_le_mul_of_nonneg_left (exp_neg_div_le ha hr (n+1)) (by positivity)
    _ = C*‖w‖^n := by
      dsimp [C]
      simp only [pow_succ]
      field_simp

private theorem im_disk_lower {w v : ℂ} (hv : ‖v-w‖ ≤ w.im/2) : w.im/2 ≤ v.im := by
  have hh : |v.im-w.im| ≤ w.im/2 := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (v-w)).trans hv
  linarith [(abs_le.mp hh).1]

private theorem norm_disk_upper {w v : ℂ} (hv : ‖v-w‖ ≤ w.im/2) :
    ‖v‖ ≤ ‖w‖+w.im/2 := by
  calc
    ‖v‖ = ‖v-w+w‖ := by congr 1; ring
    _ ≤ ‖v-w‖+‖w‖ := norm_add_le _ _
    _ ≤ ‖w‖+w.im/2 := by linarith

/-- Shrinking Cauchy disks transfer the odd-cusp flatness to every derivative. -/
theorem oddTheta_iteratedDeriv_power_bound (m n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w : ℂ, 0 < w.im → ‖w‖ ≤ 1/40 → ‖w‖ ≤ 2*w.im →
      ‖iteratedDeriv m oddTheta w‖ ≤ D*‖w‖^n := by
  obtain ⟨C,hC,hbound⟩ := oddTheta_power_bound (m+n)
  let D : ℝ := (m.factorial:ℝ)*C*2^(m+n)*4^m
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro w hw hr1 hcone
  have hr : 0<‖w‖ := norm_pos_iff.mpr (ne_zero_of_im_pos hw)
  have hy : w.im ≤ ‖w‖ := (le_abs_self w.im).trans (Complex.abs_im_le_norm w)
  have hrad : 0<w.im/2 := by positivity
  have hd : DiffContOnCl ℂ oddTheta (Metric.ball w (w.im/2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball w hrad.ne']
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm] at hv
    have hvim : 0<v.im := lt_of_lt_of_le hrad (im_disk_lower hv)
    apply DifferentiableAt.differentiableWithinAt
    exact (differentiableAt_jacobiTheta (by simpa using hvim)).comp v
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1+v) v)
  have hcircle : ∀ v ∈ Metric.sphere w (w.im/2), ‖oddTheta v‖ ≤ C*(2*‖w‖)^(m+n) := by
    intro v hv
    rw [Metric.mem_sphere, dist_eq_norm] at hv
    have hvle := hv.le
    have hvi := im_disk_lower hvle
    have hvn := norm_disk_upper hvle
    have hvsmall : ‖v‖ ≤ 1/20 := by linarith
    have hvcone : ‖v‖ ≤ 5*v.im := by linarith
    have hvnorm : ‖v‖ ≤ 2*‖w‖ := by linarith
    exact (hbound v (by linarith) hvsmall hvcone).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hvnorm (m+n)) hC)
  have hcb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hrad hd hcircle
  have hden : (‖w‖/4)^m ≤ (w.im/2)^m :=
    pow_le_pow_left₀ (by positivity) (by linarith) m
  calc
    ‖iteratedDeriv m oddTheta w‖ ≤ (m.factorial:ℝ)*(C*(2*‖w‖)^(m+n))/(w.im/2)^m := hcb
    _ ≤ (m.factorial:ℝ)*(C*(2*‖w‖)^(m+n))/(‖w‖/4)^m :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = D*‖w‖^n := by
      dsimp [D]
      rw [mul_pow, div_pow, pow_add]
      field_simp
      ring

theorem analytic_oddTheta : AnalyticOnNhd ℂ oddTheta {w : ℂ | 0<w.im} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_im)
  intro w hw
  exact ((differentiableAt_jacobiTheta (by simpa using hw)).comp w
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1+w) w)).differentiableWithinAt

/-- Every derivative tends to zero on a non-tangential approach to the odd cusp. -/
theorem tendsto_oddTheta_iteratedDeriv_zero {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto w l (𝓝 0)) (hcone : ∀ᶠ t in l, 0<(w t).im ∧ ‖w t‖≤2*(w t).im)
    (m : ℕ) : Tendsto (fun t => iteratedDeriv m oddTheta (w t)) l (𝓝 0) := by
  obtain ⟨D,hD,hbound⟩ := oddTheta_iteratedDeriv_power_bound m 1
  have hn : Tendsto (fun t => ‖w t‖) l (𝓝 0) := by simpa using hw.norm
  have hsmall : ∀ᶠ t in l, ‖w t‖≤1/40 :=
    (hn.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/40))).mono fun _ h => h.le
  have hb : ∀ᶠ t in l, ‖iteratedDeriv m oddTheta (w t)‖ ≤ D*‖w t‖ := by
    filter_upwards [hcone,hsmall] with t ht hs
    simpa only [pow_one] using hbound (w t) ht.1 hs ht.2
  apply squeeze_zero_norm' hb
  simpa using hn.const_mul D

end RHTower.ThetaImaginaryArc
