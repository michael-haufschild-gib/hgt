import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.HardyThetaSource
import GaloisForLFunctions.RHTower.ThetaCuspReflection

/-!
# The literal theta source satisfies the complex Ward equation

The centered potential `exp(z/2) * theta(I * exp(2*z))` is holomorphic
on the theta source strip. Its real derivatives agree with the existing
literal theta-tail jets. Analytic continuation therefore extends the exact
real Ward equation to `thetaCuspStripSource` throughout that strip.

This is the source-specific differential identity needed by the imaginary-axis
arc-charge argument. Endpoint flatness and the arc charges are not proved here.
-/

open Complex Filter Topology Set HurwitzZeta
noncomputable section
namespace RHTower.ThetaImaginaryArc


def Potential (z : ℂ) : ℂ := Complex.exp (z/2) * jacobiTheta (Complex.I*Complex.exp (2*z))

def realJet (m : ℕ) (x : ℝ) : ℝ :=
  2*thetaCuspTailDerivative m x + Real.exp (x/2)/(2:ℝ)^m

private theorem double_mem_hardyStrip {z : ℂ} (hz : z ∈ thetaCuspStrip) : 2*z ∈ hardyStrip := by
  change |(2*z).im| < Real.pi/2
  have hz' : |z.im| < Real.pi/4 := hz
  norm_num [Complex.mul_im, abs_mul]
  linarith

theorem analytic_potential : AnalyticOnNhd ℂ Potential thetaCuspStrip := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_thetaCuspStrip
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have harg : DifferentiableAt ℂ (fun w : ℂ => Complex.I*Complex.exp (2*w)) z := by fun_prop
  have ht := (differentiableAt_jacobiTheta (im_I_mul_exp_pos (double_mem_hardyStrip hz))).comp z harg
  exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w/2)) z).mul ht

theorem potential_real (x : ℝ) : Potential (x:ℂ) = (realJet 0 x : ℂ) := by
  have hθ := jacobiTheta_I_mul_ofReal (Real.exp_pos (2*x))
  have hpow : Complex.exp (2*(x:ℂ)) = (Real.exp (2*x) : ℂ) := by
    rw [show 2*(x:ℂ) = ((2*x:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  have hhalf : Complex.exp ((x:ℂ)/2) = (Real.exp (x/2) : ℂ) := by
    rw [show (x:ℂ)/2 = ((x/2:ℝ):ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  rw [Potential, hpow, hhalf, realJet, thetaCuspTailDerivative_zero_eq_evenKernel]
  push_cast at hθ ⊢
  linear_combination Complex.exp ((x:ℂ)/2)*hθ

theorem hasDerivAt_realJet (m : ℕ) (x : ℝ) :
    HasDerivAt (realJet m) (realJet (m+1) x) x := by
  have he := ((((hasDerivAt_id x).div_const (2:ℝ)).exp).div_const ((2:ℝ)^m))
  have ht := ((hasDerivAt_thetaCuspTailDerivative m x).const_mul (2:ℝ)).add he
  apply ht.congr_deriv
  dsimp [realJet]
  rw [pow_succ]
  ring

private theorem real_mem (x : ℝ) : (x:ℂ) ∈ thetaCuspStrip := by
  simp [thetaCuspStrip, Real.pi_pos]

theorem deriv_potential_real (x : ℝ) : deriv Potential (x:ℂ) = (realJet 1 x : ℂ) := by
  have hc := (analytic_potential (x:ℂ) (real_mem x)).differentiableAt.hasDerivAt.comp_ofReal
  have hr := (hasDerivAt_realJet 0 x).ofReal_comp
  have hc' : HasDerivAt (fun y : ℝ => (realJet 0 y : ℂ)) (deriv Potential (x:ℂ)) x := by
    simpa only [potential_real] using hc
  exact hc'.unique hr

theorem deriv2_potential_real (x : ℝ) : deriv (deriv Potential) (x:ℂ) = (realJet 2 x : ℂ) := by
  have hc := (analytic_potential.deriv (x:ℂ) (real_mem x)).differentiableAt.hasDerivAt.comp_ofReal
  have hr := (hasDerivAt_realJet 1 x).ofReal_comp
  have hc' : HasDerivAt (fun y : ℝ => (realJet 1 y : ℂ)) (deriv (deriv Potential) (x:ℂ)) x := by
    simpa only [deriv_potential_real] using hc
  exact hc'.unique hr

theorem source_real_ward (x : ℝ) :
    ((realJet 2 x - realJet 0 x / 4)/2 : ℝ) = thetaCuspFullSource x := by
  rw [thetaCuspFullSource_eq_tail_second_sub, realJet, realJet]
  ring

/-- The Ward equation holds for the literal source throughout its holomorphic strip. -/
theorem source_complex_ward {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    thetaCuspStripSource z = (deriv (deriv Potential) z - Potential z/4)/2 := by
  let F : ℂ → ℂ := fun w => (deriv (deriv Potential) w - Potential w/4)/2 - thetaCuspStripSource w
  have hFan : AnalyticOnNhd ℂ F thetaCuspStrip :=
    ((analytic_potential.deriv.deriv.sub analytic_potential.div_const).div_const).sub
      analyticOnNhd_thetaCuspStripSource
  have hreal : ∀ x : ℝ, F (x:ℂ) = 0 := by
    intro x
    dsimp [F]
    rw [deriv2_potential_real, potential_real, thetaCuspStripSource_ofReal]
    have hh := congrArg (fun v : ℝ => (v:ℂ)) (source_real_ward x)
    push_cast at hh
    linear_combination hh
  have hfreq : ∃ᶠ w in 𝓝[≠] (0:ℂ), F w = 0 := by
    have htend : Tendsto (fun n : ℕ => ((1/((n:ℝ)+1):ℝ):ℂ)) atTop (𝓝[≠] (0:ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hh := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [Function.comp_def, Complex.ofReal_zero] using hh
      · exact Filter.Eventually.of_forall fun n => by
          simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_ne_zero]
          positivity
    exact htend.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => hreal _))
  have heq := hFan.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_thetaCuspStrip (real_mem 0) hfreq
  have hh := heq hz
  dsimp [F] at hh
  linear_combination -hh

end RHTower.ThetaImaginaryArc
