import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.GaussianLabelSeparation
import GaloisForLFunctions.RHTower.ThetaQuadratureDefectSpectralKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The binary Gaussian entropy boundary layer

At log likelihood ratio z, the geometric mean of the two weighted
densities is multiplied by an even, integrable function. Its integral
is exactly 4π. The mass follows by differentiating an explicit primitive
involving arctan(exp(z/2)).
-/

noncomputable section
open MeasureTheory Filter Real
open scoped Topology
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair

private def side (x : ℝ) := exp (-x/2)*log (1+exp x)

/-- The density of the conditional label loss in log-odds coordinates. -/
def oddsKernel (x : ℝ) := side x+side (-x)

private theorem side_pos (x : ℝ) : 0<side x :=
  mul_pos (exp_pos _) (log_pos (by linarith only [exp_pos x]))

theorem oddsKernel_pos (x : ℝ) : 0<oddsKernel x := add_pos (side_pos _) (side_pos _)

private theorem side_cont : Continuous side := by
  unfold side
  apply Continuous.mul
  · fun_prop
  · exact (continuous_const.add continuous_exp).log (fun x => (add_pos zero_lt_one (exp_pos x)).ne')

theorem oddsKernel_cont : Continuous oddsKernel :=
  side_cont.add (side_cont.comp continuous_neg)

private theorem left_tail (x : ℝ) : side x≤exp (x/2) := by
  have hl : log (1+exp x)≤exp x := by
    linarith only [log_le_sub_one_of_pos (show 0<1+exp x by positivity)]
  calc
    _ ≤ exp (-x/2)*exp x := mul_le_mul_of_nonneg_left hl (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

private theorem right_tail (x : ℝ) : side x≤4*exp (-x/4) := by
  let y := exp (x/4)
  have hy := exp_pos (x/4)
  have he : y^4=exp x := by unfold y; rw [← exp_nat_mul]; congr 1; ring
  have hpow : 1+exp x ≤ (1+y)^4 := by
    rw [← he]
    nlinarith only [show 0≤y from hy.le,sq_nonneg y,pow_nonneg hy.le 3]
  have hl := log_le_log (show 0<1+exp x by positivity) hpow
  rw [log_pow] at hl
  norm_num at hl
  have hlog : log (1+y) ≤ y :=
    (log_le_sub_one_of_pos (show 0<1+y by positivity)).trans_eq (by ring)
  have hb : log (1+exp x)≤4*y := by linarith only [hl,hlog]
  calc
    _ ≤ exp (-x/2)*(4*y) := mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = 4*(exp (-x/2)*y) := by ring
    _ = _ := by unfold y; rw [← exp_add]; congr 2; ring

private theorem side_int : Integrable side := by
  apply (_root_.RHTower.integrable_exp_neg_abs_div_four.const_mul 4).mono' side_cont.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_pos (side_pos x)]
  rcases le_total 0 x with h|h
  · simpa only [abs_of_nonneg h,neg_div] using right_tail x
  · rw [abs_of_nonpos h]
    have hl : x/2≤ -(-x/4) := by linarith only [h]
    exact (left_tail x).trans ((exp_le_exp.mpr hl).trans (by linarith only [exp_pos (-(-x/4))]))

theorem oddsKernel_integrable : Integrable oddsKernel := side_int.add side_int.comp_neg

private def primitive (x : ℝ) : ℝ := -2*side x+4*Real.arctan (Real.exp (x/2))

private theorem primitive_deriv (x : ℝ) : HasDerivAt primitive (side x) x := by
  let y := exp (x/2)
  have hy : y≠0 := (exp_pos _).ne'
  have hp : y^2=exp x := by unfold y; rw [← exp_nat_mul]; congr 1; ring
  have hm : exp (-x/2)=y⁻¹ := by rw [neg_div,exp_neg]
  have e := ((hasDerivAt_id x).div_const 2).exp
  have d := (((hasDerivAt_id x).neg.div_const 2).exp).mul
    (((hasDerivAt_exp x).const_add 1).log (by positivity))
  have full := (d.const_mul (-2)).add (((hasDerivAt_arctan y).comp x e).const_mul 4)
  have coeff :
      -2*(exp (-x/2)*(-1/2)*log (1+exp x)+exp (-x/2)*(exp x/(1+exp x)))+
        4*(1/(1+y^2)*(exp (x/2)*(1/2))) = side x := by
    rw [side,hm,← hp]
    change -2*(y⁻¹*(-1/2)*log (1+y^2)+y⁻¹*(y^2/(1+y^2)))+
      4*(1/(1+y^2)*(y*(1/2))) = y⁻¹*log (1+y^2)
    field_simp [hy,show 1+y^2≠0 by positivity]
    ring
  simp only [Pi.neg_apply,id_eq,coeff] at full
  exact full

private theorem left_limit : Tendsto side atBot (𝓝 0) := by
  apply squeeze_zero (fun x => (side_pos x).le) left_tail
  exact tendsto_exp_atBot.comp (tendsto_id.atBot_div_const (by norm_num : (0:ℝ)<2))

private theorem right_limit : Tendsto side atTop (𝓝 0) := by
  apply squeeze_zero (fun x => (side_pos x).le) right_tail
  have h := (tendsto_exp_atBot.comp ((tendsto_neg_atTop_atBot).atBot_div_const (by norm_num : (0:ℝ)<4))).const_mul 4
  simpa only [Function.comp_def,mul_zero] using h

private theorem side_mass : (∫ x, side x)=2*π := by
  have H := tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2)
  have e := tendsto_exp_atBot.comp (tendsto_id.atBot_div_const (by norm_num : (0:ℝ)<2))
  have low : Tendsto primitive atBot (𝓝 0) := by
    unfold primitive
    simpa only [Function.comp_def,id_eq,mul_zero,arctan_zero,add_zero] using
      (left_limit.const_mul (-2)).add ((continuous_arctan.continuousAt.tendsto.comp e).const_mul 4)
  have high : Tendsto primitive atTop (𝓝 (4*(π/2))) := by
    unfold primitive
    simpa only [Function.comp_def,id_eq,mul_zero,zero_add] using
      (right_limit.const_mul (-2)).add
        ((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp (tendsto_exp_atTop.comp H)).const_mul 4)
  rw [integral_of_hasDerivAt_of_tendsto primitive_deriv side_int low high]
  ring

/-- Total log-odds mass controlling the sharp small-noise entropy prefactor. -/
theorem oddsKernel_mass : (∫ x, oddsKernel x)=4*π := by
  rw [show (∫ x, oddsKernel x)=(∫ x, side x)+(∫ x, side (-x)) from integral_add side_int side_int.comp_neg,
    integral_neg_eq_self,side_mass]
  ring

/-- Conditional entropy at two positive densities factors through their
geometric mean and the log likelihood ratio. -/
theorem log_odds_loss (A B : {u : ℝ // 0<u}) :
    A.val*(log (A.val+B.val)-log A.val)+B.val*(log (A.val+B.val)-log B.val) =
      sqrt (A.val*B.val)*oddsKernel (log B.val-log A.val) := by
  let z := log B.val-log A.val
  let m := (log A.val+log B.val)/2
  have ea : exp (m-z/2)=A.val := by rw [show m-z/2=log A.val by dsimp [m,z]; ring,exp_log A.property]
  have eb : exp (m+z/2)=B.val := by rw [show m+z/2=log B.val by dsimp [m,z]; ring,exp_log B.property]
  have hm : sqrt (A.val*B.val)=exp m := by
    rw [← ea,← eb,← exp_add,show m-z/2+(m+z/2)=m+m by ring,exp_add,← sq,sqrt_sq (exp_pos _).le]
  have hz : exp z=B.val/A.val := by dsimp only [z]; rw [exp_sub,exp_log A.property,exp_log B.property]
  have hn : exp (-z)=A.val/B.val := by rw [exp_neg,hz,inv_div]
  have la : log (A.val+B.val)-log A.val=log (1+exp z) := by
    rw [← log_div (add_pos A.property B.property).ne' A.property.ne',hz,add_div,div_self A.property.ne']
  have lb : log (A.val+B.val)-log B.val=log (1+exp (-z)) := by
    rw [← log_div (add_pos A.property B.property).ne' B.property.ne',hn,add_div,div_self B.property.ne',add_comm]
  change _=sqrt (A.val*B.val)*oddsKernel z
  have fa : exp m*exp (-z/2) = A.val := by
    rw [← exp_add,show m+-z/2=m-z/2 by ring]
    exact ea
  have fb : exp m*exp (z/2) = B.val := by rw [← exp_add]; exact eb
  rw [hm,la,lb]
  simp only [oddsKernel,side,neg_neg,mul_add (exp m),← mul_assoc (exp m),fa,fb]

/-- A vanishing Gaussian damping in the log-odds coordinate preserves
the full boundary-layer mass for any fixed prior odds. -/
theorem damped_odds_limit (h d : ℝ) :
    Tendsto (fun l : ℝ => ∫ z, oddsKernel z*exp (-(exp l)*(z-h)^2/(2*d^2))) atBot (𝓝 (4*π)) := by
  rw [← oddsKernel_mass]
  apply tendsto_integral_filter_of_dominated_convergence oddsKernel
  · exact .of_forall fun l => (oddsKernel_cont.mul (by fun_prop)).aestronglyMeasurable
  · exact .of_forall fun l => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_pos (mul_pos (oddsKernel_pos _) (exp_pos _))]
      exact mul_le_of_le_one_right (oddsKernel_pos _).le (exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (exp_pos l).le) (sq_nonneg _))
          (by positivity)))
  · exact oddsKernel_integrable
  · refine ae_of_all _ fun z => ?_
    have ht := Real.continuous_exp.continuousAt.tendsto.comp
      (((tendsto_exp_atBot.neg).mul_const ((z-h)^2)).div_const (2*d^2))
    simpa only [Function.comp_apply,neg_zero,zero_mul,zero_div,exp_zero,mul_one] using
      ht.const_mul (oddsKernel z)

#print axioms oddsKernel_mass
#print axioms log_odds_loss
#print axioms damped_odds_limit
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.NoisyPair
