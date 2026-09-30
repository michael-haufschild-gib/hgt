import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionDensityTail
import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionMeasure
import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionEndpointComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed



open MeasureTheory Filter Set Metric Topology
open scoped BigOperators

namespace RHTower
noncomputable section

private def infiniteBorelEntireFactorialKernel (z : ℂ) : ℂ :=
  ∑' j : ℕ, z^(2*j)/((2*j).factorial:ℂ)^2

private theorem infiniteBorel_evenDiagonal_injective :
    Function.Injective (fun j : ℕ => (2*j,2*j)) := by
  intro j k h
  have h' := congrArg Prod.fst h
  change 2*j=2*k at h'
  omega

private theorem infiniteBorel_sqrt_diagonal_eq {r : ℝ} (hr : 0≤r) (j : ℕ) :
    ((Real.sqrt r)^(2*j)/((2*j).factorial:ℝ))*
      ((Real.sqrt r)^(2*j)/((2*j).factorial:ℝ)) =
      r^(2*j)/((2*j).factorial:ℝ)^2 := by
  rw [div_mul_div_comm]
  congr 1
  · rw [← mul_pow,← pow_two,Real.sq_sqrt hr]
  · ring

private theorem infiniteBorel_factorialKernel_summable_norm (z : ℂ) :
    Summable (fun j : ℕ => ‖z^(2*j)/((2*j).factorial:ℂ)^2‖) := by
  let f : ℕ→ℝ := fun n => (Real.sqrt ‖z‖)^n/(n.factorial:ℝ)
  have hf : Summable f := Real.summable_pow_div_factorial (Real.sqrt ‖z‖)
  have hf0 : 0≤f := fun n => div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Nat.cast_nonneg _)
  have hp := hf.mul_of_nonneg hf hf0 hf0
  have hd := hp.comp_injective infiniteBorel_evenDiagonal_injective
  apply hd.congr
  intro j
  simp only [Function.comp_def,f]
  rw [infiniteBorel_sqrt_diagonal_eq (norm_nonneg z)]
  simp only [norm_div,norm_pow,Complex.norm_natCast]

private theorem infiniteBorel_factorialKernel_normSum_le (z : ℂ) :
    (∑'j:ℕ,‖z^(2*j)/((2*j).factorial:ℂ)^2‖) ≤
      Real.exp (2*Real.sqrt ‖z‖) := by
  let f : ℕ→ℝ := fun n => (Real.sqrt ‖z‖)^n/(n.factorial:ℝ)
  have hf : Summable f := Real.summable_pow_div_factorial (Real.sqrt ‖z‖)
  have hf0 : 0≤f := fun n => div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Nat.cast_nonneg _)
  have hp := hf.mul_of_nonneg hf hf0 hf0
  have hs : HasSum f (Real.exp (Real.sqrt ‖z‖)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (Real.sqrt ‖z‖)
  calc
    _ = ∑'j:ℕ,(fun p:ℕ×ℕ=>f p.1*f p.2) (2*j,2*j) := by
      apply tsum_congr
      intro j
      dsimp only [f]
      rw [infiniteBorel_sqrt_diagonal_eq (norm_nonneg z)]
      simp only [norm_div,norm_pow,Complex.norm_natCast]
    _ ≤ ∑'p:ℕ×ℕ,f p.1*f p.2 :=
      tsum_comp_le_tsum_of_inj hp (fun p=>mul_nonneg (hf0 _) (hf0 _))
        infiniteBorel_evenDiagonal_injective
    _ = (∑'n:ℕ,f n)*(∑'n:ℕ,f n) := (hf.tsum_mul_tsum hf hp).symm
    _ = Real.exp (2*Real.sqrt ‖z‖) := by
      rw [hs.tsum_eq,← Real.exp_add]
      congr 1
      ring

private theorem infiniteBorel_factorialKernel_norm_le (z : ℂ) :
    ‖infiniteBorelEntireFactorialKernel z‖ ≤ Real.exp (2*Real.sqrt ‖z‖) :=
  (norm_tsum_le_tsum_norm (infiniteBorel_factorialKernel_summable_norm z)).trans
    (infiniteBorel_factorialKernel_normSum_le z)

private theorem infiniteBorel_factorialTerm_norm_le {T : ℝ} {z : ℂ}
    (hz : ‖z‖≤T) (j : ℕ) :
    ‖z^(2*j)/((2*j).factorial:ℂ)^2‖≤T^(2*j)/((2*j).factorial:ℝ) := by
  have hf : (1:ℝ)≤((2*j).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.zero_le (2*j))
  have hfs : ((2*j).factorial:ℝ)≤((2*j).factorial:ℝ)^2 := by nlinarith
  simp only [norm_div,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ T^(2*j)/((2*j).factorial:ℝ)^2 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hz _) (sq_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg ((norm_nonneg z).trans hz) _)
      (by positivity) hfs

private theorem infiniteBorel_factorialKernel_uniform {T : ℝ} (_hT : 0≤T) :
    HasSumUniformlyOn (fun j:ℕ=>fun z:ℂ=>z^(2*j)/((2*j).factorial:ℂ)^2)
      infiniteBorelEntireFactorialKernel (closedBall 0 T) := by
  exact HasSumUniformlyOn.of_norm_le_summable (Real.hasSum_cosh T).summable
    (fun j z hz=>infiniteBorel_factorialTerm_norm_le
      (by simpa only [mem_closedBall,dist_zero_right] using hz) j)

private theorem infiniteBorel_factorialKernel_analyticAt (z : ℂ) :
    AnalyticAt ℂ infiniteBorelEntireFactorialKernel z := by
  let T : ℝ := ‖z‖+1
  have hd : DifferentiableOn ℂ infiniteBorelEntireFactorialKernel (ball 0 T) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (Real.hasSum_cosh T).summable
      ?_ isOpen_ball ?_
    · intro j
      fun_prop
    · intro j w hw
      exact infiniteBorel_factorialTerm_norm_le
        (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hw)) j
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simp [T]))

end
end RHTower


open MeasureTheory Filter Set Topology
open scoped BigOperators
namespace RHTower

private theorem infiniteBorel_integrable_power_exp {a : ℝ} (ha : 0<a) (m : ℕ) :
    IntegrableOn (fun x:ℝ=>x^m*Real.exp (-a*x)) (Ioi 0) := by
  have hg : IntegrableOn (fun x:ℝ=>x^m*Real.exp (-x)) (Ioi 0) := by
    apply (Real.GammaIntegral_convergent (s:=(m:ℝ)+1) (by positivity)).congr
    filter_upwards with x
    simp only [show (m:ℝ)+1-1=(m:ℝ) by ring,Real.rpow_natCast,mul_comm]
  have hscaled : IntegrableOn (fun x:ℝ=>(a*x)^m*Real.exp (-(a*x))) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun x:ℝ=>x^m*Real.exp (-x)) 0 ha).2 (by simpa using hg)
  apply (hscaled.const_mul ((a⁻¹)^m)).congr
  filter_upwards with x
  rw [mul_pow]
  have h : (a⁻¹)^m*a^m=1 := by rw [← mul_pow,inv_mul_cancel₀ ha.ne',one_pow]
  change (a⁻¹)^m*(a^m*x^m*Real.exp (-(a*x)))=x^m*Real.exp (-a*x)
  rw [← mul_assoc,← mul_assoc,h,one_mul]
  congr 2
  ring

private theorem infiniteBorel_integral_power_exp {a : ℝ} (ha : 0<a) (m : ℕ) :
    (∫x:ℝ in Ioi 0,x^m*Real.exp (-a*x)) =
      (1/a)^(m+1)*(m.factorial:ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a:=(m:ℝ)+1) (r:=a) (by positivity) ha
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [show (m:ℝ)+1=(↑(m+1):ℝ) by push_cast; ring,
    Real.rpow_natCast] at h
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Real.rpow_natCast]
  congr 2
  ring

private theorem infiniteBorel_integrable_abs_power_exp {a : ℝ} (ha : 0<a) (m : ℕ) :
    Integrable (fun x:ℝ=>|x|^m*Real.exp (-a* |x|)) := by
  have hpos : IntegrableOn (fun x:ℝ=>|x|^m*Real.exp (-a* |x|)) (Ioi 0) := by
    apply (infiniteBorel_integrable_power_exp ha m).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_of_pos hx]
  have hneg : IntegrableOn (fun x:ℝ=>|x|^m*Real.exp (-a* |x|)) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume:Measure ℝ)]
    let hM : MeasurableEmbedding (fun x:ℝ=>-x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [hM.integrableOn_map_iff]
    simp_rw [Function.comp_def,abs_neg,neg_preimage,neg_Iic,neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have h := hneg.union hpos
  simpa only [Iic_union_Ioi,integrableOn_univ] using h

private theorem infiniteBorel_integral_abs_power_exp {a : ℝ} (ha : 0<a) (m : ℕ) :
    (∫x:ℝ,|x|^m*Real.exp (-a* |x|)) =
      2*((1/a)^(m+1)*(m.factorial:ℝ)) := by
  calc
    _ = 2*(∫x:ℝ in Ioi 0,x^m*Real.exp (-a*x)) :=
      integral_comp_abs (f:=fun x:ℝ=>x^m*Real.exp (-a*x))
    _ = _ := by rw [infiniteBorel_integral_power_exp ha m]

private theorem infiniteBorel_integrable_even_power_exp {a : ℝ} (ha : 0<a) (j : ℕ) :
    Integrable (fun x:ℝ=>x^(2*j)*Real.exp (-a* |x|)) := by
  convert infiniteBorel_integrable_abs_power_exp ha (2*j) using 1
  ext x
  simp only [pow_mul,sq_abs]

private theorem infiniteBorel_integral_even_power_exp {a : ℝ} (ha : 0<a) (j : ℕ) :
    (∫x:ℝ,x^(2*j)*Real.exp (-a* |x|)) =
      2*((1/a)^(2*j+1)*((2*j).factorial:ℝ)) := by
  rw [← infiniteBorel_integral_abs_power_exp ha (2*j)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [pow_mul,sq_abs]

end RHTower

namespace RHTower

private theorem infiniteBorel_sqrt_young (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    2*Real.sqrt (a*b)≤a/4+4*b := by
  rw [Real.sqrt_mul ha]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [sq_nonneg (Real.sqrt a/2-2*Real.sqrt b)]

private theorem infiniteBorel_rawKernel_integrand_norm_le
    {g : ℝ→ℝ} (hg0 : ∀x,0≤g x) (hg : ∀x,g x≤Real.exp (-|x|/2))
    (z : ℂ) (x : ℝ) :
    ‖(g x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ))‖≤
      Real.exp (4*‖z‖)*Real.exp (-|x|/4) := by
  have hy := infiniteBorel_sqrt_young |x| ‖z‖ (abs_nonneg x) (norm_nonneg z)
  have hnorm : ‖z*(x:ℂ)‖=|x| * ‖z‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    ring
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg0 x)]
  calc
    _ ≤ g x*Real.exp (2*Real.sqrt (|x| * ‖z‖)) := by
      exact mul_le_mul_of_nonneg_left (by
        simpa only [hnorm] using infiniteBorel_factorialKernel_norm_le (z*(x:ℂ))) (hg0 x)
    _ ≤ Real.exp (-|x|/2)*Real.exp (|x|/4+4*‖z‖) :=
      mul_le_mul (hg x) (Real.exp_le_exp.mpr hy) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring

private theorem infiniteBorel_integrable_rawKernel
    {g : ℝ→ℝ} (hgm : Measurable g) (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤Real.exp (-|x|/2)) (z : ℂ) :
    Integrable (fun x:ℝ=>(g x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ))) := by
  have hE : Continuous infiniteBorelEntireFactorialKernel :=
    continuous_iff_continuousAt.mpr (fun w=>(infiniteBorel_factorialKernel_analyticAt w).continuousAt)
  have hcont : Measurable (fun x:ℝ=>(g x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ))) := by
    exact (Complex.measurable_ofReal.comp hgm).mul (hE.measurable.comp (by fun_prop))
  have hI : Integrable (fun x:ℝ=>Real.exp (4*‖z‖)*Real.exp (-|x|/4)) := by
    have h := (infiniteBorel_integrable_abs_power_exp (a:=(1/4:ℝ)) (by norm_num) 0).const_mul
      (Real.exp (4*‖z‖))
    apply h.congr
    filter_upwards with x
    simp only [pow_zero,one_mul]
    congr 2; ring
  exact hI.mono' hcont.aestronglyMeasurable
    (Eventually.of_forall (infiniteBorel_rawKernel_integrand_norm_le hg0 hg z))

private theorem infiniteBorel_integrable_density_power
    {g : ℝ→ℝ} (hgm : Measurable g) (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤Real.exp (-|x|/2)) (j : ℕ) :
    Integrable (fun x:ℝ=>g x*x^(2*j)) := by
  have hcont : Measurable (fun x:ℝ=>g x*x^(2*j)) := by fun_prop
  refine (infiniteBorel_integrable_even_power_exp (a:=(1/2:ℝ)) (by norm_num) j).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hg0 x) ((even_two_mul j).pow_nonneg x))]
  calc
    _ ≤ Real.exp (-|x|/2)*x^(2*j) :=
      mul_le_mul_of_nonneg_right (hg x) ((even_two_mul j).pow_nonneg x)
    _ = _ := by
      rw [mul_comm]
      congr 2
      ring

private theorem infiniteBorel_density_moment_le
    {g : ℝ→ℝ} (hgm : Measurable g) (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤Real.exp (-|x|/2)) (j : ℕ) :
    (∫x:ℝ,g x*x^(2*j)) ≤ 4*2^(2*j)*((2*j).factorial:ℝ) := by
  have hm := infiniteBorel_integrable_density_power hgm hg0 hg j
  have he := infiniteBorel_integrable_even_power_exp (a:=(1/2:ℝ)) (by norm_num) j
  calc
    _ ≤ ∫x:ℝ,x^(2*j)*Real.exp (-(1/2)* |x|) := by
      apply integral_mono hm he
      intro x
      convert mul_le_mul_of_nonneg_right (hg x) ((even_two_mul j).pow_nonneg x) using 1; ring_nf
    _ = _ := by
      rw [infiniteBorel_integral_even_power_exp (by norm_num : (0:ℝ)<1/2) j]
      norm_num only [one_div,inv_div,inv_one,div_one]
      rw [pow_succ]
      ring

private theorem infiniteBorel_rawTaylor_integrable
    {g : ℝ→ℝ} (hgm : Measurable g) (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤Real.exp (-|x|/2)) (z : ℂ) (j : ℕ) :
    Integrable (fun x:ℝ=>(g x:ℂ)*(z*(x:ℂ))^(2*j)/((2*j).factorial:ℂ)^2) := by
  have h : Integrable (fun x:ℝ=>((g x*x^(2*j):ℝ):ℂ)) :=
    (infiniteBorel_integrable_density_power hgm hg0 hg j).ofReal
  convert h.mul_const (z^(2*j)/((2*j).factorial:ℂ)^2) using 1
  ext x
  push_cast
  ring

private theorem infiniteBorel_rawTaylor_integral_norm_le
    {g : ℝ→ℝ} (hgm : Measurable g) (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤Real.exp (-|x|/2)) (z : ℂ) (j : ℕ) :
    (∫x:ℝ,‖(g x:ℂ)*(z*(x:ℂ))^(2*j)/((2*j).factorial:ℂ)^2‖) ≤
      4*(2*‖z‖)^(2*j)/((2*j).factorial:ℝ) := by
  have hfac : (0:ℝ)<((2*j).factorial:ℝ) := by positivity
  calc
    _ = (∫x:ℝ,g x*x^(2*j))*(‖z‖^(2*j)/((2*j).factorial:ℝ)^2) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      simp only [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (hg0 x),Complex.norm_natCast]
      rw [mul_pow,show |x|^(2*j)=x^(2*j) by simp only [pow_mul,sq_abs]]
      ring
    _ ≤ (4*2^(2*j)*((2*j).factorial:ℝ))*(‖z‖^(2*j)/((2*j).factorial:ℝ)^2) :=
      mul_le_mul_of_nonneg_right (infiniteBorel_density_moment_le hgm hg0 hg j) (by positivity)
    _ = _ := by rw [mul_pow]; field_simp

private theorem infiniteBorel_rawTaylor_summable_integral_norm
    {g : ℝ→ℝ} (hgm : Measurable g) (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤Real.exp (-|x|/2)) (z : ℂ) :
    Summable (fun j:ℕ=>∫x:ℝ,‖(g x:ℂ)*(z*(x:ℂ))^(2*j)/((2*j).factorial:ℂ)^2‖) := by
  have hs : Summable (fun j:ℕ=>4*(2*‖z‖)^(2*j)/((2*j).factorial:ℝ)) := by
    simpa only [mul_div_assoc] using (Real.hasSum_cosh (2*‖z‖)).summable.mul_left 4
  exact hs.of_nonneg_of_le
    (fun j=>integral_nonneg (fun x=>norm_nonneg _))
    (infiniteBorel_rawTaylor_integral_norm_le hgm hg0 hg z)

private theorem infiniteBorel_rawKernel_integral_eq_tsum
    {g : ℝ→ℝ} (hgm : Measurable g) (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤Real.exp (-|x|/2)) (z : ℂ) :
    (∫x:ℝ,(g x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ))) =
      ∑'j:ℕ,Complex.ofReal (∫x:ℝ,g x*x^(2*j))*z^(2*j)/((2*j).factorial:ℂ)^2 := by
  have h := integral_tsum_of_summable_integral_norm
    (infiniteBorel_rawTaylor_integrable hgm hg0 hg z)
    (infiniteBorel_rawTaylor_summable_integral_norm hgm hg0 hg z)
  calc
    _ = ∫x:ℝ,∑'j:ℕ,(g x:ℂ)*(z*(x:ℂ))^(2*j)/((2*j).factorial:ℂ)^2 := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [infiniteBorelEntireFactorialKernel]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      ring
    _ = ∑'j:ℕ,∫x:ℝ,(g x:ℂ)*(z*(x:ℂ))^(2*j)/((2*j).factorial:ℂ)^2 := h.symm
    _ = _ := by
      apply tsum_congr
      intro j
      calc
        _ = ∫x:ℝ,((g x*x^(2*j):ℝ):ℂ)*(z^(2*j)/((2*j).factorial:ℂ)^2) := by
          apply integral_congr_ae
          filter_upwards with x
          push_cast
          ring
        _ = _ := by
          rw [integral_mul_const]
          have hi := integral_complex_ofReal (f:=fun x:ℝ=>g x*x^(2*j)) (μ:=volume)
          rw [hi]
          ring

private theorem infiniteBorel_rawLoss_integrand_bound
    {c L : ℝ} (hc : 0≤c) (hL : 0≤L) {z : ℂ} (hz : ‖z‖≤c*L)
    {g : ℝ→ℝ} (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x ≤ (if |x| < L then Real.exp (|x|/2-L) else Real.exp (-|x|/2)))
    (x : ℝ) :
    ‖(g x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ))‖≤
      Real.exp (-(1/2-2*Real.sqrt c)*max L |x|) := by
  have hnorm : ‖z*(x:ℂ)‖=‖z‖ * |x| := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg0 x)]
  by_cases hx:|x|<L
  · have hs : Real.sqrt (‖z‖ * |x|)≤Real.sqrt c*L := by
      calc
        _ ≤ Real.sqrt (c*L^2) := Real.sqrt_le_sqrt (by nlinarith [norm_nonneg z,abs_nonneg x])
        _ = _ := by rw [Real.sqrt_mul hc,Real.sqrt_sq hL]
    have he : ‖infiniteBorelEntireFactorialKernel (z*(x:ℂ))‖≤Real.exp (2*Real.sqrt c*L) := by
      exact (infiniteBorel_factorialKernel_norm_le _).trans
        (Real.exp_le_exp.mpr (by rw [hnorm]; linarith))
    rw [max_eq_left hx.le]
    calc
      _ ≤ Real.exp (|x|/2-L)*Real.exp (2*Real.sqrt c*L) :=
        mul_le_mul (by simpa only [if_pos hx] using hg x) he (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (L/2-L)*Real.exp (2*Real.sqrt c*L) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  · have hxL : L≤|x| := le_of_not_gt hx
    have hs : Real.sqrt (‖z‖ * |x|)≤Real.sqrt c * |x| := by
      calc
        _ ≤ Real.sqrt (c * |x|^2) := Real.sqrt_le_sqrt (by
          calc
            _ ≤ (c*L)* |x| := mul_le_mul_of_nonneg_right hz (abs_nonneg x)
            _ ≤ (c* |x|)* |x| := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxL hc) (abs_nonneg x)
            _ = _ := by ring)
        _ = _ := by rw [Real.sqrt_mul hc,Real.sqrt_sq (abs_nonneg x)]
    have he : ‖infiniteBorelEntireFactorialKernel (z*(x:ℂ))‖≤Real.exp (2*Real.sqrt c * |x|) := by
      exact (infiniteBorel_factorialKernel_norm_le _).trans
        (Real.exp_le_exp.mpr (by rw [hnorm]; linarith))
    rw [max_eq_right hxL]
    calc
      _ ≤ Real.exp (-|x|/2)*Real.exp (2*Real.sqrt c * |x|) :=
        mul_le_mul (by simpa only [if_neg hx] using hg x) he (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; ring

private theorem infiniteBorel_integrable_max_exp {κ : ℝ} (hκ : 0<κ) (L : ℝ) :
    Integrable (fun x:ℝ=>Real.exp (-κ*max L |x|)) := by
  have hm : Measurable (fun x:ℝ=>Real.exp (-κ*max L |x|)) := by fun_prop
  refine (infiniteBorel_integrable_abs_power_exp hκ 0).mono' hm.aestronglyMeasurable ?_
  filter_upwards with x
  simp only [pow_zero,one_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (le_max_right L |x|) (by linarith)

private theorem infiniteBorel_integral_max_exp {κ L : ℝ} (hκ : 0<κ) (hL : 0≤L) :
    (∫x:ℝ,Real.exp (-κ*max L |x|))=2*(L+1/κ)*Real.exp (-κ*L) := by
  have hI := infiniteBorel_integrable_max_exp hκ L
  have habs : (∫x:ℝ,Real.exp (-κ*max L |x|))=
      2*(∫x:ℝ in Ioi 0,Real.exp (-κ*max L x)) :=
    integral_comp_abs (f:=fun x:ℝ=>Real.exp (-κ*max L x))
  rw [habs,← Ioc_union_Ioi_eq_Ioi hL]
  have hconst : IntegrableOn (fun x:ℝ=>Real.exp (-κ*L)) (Ioc 0 L) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have htail : IntegrableOn (fun x:ℝ=>Real.exp (-κ*x)) (Ioi L) := by
    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a:=-κ) (by linarith) L
  have ha : IntegrableOn (fun x:ℝ=>Real.exp (-κ*max L x)) (Ioc 0 L) := by
    apply hconst.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [max_eq_left hx.2]
  have hb : IntegrableOn (fun x:ℝ=>Real.exp (-κ*max L x)) (Ioi L) := by
    apply htail.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [max_eq_right hx.le]
  rw [setIntegral_union (by exact Set.disjoint_left.mpr (fun x hx hy=>not_lt_of_ge hx.2 hy)) measurableSet_Ioi ha hb]
  have hea : (∫x:ℝ in Ioc 0 L,Real.exp (-κ*max L x))=L*Real.exp (-κ*L) := by
    calc
      _ = ∫x:ℝ in Ioc 0 L,Real.exp (-κ*L) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx; dsimp only; rw [max_eq_left hx.2]
      _ = _ := by simp only [integral_const,measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le hL,sub_zero,smul_eq_mul]
  have heb : (∫x:ℝ in Ioi L,Real.exp (-κ*max L x))=Real.exp (-κ*L)/κ := by
    calc
      _ = ∫x:ℝ in Ioi L,Real.exp (-κ*x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx; dsimp only; rw [max_eq_right hx.le]
      _ = _ := by
        simpa only [neg_mul,neg_div_neg_eq] using integral_exp_mul_Ioi (a:=-κ) (by linarith) L
  rw [hea,heb]
  ring

private theorem infiniteBorel_rawLoss_integral_norm_le
    {c L : ℝ} (hc : 0≤c) (hL : 0≤L) (hκ : 0<1/2-2*Real.sqrt c)
    {z : ℂ} (hz : ‖z‖≤c*L) {g : ℝ→ℝ} (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤(if |x|<L then Real.exp (|x|/2-L) else Real.exp (-|x|/2))) :
    ‖∫x:ℝ,(g x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ))‖≤
      2*(L+1/(1/2-2*Real.sqrt c))*Real.exp (-(1/2-2*Real.sqrt c)*L) := by
  calc
    _ ≤ ∫x:ℝ,Real.exp (-(1/2-2*Real.sqrt c)*max L |x|) :=
      norm_integral_le_of_norm_le (infiniteBorel_integrable_max_exp hκ L)
        (Eventually.of_forall (infiniteBorel_rawLoss_integrand_bound hc hL hz hg0 hg))
    _ = _ := infiniteBorel_integral_max_exp hκ hL

end RHTower





open Filter Set Metric Topology
open scoped BigOperators
namespace RHTower
noncomputable section

private def infiniteBorelCoefficientSeries (a : ℕ→ℝ) (z : ℂ) : ℂ :=
  ∑'j:ℕ,(a j:ℂ)*z^(2*j)

private theorem infiniteBorel_coefficientTerm_norm_le {a : ℕ→ℝ} {K R T : ℝ}
    (hK : 0≤K) (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ))
    {z : ℂ} (hz : ‖z‖≤T) (j : ℕ) :
    ‖(a j:ℂ)*z^(2*j)‖≤K*((R*T)^(2*j)/((2*j).factorial:ℝ)) := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow]
  calc
    _ ≤ (K*R^(2*j)/((2*j).factorial:ℝ))*T^(2*j) :=
      mul_le_mul (ha j) (pow_le_pow_left₀ (norm_nonneg z) hz _)
        (pow_nonneg (norm_nonneg z) _) (div_nonneg (mul_nonneg hK (by
          rw [pow_mul]; positivity)) (Nat.cast_nonneg _))
    _ = _ := by rw [mul_pow]; ring

private theorem infiniteBorel_coefficientSeries_summable_norm {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0≤K) (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ)) (z : ℂ) :
    Summable (fun j:ℕ=>‖(a j:ℂ)*z^(2*j)‖) := by
  exact ((Real.hasSum_cosh (R*‖z‖)).summable.mul_left K).of_nonneg_of_le
    (fun _=>norm_nonneg _) (infiniteBorel_coefficientTerm_norm_le hK ha (le_refl _) )

private theorem infiniteBorel_coefficientSeries_norm_le {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0≤K) (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ)) (z : ℂ) :
    ‖infiniteBorelCoefficientSeries a z‖≤K*Real.cosh (R*‖z‖) := by
  calc
    _ ≤ ∑'j:ℕ,‖(a j:ℂ)*z^(2*j)‖ :=
      norm_tsum_le_tsum_norm (infiniteBorel_coefficientSeries_summable_norm hK ha z)
    _ ≤ ∑'j:ℕ,K*((R*‖z‖)^(2*j)/((2*j).factorial:ℝ)) :=
      (infiniteBorel_coefficientSeries_summable_norm hK ha z).tsum_le_tsum
        (infiniteBorel_coefficientTerm_norm_le hK ha (le_refl _))
        ((Real.hasSum_cosh (R*‖z‖)).summable.mul_left K)
    _ = _ := by rw [tsum_mul_left,← (Real.hasSum_cosh _).tsum_eq]

private theorem infiniteBorel_coefficientSeries_uniform {a : ℕ→ℝ} {K R T : ℝ}
    (hK : 0≤K) (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ)) :
    HasSumUniformlyOn (fun j:ℕ=>fun z:ℂ=>(a j:ℂ)*z^(2*j))
      (infiniteBorelCoefficientSeries a) (closedBall 0 T) := by
  exact HasSumUniformlyOn.of_norm_le_summable
    ((Real.hasSum_cosh (R*T)).summable.mul_left K)
    (fun j z hz=>infiniteBorel_coefficientTerm_norm_le hK ha
      (by simpa only [mem_closedBall,dist_zero_right] using hz) j)

private theorem infiniteBorel_coefficientSeries_locallyUniform {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0≤K) (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ)) :
    SummableLocallyUniformlyOn (fun j:ℕ=>fun z:ℂ=>(a j:ℂ)*z^(2*j)) univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro S hS hSc
  obtain ⟨T,hT⟩ := hSc.bddAbove_image continuous_norm.continuousOn
  refine ⟨_,(Real.hasSum_cosh (R*T)).summable.mul_left K,?_⟩
  intro j z hz
  exact infiniteBorel_coefficientTerm_norm_le hK ha (hT ⟨z,hz,rfl⟩) j

private theorem infiniteBorel_coefficientSeries_analyticAt {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0≤K) (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ)) (z : ℂ) :
    AnalyticAt ℂ (infiniteBorelCoefficientSeries a) z := by
  let T : ℝ := ‖z‖+1
  have hd : DifferentiableOn ℂ (infiniteBorelCoefficientSeries a) (ball 0 T) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((Real.hasSum_cosh (R*T)).summable.mul_left K) ?_ isOpen_ball ?_
    · intro j
      fun_prop
    · intro j w hw
      exact infiniteBorel_coefficientTerm_norm_le hK ha
        (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hw)) j
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simp [T]))

private theorem infiniteBorel_coefficientSeries_ofReal (a : ℕ→ℝ) (t : ℝ) :
    infiniteBorelCoefficientSeries a (t:ℂ)=(∑'j:ℕ,a j*t^(2*j):ℝ) := by
  unfold infiniteBorelCoefficientSeries
  simp_rw [← Complex.ofReal_pow,← Complex.ofReal_mul]
  exact (Complex.ofReal_tsum _).symm

private theorem infiniteBorel_coefficientSeries_realSummable {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0≤K) (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ)) (t : ℝ) :
    Summable (fun j:ℕ=>a j*t^(2*j)) := by
  have h := (infiniteBorel_coefficientSeries_summable_norm hK ha (t:ℂ)).of_norm
  have hre := h.mapL Complex.reCLM
  simpa only [← Complex.ofReal_pow,← Complex.ofReal_mul,
    Complex.reCLM_apply,Complex.ofReal_re] using hre

private theorem infiniteBorel_coefficientSeries_ge_one {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0≤K) (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ))
    (ha0 : a 0=1) (haPos : ∀j,0≤a j) (t : ℝ) :
    1≤∑'j:ℕ,a j*t^(2*j) := by
  have h := (infiniteBorel_coefficientSeries_realSummable hK ha t).le_tsum 0
    (fun j _=>mul_nonneg (haPos j) (by rw [pow_mul]; positivity))
  simpa only [ha0,mul_zero,pow_zero,mul_one] using h

private theorem infiniteBorel_coefficientSeries_error_tendsto
    {aN : ℕ→ℕ→ℝ} {a : ℕ→ℝ} {K R T : ℝ}
    (_hK : 0≤K) (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ))
    (haN : ∀ᶠN:ℕ in atTop,∀j,|aN N j|≤K*R^(2*j)/((2*j).factorial:ℝ))
    (hlim : ∀j,Tendsto (fun N:ℕ=>aN N j) atTop (nhds (a j))) :
    Tendsto (fun N:ℕ=>∑'j:ℕ,|aN N j-a j| * T^(2*j)) atTop (nhds 0) := by
  have hs : Summable (fun j:ℕ=>2*K*((R*T)^(2*j)/((2*j).factorial:ℝ))) :=
    (Real.hasSum_cosh (R*T)).summable.mul_left (2*K)
  have ht (j:ℕ) : Tendsto (fun N:ℕ=>|aN N j-a j| * T^(2*j)) atTop (nhds 0) := by
    simpa only [sub_self,abs_zero,zero_mul] using ((hlim j).sub_const (a j)).abs.mul_const (T^(2*j))
  have hb : ∀ᶠN:ℕ in atTop,∀j,
      ‖|aN N j-a j| * T^(2*j)‖≤2*K*((R*T)^(2*j)/((2*j).factorial:ℝ)) := by
    filter_upwards [haN] with N hN
    intro j
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) ((even_two_mul j).pow_nonneg T))]
    calc
      _ ≤ (|aN N j|+|a j|)*T^(2*j) :=
        mul_le_mul_of_nonneg_right (by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (aN N j) 0 (a j)) ((even_two_mul j).pow_nonneg T)
      _ ≤ (K*R^(2*j)/((2*j).factorial:ℝ)+K*R^(2*j)/((2*j).factorial:ℝ))*T^(2*j) :=
        mul_le_mul_of_nonneg_right (add_le_add (hN j) (ha j)) ((even_two_mul j).pow_nonneg T)
      _ = _ := by rw [mul_pow]; ring
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hs ht hb

private theorem infiniteBorel_coefficientSeries_error_bound
    {aN a : ℕ→ℝ} {K R T : ℝ} (hK : 0≤K)
    (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ))
    (haN : ∀j,|aN j|≤K*R^(2*j)/((2*j).factorial:ℝ))
    {z : ℂ} (hz : ‖z‖≤T) :
    ‖infiniteBorelCoefficientSeries aN z-infiniteBorelCoefficientSeries a z‖≤
      ∑'j:ℕ,|aN j-a j| * T^(2*j) := by
  have hdiff (j:ℕ) : |aN j-a j|≤(2*K)*R^(2*j)/((2*j).factorial:ℝ) := by
    calc
      _ ≤ |aN j|+|a j| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (aN j) 0 (a j)
      _ ≤ K*R^(2*j)/((2*j).factorial:ℝ)+K*R^(2*j)/((2*j).factorial:ℝ) := add_le_add (haN j) (ha j)
      _ = _ := by ring
  have hs := (infiniteBorel_coefficientSeries_summable_norm hK haN z).of_norm
  have ht := (infiniteBorel_coefficientSeries_summable_norm hK ha z).of_norm
  have hu : Summable (fun j:ℕ=>|aN j-a j| * T^(2*j)) :=
    ((Real.hasSum_cosh (R*T)).summable.mul_left (2*K)).of_nonneg_of_le
      (fun j=>mul_nonneg (abs_nonneg _) ((even_two_mul j).pow_nonneg T))
      (fun j=>by
        exact (mul_le_mul_of_nonneg_right (hdiff j) ((even_two_mul j).pow_nonneg T)).trans_eq (by rw [mul_pow]; ring))
  unfold infiniteBorelCoefficientSeries
  rw [← hs.tsum_sub ht]
  calc
    _ ≤ ∑'j:ℕ,‖(aN j:ℂ)*z^(2*j)-(a j:ℂ)*z^(2*j)‖ :=
      norm_tsum_le_tsum_norm (hs.sub ht).norm
    _ ≤ _ := (hs.sub ht).norm.tsum_le_tsum (fun j=>by
      rw [← sub_mul,← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz _) (abs_nonneg _)) hu

private theorem infiniteBorel_coefficientSeries_tendstoUniformlyOn
    {aN : ℕ→ℕ→ℝ} {a : ℕ→ℝ} {K R T : ℝ}
    (hK : 0≤K) (ha : ∀j,|a j|≤K*R^(2*j)/((2*j).factorial:ℝ))
    (haN : ∀ᶠN:ℕ in atTop,∀j,|aN N j|≤K*R^(2*j)/((2*j).factorial:ℝ))
    (hlim : ∀j,Tendsto (fun N:ℕ=>aN N j) atTop (nhds (a j))) :
    TendstoUniformlyOn (fun N:ℕ=>infiniteBorelCoefficientSeries (aN N))
      (infiniteBorelCoefficientSeries a) atTop (closedBall 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := infiniteBorel_coefficientSeries_error_tendsto hK ha haN hlim (T:=T)
  filter_upwards [haN,he.eventually (gt_mem_nhds hε)] with N hN hE
  intro z hz
  rw [dist_eq_norm, norm_sub_rev]
  exact (infiniteBorel_coefficientSeries_error_bound hK ha hN
    (by simpa only [mem_closedBall,dist_zero_right] using hz)).trans_lt hE

end
end RHTower


open Filter Set Topology
namespace RHTower

private theorem infiniteBorel_inverse_square_error
    {s a b d : ℝ} (hs : 0<s) (hsa : s≤a) (hab : a≤b) (hb : b≤2)
    (hd : b-a≤d) :
    0≤1/a^2-1/b^2 ∧ 1/a^2-1/b^2≤4*d/s^4 := by
  have ha : 0<a := hs.trans_le hsa
  have hbp : 0<b := ha.trans_le hab
  have hd0 : 0≤d := (sub_nonneg.mpr hab).trans hd
  have hnum : (b-a)*(b+a)≤4*d := by
    calc
      _ ≤ d*(b+a) := mul_le_mul_of_nonneg_right hd (by positivity)
      _ ≤ d*4 := mul_le_mul_of_nonneg_left (by linarith) hd0
      _ = _ := by ring_nf
  have hsqa : s^2≤a^2 := by nlinarith
  have hsqb : s^2≤b^2 := by nlinarith
  have hden : s^4≤a^2*b^2 := by
    rw [show s^4=s^2*s^2 by ring_nf]
    exact mul_le_mul hsqa hsqb (sq_nonneg _) (sq_nonneg _)
  have he : 1/a^2-1/b^2=(b-a)*(b+a)/(a^2*b^2) := by
    field_simp
    ring_nf
  rw [he]
  refine ⟨div_nonneg (mul_nonneg (sub_nonneg.mpr hab) (by positivity)) (by positivity),?_⟩
  calc
    _ ≤ (4*d)/(a^2*b^2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden

private theorem infiniteBorel_normalized_error_le
    {s a b c L κ : ℝ} (hs : 0<s) (hsa : s≤a) (hab : a≤b) (hb : b≤2)
    (hd : b-a≤2*Real.exp (-L/2)) (hκ : 0<κ) (hL : 0≤L)
    {z Rfinite Rinfinite : ℂ} (hz : ‖z‖≤c*L)
    (herror : ‖Rfinite-Rinfinite‖≤2*(L+1/κ)*Real.exp (-κ*L))
    (hraw : ‖Rinfinite‖≤4*Real.exp (2*‖z‖)) :
    ‖Rfinite/(a:ℂ)^2-Rinfinite/(b:ℂ)^2‖≤
      (2/s^2)*(L+1/κ)*Real.exp (-κ*L)+
        (32/s^4)*Real.exp (-(1/2-2*c)*L) := by
  have ha : 0<a := hs.trans_le hsa
  have hbp : 0<b := ha.trans_le hab
  have hai : (a:ℂ)≠0 := by exact_mod_cast ha.ne'
  have hbi : (b:ℂ)≠0 := by exact_mod_cast hbp.ne'
  have hinv := infiniteBorel_inverse_square_error hs hsa hab hb hd
  have hsq : s^2≤a^2 := by nlinarith
  have he : Rfinite/(a:ℂ)^2-Rinfinite/(b:ℂ)^2=
      (Rfinite-Rinfinite)/(a:ℂ)^2+Rinfinite*((1/a^2-1/b^2:ℝ):ℂ) := by
    push_cast
    field_simp
    ring_nf
  rw [he]
  calc
    _ ≤ ‖(Rfinite-Rinfinite)/(a:ℂ)^2‖+‖Rinfinite*((1/a^2-1/b^2:ℝ):ℂ)‖ := norm_add_le _ _
    _ = ‖Rfinite-Rinfinite‖/a^2+‖Rinfinite‖*(1/a^2-1/b^2) := by
      simp only [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,norm_mul,abs_of_pos ha,
        abs_of_nonneg hinv.1]
    _ ≤ (2*(L+1/κ)*Real.exp (-κ*L))/s^2+
        (4*Real.exp (2*c*L))*(8*Real.exp (-L/2)/s^4) := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_right herror (sq_nonneg a)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq)
      · apply mul_le_mul
        · exact hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num))
        · exact hinv.2.trans_eq (by ring_nf)
        · exact hinv.1
        · positivity
    _ = _ := by
      rw [show (4*Real.exp (2*c*L))*(8*Real.exp (-L/2)/s^4)=
        (32/s^4)*(Real.exp (2*c*L)*Real.exp (-L/2)) by ring_nf,←Real.exp_add]
      congr 1
      · ring_nf
      · congr 1
        ring_nf

private theorem infiniteBorel_growingError_tendsto_zero
    {s κ α : ℝ} (hκ : 0<κ) (hα : 0<α) :
    Tendsto (fun L:ℝ=>(2/s^2)*(L+1/κ)*Real.exp (-κ*L)+
      (32/s^4)*Real.exp (-α*L)) atTop (nhds 0) := by
  have ht : Tendsto (fun L:ℝ=>L*Real.exp (-κ*L)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 κ hκ
  have he : Tendsto (fun L:ℝ=>Real.exp (-κ*L)) atTop (nhds 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hκ)
  have heα : Tendsto (fun L:ℝ=>Real.exp (-α*L)) atTop (nhds 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hα)
  have h := (ht.add (he.const_mul (1/κ))).const_mul (2/s^2) |>.add (heα.const_mul (32/s^4))
  simp only [mul_zero,add_zero] at h
  exact h.congr (fun L=>by ring_nf)

end RHTower

namespace RHTower

private theorem infiniteBorel_moment_error_le
    {g h : ℝ→ℝ} {D a : ℝ} (_hD : 0≤D) (ha : 0<a)
    (herr : ∀x,|g x-h x|≤D*Real.exp (-a*|x|)) (j:ℕ)
    (hg : Integrable (fun x:ℝ=>x^(2*j)*g x))
    (hh : Integrable (fun x:ℝ=>x^(2*j)*h x)) :
    |(∫x:ℝ,x^(2*j)*g x)-(∫x:ℝ,x^(2*j)*h x)|≤
      D*(2*((1/a)^(2*j+1)*((2*j).factorial:ℝ))) := by
  rw [← integral_sub hg hh,←Real.norm_eq_abs]
  calc
    _ ≤ ∫x:ℝ,D*(x^(2*j)*Real.exp (-a*|x|)) := by
      exact norm_integral_le_of_norm_le ((infiniteBorel_integrable_even_power_exp ha j).const_mul D)
        (Eventually.of_forall fun x=>by
          rw [← mul_sub,Real.norm_eq_abs,abs_mul,
            abs_of_nonneg ((even_two_mul j).pow_nonneg x)]
          exact (mul_le_mul_of_nonneg_left (herr x) ((even_two_mul j).pow_nonneg x)).trans_eq (by ring))
    _ = _ := by rw [integral_const_mul,infiniteBorel_integral_even_power_exp ha j]

private theorem infiniteBorel_normalized_moment_error
    {Z D h d : ℝ} (hZ : 0<Z) (_hD : 0≤D) (j:ℕ)
    (herr : |Z^2*d-h*(4*2^(2*j)*((2*j).factorial:ℝ))|≤
      D*2*((2/3)^(2*j+1)*((2*j).factorial:ℝ))) :
    |d/(2^(2*j)*((2*j).factorial:ℝ))-4*h/Z^2|≤
      (4*D/(3*Z^2))*(1/9)^j := by
  have hfac : (0:ℝ)<((2*j).factorial:ℝ) := by positivity
  have hpow : (0:ℝ)<2^(2*j) := by positivity
  have he : d/(2^(2*j)*((2*j).factorial:ℝ))-4*h/Z^2=
      (Z^2*d-h*(4*2^(2*j)*((2*j).factorial:ℝ)))/
        (Z^2*(2^(2*j)*((2*j).factorial:ℝ))) := by field_simp
  rw [he,abs_div,abs_of_pos (by positivity : 0<Z^2*(2^(2*j)*((2*j).factorial:ℝ)))]
  calc
    _ ≤ (D*2*((2/3)^(2*j+1)*((2*j).factorial:ℝ)))/
        (Z^2*(2^(2*j)*((2*j).factorial:ℝ))) :=
      div_le_div_of_nonneg_right herr (by positivity)
    _ = _ := by
      have hp : (2/3:ℝ)^(2*j+1)=(2/3)*2^(2*j)*(1/9)^j := by
        rw [pow_succ,pow_mul,pow_mul,show (2/3:ℝ)^2=2^2*(1/9) by ring,mul_pow]
        ring
      rw [hp]
      field_simp
      norm_num


end RHTower

namespace RHTower

private theorem infiniteBorel_cosh_two_hasSum (z : ℂ) :
    HasSum (fun j:ℕ=>Complex.ofReal ((2:ℝ)^(2*j)/((2*j).factorial:ℝ))*z^(2*j))
      (Complex.cosh (2*z)) := by
  apply (Complex.hasSum_cosh (2*z)).congr
  intro j
  simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_natCast,mul_pow]
  ring_nf

private theorem infiniteBorel_complex_remainder_bound
    {a : ℕ→ℝ} {K C ell : ℝ} (hK : 0≤K) (hC : 0≤C)
    (ha : ∀j,|a j|≤K*2^(2*j)/((2*j).factorial:ℝ))
    (herr : ∀j,|a j-ell*(2^(2*j)/((2*j).factorial:ℝ))|≤
      C*(2/3)^(2*j)/((2*j).factorial:ℝ)) (z : ℂ) :
    ‖infiniteBorelCoefficientSeries a z-(ell:ℂ)*Complex.cosh (2*z)‖≤
      C*Real.cosh (2*‖z‖/3) := by
  let r : ℕ→ℝ := fun j=>a j-ell*(2^(2*j)/((2*j).factorial:ℝ))
  have hr := infiniteBorel_coefficientSeries_norm_le hC herr z
  have hs := (infiniteBorel_coefficientSeries_summable_norm hK ha z).of_norm
  have ht := (infiniteBorel_cosh_two_hasSum z).summable.mul_left (ell:ℂ)
  have he : infiniteBorelCoefficientSeries r z=
      infiniteBorelCoefficientSeries a z-(ell:ℂ)*Complex.cosh (2*z) := by
    unfold infiniteBorelCoefficientSeries
    have hterm (j:ℕ) : (r j:ℂ)*z^(2*j)=
        (a j:ℂ)*z^(2*j)-(ell:ℂ)*(Complex.ofReal (2^(2*j)/((2*j).factorial:ℝ))*z^(2*j)) := by
      dsimp only [r]
      push_cast
      ring_nf
    simp_rw [hterm]
    rw [hs.tsum_sub ht,tsum_mul_left,(infiniteBorel_cosh_two_hasSum z).tsum_eq]
  rw [he] at hr
  simpa only [show (2/3:ℝ)*‖z‖=2*‖z‖/3 by ring_nf] using hr


end RHTower


open Filter Set Topology
namespace RHTower

private theorem infiniteBorel_cosh_le_exp {x : ℝ} (hx : 0≤x) :
    Real.cosh x≤Real.exp x := by
  rw [Real.cosh_eq]
  have h : Real.exp (-x)≤Real.exp x := Real.exp_le_exp.mpr (by linarith)
  linarith

private theorem infiniteBorel_exp_le_two_cosh (x : ℝ) :
    Real.exp x≤2*Real.cosh x := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-x)]

private theorem infiniteBorel_cosh_ratio_bound {C t : ℝ} (hC : 0≤C) (ht : 0≤t) :
    C*Real.cosh (2*t/3)/Real.cosh (2*t)≤2*C*Real.exp (-(4/3)*t) := by
  have hsmall := infiniteBorel_cosh_le_exp (by linarith : 0≤2*t/3)
  have hlarge := infiniteBorel_exp_le_two_cosh (2*t)
  calc
    _ ≤ (C*Real.exp (2*t/3))/Real.cosh (2*t) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hC) (Real.cosh_pos _).le
    _ ≤ (C*Real.exp (2*t/3))/(Real.exp (2*t)/2) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (Real.exp_pos _).le)
        (by positivity) (by linarith)
    _ = _ := by
      have he : Real.exp (-(4/3)*t)=Real.exp (2*t/3)/Real.exp (2*t) := by
        rw [← Real.exp_sub]
        congr 1
        ring
      rw [he]
      field_simp

private theorem infiniteBorel_real_relative_error {f : ℝ→ℝ} {C ell : ℝ}
    (hC : 0≤C)
    (herror : ∀t:ℝ,0≤t→|f t-ell*Real.cosh (2*t)|≤C*Real.cosh (2*t/3))
    {t : ℝ} (ht : 0≤t) :
    |f t/Real.cosh (2*t)-ell|≤2*C*Real.exp (-(4/3)*t) := by
  have he : f t/Real.cosh (2*t)-ell=
      (f t-ell*Real.cosh (2*t))/Real.cosh (2*t) := by
    field_simp [(Real.cosh_pos _).ne']
  rw [he,abs_div,abs_of_pos (Real.cosh_pos _)]
  exact (div_le_div_of_nonneg_right (herror t ht) (Real.cosh_pos _).le).trans
    (infiniteBorel_cosh_ratio_bound hC ht)

private theorem infiniteBorel_scaled_cosh_eq (t : ℝ) :
    Real.exp (-2*t)*Real.cosh (2*t)=(1+Real.exp (-4*t))/2 := by
  have hpos : Real.exp (-2*t)*Real.exp (2*t)=1 := by
    rw [← Real.exp_add]
    norm_num
  have hneg : Real.exp (-2*t)*Real.exp (-(2*t))=Real.exp (-4*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.cosh_eq]
  calc
    _ = (Real.exp (-2*t)*Real.exp (2*t)+Real.exp (-2*t)*Real.exp (-(2*t)))/2 := by ring
    _ = _ := by rw [hpos,hneg]

private theorem infiniteBorel_scaled_cosh_tendsto :
    Tendsto (fun t:ℝ=>Real.exp (-2*t)*Real.cosh (2*t)) atTop (𝓝 (1/2)) := by
  have he : Tendsto (fun t:ℝ=>Real.exp (-4*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
  have h := (he.const_add (1:ℝ)).div_const 2
  simp only [add_zero] at h
  exact h.congr (fun t=>(infiniteBorel_scaled_cosh_eq t).symm)

private theorem infiniteBorel_real_relative_tendsto {f : ℝ→ℝ} {C ell : ℝ}
    (hC : 0≤C)
    (herror : ∀t:ℝ,0≤t→|f t-ell*Real.cosh (2*t)|≤C*Real.cosh (2*t/3)) :
    Tendsto (fun t:ℝ=>f t/Real.cosh (2*t)) atTop (𝓝 ell) := by
  have hbound : Tendsto (fun t:ℝ=>2*C*Real.exp (-(4/3)*t)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(4/3:ℝ)<0))
    simpa only [Function.comp_def,id_eq,mul_zero] using he.const_mul (2*C)
  have hzero : Tendsto (fun t:ℝ=>f t/Real.cosh (2*t)-ell) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    simpa only [Real.norm_eq_abs] using infiniteBorel_real_relative_error hC herror ht
  have h := hzero.add_const ell
  simpa only [sub_add_cancel,zero_add] using h

private theorem infiniteBorel_real_scaled_error_bound {f : ℝ→ℝ} {C ell : ℝ}
    (hC : 0≤C)
    (herror : ∀t:ℝ,0≤t→|f t-ell*Real.cosh (2*t)|≤C*Real.cosh (2*t/3))
    {t : ℝ} (ht : 0≤t) :
    |Real.exp (-2*t)*(f t-ell*Real.cosh (2*t))|≤C*Real.exp (-(4/3)*t) := by
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-2*t)*(C*Real.cosh (2*t/3)) :=
      mul_le_mul_of_nonneg_left (herror t ht) (Real.exp_pos _).le
    _ ≤ Real.exp (-2*t)*(C*Real.exp (2*t/3)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (infiniteBorel_cosh_le_exp (by linarith)) hC)
        (Real.exp_pos _).le
    _ = _ := by
      rw [mul_left_comm,← Real.exp_add]
      have he : -2*t+2*t/3=-(4/3)*t := by ring
      rw [he]

private theorem infiniteBorel_real_scaled_tendsto {f : ℝ→ℝ} {C ell : ℝ}
    (hC : 0≤C)
    (herror : ∀t:ℝ,0≤t→|f t-ell*Real.cosh (2*t)|≤C*Real.cosh (2*t/3)) :
    Tendsto (fun t:ℝ=>Real.exp (-2*t)*f t) atTop (𝓝 (ell/2)) := by
  have hbound : Tendsto (fun t:ℝ=>C*Real.exp (-(4/3)*t)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(4/3:ℝ)<0))
    simpa only [Function.comp_def,id_eq,mul_zero] using he.const_mul C
  have hz : Tendsto (fun t:ℝ=>Real.exp (-2*t)*(f t-ell*Real.cosh (2*t))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    simpa only [Real.norm_eq_abs] using infiniteBorel_real_scaled_error_bound hC herror ht
  have h := hz.add (infiniteBorel_scaled_cosh_tendsto.const_mul ell)
  simp only [zero_add] at h
  have hl : ell*(1/2)=ell/2 := by ring
  rw [hl] at h
  exact h.congr (fun t=>by ring)

private theorem infiniteBorel_reference_gap_scaled_tendsto {f : ℝ→ℝ} {C ell : ℝ}
    (hC : 0≤C)
    (herror : ∀t:ℝ,0≤t→|f t-ell*Real.cosh (2*t)|≤C*Real.cosh (2*t/3)) :
    Tendsto (fun t:ℝ=>Real.exp (-2*t)*(Real.cosh (2*t)-f t)) atTop (𝓝 ((1-ell)/2)) := by
  have h := infiniteBorel_scaled_cosh_tendsto.sub (infiniteBorel_real_scaled_tendsto hC herror)
  have hl : (1/2:ℝ)-ell/2=(1-ell)/2 := by ring
  rw [hl] at h
  exact h.congr (fun t=>by ring)

private theorem infiniteBorel_reference_gap_tendsto {f : ℝ→ℝ} {C ell : ℝ}
    (hC : 0≤C) (hell : ell<1)
    (herror : ∀t:ℝ,0≤t→|f t-ell*Real.cosh (2*t)|≤C*Real.cosh (2*t/3)) :
    Tendsto (fun t:ℝ=>Real.cosh (2*t)-f t) atTop atTop := by
  have he : Tendsto (fun t:ℝ=>Real.exp (2*t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  have h := he.atTop_mul_pos (by linarith : 0<(1-ell)/2)
    (infiniteBorel_reference_gap_scaled_tendsto hC herror)
  exact h.congr (fun t=>by
    rw [← mul_assoc,← Real.exp_add]
    norm_num)

end RHTower


open Filter Topology
namespace RHTower

private theorem infiniteBorel_square_normalizer_gt {Z : ℝ} (hZ : 71/60<Z) :
    7/5<Z^2 := by
  have hZ0 : 0<Z := by linarith
  nlinarith

private theorem infiniteBorel_momentErrorScale_lt {Z : ℝ} (hZ : 71/60<Z) :
    Real.pi^2/(12*Z^2)<20/21 := by
  have hZ0 : 0<Z := by linarith
  have hZsq := infiniteBorel_square_normalizer_gt hZ
  have hp2 : Real.pi^2<16 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
  apply (div_lt_iff₀ (by positivity : 0<12*Z^2)).2
  nlinarith

private theorem infiniteBorel_degree_four_ratio_lt_one {a ell C : ℝ} {j : ℕ}
    (hj : 4≤j) (hell : ell<5040/5041) (hC0 : 0≤C) (hC : C<20/21)
    (herror : |a-ell|≤C*(1/9:ℝ)^j) : a<1 := by
  have hp : (1/9:ℝ)^j≤(1/9:ℝ)^4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have he := (le_abs_self (a-ell)).trans (herror.trans (mul_le_mul_of_nonneg_left hp hC0))
  norm_num at he
  linarith

private theorem infiniteBorel_moment_ratio_tendsto {a : ℕ→ℝ} {ell C : ℝ}
    (herror : ∀j,|a j-ell|≤C*(1/9:ℝ)^j) :
    Tendsto a atTop (𝓝 ell) := by
  have hp : Tendsto (fun j:ℕ=>(1/9:ℝ)^j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hz : Tendsto (fun j=>a j-ell) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j=>by simpa only [Real.norm_eq_abs] using herror j)
    simpa only [mul_zero] using hp.const_mul C
  simpa only [sub_add_cancel,zero_add] using hz.add_const ell

end RHTower

namespace RHTower

private theorem infiniteBorel_rawKernel_integral_norm_le
    {g : ℝ→ℝ} (hgm : Measurable g) (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤Real.exp (-|x|/2)) (z : ℂ) :
    ‖∫x:ℝ,(g x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ))‖≤
      4*Real.cosh (2*‖z‖) := by
  let a : ℕ→ℝ := fun j=>(∫x:ℝ,g x*x^(2*j))/((2*j).factorial:ℝ)^2
  have ha (j:ℕ) : |a j|≤4*2^(2*j)/((2*j).factorial:ℝ) := by
    dsimp only [a]
    rw [abs_of_nonneg (div_nonneg (integral_nonneg (fun x=>mul_nonneg (hg0 x) ((even_two_mul j).pow_nonneg x))) (sq_nonneg _))]
    calc
      _ ≤ (4*2^(2*j)*((2*j).factorial:ℝ))/((2*j).factorial:ℝ)^2 :=
        div_le_div_of_nonneg_right (infiniteBorel_density_moment_le hgm hg0 hg j) (sq_nonneg _)
      _ = _ := by field_simp
  have he : (∫x:ℝ,(g x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))=
      infiniteBorelCoefficientSeries a z := by
    rw [infiniteBorel_rawKernel_integral_eq_tsum hgm hg0 hg]
    unfold infiniteBorelCoefficientSeries
    apply tsum_congr
    intro j
    dsimp only [a]
    push_cast
    ring
  rw [he]
  exact infiniteBorel_coefficientSeries_norm_le (by norm_num : (0:ℝ)≤4) ha z

end RHTower

namespace RHTower

private theorem infiniteBorel_rawKernel_eq_normalized
    {g : ℝ→ℝ} (hgm : Measurable g) (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤Real.exp (-|x|/2)) {Z : ℝ} {d : ℕ→ℝ}
    (hmoment : ∀j,(∫x:ℝ,g x*x^(2*j))=Z^2*d j) (z : ℂ) :
    (∫x:ℝ,(g x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))=
      (Z:ℂ)^2*infiniteBorelCoefficientSeries
        (fun j:ℕ=>d j/((2*j).factorial:ℝ)^2) z := by
  rw [infiniteBorel_rawKernel_integral_eq_tsum hgm hg0 hg]
  unfold infiniteBorelCoefficientSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [hmoment]
  push_cast
  ring

private theorem infiniteBorel_normalizedKernel_eq_raw_div
    {g : ℝ→ℝ} (hgm : Measurable g) (hg0 : ∀x,0≤g x)
    (hg : ∀x,g x≤Real.exp (-|x|/2)) {Z : ℝ} (hZ : 0<Z) {d : ℕ→ℝ}
    (hmoment : ∀j,(∫x:ℝ,g x*x^(2*j))=Z^2*d j) (z : ℂ) :
    infiniteBorelCoefficientSeries (fun j:ℕ=>d j/((2*j).factorial:ℝ)^2) z =
      (∫x:ℝ,(g x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))/(Z:ℂ)^2 := by
  rw [infiniteBorel_rawKernel_eq_normalized hgm hg0 hg hmoment z]
  have hz : (Z:ℂ)≠0 := by exact_mod_cast hZ.ne'
  field_simp

end RHTower

namespace RHTower

private theorem infiniteBorel_rawKernel_difference_norm_le
    {gInf gN : ℝ→ℝ} (hmInf : Measurable gInf) (hmN : Measurable gN)
    (hnInf : ∀x,0≤gInf x) (hnN : ∀x,0≤gN x)
    (hbInf : ∀x,gInf x≤Real.exp (-|x|/2)) (hbN : ∀x,gN x≤Real.exp (-|x|/2))
    {c L : ℝ} (hc : 0≤c) (hL : 0≤L) (hκ : 0<1/2-2*Real.sqrt c)
    {z : ℂ} (hz : ‖z‖≤c*L) (hd0 : ∀x,0≤gInf x-gN x)
    (hd : ∀x,gInf x-gN x≤(if |x|<L then Real.exp (|x|/2-L) else Real.exp (-|x|/2))) :
    ‖(∫x:ℝ,(gN x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))-
      (∫x:ℝ,(gInf x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))‖≤
      2*(L+1/(1/2-2*Real.sqrt c))*Real.exp (-(1/2-2*Real.sqrt c)*L) := by
  have hiInf := infiniteBorel_integrable_rawKernel hmInf hnInf hbInf z
  have hiN := infiniteBorel_integrable_rawKernel hmN hnN hbN z
  have he : (∫x:ℝ,(gN x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))-
      (∫x:ℝ,(gInf x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))=
      -(∫x:ℝ,((gInf x-gN x:ℝ):ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ))) := by
    rw [←integral_sub hiN hiInf,←integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    push_cast
    ring
  rw [he,norm_neg]
  exact infiniteBorel_rawLoss_integral_norm_le hc hL hκ hz hd0 hd

end RHTower

namespace RHTower
noncomputable section

/-- Literal complete normalized paired-eta difference coefficient. -/
def liClockPairedEtaInfinitePartitionBorelCoefficient (j : ℕ) : ℝ :=
  liClockPairedEtaInfiniteSymmetrizedEvenMoment j / ((2*j).factorial:ℝ)^2

/-- Complete real clock, retaining every infinite-source coefficient. -/
def liClockPairedEtaInfinitePartitionBorelKernel (t : ℝ) : ℝ :=
  ∑'j:ℕ,liClockPairedEtaInfinitePartitionBorelCoefficient j*t^(2*j)

/-- Entire complex clock of the actual normalized infinite partition. -/
def liClockPairedEtaInfinitePartitionBorelKernelComplex (z : ℂ) : ℂ :=
  ∑'j:ℕ,(liClockPairedEtaInfinitePartitionBorelCoefficient j:ℂ)*z^(2*j)

/-- Literal normalized half-line difference coefficient. -/
def liClockPairedEtaHalfLineBorelCoefficient (j : ℕ) : ℝ :=
  liClockPairedEtaHalfLineSymmetrizedEvenMoment j / ((2*j).factorial:ℝ)^2

def liClockPairedEtaHalfLineBorelKernel (t : ℝ) : ℝ :=
  ∑'j:ℕ,liClockPairedEtaHalfLineBorelCoefficient j*t^(2*j)

def liClockPairedEtaHalfLineBorelKernelComplex (z : ℂ) : ℂ :=
  ∑'j:ℕ,(liClockPairedEtaHalfLineBorelCoefficient j:ℂ)*z^(2*j)

/-- Exact source-normalized geometric error scale. -/
def liClockPairedEtaInfinitePartitionMomentErrorScale : ℝ :=
  Real.pi^2/(12*liClockPairedEtaInfinitePartitionNormalizer^2)

/-- Complete raw-loss and both-normalizer error on the growing complex disk. -/
def liClockPairedEtaInfinitePartitionGrowingDiskError (c : ℝ) (N : ℕ) : ℝ :=
  (2/(2-Real.sqrt 2)^2)*
    (Real.log (2*(N:ℝ))+1/(1/2-2*Real.sqrt c))*
    Real.exp (-(1/2-2*Real.sqrt c)*Real.log (2*(N:ℝ)))+
  (32/(2-Real.sqrt 2)^4)*
    Real.exp (-(1/2-2*c)*Real.log (2*(N:ℝ)))

/-- Every normalized half-line difference moment, with the exact even factorial. -/
theorem liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq (j : ℕ) :
    liClockPairedEtaHalfLineSymmetrizedEvenMoment j=4^j*((2*j).factorial:ℝ) := by
  have hr := liClockPairedEtaHalfLineRawDifferenceDensity_moment j
  simp_rw [liClockPairedEtaHalfLineRawDifferenceDensity_eq] at hr
  rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two] at hr
  have he : (∫x:ℝ,x^(2*j)*Real.exp (-|x|/2))=4*2^(2*j)*((2*j).factorial:ℝ) := by
    calc
      _ = ∫x:ℝ,x^(2*j)*Real.exp (-(1/2)*|x|) := by
        apply integral_congr_ae
        filter_upwards with x
        congr 2; ring
      _ = _ := by
        rw [infiniteBorel_integral_even_power_exp (by norm_num : (0:ℝ)<1/2) j]
        norm_num only [one_div,inv_div,inv_one,div_one]
        rw [pow_succ]
        ring
  rw [he] at hr
  have hp : (4:ℝ)^j=2^(2*j) := by rw [pow_mul]; norm_num
  rw [hp]
  nlinarith

theorem liClockPairedEtaHalfLineBorelCoefficient_eq (j : ℕ) :
    liClockPairedEtaHalfLineBorelCoefficient j=2^(2*j)/((2*j).factorial:ℝ) := by
  unfold liClockPairedEtaHalfLineBorelCoefficient
  rw [liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq,
    show (4:ℝ)^j=2^(2*j) by rw [pow_mul]; norm_num]
  field_simp

theorem liClockPairedEtaInfinitePartitionBorelCoefficient_pos (j : ℕ) :
    0<liClockPairedEtaInfinitePartitionBorelCoefficient j :=
  div_pos (liClockPairedEtaInfiniteSymmetrizedEvenMoment_pos j) (by positivity)

theorem liClockPairedEtaInfinitePartitionBorelCoefficient_le (j : ℕ) :
    liClockPairedEtaInfinitePartitionBorelCoefficient j≤
      (4/liClockPairedEtaInfinitePartitionNormalizer^2)*2^(2*j)/((2*j).factorial:ℝ) := by
  unfold liClockPairedEtaInfinitePartitionBorelCoefficient
  calc
    _ ≤ ((4/liClockPairedEtaInfinitePartitionNormalizer^2)*
        liClockPairedEtaHalfLineSymmetrizedEvenMoment j)/((2*j).factorial:ℝ)^2 :=
      div_le_div_of_nonneg_right (liClockPairedEtaInfiniteSymmetrizedEvenMoment_le_halfLine j) (sq_nonneg _)
    _ = _ := by
      rw [liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq,
        show (4:ℝ)^j=2^(2*j) by rw [pow_mul]; norm_num]
      field_simp

private theorem infiniteBorel_actual_coefficient_bound (j : ℕ) :
    |liClockPairedEtaInfinitePartitionBorelCoefficient j|≤
      (4/liClockPairedEtaInfinitePartitionNormalizer^2)*2^(2*j)/((2*j).factorial:ℝ) := by
  rw [abs_of_pos (liClockPairedEtaInfinitePartitionBorelCoefficient_pos j)]
  exact liClockPairedEtaInfinitePartitionBorelCoefficient_le j

private theorem infiniteBorel_actual_coefficient_scale_nonneg :
    0≤4/liClockPairedEtaInfinitePartitionNormalizer^2 := by positivity

private theorem infiniteBorel_firstMass_pos : 0<2-Real.sqrt 2 := by
  nlinarith [Real.sqrt_nonneg (2:ℝ),Real.sq_sqrt (by norm_num : 0≤(2:ℝ))]

private theorem infiniteBorel_halfLine_coefficient_bound (j : ℕ) :
    |liClockPairedEtaHalfLineBorelCoefficient j|≤1*2^(2*j)/((2*j).factorial:ℝ) := by
  rw [liClockPairedEtaHalfLineBorelCoefficient_eq,one_mul,abs_of_nonneg (by positivity)]

/-- Absolute convergence of the full actual complex Borel clock. -/
theorem summable_norm_liClockPairedEtaInfinitePartitionBorelTermComplex (z : ℂ) :
    Summable (fun j:ℕ=>‖(liClockPairedEtaInfinitePartitionBorelCoefficient j:ℂ)*z^(2*j)‖) :=
  infiniteBorel_coefficientSeries_summable_norm infiniteBorel_actual_coefficient_scale_nonneg
    infiniteBorel_actual_coefficient_bound z

theorem summable_norm_liClockPairedEtaHalfLineBorelTermComplex (z : ℂ) :
    Summable (fun j:ℕ=>‖(liClockPairedEtaHalfLineBorelCoefficient j:ℂ)*z^(2*j)‖) :=
  infiniteBorel_coefficientSeries_summable_norm (by norm_num : (0:ℝ)≤1)
    infiniteBorel_halfLine_coefficient_bound z

/-- Local uniform convergence, using every actual-source coefficient. -/
theorem hasSumUniformlyOn_liClockPairedEtaInfinitePartitionBorelKernelComplex (T : ℝ) :
    HasSumUniformlyOn (fun j:ℕ=>fun z:ℂ=>(liClockPairedEtaInfinitePartitionBorelCoefficient j:ℂ)*z^(2*j))
      liClockPairedEtaInfinitePartitionBorelKernelComplex (closedBall 0 T) :=
  infiniteBorel_coefficientSeries_uniform infiniteBorel_actual_coefficient_scale_nonneg
    infiniteBorel_actual_coefficient_bound

theorem summableLocallyUniformlyOn_liClockPairedEtaInfinitePartitionBorelTermComplex :
    SummableLocallyUniformlyOn (fun j:ℕ=>fun z:ℂ=>(liClockPairedEtaInfinitePartitionBorelCoefficient j:ℂ)*z^(2*j)) univ :=
  infiniteBorel_coefficientSeries_locallyUniform infiniteBorel_actual_coefficient_scale_nonneg
    infiniteBorel_actual_coefficient_bound

/-- The complete normalized Borel clock is entire; its MGF need not be entire. -/
theorem analyticAt_liClockPairedEtaInfinitePartitionBorelKernelComplex (z : ℂ) :
    AnalyticAt ℂ liClockPairedEtaInfinitePartitionBorelKernelComplex z :=
  infiniteBorel_coefficientSeries_analyticAt infiniteBorel_actual_coefficient_scale_nonneg
    infiniteBorel_actual_coefficient_bound z

theorem liClockPairedEtaHalfLineBorelKernelComplex_eq_cosh (z : ℂ) :
    liClockPairedEtaHalfLineBorelKernelComplex z=Complex.cosh (2*z) := by
  unfold liClockPairedEtaHalfLineBorelKernelComplex
  simp_rw [liClockPairedEtaHalfLineBorelCoefficient_eq]
  exact (infiniteBorel_cosh_two_hasSum z).tsum_eq

theorem liClockPairedEtaInfinitePartitionBorelKernelComplex_ofReal (t : ℝ) :
    liClockPairedEtaInfinitePartitionBorelKernelComplex (t:ℂ)=
      (liClockPairedEtaInfinitePartitionBorelKernel t:ℂ) :=
  infiniteBorel_coefficientSeries_ofReal liClockPairedEtaInfinitePartitionBorelCoefficient t

theorem liClockPairedEtaHalfLineBorelKernelComplex_ofReal (t : ℝ) :
    liClockPairedEtaHalfLineBorelKernelComplex (t:ℂ)=(liClockPairedEtaHalfLineBorelKernel t:ℂ) :=
  infiniteBorel_coefficientSeries_ofReal liClockPairedEtaHalfLineBorelCoefficient t

theorem liClockPairedEtaHalfLineBorelKernel_eq_cosh (t : ℝ) :
    liClockPairedEtaHalfLineBorelKernel t=Real.cosh (2*t) := by
  apply Complex.ofReal_injective
  rw [←liClockPairedEtaHalfLineBorelKernelComplex_ofReal,liClockPairedEtaHalfLineBorelKernelComplex_eq_cosh]
  norm_cast

theorem liClockPairedEtaInfinitePartitionBorelKernel_ge_one (t : ℝ) :
    1≤liClockPairedEtaInfinitePartitionBorelKernel t := by
  apply infiniteBorel_coefficientSeries_ge_one infiniteBorel_actual_coefficient_scale_nonneg
    infiniteBorel_actual_coefficient_bound
  · unfold liClockPairedEtaInfinitePartitionBorelCoefficient
    rw [liClockPairedEtaInfiniteSymmetrizedEvenMoment_zero]
    norm_num
  · exact fun j=>(liClockPairedEtaInfinitePartitionBorelCoefficient_pos j).le

private theorem infiniteBorel_coefficient_bound_of_moment
    {d K : ℝ} (hd : 0≤d) (j : ℕ)
    (hbound : d≤K*(2^(2*j)*((2*j).factorial:ℝ))) :
    |d/((2*j).factorial:ℝ)^2|≤K*2^(2*j)/((2*j).factorial:ℝ) := by
  rw [abs_of_nonneg (div_nonneg hd (sq_nonneg _))]
  calc
    _ ≤ (K*(2^(2*j)*((2*j).factorial:ℝ)))/((2*j).factorial:ℝ)^2 :=
      div_le_div_of_nonneg_right hbound (sq_nonneg _)
    _ = _ := by field_simp

private theorem infiniteBorel_finite_coefficient_bound {N : ℕ} (hN : 0<N) (j : ℕ) :
    |liClockPairedEtaPartitionBorelCoefficient N j|≤
      (4/(2-Real.sqrt 2)^2)*2^(2*j)/((2*j).factorial:ℝ) := by
  unfold liClockPairedEtaPartitionBorelCoefficient
  apply infiniteBorel_coefficient_bound_of_moment (liClockPairedEtaSymmetrizedEvenMoment_pos hN j).le j
  have h := liClockPairedEtaSymmetrizedEvenMoment_le_halfLine_uniform hN j
  rw [liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq,
    show (4:ℝ)^j=2^(2*j) by rw [pow_mul]; norm_num] at h
  exact h

private theorem infiniteBorel_contiguous_coefficient_bound {N : ℕ} (hN : 0<N) (j : ℕ) :
    |liClockPairedEtaContiguousBorelCoefficient (Real.log (2*(N:ℝ))) j|≤
      (4/(2-Real.sqrt 2)^2)*2^(2*j)/((2*j).factorial:ℝ) := by
  have hL : 0<Real.log (2*(N:ℝ)) := by
    apply Real.log_pos
    have hc : (1:ℝ)≤(N:ℝ) := by exact_mod_cast (show 1≤N by omega)
    linarith
  unfold liClockPairedEtaContiguousBorelCoefficient
  apply infiniteBorel_coefficient_bound_of_moment (liClockPairedEtaContiguousSymmetrizedEvenMoment_pos hL j).le j
  have h := liClockPairedEtaContiguousSymmetrizedEvenMoment_le_halfLine_uniform hN j
  rw [liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq,
    show (4:ℝ)^j=2^(2*j) by rw [pow_mul]; norm_num] at h
  exact h

private theorem infiniteBorel_finite_coefficient_tendsto (j : ℕ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaPartitionBorelCoefficient N j) atTop
      (nhds (liClockPairedEtaInfinitePartitionBorelCoefficient j)) :=
  (tendsto_liClockPairedEtaInfiniteSymmetrizedEvenMoment j).div_const _

private theorem infiniteBorel_contiguous_coefficient_tendsto (j : ℕ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaContiguousBorelCoefficient (Real.log (2*(N:ℝ))) j) atTop
      (nhds (liClockPairedEtaHalfLineBorelCoefficient j)) :=
  (tendsto_liClockPairedEtaHalfLineSymmetrizedEvenMoment j).div_const _

private theorem infiniteBorel_actual_uniform_coefficient_bound (j : ℕ) :
    |liClockPairedEtaInfinitePartitionBorelCoefficient j|≤
      (4/(2-Real.sqrt 2)^2)*2^(2*j)/((2*j).factorial:ℝ) := by
  apply le_of_tendsto (infiniteBorel_finite_coefficient_tendsto j).abs
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact infiniteBorel_finite_coefficient_bound (by omega) j

private theorem infiniteBorel_halfLine_uniform_coefficient_bound (j : ℕ) :
    |liClockPairedEtaHalfLineBorelCoefficient j|≤
      (4/(2-Real.sqrt 2)^2)*2^(2*j)/((2*j).factorial:ℝ) := by
  apply le_of_tendsto (infiniteBorel_contiguous_coefficient_tendsto j).abs
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact infiniteBorel_contiguous_coefficient_bound (by omega) j

/-- Fixed compact complex disks converge for the literal finite interval union. -/
theorem tendstoUniformlyOn_liClockPairedEtaPartitionBorelKernelComplex (T : ℝ) :
    TendstoUniformlyOn liClockPairedEtaPartitionBorelKernelComplex
      liClockPairedEtaInfinitePartitionBorelKernelComplex atTop (closedBall 0 T) := by
  apply infiniteBorel_coefficientSeries_tendstoUniformlyOn (by positivity : (0:ℝ)≤4/(2-Real.sqrt 2)^2)
    infiniteBorel_actual_uniform_coefficient_bound
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact infiniteBorel_finite_coefficient_bound (by omega)
  · exact infiniteBorel_finite_coefficient_tendsto

/-- Fixed compact complex disks converge for the full finite half-line reference. -/
theorem tendstoUniformlyOn_liClockPairedEtaContiguousBorelKernelComplex (T : ℝ) :
    TendstoUniformlyOn (fun N:ℕ=>liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))))
      liClockPairedEtaHalfLineBorelKernelComplex atTop (closedBall 0 T) := by
  apply infiniteBorel_coefficientSeries_tendstoUniformlyOn (by positivity : (0:ℝ)≤4/(2-Real.sqrt 2)^2)
    infiniteBorel_halfLine_uniform_coefficient_bound
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact infiniteBorel_contiguous_coefficient_bound (by omega)
  · exact infiniteBorel_contiguous_coefficient_tendsto

private theorem infiniteBorel_actual_raw_le (x : ℝ) :
    liClockPairedEtaInfinitePartitionRawDifferenceDensity x≤Real.exp (-|x|/2) :=
  (liClockPairedEtaInfinitePartitionRawDifferenceDensity_le_halfLine x).trans_eq
    (liClockPairedEtaHalfLineRawDifferenceDensity_eq x)

private theorem infiniteBorel_finite_raw_le (N : ℕ) (x : ℝ) :
    liClockPairedEtaPartitionRawDifferenceDensity N x≤Real.exp (-|x|/2) :=
  (liClockPairedEtaPartitionRawDifferenceDensity_le_halfLine N x).trans_eq
    (liClockPairedEtaHalfLineRawDifferenceDensity_eq x)

private theorem infiniteBorel_contiguous_raw_le (L x : ℝ) :
    liClockPairedEtaContiguousRawDifferenceDensity L x≤Real.exp (-|x|/2) :=
  (liClockPairedEtaContiguousRawDifferenceDensity_le_halfLine L x).trans_eq
    (liClockPairedEtaHalfLineRawDifferenceDensity_eq x)

private theorem infiniteBorel_actual_raw_moment (j : ℕ) :
    (∫x:ℝ,liClockPairedEtaInfinitePartitionRawDifferenceDensity x*x^(2*j))=
      liClockPairedEtaInfinitePartitionNormalizer^2*liClockPairedEtaInfiniteSymmetrizedEvenMoment j := by
  rw [show (fun x:ℝ=>liClockPairedEtaInfinitePartitionRawDifferenceDensity x*x^(2*j))=
    (fun x:ℝ=>x^(2*j)*liClockPairedEtaInfinitePartitionRawDifferenceDensity x) by funext x; ring]
  exact liClockPairedEtaInfinitePartitionRawDifferenceDensity_moment j

private theorem infiniteBorel_halfLine_raw_moment (j : ℕ) :
    (∫x:ℝ,liClockPairedEtaHalfLineRawDifferenceDensity x*x^(2*j))=
      liClockPairedEtaHalfLinePartitionNormalizer^2*liClockPairedEtaHalfLineSymmetrizedEvenMoment j := by
  rw [show (fun x:ℝ=>liClockPairedEtaHalfLineRawDifferenceDensity x*x^(2*j))=
    (fun x:ℝ=>x^(2*j)*liClockPairedEtaHalfLineRawDifferenceDensity x) by funext x; ring]
  exact liClockPairedEtaHalfLineRawDifferenceDensity_moment j

private theorem infiniteBorel_finite_raw_moment {N : ℕ} (hN : 0<N) (j : ℕ) :
    (∫x:ℝ,liClockPairedEtaPartitionRawDifferenceDensity N x*x^(2*j))=
      liClockPairedEtaPartitionNormalizer N^2*liClockPairedEtaSymmetrizedEvenMoment N j := by
  rw [show (fun x:ℝ=>liClockPairedEtaPartitionRawDifferenceDensity N x*x^(2*j))=
    (fun x:ℝ=>x^(2*j)*liClockPairedEtaPartitionRawDifferenceDensity N x) by funext x; ring]
  exact liClockPairedEtaPartitionRawDifferenceDensity_moment hN j

private theorem infiniteBorel_contiguous_raw_moment {L : ℝ} (hL : 0<L) (j : ℕ) :
    (∫x:ℝ,liClockPairedEtaContiguousRawDifferenceDensity L x*x^(2*j))=
      liClockPairedEtaContiguousPartitionNormalizer L^2*liClockPairedEtaContiguousSymmetrizedEvenMoment L j := by
  rw [show (fun x:ℝ=>liClockPairedEtaContiguousRawDifferenceDensity L x*x^(2*j))=
    (fun x:ℝ=>x^(2*j)*liClockPairedEtaContiguousRawDifferenceDensity L x) by funext x; ring]
  exact liClockPairedEtaContiguousRawDifferenceDensity_moment hL j

private theorem infiniteBorel_actual_kernel_eq_raw_div (z : ℂ) :
    liClockPairedEtaInfinitePartitionBorelKernelComplex z=
      (∫x:ℝ,(liClockPairedEtaInfinitePartitionRawDifferenceDensity x:ℂ)*
        infiniteBorelEntireFactorialKernel (z*(x:ℂ)))/(liClockPairedEtaInfinitePartitionNormalizer:ℂ)^2 :=
  infiniteBorel_normalizedKernel_eq_raw_div measurable_liClockPairedEtaInfinitePartitionRawDifferenceDensity
    liClockPairedEtaInfinitePartitionRawDifferenceDensity_nonneg infiniteBorel_actual_raw_le
    liClockPairedEtaInfinitePartitionNormalizer_pos infiniteBorel_actual_raw_moment z

private theorem infiniteBorel_halfLine_kernel_eq_raw_div (z : ℂ) :
    liClockPairedEtaHalfLineBorelKernelComplex z=
      (∫x:ℝ,(liClockPairedEtaHalfLineRawDifferenceDensity x:ℂ)*
        infiniteBorelEntireFactorialKernel (z*(x:ℂ)))/(liClockPairedEtaHalfLinePartitionNormalizer:ℂ)^2 :=
  infiniteBorel_normalizedKernel_eq_raw_div measurable_liClockPairedEtaHalfLineRawDifferenceDensity
    liClockPairedEtaHalfLineRawDifferenceDensity_nonneg
    (fun x=>(liClockPairedEtaHalfLineRawDifferenceDensity_eq x).le)
    (by rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two]; norm_num) infiniteBorel_halfLine_raw_moment z

private theorem infiniteBorel_finite_kernel_eq_raw_div {N : ℕ} (hN : 0<N) (z : ℂ) :
    liClockPairedEtaPartitionBorelKernelComplex N z=
      (∫x:ℝ,(liClockPairedEtaPartitionRawDifferenceDensity N x:ℂ)*
        infiniteBorelEntireFactorialKernel (z*(x:ℂ)))/(liClockPairedEtaPartitionNormalizer N:ℂ)^2 :=
  infiniteBorel_normalizedKernel_eq_raw_div (continuous_liClockPairedEtaPartitionRawDifferenceDensity N).measurable
    (liClockPairedEtaPartitionRawDifferenceDensity_nonneg N) (infiniteBorel_finite_raw_le N)
    (liClockPairedEtaPartitionNormalizer_pos hN) (infiniteBorel_finite_raw_moment hN) z

private theorem infiniteBorel_contiguous_kernel_eq_raw_div {L : ℝ} (hL : 0<L) (z : ℂ) :
    liClockPairedEtaContiguousBorelKernelComplex L z=
      (∫x:ℝ,(liClockPairedEtaContiguousRawDifferenceDensity L x:ℂ)*
        infiniteBorelEntireFactorialKernel (z*(x:ℂ)))/(liClockPairedEtaContiguousPartitionNormalizer L:ℂ)^2 :=
  infiniteBorel_normalizedKernel_eq_raw_div (continuous_liClockPairedEtaContiguousRawDifferenceDensity L).measurable
    (liClockPairedEtaContiguousRawDifferenceDensity_nonneg L) (infiniteBorel_contiguous_raw_le L)
    (liClockPairedEtaContiguousPartitionNormalizer_pos hL) (infiniteBorel_contiguous_raw_moment hL) z

private theorem infiniteBorel_lossExponent_pos {c : ℝ} (hc0 : 0≤c) (hc : c<1/16) :
    0<1/2-2*Real.sqrt c := by
  nlinarith [Real.sqrt_nonneg c,Real.sq_sqrt hc0]

private theorem infiniteBorel_logEndpoint_pos {N : ℕ} (hN : 0<N) :
    0<Real.log (2*(N:ℝ)) := by
  apply Real.log_pos
  have hn : (1:ℝ)≤(N:ℝ) := by exact_mod_cast (show 1≤N by omega)
  linarith

/-- Absolute summability of every complete raw-source Taylor integral. -/
theorem summable_integral_norm_liClockPairedEtaInfinitePartitionBorelRawTermComplex (z : ℂ) :
    Summable (fun j:ℕ=>∫x:ℝ,‖(liClockPairedEtaInfinitePartitionRawDifferenceDensity x:ℂ)*
      (z*(x:ℂ))^(2*j)/((2*j).factorial:ℂ)^2‖) :=
  infiniteBorel_rawTaylor_summable_integral_norm measurable_liClockPairedEtaInfinitePartitionRawDifferenceDensity
    liClockPairedEtaInfinitePartitionRawDifferenceDensity_nonneg infiniteBorel_actual_raw_le z

theorem summable_integral_norm_liClockPairedEtaHalfLineBorelRawTermComplex (z : ℂ) :
    Summable (fun j:ℕ=>∫x:ℝ,‖(liClockPairedEtaHalfLineRawDifferenceDensity x:ℂ)*
      (z*(x:ℂ))^(2*j)/((2*j).factorial:ℂ)^2‖) :=
  infiniteBorel_rawTaylor_summable_integral_norm measurable_liClockPairedEtaHalfLineRawDifferenceDensity
    liClockPairedEtaHalfLineRawDifferenceDensity_nonneg
    (fun x=>(liClockPairedEtaHalfLineRawDifferenceDensity_eq x).le) z

/-- Full actual finite-source error on the complete growing complex disk. -/
theorem norm_liClockPairedEtaPartitionBorelKernelComplex_sub_infinite_le
    {c : ℝ} (hc0 : 0≤c) (hc : c<1/16) {N : ℕ} (hN : 0<N) {z : ℂ}
    (hz : ‖z‖≤c*Real.log (2*(N:ℝ))) :
    ‖liClockPairedEtaPartitionBorelKernelComplex N z-
      liClockPairedEtaInfinitePartitionBorelKernelComplex z‖≤
      liClockPairedEtaInfinitePartitionGrowingDiskError c N := by
  have hL := infiniteBorel_logEndpoint_pos hN
  have hκ := infiniteBorel_lossExponent_pos hc0 hc
  have hdiff (x:ℝ) := liClockPairedEtaInfinitePartitionRawDifferenceDensity_sub_finite_le hN x
  have herr : ‖(∫x:ℝ,(liClockPairedEtaPartitionRawDifferenceDensity N x:ℂ)*
      infiniteBorelEntireFactorialKernel (z*(x:ℂ)))-
      (∫x:ℝ,(liClockPairedEtaInfinitePartitionRawDifferenceDensity x:ℂ)*
        infiniteBorelEntireFactorialKernel (z*(x:ℂ)))‖≤
      2*(Real.log (2*(N:ℝ))+1/(1/2-2*Real.sqrt c))*
        Real.exp (-(1/2-2*Real.sqrt c)*Real.log (2*(N:ℝ))) := by
    apply infiniteBorel_rawKernel_difference_norm_le
      measurable_liClockPairedEtaInfinitePartitionRawDifferenceDensity
      (continuous_liClockPairedEtaPartitionRawDifferenceDensity N).measurable
      liClockPairedEtaInfinitePartitionRawDifferenceDensity_nonneg
      (liClockPairedEtaPartitionRawDifferenceDensity_nonneg N)
      infiniteBorel_actual_raw_le (infiniteBorel_finite_raw_le N) hc0 hL.le hκ hz
    · exact fun x=>(hdiff x).1
    · intro x
      exact (hdiff x).2.trans_eq (liClockPairedEtaHalfLineRawDifferenceDensity_sub_contiguous _ x)
  have hraw : ‖∫x:ℝ,(liClockPairedEtaInfinitePartitionRawDifferenceDensity x:ℂ)*
      infiniteBorelEntireFactorialKernel (z*(x:ℂ))‖≤4*Real.exp (2*‖z‖) :=
    (infiniteBorel_rawKernel_integral_norm_le measurable_liClockPairedEtaInfinitePartitionRawDifferenceDensity
      liClockPairedEtaInfinitePartitionRawDifferenceDensity_nonneg infiniteBorel_actual_raw_le z).trans
      (mul_le_mul_of_nonneg_left (infiniteBorel_cosh_le_exp (by positivity : 0≤2*‖z‖)) (by norm_num))
  rw [infiniteBorel_finite_kernel_eq_raw_div hN,infiniteBorel_actual_kernel_eq_raw_div]
  exact infiniteBorel_normalized_error_le infiniteBorel_firstMass_pos
    (liClockPairedEtaPartitionNormalizer_ge_first hN) (liClockPairedEtaPartitionNormalizer_le_infinite N)
    liClockPairedEtaInfinitePartitionNormalizer_lt_two.le
    (liClockPairedEtaInfinitePartitionNormalizer_sub_finite_le hN).2 hκ hL.le hz herr hraw

/-- Full finite reference error, preserving its own squared normalization. -/
theorem norm_liClockPairedEtaContiguousBorelKernelComplex_sub_halfLine_le
    {c : ℝ} (hc0 : 0≤c) (hc : c<1/16) {N : ℕ} (hN : 0<N) {z : ℂ}
    (hz : ‖z‖≤c*Real.log (2*(N:ℝ))) :
    ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z-
      liClockPairedEtaHalfLineBorelKernelComplex z‖≤
      liClockPairedEtaInfinitePartitionGrowingDiskError c N := by
  have hL := infiniteBorel_logEndpoint_pos hN
  have hκ := infiniteBorel_lossExponent_pos hc0 hc
  have hmass := liClockPairedEtaHalfLinePartitionNormalizer_sub_contiguous hL.le
  have hdiff0 (x:ℝ) : 0≤liClockPairedEtaHalfLineRawDifferenceDensity x-
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x :=
    sub_nonneg.mpr (liClockPairedEtaContiguousRawDifferenceDensity_le_halfLine _ x)
  have herr : ‖(∫x:ℝ,(liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x:ℂ)*
      infiniteBorelEntireFactorialKernel (z*(x:ℂ)))-
      (∫x:ℝ,(liClockPairedEtaHalfLineRawDifferenceDensity x:ℂ)*
        infiniteBorelEntireFactorialKernel (z*(x:ℂ)))‖≤
      2*(Real.log (2*(N:ℝ))+1/(1/2-2*Real.sqrt c))*
        Real.exp (-(1/2-2*Real.sqrt c)*Real.log (2*(N:ℝ))) := by
    apply infiniteBorel_rawKernel_difference_norm_le
      measurable_liClockPairedEtaHalfLineRawDifferenceDensity
      (continuous_liClockPairedEtaContiguousRawDifferenceDensity _).measurable
      liClockPairedEtaHalfLineRawDifferenceDensity_nonneg
      (liClockPairedEtaContiguousRawDifferenceDensity_nonneg _)
      (fun x=>(liClockPairedEtaHalfLineRawDifferenceDensity_eq x).le)
      (infiniteBorel_contiguous_raw_le _) hc0 hL.le hκ hz hdiff0
    intro x
    exact (liClockPairedEtaHalfLineRawDifferenceDensity_sub_contiguous _ x).le
  have hraw : ‖∫x:ℝ,(liClockPairedEtaHalfLineRawDifferenceDensity x:ℂ)*
      infiniteBorelEntireFactorialKernel (z*(x:ℂ))‖≤4*Real.exp (2*‖z‖) :=
    (infiniteBorel_rawKernel_integral_norm_le measurable_liClockPairedEtaHalfLineRawDifferenceDensity
      liClockPairedEtaHalfLineRawDifferenceDensity_nonneg
      (fun x=>(liClockPairedEtaHalfLineRawDifferenceDensity_eq x).le) z).trans
      (mul_le_mul_of_nonneg_left (infiniteBorel_cosh_le_exp (by positivity : 0≤2*‖z‖)) (by norm_num))
  have hab : liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))≤
      liClockPairedEtaHalfLinePartitionNormalizer := by linarith [Real.exp_pos (-Real.log (2*(N:ℝ))/2)]
  rw [infiniteBorel_contiguous_kernel_eq_raw_div hL,infiniteBorel_halfLine_kernel_eq_raw_div]
  exact infiniteBorel_normalized_error_le infiniteBorel_firstMass_pos
    (liClockPairedEtaContiguousPartitionNormalizer_ge_first hN) hab
    liClockPairedEtaHalfLinePartitionNormalizer_eq_two.le hmass.le hκ hL.le hz herr hraw

/-- The common absolute two-normalizer error vanishes throughout the admissible range. -/
theorem tendsto_liClockPairedEtaInfinitePartitionGrowingDiskError_zero
    {c : ℝ} (hc0 : 0≤c) (hc : c<1/16) :
    Tendsto (liClockPairedEtaInfinitePartitionGrowingDiskError c) atTop (nhds 0) := by
  have hκ := infiniteBorel_lossExponent_pos hc0 hc
  have hα : 0<1/2-2*c := by linarith
  exact (infiniteBorel_growingError_tendsto_zero (s:=2-Real.sqrt 2) hκ hα).comp
    tendsto_liClockPairedEtaPartitionLogEndpoint

theorem hasSumUniformlyOn_liClockPairedEtaHalfLineBorelKernelComplex (T : ℝ) :
    HasSumUniformlyOn (fun j:ℕ=>fun z:ℂ=>(liClockPairedEtaHalfLineBorelCoefficient j:ℂ)*z^(2*j))
      liClockPairedEtaHalfLineBorelKernelComplex (closedBall 0 T) :=
  infiniteBorel_coefficientSeries_uniform (by norm_num : (0:ℝ)≤1) infiniteBorel_halfLine_coefficient_bound

theorem summableLocallyUniformlyOn_liClockPairedEtaHalfLineBorelTermComplex :
    SummableLocallyUniformlyOn (fun j:ℕ=>fun z:ℂ=>(liClockPairedEtaHalfLineBorelCoefficient j:ℂ)*z^(2*j)) univ :=
  infiniteBorel_coefficientSeries_locallyUniform (by norm_num : (0:ℝ)≤1) infiniteBorel_halfLine_coefficient_bound

theorem analyticAt_liClockPairedEtaHalfLineBorelKernelComplex (z : ℂ) :
    AnalyticAt ℂ liClockPairedEtaHalfLineBorelKernelComplex z :=
  infiniteBorel_coefficientSeries_analyticAt (by norm_num : (0:ℝ)≤1) infiniteBorel_halfLine_coefficient_bound z

theorem liClockPairedEtaInfinitePartitionBorelCoefficient_zero :
    liClockPairedEtaInfinitePartitionBorelCoefficient 0=1 := by
  unfold liClockPairedEtaInfinitePartitionBorelCoefficient
  rw [liClockPairedEtaInfiniteSymmetrizedEvenMoment_zero]
  norm_num

theorem liClockPairedEtaInfinitePartitionBorelKernelComplex_zero :
    liClockPairedEtaInfinitePartitionBorelKernelComplex 0=1 := by
  classical
  unfold liClockPairedEtaInfinitePartitionBorelKernelComplex
  have hterm (j:ℕ) : (liClockPairedEtaInfinitePartitionBorelCoefficient j:ℂ)*0^(2*j)=
      if j=0 then 1 else 0 := by
    by_cases hj:j=0
    · subst j; simp [liClockPairedEtaInfinitePartitionBorelCoefficient_zero]
    · have hn : 2*j≠0 := by omega
      simp only [zero_pow hn,mul_zero,if_neg hj]
  simp_rw [hterm]
  simp

theorem liClockPairedEtaInfinitePartitionBorelKernel_zero :
    liClockPairedEtaInfinitePartitionBorelKernel 0=1 := by
  apply Complex.ofReal_injective
  rw [←liClockPairedEtaInfinitePartitionBorelKernelComplex_ofReal]
  simpa using liClockPairedEtaInfinitePartitionBorelKernelComplex_zero

theorem liClockPairedEtaInfinitePartitionBorelKernelComplex_ofReal_im (t : ℝ) :
    (liClockPairedEtaInfinitePartitionBorelKernelComplex (t:ℂ)).im=0 := by
  rw [liClockPairedEtaInfinitePartitionBorelKernelComplex_ofReal,Complex.ofReal_im]

end
end RHTower

namespace RHTower
noncomputable section

theorem liClockPairedEtaInfinitePartitionMomentErrorScale_nonneg :
    0≤liClockPairedEtaInfinitePartitionMomentErrorScale := by
  unfold liClockPairedEtaInfinitePartitionMomentErrorScale
  positivity

theorem liClockPairedEtaInfinitePartitionMomentErrorScale_lt_twenty_div_twentyOne :
    liClockPairedEtaInfinitePartitionMomentErrorScale<20/21 := by
  unfold liClockPairedEtaInfinitePartitionMomentErrorScale
  apply infiniteBorel_momentErrorScale_lt
  exact (by norm_num : (71/60:ℝ)<9697/8190).trans
    liClockPairedEtaInfinitePartitionNormalizer_gt_9697_div_8190

/-- Complete all-order normalized moment discrepancy from the actual arithmetic tail. -/
theorem liClockPairedEtaInfinitePartitionMomentRatio_error_le (j : ℕ) :
    |liClockPairedEtaInfiniteSymmetrizedEvenMoment j/liClockPairedEtaHalfLineSymmetrizedEvenMoment j-
      liClockPairedEtaInfinitePartitionComparisonLimit|≤
      liClockPairedEtaInfinitePartitionMomentErrorScale*(1/9)^j := by
  have hg := integrable_pow_mul_liClockPairedEtaInfinitePartitionRawDifferenceDensity j
  have hh : Integrable (fun x:ℝ=>x^(2*j)*((Real.log 2/2)*liClockPairedEtaHalfLineRawDifferenceDensity x)) := by
    convert (integrable_pow_mul_liClockPairedEtaHalfLineRawDifferenceDensity j).const_mul (Real.log 2/2) using 1
    funext x; ring
  have he := infiniteBorel_moment_error_le (D:=Real.pi^2/16) (a:=3/2)
    (by positivity) (by norm_num)
    (fun x=>by
      rw [liClockPairedEtaHalfLineRawDifferenceDensity_eq]
      exact (liClockPairedEtaInfinitePartitionRawDifferenceDensity_error_le x).trans_eq
        (by congr 2; ring)) j hg hh
  rw [liClockPairedEtaInfinitePartitionRawDifferenceDensity_moment] at he
  have hfun : (fun x:ℝ=>x^(2*j)*((Real.log 2/2)*liClockPairedEtaHalfLineRawDifferenceDensity x))=
      fun x:ℝ=>(Real.log 2/2)*(x^(2*j)*liClockPairedEtaHalfLineRawDifferenceDensity x) := by funext x; ring
  rw [hfun,integral_const_mul,liClockPairedEtaHalfLineRawDifferenceDensity_moment,
    liClockPairedEtaHalfLinePartitionNormalizer_eq_two,liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq] at he
  have hp : (4:ℝ)^j=2^(2*j) := by rw [pow_mul]; norm_num
  rw [hp] at he
  have herr : |liClockPairedEtaInfinitePartitionNormalizer^2*liClockPairedEtaInfiniteSymmetrizedEvenMoment j-
      (Real.log 2/2)*(4*2^(2*j)*((2*j).factorial:ℝ))|≤
      (Real.pi^2/16)*2*((2/3)^(2*j+1)*((2*j).factorial:ℝ)) := by
    convert he using 1 <;> norm_num <;> ring_nf
  have h := infiniteBorel_normalized_moment_error liClockPairedEtaInfinitePartitionNormalizer_pos
    (D:=Real.pi^2/16) (h:=Real.log 2/2) (by positivity) j herr
  unfold liClockPairedEtaInfinitePartitionComparisonLimit liClockPairedEtaInfinitePartitionMomentErrorScale
  rw [liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq,hp]
  convert h using 1 <;> congr 1 <;> ring

/-- The actual all-order moment ratio tends to its literal source normalization. -/
theorem tendsto_liClockPairedEtaInfinitePartitionMomentRatio :
    Tendsto (fun j:ℕ=>liClockPairedEtaInfiniteSymmetrizedEvenMoment j/
      liClockPairedEtaHalfLineSymmetrizedEvenMoment j) atTop
      (nhds liClockPairedEtaInfinitePartitionComparisonLimit) :=
  infiniteBorel_moment_ratio_tendsto liClockPairedEtaInfinitePartitionMomentRatio_error_le

/-- Exact finite-degree comparison starts at degree four, with no moment-sign premise. -/
theorem liClockPairedEtaInfiniteSymmetrizedEvenMoment_lt_halfLine {j : ℕ} (hj : 4≤j) :
    liClockPairedEtaInfiniteSymmetrizedEvenMoment j<liClockPairedEtaHalfLineSymmetrizedEvenMoment j := by
  have h := infiniteBorel_degree_four_ratio_lt_one hj
    liClockPairedEtaInfinitePartitionComparisonLimit_lt_5040_div_5041
    liClockPairedEtaInfinitePartitionMomentErrorScale_nonneg
    liClockPairedEtaInfinitePartitionMomentErrorScale_lt_twenty_div_twentyOne
    (liClockPairedEtaInfinitePartitionMomentRatio_error_le j)
  exact (div_lt_one (liClockPairedEtaHalfLineSymmetrizedEvenMoment_pos j)).mp h

private theorem infiniteBorel_actual_remainder_coefficient_bound (j : ℕ) :
    |liClockPairedEtaInfinitePartitionBorelCoefficient j-
      liClockPairedEtaInfinitePartitionComparisonLimit*(2^(2*j)/((2*j).factorial:ℝ))|≤
      liClockPairedEtaInfinitePartitionMomentErrorScale*(2/3)^(2*j)/((2*j).factorial:ℝ) := by
  have hf : (0:ℝ)<((2*j).factorial:ℝ) := by positivity
  have hp : (0:ℝ)<2^(2*j) := by positivity
  have h := liClockPairedEtaInfinitePartitionMomentRatio_error_le j
  rw [liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq,
    show (4:ℝ)^j=2^(2*j) by rw [pow_mul]; norm_num] at h
  have he : liClockPairedEtaInfinitePartitionBorelCoefficient j-
      liClockPairedEtaInfinitePartitionComparisonLimit*(2^(2*j)/((2*j).factorial:ℝ))=
      (liClockPairedEtaInfiniteSymmetrizedEvenMoment j/(2^(2*j)*((2*j).factorial:ℝ))-
        liClockPairedEtaInfinitePartitionComparisonLimit)*(2^(2*j)/((2*j).factorial:ℝ)) := by
    unfold liClockPairedEtaInfinitePartitionBorelCoefficient
    field_simp
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0≤2^(2*j)/((2*j).factorial:ℝ))]
  calc
    _ ≤ (liClockPairedEtaInfinitePartitionMomentErrorScale*(1/9)^j)*(2^(2*j)/((2*j).factorial:ℝ)) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by
      rw [pow_mul,pow_mul,show (2/3:ℝ)^2=2^2*(1/9) by ring,mul_pow]
      ring

/-- Full complex entire-clock remainder, retaining every actual source moment. -/
theorem norm_liClockPairedEtaInfinitePartitionBorelKernelComplex_sub_scaled_cosh_le (z : ℂ) :
    ‖liClockPairedEtaInfinitePartitionBorelKernelComplex z-
      (liClockPairedEtaInfinitePartitionComparisonLimit:ℂ)*Complex.cosh (2*z)‖≤
      liClockPairedEtaInfinitePartitionMomentErrorScale*Real.cosh (2*‖z‖/3) :=
  infiniteBorel_complex_remainder_bound infiniteBorel_actual_coefficient_scale_nonneg
    liClockPairedEtaInfinitePartitionMomentErrorScale_nonneg infiniteBorel_actual_coefficient_bound
    infiniteBorel_actual_remainder_coefficient_bound z

theorem abs_liClockPairedEtaInfinitePartitionBorelKernel_sub_scaled_cosh_le (t : ℝ) :
    |liClockPairedEtaInfinitePartitionBorelKernel t-
      liClockPairedEtaInfinitePartitionComparisonLimit*Real.cosh (2*t)|≤
      liClockPairedEtaInfinitePartitionMomentErrorScale*Real.cosh (2*|t|/3) := by
  have h := norm_liClockPairedEtaInfinitePartitionBorelKernelComplex_sub_scaled_cosh_le (t:ℂ)
  rw [liClockPairedEtaInfinitePartitionBorelKernelComplex_ofReal] at h
  norm_cast at h

private theorem infiniteBorel_actual_real_remainder (t : ℝ) (ht : 0≤t) :
    |liClockPairedEtaInfinitePartitionBorelKernel t-
      liClockPairedEtaInfinitePartitionComparisonLimit*Real.cosh (2*t)|≤
      liClockPairedEtaInfinitePartitionMomentErrorScale*Real.cosh (2*t/3) := by
  simpa only [abs_of_nonneg ht] using abs_liClockPairedEtaInfinitePartitionBorelKernel_sub_scaled_cosh_le t

theorem liClockPairedEtaInfinitePartitionBorelKernel_relative_error_le {t : ℝ} (ht : 0≤t) :
    |liClockPairedEtaInfinitePartitionBorelKernel t/liClockPairedEtaHalfLineBorelKernel t-
      liClockPairedEtaInfinitePartitionComparisonLimit|≤
      2*liClockPairedEtaInfinitePartitionMomentErrorScale*Real.exp (-(4/3)*t) := by
  rw [liClockPairedEtaHalfLineBorelKernel_eq_cosh]
  exact infiniteBorel_real_relative_error liClockPairedEtaInfinitePartitionMomentErrorScale_nonneg
    infiniteBorel_actual_real_remainder ht

theorem tendsto_liClockPairedEtaInfinitePartitionBorelKernel_div_halfLine :
    Tendsto (fun t:ℝ=>liClockPairedEtaInfinitePartitionBorelKernel t/liClockPairedEtaHalfLineBorelKernel t)
      atTop (nhds liClockPairedEtaInfinitePartitionComparisonLimit) := by
  simp_rw [liClockPairedEtaHalfLineBorelKernel_eq_cosh]
  exact infiniteBorel_real_relative_tendsto liClockPairedEtaInfinitePartitionMomentErrorScale_nonneg
    infiniteBorel_actual_real_remainder

theorem tendsto_liClockPairedEtaInfinitePartitionBorelKernel_scaled :
    Tendsto (fun t:ℝ=>Real.exp (-2*t)*liClockPairedEtaInfinitePartitionBorelKernel t)
      atTop (nhds (liClockPairedEtaInfinitePartitionComparisonLimit/2)) :=
  infiniteBorel_real_scaled_tendsto liClockPairedEtaInfinitePartitionMomentErrorScale_nonneg
    infiniteBorel_actual_real_remainder

theorem tendsto_liClockPairedEtaHalfLineBorelKernel_sub_infinite_scaled :
    Tendsto (fun t:ℝ=>Real.exp (-2*t)*(liClockPairedEtaHalfLineBorelKernel t-
      liClockPairedEtaInfinitePartitionBorelKernel t))
      atTop (nhds ((1-liClockPairedEtaInfinitePartitionComparisonLimit)/2)) := by
  simp_rw [liClockPairedEtaHalfLineBorelKernel_eq_cosh]
  exact infiniteBorel_reference_gap_scaled_tendsto liClockPairedEtaInfinitePartitionMomentErrorScale_nonneg
    infiniteBorel_actual_real_remainder

/-- The complete normalized reference deficit escapes positively. -/
theorem tendsto_liClockPairedEtaHalfLineBorelKernel_sub_infinite :
    Tendsto (fun t:ℝ=>liClockPairedEtaHalfLineBorelKernel t-
      liClockPairedEtaInfinitePartitionBorelKernel t) atTop atTop := by
  simp_rw [liClockPairedEtaHalfLineBorelKernel_eq_cosh]
  apply infiniteBorel_reference_gap_tendsto liClockPairedEtaInfinitePartitionMomentErrorScale_nonneg
  · linarith [liClockPairedEtaInfinitePartitionComparisonLimit_lt_5040_div_5041]
  · exact infiniteBorel_actual_real_remainder

end
end RHTower

namespace RHTower
noncomputable section

/-- Complete raw reference truncation envelope, retaining both source coordinates. -/
def liClockPairedEtaInfinitePartitionRawLossEnvelope (N : ℕ) (z : ℂ) : ℝ :=
  ∫ x : ℝ,
    (liClockPairedEtaHalfLineRawDifferenceDensity x -
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x) *
    Real.exp (2*Real.sqrt (‖z‖*|x|))

private theorem infiniteBorel_reference_loss_bounds (N : ℕ) (x : ℝ) :
    0≤liClockPairedEtaHalfLineRawDifferenceDensity x-
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x ∧
    liClockPairedEtaHalfLineRawDifferenceDensity x-
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x≤
        Real.exp (-|x|/2) := by
  constructor
  · exact sub_nonneg.mpr (liClockPairedEtaContiguousRawDifferenceDensity_le_halfLine _ x)
  · have hn := liClockPairedEtaContiguousRawDifferenceDensity_nonneg
      (Real.log (2*(N:ℝ))) x
    rw [liClockPairedEtaHalfLineRawDifferenceDensity_eq]
    linarith

private theorem infiniteBorel_reference_loss_integrand_le (N : ℕ) (z : ℂ) (x : ℝ) :
    (liClockPairedEtaHalfLineRawDifferenceDensity x-
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x)*
      Real.exp (2*Real.sqrt (‖z‖*|x|))≤
        Real.exp (4*‖z‖)*Real.exp (-|x|/4) := by
  have hy : 2*Real.sqrt (‖z‖*|x|)≤|x|/4+4*‖z‖ := by
    rw [mul_comm ‖z‖ |x|]
    exact infiniteBorel_sqrt_young |x| ‖z‖ (abs_nonneg _) (norm_nonneg _)
  calc
    _ ≤ Real.exp (-|x|/2)*Real.exp (|x|/4+4*‖z‖) :=
      mul_le_mul (infiniteBorel_reference_loss_bounds N x).2 (Real.exp_le_exp.mpr hy)
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by
      rw [←Real.exp_add,←Real.exp_add]
      congr 1
      ring_nf

/-- Genuine integrability of the complete reference-loss envelope. -/
theorem integrable_liClockPairedEtaInfinitePartitionRawLossEnvelope
    {N : ℕ} (_hN : 0<N) (z : ℂ) :
    Integrable (fun x : ℝ =>
      (liClockPairedEtaHalfLineRawDifferenceDensity x-
        liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x)*
      Real.exp (2*Real.sqrt (‖z‖*|x|))) := by
  have hm : Measurable (fun x : ℝ =>
      (liClockPairedEtaHalfLineRawDifferenceDensity x-
        liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x)*
      Real.exp (2*Real.sqrt (‖z‖*|x|))) :=
    (measurable_liClockPairedEtaHalfLineRawDifferenceDensity.sub
      (continuous_liClockPairedEtaContiguousRawDifferenceDensity _).measurable).mul (by fun_prop)
  have hI : Integrable (fun x:ℝ=>Real.exp (4*‖z‖)*Real.exp (-|x|/4)) := by
    have h := (infiniteBorel_integrable_abs_power_exp (a:=(1/4:ℝ)) (by norm_num) 0).const_mul
      (Real.exp (4*‖z‖))
    apply h.congr
    filter_upwards with x
    simp only [pow_zero,one_mul]
    congr 2
    ring_nf
  apply hI.mono' hm.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (infiniteBorel_reference_loss_bounds N x).1 (Real.exp_pos _).le)]
  exact infiniteBorel_reference_loss_integrand_le N z x

private theorem infiniteBorel_rawKernel_difference_le_referenceEnvelope
    {N : ℕ} (hN : 0<N) {gInf gN : ℝ→ℝ}
    (hmInf : Measurable gInf) (hmN : Measurable gN)
    (hnInf : ∀x,0≤gInf x) (hnN : ∀x,0≤gN x)
    (hbInf : ∀x,gInf x≤Real.exp (-|x|/2))
    (hbN : ∀x,gN x≤Real.exp (-|x|/2))
    (hd0 : ∀x,0≤gInf x-gN x)
    (hd : ∀x,gInf x-gN x≤liClockPairedEtaHalfLineRawDifferenceDensity x-
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x)
    (z : ℂ) :
    ‖(∫x:ℝ,(gN x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))-
      (∫x:ℝ,(gInf x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))‖≤
      liClockPairedEtaInfinitePartitionRawLossEnvelope N z := by
  have hiInf := infiniteBorel_integrable_rawKernel hmInf hnInf hbInf z
  have hiN := infiniteBorel_integrable_rawKernel hmN hnN hbN z
  have he : (∫x:ℝ,(gN x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))-
      (∫x:ℝ,(gInf x:ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ)))=
      -(∫x:ℝ,((gInf x-gN x:ℝ):ℂ)*infiniteBorelEntireFactorialKernel (z*(x:ℂ))) := by
    rw [←integral_sub hiN hiInf,←integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    push_cast
    ring_nf
  rw [he,norm_neg]
  apply norm_integral_le_of_norm_le
    (integrable_liClockPairedEtaInfinitePartitionRawLossEnvelope hN z)
  filter_upwards with x
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hd0 x)]
  have hnorm : ‖z*(x:ℂ)‖=‖z‖*|x| := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul (hd x) (by
    simpa only [hnorm] using infiniteBorel_factorialKernel_norm_le (z*(x:ℂ)))
    (norm_nonneg _) (infiniteBorel_reference_loss_bounds N x).1

private theorem infiniteBorel_normalized_error_le_referenceEnvelope
    {s a b L U : ℝ} (hs : 0<s) (hsa : s≤a) (hab : a≤b) (hb : b≤2)
    (hd : b-a≤2*Real.exp (-L/2)) {z Rfinite Rinfinite : ℂ}
    (herror : ‖Rfinite-Rinfinite‖≤U)
    (hraw : ‖Rinfinite‖≤4*Real.exp (2*‖z‖)) :
    ‖Rfinite/(a:ℂ)^2-Rinfinite/(b:ℂ)^2‖≤
      U/s^2+(32/s^4)*Real.exp (-L/2+2*‖z‖) := by
  have ha : 0<a := hs.trans_le hsa
  have hbp : 0<b := ha.trans_le hab
  have hai : (a:ℂ)≠0 := by exact_mod_cast ha.ne'
  have hbi : (b:ℂ)≠0 := by exact_mod_cast hbp.ne'
  have hinv := infiniteBorel_inverse_square_error hs hsa hab hb hd
  have hsq : s^2≤a^2 := by nlinarith
  have hU : 0≤U := (norm_nonneg _).trans herror
  have he : Rfinite/(a:ℂ)^2-Rinfinite/(b:ℂ)^2=
      (Rfinite-Rinfinite)/(a:ℂ)^2+Rinfinite*((1/a^2-1/b^2:ℝ):ℂ) := by
    push_cast
    field_simp
    ring_nf
  rw [he]
  calc
    _ ≤ ‖(Rfinite-Rinfinite)/(a:ℂ)^2‖+‖Rinfinite*((1/a^2-1/b^2:ℝ):ℂ)‖ := norm_add_le _ _
    _ = ‖Rfinite-Rinfinite‖/a^2+‖Rinfinite‖*(1/a^2-1/b^2) := by
      simp only [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,norm_mul,abs_of_pos ha,
        abs_of_nonneg hinv.1]
    _ ≤ U/s^2+(4*Real.exp (2*‖z‖))*(8*Real.exp (-L/2)/s^4) := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_right herror (sq_nonneg a)).trans
          (div_le_div_of_nonneg_left hU (by positivity) hsq)
      · exact mul_le_mul hraw (hinv.2.trans_eq (by ring_nf)) hinv.1 (by positivity)
    _ = _ := by
      rw [show (4*Real.exp (2*‖z‖))*(8*Real.exp (-L/2)/s^4)=
        (32/s^4)*(Real.exp (2*‖z‖)*Real.exp (-L/2)) by ring_nf,←Real.exp_add]
      congr 2
      ring_nf

/-- Complete actual-source error controlled by the literal raw reference loss. -/
theorem norm_liClockPairedEtaPartitionBorelKernelComplex_sub_infinite_le_rawLossEnvelope
    {N : ℕ} (hN : 0<N) (z : ℂ) :
    ‖liClockPairedEtaPartitionBorelKernelComplex N z-
      liClockPairedEtaInfinitePartitionBorelKernelComplex z‖≤
      liClockPairedEtaInfinitePartitionRawLossEnvelope N z/(2-Real.sqrt 2)^2+
        (32/(2-Real.sqrt 2)^4)*Real.exp (-Real.log (2*(N:ℝ))/2+2*‖z‖) := by
  have herr := infiniteBorel_rawKernel_difference_le_referenceEnvelope hN
    measurable_liClockPairedEtaInfinitePartitionRawDifferenceDensity
    (continuous_liClockPairedEtaPartitionRawDifferenceDensity N).measurable
    liClockPairedEtaInfinitePartitionRawDifferenceDensity_nonneg
    (liClockPairedEtaPartitionRawDifferenceDensity_nonneg N)
    infiniteBorel_actual_raw_le (infiniteBorel_finite_raw_le N)
    (fun x=>(liClockPairedEtaInfinitePartitionRawDifferenceDensity_sub_finite_le hN x).1)
    (fun x=>(liClockPairedEtaInfinitePartitionRawDifferenceDensity_sub_finite_le hN x).2) z
  have hraw : ‖∫x:ℝ,(liClockPairedEtaInfinitePartitionRawDifferenceDensity x:ℂ)*
      infiniteBorelEntireFactorialKernel (z*(x:ℂ))‖≤4*Real.exp (2*‖z‖) :=
    (infiniteBorel_rawKernel_integral_norm_le measurable_liClockPairedEtaInfinitePartitionRawDifferenceDensity
      liClockPairedEtaInfinitePartitionRawDifferenceDensity_nonneg infiniteBorel_actual_raw_le z).trans
      (mul_le_mul_of_nonneg_left (infiniteBorel_cosh_le_exp (by positivity : 0≤2*‖z‖)) (by norm_num))
  rw [infiniteBorel_finite_kernel_eq_raw_div hN,infiniteBorel_actual_kernel_eq_raw_div]
  exact infiniteBorel_normalized_error_le_referenceEnvelope infiniteBorel_firstMass_pos
    (liClockPairedEtaPartitionNormalizer_ge_first hN) (liClockPairedEtaPartitionNormalizer_le_infinite N)
    liClockPairedEtaInfinitePartitionNormalizer_lt_two.le
    (liClockPairedEtaInfinitePartitionNormalizer_sub_finite_le hN).2 herr hraw

/-- Complete reference-source error with its own two squared normalizers. -/
theorem norm_liClockPairedEtaContiguousBorelKernelComplex_sub_halfLine_le_rawLossEnvelope
    {N : ℕ} (hN : 0<N) (z : ℂ) :
    ‖liClockPairedEtaContiguousBorelKernelComplex (Real.log (2*(N:ℝ))) z-
      liClockPairedEtaHalfLineBorelKernelComplex z‖≤
      liClockPairedEtaInfinitePartitionRawLossEnvelope N z/(2-Real.sqrt 2)^2+
        (32/(2-Real.sqrt 2)^4)*Real.exp (-Real.log (2*(N:ℝ))/2+2*‖z‖) := by
  have hL := infiniteBorel_logEndpoint_pos hN
  have herr := infiniteBorel_rawKernel_difference_le_referenceEnvelope hN
    measurable_liClockPairedEtaHalfLineRawDifferenceDensity
    (continuous_liClockPairedEtaContiguousRawDifferenceDensity _).measurable
    liClockPairedEtaHalfLineRawDifferenceDensity_nonneg
    (liClockPairedEtaContiguousRawDifferenceDensity_nonneg _)
    (fun x=>(liClockPairedEtaHalfLineRawDifferenceDensity_eq x).le)
    (infiniteBorel_contiguous_raw_le _)
    (fun x=>sub_nonneg.mpr (liClockPairedEtaContiguousRawDifferenceDensity_le_halfLine _ x))
    (fun _=>le_rfl) z
  have hraw : ‖∫x:ℝ,(liClockPairedEtaHalfLineRawDifferenceDensity x:ℂ)*
      infiniteBorelEntireFactorialKernel (z*(x:ℂ))‖≤4*Real.exp (2*‖z‖) :=
    (infiniteBorel_rawKernel_integral_norm_le measurable_liClockPairedEtaHalfLineRawDifferenceDensity
      liClockPairedEtaHalfLineRawDifferenceDensity_nonneg
      (fun x=>(liClockPairedEtaHalfLineRawDifferenceDensity_eq x).le) z).trans
      (mul_le_mul_of_nonneg_left (infiniteBorel_cosh_le_exp (by positivity : 0≤2*‖z‖)) (by norm_num))
  have hmass := liClockPairedEtaHalfLinePartitionNormalizer_sub_contiguous hL.le
  have hab : liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))≤
      liClockPairedEtaHalfLinePartitionNormalizer := by linarith [Real.exp_pos (-Real.log (2*(N:ℝ))/2)]
  rw [infiniteBorel_contiguous_kernel_eq_raw_div hL,infiniteBorel_halfLine_kernel_eq_raw_div]
  exact infiniteBorel_normalized_error_le_referenceEnvelope infiniteBorel_firstMass_pos
    (liClockPairedEtaContiguousPartitionNormalizer_ge_first hN) hab
    liClockPairedEtaHalfLinePartitionNormalizer_eq_two.le hmass.le herr hraw

end
end RHTower
