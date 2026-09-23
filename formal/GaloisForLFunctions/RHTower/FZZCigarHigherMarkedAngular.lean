import GaloisForLFunctions.RHTower.FZZCigarHigherScreeningAngular
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Original higher logarithmic screening source

Harmonic Poisson reproduction evaluates the original inverse-square logarithmic
angular insertion. Dominated parameter differentiation on compact parameter–angle
rectangles retains the unmarked term created by differentiating the logarithm.
The resulting recurrence evaluates the fourth- and sixth-power insertions.

At exponent `-6`, the regular-factor mark has divergent angular coefficients
`-3*r^(2 : ℕ)-21*r^(4 : ℕ)`. An explicit logarithmic Taylor bound admits the remaining radial
source, and FTC plus dominated convergence gives its corrected cutoff limit.
The singular-factor mark multiplies the original unmarked angular source by
`log r`; continuity of `r*log r` admits its remainder and gives the different
power-log and squared-log corrections. These are original angular integrals,
not assumed values of a continued special function.

Every public theorem discharges its analytic domain from real data. The planar
transport of these two different local marks, their exterior, full CFT
normalization, physical parameter derivatives and mixed Ward law remain separate
obligations. No phase-frame choice, stationarity, or RH assertion is assumed.
-/

open MeasureTheory Set Metric Filter Complex InnerProductSpace
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

/-- Original angular integral with a logarithmic regular-factor insertion. -/
def fzzScreeningHigherMarkedAngular (n : ℕ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z : ℂ => Real.log ‖1-z‖ * (‖1-z‖^(2*n))⁻¹) 0 r

private def angularQ (r θ : ℝ) : ℝ := 1-2*r*Real.cos θ+r^(2 : ℕ)
private def angularPower (n : ℕ) (r θ : ℝ) : ℝ := (angularQ r θ^n)⁻¹
private def angularMean (n : ℕ) (r : ℝ) : ℝ :=
  (2*Real.pi)⁻¹*(∫ θ : ℝ in Ioc 0 (2*Real.pi), angularPower n r θ)
private def angularPowerDerivative (n : ℕ) (r θ : ℝ) : ℝ :=
  2*((n+1 : ℕ) : ℝ)*(Real.cos θ-r)*(angularQ r θ^(n+2))⁻¹

private theorem angularQ_pos (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < angularQ r θ := by
  have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) (show 0 ≤ 2*r by positivity)
  have hs : 0 < (1-r)^(2 : ℕ) := by
    have h : 0 < 1-r := by linarith
    positivity
  unfold angularQ
  nlinarith

private theorem norm_circle_eq_angularQ (r θ : ℝ) :
    ‖1-(r : ℂ)*circleMap 0 1 θ‖^(2 : ℕ) = angularQ r θ := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, circleMap_zero_re, circleMap_zero_im, one_mul,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  have ht : r^(2 : ℕ)*(Real.sin θ^(2 : ℕ)+Real.cos θ^(2 : ℕ))=r^(2 : ℕ) := by
    rw [Real.sin_sq_add_cos_sq, mul_one]
  unfold angularQ
  nlinarith [ht]

private theorem angularQ_hasDerivAt (r θ : ℝ) :
    HasDerivAt (fun t => angularQ t θ) (2*r-2*Real.cos θ) r := by
  have h := ((hasDerivAt_const r (1 : ℝ)).sub
    ((hasDerivAt_id r).const_mul (2*Real.cos θ))).add ((hasDerivAt_id r).pow 2)
  convert! h using 1
  · ext t
    simp only [angularQ, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [id_eq]
    ring

private theorem angularPower_hasDerivAt (n : ℕ) (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt (fun t => angularPower (n+1) t θ) (angularPowerDerivative n r θ) r := by
  have hq := (angularQ_pos r θ hr0 hr1).ne'
  have h := ((angularQ_hasDerivAt r θ).pow (n+1)).inv (pow_ne_zero _ hq)
  convert! h using 1
  dsimp [angularPowerDerivative]
  simp only [pow_succ]
  field_simp [hq, pow_ne_zero n hq]
  ring

private theorem angularPower_continuous (n : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (angularPower n r) := by
  apply Continuous.inv₀
  · unfold angularQ
    fun_prop
  · intro θ
    exact pow_ne_zero _ (angularQ_pos r θ hr0 hr1).ne'

private theorem higherAngular_eq_mean (n : ℕ) (r : ℝ) :
    fzzScreeningHigherAngular n r = angularMean n r := by
  rw [fzzScreeningHigherAngular, Real.circleAverage_eq_circleAverage_zero_one,
    Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)]
  simp only [add_zero, angularMean, angularPower, pow_mul, norm_circle_eq_angularQ]

private theorem angularRadius_range (u : ℝ) :
    0 < fzzScreeningAngularRadius u ∧ fzzScreeningAngularRadius u < 1 := by
  have hp := Real.exp_pos u
  constructor
  · unfold fzzScreeningAngularRadius
    positivity
  · rw [fzzScreeningAngularRadius, inv_lt_one₀ (by positivity)]
    linarith


private theorem markedDen_pos (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < 1-r^(2 : ℕ) := by nlinarith

private theorem marked_one_unit (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun z : ℂ => Real.log ‖1-(r : ℂ)*z‖ *
      (‖1-(r : ℂ)*z‖^(2 : ℕ))⁻¹) 0 1 = Real.log (1-r^(2 : ℕ))/(1-r^(2 : ℕ)) := by
  have hn := (markedDen_pos r hr0 hr1).ne'
  have hzero : ∀ z : ℂ, z ∈ closedBall 0 1 → 1-(r : ℂ)*z ≠ 0 := by
    intro z hz he
    have hnorm : ‖z‖ ≤ 1 := by simpa using hz
    have hm : ‖(r : ℂ)*z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      calc r*‖z‖ ≤ r*1 := mul_le_mul_of_nonneg_left hnorm hr0
           _ < 1 := by simpa using hr1
    have heq : (r : ℂ)*z = 1 := (sub_eq_zero.mp he).symm
    rw [heq, norm_one] at hm
    exact (lt_irrefl _ hm)
  have hh : HarmonicOnNhd (fun z : ℂ => Real.log ‖1-(r : ℂ)*z‖) (closedBall 0 1) := by
    intro z hz
    exact ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) :
      AnalyticAt ℂ (fun z : ℂ => 1-(r : ℂ)*z) z).harmonicAt_log_norm (hzero z hz)
  have hb : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball, dist_eq_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hp := hh.circleAverage_poissonKernel_smul hb
  have hc : Real.circleAverage (fun z : ℂ => Real.log ‖1-(r : ℂ)*z‖ *
        (‖1-(r : ℂ)*z‖^(2 : ℕ))⁻¹) 0 1 =
      Real.circleAverage ((1-r^(2 : ℕ))⁻¹ •
        (poissonKernel 0 (r : ℂ) • (fun z : ℂ => Real.log ‖1-(r : ℂ)*z‖))) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, poissonKernel, sub_zero]
    rw [_root_.RHTower.norm_one_sub_mul_eq_norm_sub hz1, hz1, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0]
    field_simp [hn]
  rw [hc, Real.circleAverage_smul, hp, smul_eq_mul]
  have he : (1 : ℂ)-(r : ℂ)*(r : ℂ) = ((1-r^(2 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (markedDen_pos r hr0 hr1)]
  ring

private theorem marked_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    fzzScreeningHigherMarkedAngular 1 r = Real.log (1-r^(2 : ℕ))/(1-r^(2 : ℕ)) := by
  rw [fzzScreeningHigherMarkedAngular, Real.circleAverage_eq_circleAverage_zero_one]
  simpa only [add_zero, Nat.mul_one] using marked_one_unit r hr0 hr1


private def angularMark (n : ℕ) (r θ : ℝ) : ℝ :=
  Real.log (angularQ r θ)/2*angularPower n r θ
private def angularMarkMean (n : ℕ) (r : ℝ) : ℝ :=
  (2*Real.pi)⁻¹*(∫ θ : ℝ in Ioc 0 (2*Real.pi), angularMark n r θ)
private def angularMarkDerivative (n : ℕ) (r θ : ℝ) : ℝ :=
  (Real.cos θ-r)*(((n+1 : ℕ) : ℝ)*Real.log (angularQ r θ)-1)*
    angularPower (n+2) r θ

private theorem angularMark_continuous (n : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (angularMark n r) := by
  exact (((show Continuous (angularQ r) by unfold angularQ; fun_prop).log
    (fun θ => (angularQ_pos r θ hr0 hr1).ne')).div_const 2).mul
      (angularPower_continuous n r hr0 hr1)

private theorem angularMarkDerivative_continuous (n : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) : Continuous (angularMarkDerivative n r) := by
  have hl : Continuous (fun θ => Real.log (angularQ r θ)) :=
    (show Continuous (angularQ r) by unfold angularQ; fun_prop).log
      (fun θ => (angularQ_pos r θ hr0 hr1).ne')
  exact ((show Continuous (fun θ : ℝ => Real.cos θ-r) by fun_prop).mul
    ((hl.const_mul _).sub continuous_const)).mul (angularPower_continuous (n+2) r hr0 hr1)

private theorem angularMark_hasDerivAt (n : ℕ) (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt (fun t => angularMark (n+1) t θ) (angularMarkDerivative n r θ) r := by
  have hq := (angularQ_pos r θ hr0 hr1).ne'
  have h := (((angularQ_hasDerivAt r θ).log hq).div_const 2).mul
    (angularPower_hasDerivAt n r θ hr0 hr1)
  convert! h using 1
  dsimp [angularMarkDerivative, angularPowerDerivative, angularPower]
  simp only [pow_succ]
  field_simp [hq, pow_ne_zero n hq]
  ring

private theorem angularMarkMean_hasDerivAt (n : ℕ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt (angularMarkMean (n+1))
      ((2*Real.pi)⁻¹*(∫ θ : ℝ in Ioc 0 (2*Real.pi), angularMarkDerivative n r θ)) r := by
  let lo := r/2
  let hi := (1+r)/2
  let K := Icc lo hi ×ˢ Icc (0 : ℝ) (2*Real.pi)
  have hbounds : ∀ p : ℝ × ℝ, p ∈ K → 0 ≤ p.1 ∧ p.1 < 1 := by
    intro p hp
    dsimp [K,lo,hi] at hp
    constructor <;> linarith [hp.1.1,hp.1.2]
  have hq : ContinuousOn (fun p : ℝ × ℝ => angularQ p.1 p.2) K := by
    unfold angularQ
    fun_prop
  have hinv : ContinuousOn (fun p : ℝ × ℝ => (angularQ p.1 p.2^(n+2))⁻¹) K :=
    (hq.pow (n+2)).inv₀ (fun p hp => pow_ne_zero _
      (angularQ_pos p.1 p.2 (hbounds p hp).1 (hbounds p hp).2).ne')
  have hl := hq.log (fun p hp =>
    (angularQ_pos p.1 p.2 (hbounds p hp).1 (hbounds p hp).2).ne')
  have hc : ContinuousOn (fun p : ℝ × ℝ => angularMarkDerivative n p.1 p.2) K :=
    ((show ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2-p.1) K by fun_prop).mul
      ((hl.const_mul _).sub continuousOn_const)).mul hinv
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  have hn : Ioo lo hi ∈ 𝓝 r := Ioo_mem_nhds (by dsimp [lo]; linarith) (by dsimp [hi]; linarith)
  have hrange : ∀ t ∈ Ioo lo hi, 0 ≤ t ∧ t < 1 := by
    intro t ht
    dsimp [lo,hi] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) (2*Real.pi)))
    (F := fun t θ => angularMark (n+1) t θ)
    (F' := fun t θ => angularMarkDerivative n t θ) (bound := fun _ => C) hn
    (by filter_upwards [hn] with t ht
        exact (angularMark_continuous (n+1) t (hrange t ht).1 (hrange t ht).2).aestronglyMeasurable.restrict)
    ((angularMark_continuous (n+1) r hr0.le hr1).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((angularMarkDerivative_continuous n r hr0.le hr1).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
        intro t ht
        exact hC (t,θ) ⟨⟨ht.1.le,ht.2.le⟩,⟨hθ.1.le,hθ.2⟩⟩)
    (integrable_const C)
    (by filter_upwards with θ
        intro t ht
        exact angularMark_hasDerivAt n t θ (hrange t ht).1 (hrange t ht).2)).2
  exact hd.const_mul (2*Real.pi)⁻¹

private theorem angularMark_recurrence (n : ℕ) (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    r*angularMarkDerivative n r θ =
      ((n+1 : ℕ) : ℝ)*((1-r^(2 : ℕ))*angularMark (n+2) r θ-angularMark (n+1) r θ)-
        ((1-r^(2 : ℕ))*angularPower (n+2) r θ-angularPower (n+1) r θ)/2 := by
  have hq := (angularQ_pos r θ hr0 hr1).ne'
  unfold angularMarkDerivative angularMark angularPower
  simp only [pow_succ]
  field_simp [hq, pow_ne_zero n hq]
  unfold angularQ
  ring

private theorem angularMarkMean_recurrence (n : ℕ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    r*deriv (angularMarkMean (n+1)) r =
      ((n+1 : ℕ) : ℝ)*((1-r^(2 : ℕ))*angularMarkMean (n+2) r-angularMarkMean (n+1) r)-
        ((1-r^(2 : ℕ))*angularMean (n+2) r-angularMean (n+1) r)/2 := by
  have h1 : IntegrableOn (angularPower (n+1) r) (Ioc 0 (2*Real.pi)) :=
    (angularPower_continuous (n+1) r hr0.le hr1).integrableOn_Icc.mono_set
      (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := 2*Real.pi))
  have h2 : IntegrableOn (angularPower (n+2) r) (Ioc 0 (2*Real.pi)) :=
    (angularPower_continuous (n+2) r hr0.le hr1).integrableOn_Icc.mono_set
      (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := 2*Real.pi))
  have hm1 : IntegrableOn (angularMark (n+1) r) (Ioc 0 (2*Real.pi)) :=
    (angularMark_continuous (n+1) r hr0.le hr1).integrableOn_Icc.mono_set
      (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := 2*Real.pi))
  have hm2 : IntegrableOn (angularMark (n+2) r) (Ioc 0 (2*Real.pi)) :=
    (angularMark_continuous (n+2) r hr0.le hr1).integrableOn_Icc.mono_set
      (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := 2*Real.pi))
  rw [(angularMarkMean_hasDerivAt n r hr0 hr1).deriv]
  have hi : (∫ θ : ℝ in Ioc 0 (2*Real.pi), r*angularMarkDerivative n r θ) =
      ∫ θ : ℝ in Ioc 0 (2*Real.pi),
        ((n+1 : ℕ) : ℝ)*((1-r^(2 : ℕ))*angularMark (n+2) r θ-angularMark (n+1) r θ)-
          ((1-r^(2 : ℕ))*angularPower (n+2) r θ-angularPower (n+1) r θ)/2 := by
    apply integral_congr_ae
    filter_upwards with θ
    exact angularMark_recurrence n r θ hr0.le hr1
  have hm := integral_sub (hm2.const_mul (1-r^(2 : ℕ))) hm1
  have hp := integral_sub (h2.const_mul (1-r^(2 : ℕ))) h1
  have hs := integral_sub (((hm2.const_mul (1-r^(2 : ℕ))).sub hm1).const_mul ((n+1 : ℕ) : ℝ))
    (((h2.const_mul (1-r^(2 : ℕ))).sub h1).div_const 2)
  simp only [Pi.sub_apply, integral_const_mul, integral_div] at hm hp hs
  rw [integral_const_mul, hs, hm, hp] at hi
  unfold angularMarkMean angularMean
  linear_combination (2*Real.pi)⁻¹*hi

private theorem higherMarkedAngular_eq_mean (n : ℕ) (r : ℝ) :
    fzzScreeningHigherMarkedAngular n r = angularMarkMean n r := by
  rw [fzzScreeningHigherMarkedAngular, Real.circleAverage_eq_circleAverage_zero_one,
    Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)]
  simp only [add_zero, angularMarkMean, angularMark, angularPower, pow_mul]
  simp_rw [← norm_circle_eq_angularQ, Real.log_pow]
  congr 2
  ext θ
  ring

private theorem marked_recurrence (n : ℕ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    r*deriv (fzzScreeningHigherMarkedAngular (n+1)) r =
      ((n+1 : ℕ) : ℝ)*((1-r^(2 : ℕ))*fzzScreeningHigherMarkedAngular (n+2) r-
        fzzScreeningHigherMarkedAngular (n+1) r)-
        ((1-r^(2 : ℕ))*fzzScreeningHigherAngular (n+2) r-fzzScreeningHigherAngular (n+1) r)/2 := by
  have he : fzzScreeningHigherMarkedAngular (n+1) = angularMarkMean (n+1) :=
    funext (higherMarkedAngular_eq_mean (n+1))
  rw [he, higherMarkedAngular_eq_mean, higherAngular_eq_mean, higherAngular_eq_mean]
  exact angularMarkMean_recurrence n r hr0 hr1

private theorem angularRadius_inverse (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    fzzScreeningAngularRadius (Real.log (r⁻¹-1)) = r := by
  have hp : 0 < r⁻¹-1 := by
    have h := (one_lt_inv₀ hr0).2 hr1
    linarith
  rw [fzzScreeningAngularRadius, Real.exp_log hp]
  ring_nf
  rw [inv_inv]

private theorem originalAngular_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    fzzScreeningHigherAngular 1 r = (1-r^(2 : ℕ))⁻¹ := by
  rw [fzzScreeningHigherAngular, Real.circleAverage_eq_circleAverage_zero_one]
  simpa only [add_zero, Nat.mul_one] using
    _root_.RHTower.circleAverage_inv_normSq_one_sub_mul hr0 hr1

private theorem originalAngular_two (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    fzzScreeningHigherAngular 2 r = (1+r^(2 : ℕ))/(1-r^(2 : ℕ))^(3 : ℕ) := by
  have h := fzzScreeningHigherAngular_two (Real.log (r⁻¹-1))
  rwa [angularRadius_inverse r hr0 hr1] at h

private theorem originalAngular_three (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    fzzScreeningHigherAngular 3 r = (1+4*r^(2 : ℕ)+r^(4 : ℕ))/(1-r^(2 : ℕ))^(5 : ℕ) := by
  have h := fzzScreeningHigherAngular_three (Real.log (r⁻¹-1))
  rwa [angularRadius_inverse r hr0 hr1] at h

private theorem markedDen_hasDerivAt (r : ℝ) :
    HasDerivAt (fun t : ℝ => 1-t^(2 : ℕ)) (-2*r) r := by
  convert! (hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).pow 2) using 1
  simp

private theorem marked_two (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    fzzScreeningHigherMarkedAngular 2 r = ((1+r^(2 : ℕ))*Real.log (1-r^(2 : ℕ))-r^(2 : ℕ))/(1-r^(2 : ℕ))^(3 : ℕ) := by
  have hn := (markedDen_pos r hr0.le hr1).ne'
  have hd : HasDerivAt (fun t : ℝ => Real.log (1-t^(2 : ℕ))/(1-t^(2 : ℕ)))
      (2*r*(Real.log (1-r^(2 : ℕ))-1)/(1-r^(2 : ℕ))^(2 : ℕ)) r := by
    convert! ((markedDen_hasDerivAt r).log hn).div (markedDen_hasDerivAt r) hn using 1
    field_simp [hn]
    ring
  have he : fzzScreeningHigherMarkedAngular 1 =ᶠ[𝓝 r]
      (fun t : ℝ => Real.log (1-t^(2 : ℕ))/(1-t^(2 : ℕ))) := by
    filter_upwards [Ioo_mem_nhds hr0 hr1] with t ht
    exact marked_one t ht.1.le ht.2
  have h := marked_recurrence 0 r hr0 hr1
  rw [(hd.congr_of_eventuallyEq he).deriv, marked_one r hr0.le hr1,
    originalAngular_one r hr0.le hr1, originalAngular_two r hr0 hr1] at h
  simp only [Nat.zero_add, Nat.cast_one, one_mul] at h
  field_simp [hn] at h ⊢
  nlinarith [h]

private theorem marked_three (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    fzzScreeningHigherMarkedAngular 3 r =
      ((1+4*r^(2 : ℕ)+r^(4 : ℕ))*Real.log (1-r^(2 : ℕ))-2*r^(2 : ℕ)-3*r^(4 : ℕ)/2)/(1-r^(2 : ℕ))^(5 : ℕ) := by
  have hn := (markedDen_pos r hr0.le hr1).ne'
  have hnum : HasDerivAt (fun t : ℝ => (1+t^(2 : ℕ))*Real.log (1-t^(2 : ℕ))-t^(2 : ℕ))
      (2*r*(Real.log (1-r^(2 : ℕ))-2/(1-r^(2 : ℕ)))) r := by
    have h := (((hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow 2)).mul
      ((markedDen_hasDerivAt r).log hn)).sub ((hasDerivAt_id r).pow 2)
    convert! h using 1
    dsimp
    field_simp [hn]
    ring
  have hd : HasDerivAt (fun t : ℝ => ((1+t^(2 : ℕ))*Real.log (1-t^(2 : ℕ))-t^(2 : ℕ))/(1-t^(2 : ℕ))^(3 : ℕ))
      (2*r*((4+2*r^(2 : ℕ))*Real.log (1-r^(2 : ℕ))-2-3*r^(2 : ℕ))/(1-r^(2 : ℕ))^(4 : ℕ)) r := by
    convert! hnum.div ((markedDen_hasDerivAt r).pow 3) (pow_ne_zero _ hn) using 1
    dsimp
    field_simp [hn]
    ring
  have he : fzzScreeningHigherMarkedAngular 2 =ᶠ[𝓝 r]
      (fun t : ℝ => ((1+t^(2 : ℕ))*Real.log (1-t^(2 : ℕ))-t^(2 : ℕ))/(1-t^(2 : ℕ))^(3 : ℕ)) := by
    filter_upwards [Ioo_mem_nhds hr0 hr1] with t ht
    exact marked_two t ht.1 ht.2
  have h := marked_recurrence 1 r hr0 hr1
  rw [(hd.congr_of_eventuallyEq he).deriv, marked_two r hr0 hr1,
    originalAngular_two r hr0 hr1, originalAngular_three r hr0 hr1] at h
  simp only [Nat.reduceAdd, Nat.cast_ofNat] at h
  field_simp [hn] at h ⊢
  nlinarith [h]

/-- The Poisson identity evaluates the original inverse-square logarithmic insertion. -/
theorem fzzScreeningHigherMarkedAngular_one (u : ℝ) :
    fzzScreeningHigherMarkedAngular 1 (fzzScreeningAngularRadius u) =
      Real.log (1-fzzScreeningAngularRadius u^(2 : ℕ))/(1-fzzScreeningAngularRadius u^(2 : ℕ)) :=
  marked_one _ (angularRadius_range u).1.le (angularRadius_range u).2

/-- Differentiation retains the unmarked term produced by the logarithmic insertion. -/
theorem fzzScreeningHigherMarkedAngular_recurrence (n : ℕ) (u : ℝ) :
    fzzScreeningAngularRadius u *
        deriv (fzzScreeningHigherMarkedAngular (n+1)) (fzzScreeningAngularRadius u) =
      ((n+1 : ℕ) : ℝ)*((1-fzzScreeningAngularRadius u^(2 : ℕ))*
        fzzScreeningHigherMarkedAngular (n+2) (fzzScreeningAngularRadius u)-
        fzzScreeningHigherMarkedAngular (n+1) (fzzScreeningAngularRadius u))-
      ((1-fzzScreeningAngularRadius u^(2 : ℕ))*
        fzzScreeningHigherAngular (n+2) (fzzScreeningAngularRadius u)-
        fzzScreeningHigherAngular (n+1) (fzzScreeningAngularRadius u))/2 :=
  marked_recurrence n _ (angularRadius_range u).1 (angularRadius_range u).2

/-- The original inverse fourth-power logarithmic insertion. -/
theorem fzzScreeningHigherMarkedAngular_two (u : ℝ) :
    fzzScreeningHigherMarkedAngular 2 (fzzScreeningAngularRadius u) =
      ((1+fzzScreeningAngularRadius u^(2 : ℕ))*Real.log (1-fzzScreeningAngularRadius u^(2 : ℕ))-
        fzzScreeningAngularRadius u^(2 : ℕ))/(1-fzzScreeningAngularRadius u^(2 : ℕ))^(3 : ℕ) :=
  marked_two _ (angularRadius_range u).1 (angularRadius_range u).2

/-- The original inverse sixth-power logarithmic insertion at the receiver collision. -/
theorem fzzScreeningHigherMarkedAngular_three (u : ℝ) :
    fzzScreeningHigherMarkedAngular 3 (fzzScreeningAngularRadius u) =
      ((1+4*fzzScreeningAngularRadius u^(2 : ℕ)+fzzScreeningAngularRadius u^(4 : ℕ))*
        Real.log (1-fzzScreeningAngularRadius u^(2 : ℕ))-2*fzzScreeningAngularRadius u^(2 : ℕ)-
        3*fzzScreeningAngularRadius u^(4 : ℕ)/2)/(1-fzzScreeningAngularRadius u^(2 : ℕ))^(5 : ℕ) :=
  marked_three _ (angularRadius_range u).1 (angularRadius_range u).2


/-- Radial source after subtracting both divergent marked angular coefficients. -/
def fzzScreeningCubicMarkedRadialRemainder (r : ℝ) : ℝ :=
  (r^(5 : ℕ))⁻¹*(fzzScreeningHigherMarkedAngular 3 r+3*r^(2 : ℕ)+21*r^(4 : ℕ))

/-- Singular radial primitive for the regular-factor logarithmic insertion. -/
def fzzScreeningCubicMarkedCollisionPrimitive (r : ℝ) : ℝ :=
  3*(r^(2 : ℕ))⁻¹/2-21*Real.log r

private def markedRemainderPoly (r : ℝ) : ℝ :=
  -78+359*r^(2 : ℕ)/2-195*r^(4 : ℕ)+102*r^(6 : ℕ)-21*r^(8 : ℕ)

private def markedRemainderBound (r : ℝ) : ℝ :=
  r*(1+4*r^(2 : ℕ)+r^(4 : ℕ))/(1-r^(2 : ℕ))^(6 : ℕ)+‖r*markedRemainderPoly r/(1-r^(2 : ℕ))^(5 : ℕ)‖

private theorem marked_remainder_eq (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    fzzScreeningCubicMarkedRadialRemainder r =
      ((1+4*r^(2 : ℕ)+r^(4 : ℕ))/((r^(5 : ℕ))*(1-r^(2 : ℕ))^(5 : ℕ)))*(Real.log (1-r^(2 : ℕ))+r^(2 : ℕ)+r^(4 : ℕ)/2)+
        r*markedRemainderPoly r/(1-r^(2 : ℕ))^(5 : ℕ) := by
  rw [fzzScreeningCubicMarkedRadialRemainder, marked_three r hr0 hr1]
  unfold markedRemainderPoly
  field_simp [hr0.ne', (markedDen_pos r hr0.le hr1).ne']
  ring

private theorem marked_remainder_bound (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ‖fzzScreeningCubicMarkedRadialRemainder r‖ ≤ markedRemainderBound r := by
  have hd := markedDen_pos r hr0.le hr1
  have hlog := Real.abs_log_sub_add_sum_range_le
    (x := r^(2 : ℕ)) (by rw [abs_of_nonneg (sq_nonneg r)]; nlinarith [hd]) 2
  have hb : ‖Real.log (1-r^(2 : ℕ))+r^(2 : ℕ)+r^(4 : ℕ)/2‖ ≤ r^(6 : ℕ)/(1-r^(2 : ℕ)) := by
    norm_num [Finset.sum_range_succ, abs_of_nonneg (sq_nonneg r), Real.norm_eq_abs] at hlog ⊢
    convert! hlog using 1 <;> congr 1 <;> ring
  let a := (1+4*r^(2 : ℕ)+r^(4 : ℕ))/((r^(5 : ℕ))*(1-r^(2 : ℕ))^(5 : ℕ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : a*(r^(6 : ℕ)/(1-r^(2 : ℕ))) = r*(1+4*r^(2 : ℕ)+r^(4 : ℕ))/(1-r^(2 : ℕ))^(6 : ℕ) := by
    dsimp [a]
    field_simp [hr0.ne', hd.ne']
  rw [marked_remainder_eq r hr0 hr1]
  calc
    ‖a*(Real.log (1-r^(2 : ℕ))+r^(2 : ℕ)+r^(4 : ℕ)/2)+r*markedRemainderPoly r/(1-r^(2 : ℕ))^(5 : ℕ)‖
      ≤ ‖a*(Real.log (1-r^(2 : ℕ))+r^(2 : ℕ)+r^(4 : ℕ)/2)‖+‖r*markedRemainderPoly r/(1-r^(2 : ℕ))^(5 : ℕ)‖ :=
        norm_add_le _ _
    _ = a*‖Real.log (1-r^(2 : ℕ))+r^(2 : ℕ)+r^(4 : ℕ)/2‖+‖r*markedRemainderPoly r/(1-r^(2 : ℕ))^(5 : ℕ)‖ := by
      rw [norm_mul, Real.norm_eq_abs a, abs_of_nonneg ha]
    _ ≤ a*(r^(6 : ℕ)/(1-r^(2 : ℕ)))+‖r*markedRemainderPoly r/(1-r^(2 : ℕ))^(5 : ℕ)‖ := by gcongr
    _ = markedRemainderBound r := by rw [he]; rfl

private theorem marked_remainder_continuousOn :
    ContinuousOn fzzScreeningCubicMarkedRadialRemainder (Ioc 0 (1/2 : ℝ)) := by
  have hden : ∀ r ∈ Ioc 0 (1/2 : ℝ), 1-r^(2 : ℕ) ≠ 0 := fun r hr =>
    (markedDen_pos r hr.1.le (by linarith [hr.2])).ne'
  have hlog : ContinuousOn (fun r : ℝ => Real.log (1-r^(2 : ℕ))) (Ioc 0 (1/2 : ℝ)) :=
    (show ContinuousOn (fun r : ℝ => 1-r^(2 : ℕ)) (Ioc 0 (1/2 : ℝ)) by fun_prop).log hden
  have hc : ContinuousOn (fun r : ℝ =>
      ((1+4*r^(2 : ℕ)+r^(4 : ℕ))/((r^(5 : ℕ))*(1-r^(2 : ℕ))^(5 : ℕ)))*(Real.log (1-r^(2 : ℕ))+r^(2 : ℕ)+r^(4 : ℕ)/2)+
        r*markedRemainderPoly r/(1-r^(2 : ℕ))^(5 : ℕ)) (Ioc 0 (1/2 : ℝ)) := by
    have hd : ContinuousOn (fun r : ℝ => 1-r^(2 : ℕ)) (Ioc 0 (1/2 : ℝ)) := by fun_prop
    have hrnz : ∀ r ∈ Ioc 0 (1/2 : ℝ), r ≠ 0 := fun r hr => hr.1.ne'
    apply ContinuousOn.add
    · apply ContinuousOn.mul
      · exact (show ContinuousOn (fun r : ℝ => 1+4*r^(2 : ℕ)+r^(4 : ℕ)) (Ioc 0 (1/2 : ℝ)) by fun_prop).div
          ((continuous_id.continuousOn.pow 5).mul (hd.pow 5))
          (fun r hr => mul_ne_zero (pow_ne_zero _ (hrnz r hr)) (pow_ne_zero _ (hden r hr)))
      · exact (hlog.add (continuous_id.continuousOn.pow 2)).add
          ((continuous_id.continuousOn.pow 4).div_const 2)
    · exact (show ContinuousOn (fun r : ℝ => r*markedRemainderPoly r) (Ioc 0 (1/2 : ℝ)) by
        unfold markedRemainderPoly; fun_prop).div (hd.pow 5)
          (fun r hr => pow_ne_zero _ (hden r hr))
  apply hc.congr
  intro r hr
  exact marked_remainder_eq r hr.1 (by linarith [hr.2])

/-- The derived marked coefficients leave an integrable original radial source. -/
theorem fzzScreeningHigherMarkedAngular_three_subtracted_integrable :
    IntegrableOn fzzScreeningCubicMarkedRadialRemainder (Ioc 0 (1/2 : ℝ)) := by
  have hden : ∀ r ∈ Icc 0 (1/2 : ℝ), 1-r^(2 : ℕ) ≠ 0 := fun r hr =>
    (markedDen_pos r hr.1 (by linarith [hr.2])).ne'
  have hc : ContinuousOn markedRemainderBound (Icc 0 (1/2 : ℝ)) := by
    have hd : ContinuousOn (fun r : ℝ => 1-r^(2 : ℕ)) (Icc 0 (1/2 : ℝ)) := by fun_prop
    unfold markedRemainderBound
    exact ((show ContinuousOn (fun r : ℝ => r*(1+4*r^(2 : ℕ)+r^(4 : ℕ))) (Icc 0 (1/2 : ℝ)) by
      fun_prop).div (hd.pow 6) (fun r hr => pow_ne_zero _ (hden r hr))).add
      (((show ContinuousOn (fun r : ℝ => r*markedRemainderPoly r) (Icc 0 (1/2 : ℝ)) by
        unfold markedRemainderPoly; fun_prop).div (hd.pow 5)
          (fun r hr => pow_ne_zero _ (hden r hr))).norm)
  have hi : IntegrableOn markedRemainderBound (Ioc 0 (1/2 : ℝ)) :=
    (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  apply hi.mono' (marked_remainder_continuousOn.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact marked_remainder_bound r hr.1 (by linarith [hr.2])

private theorem markedPrimitive_hasDerivAt (r : ℝ) (hr : 0 < r) :
    HasDerivAt fzzScreeningCubicMarkedCollisionPrimitive
      (-3*(r^(3 : ℕ))⁻¹-21*r⁻¹) r := by
  have h2 := ((hasDerivAt_id r).pow 2).inv (pow_ne_zero _ hr.ne')
  have h := ((h2.const_mul 3).div_const 2).sub ((Real.hasDerivAt_log hr.ne').const_mul 21)
  convert! h using 1
  dsimp
  field_simp [hr.ne']

private theorem marked_angular_cutoff_identity (ε : ℝ) (hε : 0 < ε) (hεR : ε ≤ 1/2) :
    (∫ r : ℝ in ε..(1/2), (r^(5 : ℕ))⁻¹*fzzScreeningHigherMarkedAngular 3 r)+
        fzzScreeningCubicMarkedCollisionPrimitive ε =
      (∫ r : ℝ in ε..(1/2), fzzScreeningCubicMarkedRadialRemainder r)+
        fzzScreeningCubicMarkedCollisionPrimitive (1/2) := by
  have hp : ContinuousOn (fun r : ℝ => -3*(r^(3 : ℕ))⁻¹-21*r⁻¹) (Icc ε (1/2)) := by
    exact (continuousOn_const.mul ((continuous_id.continuousOn.pow 3).inv₀
      (fun r hr => pow_ne_zero _ (hε.trans_le hr.1).ne'))).sub
      (continuousOn_const.mul (continuous_id.continuousOn.inv₀
        (fun r hr => (hε.trans_le hr.1).ne')))
  have hrem := marked_remainder_continuousOn.mono
    (show Icc ε (1/2) ⊆ Ioc 0 (1/2) from fun r hr => ⟨hε.trans_le hr.1,hr.2⟩)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => markedPrimitive_hasDerivAt r (by
      rw [uIcc_of_le hεR] at hr
      exact hε.trans_le hr.1)) (hp.intervalIntegrable_of_Icc hεR)
  have he : (∫ r : ℝ in ε..(1/2), (r^(5 : ℕ))⁻¹*fzzScreeningHigherMarkedAngular 3 r) =
      ∫ r : ℝ in ε..(1/2), -3*(r^(3 : ℕ))⁻¹-21*r⁻¹+
        fzzScreeningCubicMarkedRadialRemainder r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hεR] at hr
    have hr0 := hε.trans_le hr.1
    dsimp only
    unfold fzzScreeningCubicMarkedRadialRemainder
    field_simp [hr0.ne']
    ring
  rw [he, intervalIntegral.integral_add (hp.intervalIntegrable_of_Icc hεR)
    (hrem.intervalIntegrable_of_Icc hεR), hi]
  ring
private theorem marked_remainder_cutoff_limit :
    Tendsto (fun T : ℝ => ∫ r : ℝ in (Real.exp (-T))..(1/2),
      fzzScreeningCubicMarkedRadialRemainder r) atTop
      (𝓝 (∫ r : ℝ in (0 : ℝ)..(1/2), fzzScreeningCubicMarkedRadialRemainder r)) := by
  let f := fun r : ℝ => fzzScreeningCubicMarkedRadialRemainder r
  have hi : IntegrableOn f (Ioc 0 (1/2)) :=
    fzzScreeningHigherMarkedAngular_three_subtracted_integrable
  have hd := tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (μ := volume.restrict (Ioc (0 : ℝ) (1/2)))
    (F := fun T : ℝ => (Ioi (Real.exp (-T))).indicator f) (f := f) (fun r => ‖f r‖)
    (Eventually.of_forall (fun T => hi.aestronglyMeasurable.indicator measurableSet_Ioi))
    (Eventually.of_forall (fun T => Eventually.of_forall (fun r => by
      by_cases hr : r ∈ Ioi (Real.exp (-T))
      · simp [indicator_of_mem hr]
      · simp [indicator_of_notMem hr]))) hi.norm (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        apply tendsto_const_nhds.congr'
        filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually
          (gt_mem_nhds hr.1)] with T hT
        exact (indicator_of_mem hT f).symm)
  have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) ≤ (1/2 : ℝ) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1/2))).mono (fun T hT => hT.le)
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1/2)]
  apply hd.congr'
  filter_upwards [he] with T hT
  rw [setIntegral_indicator measurableSet_Ioi, intervalIntegral.integral_of_le hT]
  have hs : Ioc (0 : ℝ) (1/2) ∩ Ioi (Real.exp (-T)) = Ioc (Real.exp (-T)) (1/2) := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨⟨_,hr⟩,hTr⟩
      exact ⟨hTr,hr⟩
    · rintro ⟨hTr,hr⟩
      exact ⟨⟨(Real.exp_pos _).trans hTr,hr⟩,hTr⟩
  rw [hs]

/-- The original logarithmic angular insertion forces its power and logarithmic correction. -/
theorem fzzScreeningHigherMarkedAngular_three_cutoff_limit :
    Tendsto (fun T : ℝ => 2*Real.pi*
      ((∫ r : ℝ in (Real.exp (-T))..(1/2), (r^(5 : ℕ))⁻¹*fzzScreeningHigherMarkedAngular 3 r)+
        fzzScreeningCubicMarkedCollisionPrimitive (Real.exp (-T)))) atTop
      (𝓝 (2*Real.pi*((∫ r : ℝ in (0 : ℝ)..(1/2),
        fzzScreeningCubicMarkedRadialRemainder r)+fzzScreeningCubicMarkedCollisionPrimitive (1/2)))) := by
  have hd := (marked_remainder_cutoff_limit.add_const
    (fzzScreeningCubicMarkedCollisionPrimitive (1/2))).const_mul (2*Real.pi)
  apply hd.congr'
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1/2))] with T hT
  rw [marked_angular_cutoff_identity _ (Real.exp_pos _) hT.le]


/-- Singular-factor mark: every original angular divergence is multiplied by `log r`. -/
def fzzScreeningCubicSingularMarkedCollisionPrimitive (r : ℝ) : ℝ :=
  -(r^(4 : ℕ))⁻¹*(Real.log r/4+1/16)-9*(r^(2 : ℕ))⁻¹*(Real.log r/2+1/4)+18*(Real.log r)^(2 : ℕ)

private theorem singularMarked_remainder (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (r^(5 : ℕ))⁻¹*Real.log r*(fzzScreeningHigherAngular 3 r-1-9*r^(2 : ℕ)-36*r^(4 : ℕ)) =
      (r*Real.log r)*fzzScreeningCubicAngularRemainder r := by
  rw [originalAngular_three r hr0 hr1]
  unfold fzzScreeningCubicAngularRemainder
  field_simp [hr0.ne', (markedDen_pos r hr0.le hr1).ne']
  ring

private theorem singularMarked_continuousOn :
    ContinuousOn (fun r : ℝ => (r*Real.log r)*fzzScreeningCubicAngularRemainder r)
      (Icc 0 (1/2 : ℝ)) := by
  have hden : ∀ r ∈ Icc 0 (1/2 : ℝ), 1-r^(2 : ℕ) ≠ 0 := fun r hr =>
    (markedDen_pos r hr.1 (by linarith [hr.2])).ne'
  apply Real.continuous_mul_log.continuousOn.mul
  unfold fzzScreeningCubicAngularRemainder
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro r hr
    exact pow_ne_zero _ (hden r hr)

/-- The singular-factor logarithmic insertion has an admitted original subtracted radial source. -/
theorem fzzScreeningHigherAngular_three_log_subtracted_integrable :
    IntegrableOn (fun r : ℝ => (r^(5 : ℕ))⁻¹*Real.log r*
      (fzzScreeningHigherAngular 3 r-1-9*r^(2 : ℕ)-36*r^(4 : ℕ))) (Ioc 0 (1/2 : ℝ)) := by
  have hi : IntegrableOn (fun r : ℝ => (r*Real.log r)*fzzScreeningCubicAngularRemainder r)
      (Ioc 0 (1/2 : ℝ)) :=
    (singularMarked_continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact (singularMarked_remainder r hr.1 (by linarith [hr.2])).symm

private theorem singularMarkedPrimitive_hasDerivAt (r : ℝ) (hr : 0 < r) :
    HasDerivAt fzzScreeningCubicSingularMarkedCollisionPrimitive
      ((r^(5 : ℕ))⁻¹*Real.log r+9*(r^(3 : ℕ))⁻¹*Real.log r+36*r⁻¹*Real.log r) r := by
  have h4 := ((hasDerivAt_id r).pow 4).inv (pow_ne_zero _ hr.ne')
  have h2 := ((hasDerivAt_id r).pow 2).inv (pow_ne_zero _ hr.ne')
  have hl := Real.hasDerivAt_log hr.ne'
  have h := ((h4.neg.mul ((hl.div_const 4).add_const (1/16))).sub
    ((h2.const_mul 9).mul ((hl.div_const 2).add_const (1/4)))).add ((hl.pow 2).const_mul 18)
  convert! h using 1
  dsimp
  field_simp [hr.ne']
  ring

private theorem singularMarked_angular_cutoff_identity (ε : ℝ) (hε : 0 < ε) (hεR : ε ≤ 1/2) :
    (∫ r : ℝ in ε..(1/2), (r^(5 : ℕ))⁻¹*Real.log r*fzzScreeningHigherAngular 3 r)+
        fzzScreeningCubicSingularMarkedCollisionPrimitive ε =
      (∫ r : ℝ in ε..(1/2), (r*Real.log r)*fzzScreeningCubicAngularRemainder r)+
        fzzScreeningCubicSingularMarkedCollisionPrimitive (1/2) := by
  have hrnz : ∀ r ∈ Icc ε (1/2), r ≠ 0 := fun r hr => (hε.trans_le hr.1).ne'
  have hp : ContinuousOn (fun r : ℝ => (r^(5 : ℕ))⁻¹*Real.log r+9*(r^(3 : ℕ))⁻¹*Real.log r+
      36*r⁻¹*Real.log r) (Icc ε (1/2)) := by
    have hpow (n : ℕ) : ContinuousOn (fun r : ℝ => (r^n)⁻¹) (Icc ε (1/2)) :=
      (continuous_id.continuousOn.pow n).inv₀ (fun r hr => pow_ne_zero _ (hrnz r hr))
    have hl := continuous_id.continuousOn.log hrnz
    exact (((hpow 5).mul hl).add (((hpow 3).const_mul 9).mul hl)).add
      (((continuous_id.continuousOn.inv₀ hrnz).const_mul 36).mul hl)
  have hrem := singularMarked_continuousOn.mono
    (show Icc ε (1/2) ⊆ Icc 0 (1/2) from fun r hr => ⟨hε.le.trans hr.1,hr.2⟩)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => singularMarkedPrimitive_hasDerivAt r (by
      rw [uIcc_of_le hεR] at hr
      exact hε.trans_le hr.1)) (hp.intervalIntegrable_of_Icc hεR)
  have he : (∫ r : ℝ in ε..(1/2), (r^(5 : ℕ))⁻¹*Real.log r*fzzScreeningHigherAngular 3 r) =
      ∫ r : ℝ in ε..(1/2), (r^(5 : ℕ))⁻¹*Real.log r+9*(r^(3 : ℕ))⁻¹*Real.log r+
        36*r⁻¹*Real.log r+(r*Real.log r)*fzzScreeningCubicAngularRemainder r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hεR] at hr
    have hr0 := hε.trans_le hr.1
    dsimp only
    rw [← singularMarked_remainder r hr0 (by linarith [hr.2])]
    field_simp [hr0.ne']
    ring
  rw [he, intervalIntegral.integral_add (hp.intervalIntegrable_of_Icc hεR)
    (hrem.intervalIntegrable_of_Icc hεR), hi]
  ring
private theorem singularMarked_remainder_cutoff_limit :
    Tendsto (fun T : ℝ => ∫ r : ℝ in (Real.exp (-T))..(1/2),
      (r*Real.log r)*fzzScreeningCubicAngularRemainder r) atTop
      (𝓝 (∫ r : ℝ in (0 : ℝ)..(1/2), (r*Real.log r)*fzzScreeningCubicAngularRemainder r)) := by
  let f := fun r : ℝ => (r*Real.log r)*fzzScreeningCubicAngularRemainder r
  have hi : IntegrableOn f (Ioc 0 (1/2)) :=
    (singularMarked_continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hd := tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (μ := volume.restrict (Ioc (0 : ℝ) (1/2)))
    (F := fun T : ℝ => (Ioi (Real.exp (-T))).indicator f) (f := f) (fun r => ‖f r‖)
    (Eventually.of_forall (fun T => hi.aestronglyMeasurable.indicator measurableSet_Ioi))
    (Eventually.of_forall (fun T => Eventually.of_forall (fun r => by
      by_cases hr : r ∈ Ioi (Real.exp (-T))
      · simp [indicator_of_mem hr]
      · simp [indicator_of_notMem hr]))) hi.norm (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        apply tendsto_const_nhds.congr'
        filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually
          (gt_mem_nhds hr.1)] with T hT
        exact (indicator_of_mem hT f).symm)
  have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) ≤ (1/2 : ℝ) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1/2))).mono (fun T hT => hT.le)
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1/2)]
  apply hd.congr'
  filter_upwards [he] with T hT
  rw [setIntegral_indicator measurableSet_Ioi, intervalIntegral.integral_of_le hT]
  have hs : Ioc (0 : ℝ) (1/2) ∩ Ioi (Real.exp (-T)) = Ioc (Real.exp (-T)) (1/2) := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨⟨_,hr⟩,hTr⟩
      exact ⟨hTr,hr⟩
    · rintro ⟨hTr,hr⟩
      exact ⟨⟨(Real.exp_pos _).trans hTr,hr⟩,hTr⟩
  rw [hs]

/-- The singular-factor logarithmic insertion retains both power-log terms and the squared logarithm. -/
theorem fzzScreeningHigherAngular_three_log_cutoff_limit :
    Tendsto (fun T : ℝ => 2*Real.pi*
      ((∫ r : ℝ in (Real.exp (-T))..(1/2), (r^(5 : ℕ))⁻¹*Real.log r*fzzScreeningHigherAngular 3 r)+
        fzzScreeningCubicSingularMarkedCollisionPrimitive (Real.exp (-T)))) atTop
      (𝓝 (2*Real.pi*((∫ r : ℝ in (0 : ℝ)..(1/2),
        (r*Real.log r)*fzzScreeningCubicAngularRemainder r)+fzzScreeningCubicSingularMarkedCollisionPrimitive (1/2)))) := by
  have hd := (singularMarked_remainder_cutoff_limit.add_const
    (fzzScreeningCubicSingularMarkedCollisionPrimitive (1/2))).const_mul (2*Real.pi)
  apply hd.congr'
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1/2))] with T hT
  rw [singularMarked_angular_cutoff_identity _ (Real.exp_pos _) hT.le]

end GaloisForLFunctions.RHTower
