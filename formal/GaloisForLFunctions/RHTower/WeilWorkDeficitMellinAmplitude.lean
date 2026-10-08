import GaloisForLFunctions.RHTower.WeilWorkDeficitProductKernelMellin
import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness

/-!
# Uniform bulk amplitude of the actual product-kernel Mellin transform

Gamma reflection gives an exact norm on `Re(s) = 4`. An elementary Laplace
inequality then bounds every derivative order by one Gaussian envelope in
its saddle bulk. Global tails and differentiated amplitudes remain separate
obligations; this module makes no spectral-deficit assertion.
-/

noncomputable section
open MeasureTheory Set Complex
open scoped Real
namespace RHTower.WeilWorkDeficitAmplitude

private def mellinFactor (k : ℕ) (s : ℂ) : ℂ :=
  (-1:ℂ)^k * (s-1/2)^(2*k) * s^2 * (s-1)^2 *
    (Real.pi:ℂ)^(-s) * (Complex.Gamma (s/2))^2 / 4

/-- Saddle of the sigma-four Mellin amplitude. -/
def saddleHeight (k : ℕ) : ℝ := (2*(k:ℝ)+7)/(Real.pi/2)
/-- Value of the leading Laplace amplitude at its saddle. -/
def saddleMass (k : ℕ) : ℝ :=
  (saddleHeight k)^(2*k+7)*Real.exp (-(Real.pi/2)*saddleHeight k)

private theorem gamma_two_norm {y : ℝ} (hy : y ≠ 0) :
    ‖Complex.Gamma (2+(y:ℂ)*I)‖^2 =
      (1+y^2)*(Real.pi*y/Real.sinh (Real.pi*y)) := by
  have hz : (1+(y:ℂ)*I) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simp
  rw [show (2:ℂ)+(y:ℂ)*I=(1+(y:ℂ)*I)+1 by ring,
    Complex.Gamma_add_one _ hz, norm_mul, mul_pow, norm_Gamma_one_add_mul_I_sq hy]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [pow_two]

private theorem norm_factor (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖mellinFactor k (4+(t:ℂ)*I)‖ =
      (t^2+49/4)^k * t*(t^2+4)*(t^2+9)*(t^2+16) /
        (32*Real.pi^3*Real.sinh (Real.pi/2*t)) := by
  have hg : (4+(t:ℂ)*I)/2 = 2+((t/2:ℝ):ℂ)*I := by push_cast; ring
  have h1 : ‖(4:ℂ)+(t:ℂ)*I‖^2 = t^2+16 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have h2 : ‖(4:ℂ)+(t:ℂ)*I-1‖^2 = t^2+9 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have h3 : ‖(4:ℂ)+(t:ℂ)*I-1/2‖^(2*k) = (t^2+49/4)^k := by
    rw [pow_mul]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hpi : ‖(Real.pi:ℂ)^(-((4:ℂ)+(t:ℂ)*I))‖ = (Real.pi^4)⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp only [Complex.neg_re, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero]
    norm_num
    exact zpow_ofNat Real.pi 4
  simp only [mellinFactor, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_ofNat]
  rw [h3,h1,h2,hpi,hg,gamma_two_norm (by linarith : t/2 ≠ 0)]
  rw [show Real.pi*(t/2)=Real.pi/2*t by ring]
  field_simp
  ring

private theorem height_identity (k : ℕ) :
    (Real.pi/2)*saddleHeight k = 2*(k:ℝ)+7 := by
  unfold saddleHeight
  field_simp

private theorem height_two (k : ℕ) : 2 ≤ saddleHeight k := by
  unfold saddleHeight
  rw [le_div_iff₀ (by positivity : (0:ℝ)<Real.pi/2)]
  nlinarith [Real.pi_lt_four, (Nat.cast_nonneg k : (0:ℝ)≤k)]

private theorem log_curve {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    Real.log r ≤ r-1-(r-1)^2/9 := by
  have hq0 := Real.sqrt_nonneg r
  have hq := Real.sq_sqrt hr.le
  have hq2 : Real.sqrt r ≤ 2 := by nlinarith
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hr)
  rw [Real.log_sqrt hr.le] at hlog
  have hp : (r-1)^2 ≤ 9*(Real.sqrt r-1)^2 := by
    calc (r-1)^2 = (Real.sqrt r-1)^2*(Real.sqrt r+1)^2 := by nlinarith [sq_nonneg (Real.sqrt r)]
         _ ≤ (Real.sqrt r-1)^2*9 :=
           mul_le_mul_of_nonneg_left (by nlinarith : (Real.sqrt r+1)^2 ≤ 9) (sq_nonneg _)
         _ = _ := by ring
  nlinarith

private theorem laplace_gaussian (k : ℕ) {t : ℝ}
    (ht : saddleHeight k/2 ≤ t) (ht2 : t ≤ 2*saddleHeight k) :
    t^(2*k+7)*Real.exp (-(Real.pi/2)*t) ≤
      saddleMass k * Real.exp (-(Real.pi/2)*(t-saddleHeight k)^2/(9*saddleHeight k)) := by
  have hT : 0 < saddleHeight k := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (height_two k)
  have ht0 : 0 < t := by linarith
  have hr : 0 < t/saddleHeight k := div_pos ht0 hT
  have hr2 : t/saddleHeight k ≤ 2 := (div_le_iff₀ hT).2 (by linarith)
  have hlog := mul_le_mul_of_nonneg_left (log_curve hr hr2)
    (show 0 ≤ (Real.pi/2)*saddleHeight k by positivity)
  have hN : ((2*k+7:ℕ):ℝ) = (Real.pi/2)*saddleHeight k := by
    rw [height_identity]
    push_cast
    ring
  have he : ((2*k+7:ℕ):ℝ)*Real.log (t/saddleHeight k) - (Real.pi/2)*(t-saddleHeight k) ≤
      -(Real.pi/2)*(t-saddleHeight k)^2/(9*saddleHeight k) := by
    rw [hN]
    calc _ ≤ (Real.pi/2)*saddleHeight k *
        (t/saddleHeight k-1-(t/saddleHeight k-1)^2/9) - (Real.pi/2)*(t-saddleHeight k) :=
          sub_le_sub_right hlog _
         _ = _ := by field_simp; ring
  have hfactor : t^(2*k+7)*Real.exp (-(Real.pi/2)*t) = saddleMass k *
      Real.exp (((2*k+7:ℕ):ℝ)*Real.log (t/saddleHeight k) - (Real.pi/2)*(t-saddleHeight k)) := by
    have hp (u : ℝ) (hu : 0 < u) : u^(2*k+7) =
        Real.exp (((2*k+7:ℕ):ℝ)*Real.log u) := by
      rw [Real.exp_nat_mul, Real.exp_log hu]
    simp only [saddleMass, hp t ht0, hp (saddleHeight k) hT]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      Real.log_div ht0.ne' hT.ne']
    congr 1
    ring
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 he) (by unfold saddleMass; positivity)

private theorem reciprocal_sinh {u : ℝ} (hu : 1 ≤ u) :
    1/Real.sinh u ≤ 4*Real.exp (-u) := by
  have he := Real.add_one_le_exp (2*u)
  have hi : Real.exp (-2*u) ≤ 1/2 := by
    rw [show -2*u=-(2*u) by ring, Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    linarith
  have hp : Real.exp (-u) = Real.exp u * Real.exp (-2*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : Real.exp u/4 ≤ Real.sinh u := by
    rw [Real.sinh_eq,hp]
    nlinarith [mul_le_mul_of_nonneg_left hi (Real.exp_pos u).le]
  have hs0 : 0 < Real.sinh u := Real.sinh_pos_iff.2 (by linarith)
  rw [div_le_iff₀ hs0]
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-u)).le
  have heq : Real.exp u*Real.exp (-u)=1 := by rw [← Real.exp_add]; simp
  nlinarith

private theorem power_correction (k : ℕ) {t : ℝ} (ht : saddleHeight k/2 ≤ t) :
    (t^2+49/4)^k ≤ t^(2*k)*Real.exp (49*Real.pi/4) := by
  have ht1 : 1 ≤ t := by linarith [height_two k]
  have ht0 : 0 < t := by linarith
  have hk : (k:ℝ) ≤ Real.pi*t^2 := by
    have hT : saddleHeight k ≤ 2*t^2 := by nlinarith
    have hh := height_identity k
    have hp := mul_le_mul_of_nonneg_left hT (Real.pi_pos.le)
    nlinarith [Real.pi_pos]
  have hexp : (k:ℝ)*(49/4/t^2) ≤ 49*Real.pi/4 := by
    rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos ht0)]
    nlinarith
  have hbase : (1+49/4/t^2)^k ≤ Real.exp (49/4/t^2)^k :=
    pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp (49/4/t^2)) k
  rw [← Real.exp_nat_mul] at hbase
  have hbound := hbase.trans (Real.exp_le_exp.2 hexp)
  rw [show t^2+49/4=t^2*(1+49/4/t^2) by field_simp, mul_pow, ← pow_mul]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

private def bulkConstant : ℝ := 850*Real.exp (49*Real.pi/4)/(8*Real.pi^3)

private theorem factor_laplace (k : ℕ) {t : ℝ} (ht : saddleHeight k/2 ≤ t) :
    ‖mellinFactor k (4+(t:ℂ)*I)‖ ≤
      bulkConstant*(t^(2*k+7)*Real.exp (-(Real.pi/2)*t)) := by
  have ht1 : 1 ≤ t := by linarith [height_two k]
  have ht0 : 0 < t := by linarith
  have hu : 1 ≤ Real.pi/2*t := by nlinarith [Real.pi_gt_three]
  have hp := power_correction k ht
  have hs := reciprocal_sinh hu
  have h4 : t^2+4 ≤ 5*t^2 := by nlinarith
  have h9 : t^2+9 ≤ 10*t^2 := by nlinarith
  have h16 : t^2+16 ≤ 17*t^2 := by nlinarith
  rw [norm_factor k ht0]
  calc _ = ((t^2+49/4)^k*t*(t^2+4)*(t^2+9)*(t^2+16)/(32*Real.pi^3))*
      (1/Real.sinh (Real.pi/2*t)) := by ring
       _ ≤ (t^(2*k)*Real.exp (49*Real.pi/4)*t*(5*t^2)*(10*t^2)*(17*t^2)/(32*Real.pi^3))*
      (4*Real.exp (-(Real.pi/2*t))) := by gcongr
       _ = _ := by unfold bulkConstant; rw [pow_add]; ring_nf

open WeilWorkDeficitPrimeKernel WeilWorkDeficitMellin

/-- Exact norm of the literal product-kernel Mellin transform on the line Re(s)=4. -/
theorem productKernel_mellin_norm (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖∫ x in Ioi (0:ℝ), (x:ℂ)^((4+(t:ℂ)*I)-1)*(productKernel k x:ℂ)‖ =
      (t^2+49/4)^k * t*(t^2+4)*(t^2+9)*(t^2+16) /
        (32*Real.pi^3*Real.sinh (Real.pi/2*t)) := by
  rw [productKernel_mellin k (by simp : 0 < ((4:ℂ)+(t:ℂ)*I).re)]
  exact norm_factor k ht

/-- A common Gaussian bound for the actual Mellin amplitude uniform in the derivative order `k`. -/
theorem exists_productKernel_mellin_bulk_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (t : ℝ), saddleHeight k/2 ≤ t → t ≤ 2*saddleHeight k →
      ‖∫ x in Ioi (0:ℝ), (x:ℂ)^((4+(t:ℂ)*I)-1)*(productKernel k x:ℂ)‖ ≤
        C*saddleMass k * Real.exp (-(Real.pi/2)*(t-saddleHeight k)^2/(9*saddleHeight k)) := by
  have hC : 0 < bulkConstant := by unfold bulkConstant; positivity
  refine ⟨bulkConstant,hC,fun k t ht ht2 => ?_⟩
  rw [productKernel_mellin k (by simp : 0 < ((4:ℂ)+(t:ℂ)*I).re)]
  change ‖mellinFactor k (4+(t:ℂ)*I)‖ ≤ _
  exact (factor_laplace k ht).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (laplace_gaussian k ht ht2) hC.le)

end RHTower.WeilWorkDeficitAmplitude
