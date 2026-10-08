import GaloisForLFunctions.RHTower.WeilWorkDeficitMellinAmplitude
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import GaloisForLFunctions.RHTower.StripHorizontalShift


/-!
# Global amplitude of the actual product-kernel Mellin transform

Gamma reflection and a global Laplace inequality bound the full line
`Re(s)=4`, including zero and both height tails, by one envelope for every
derivative order. The envelope is absolutely integrable with total mass
bounded by saddle amplitude times square-root saddle width.

This closes the vertical integrability dependency of the Weil-work kernel
analysis. Critical-line local asymptotics, higher differentiated envelopes,
and spectral-deficit production remain separate obligations.
-/

noncomputable section
open MeasureTheory Set Complex
open scoped Real
open RHTower.WeilWorkDeficitAmplitude RHTower.WeilWorkDeficitMellin
open RHTower.WeilWorkDeficitPrimeKernel
namespace RHTower.WeilWorkDeficitGlobalAmplitude

/-- The literal Mellin transform of the actual derivative product kernel on `Re(s)=4`. -/
def verticalMellin (k : ℕ) (t : ℝ) : ℂ :=
  ∫ x in Ioi (0:ℝ), (x:ℂ)^((4+(t:ℂ)*I)-1)*(productKernel k x:ℂ)

private theorem vertical_eq (k : ℕ) (t : ℝ) :
    verticalMellin k t = (-1:ℂ)^k * ((4:ℂ)+t*I-1/2)^(2*k) *
      ((4:ℂ)+t*I)^2 * ((4:ℂ)+t*I-1)^2 *
      (Real.pi:ℂ)^(-((4:ℂ)+t*I)) * Complex.Gamma (((4:ℂ)+t*I)/2)^2 / 4 :=
  productKernel_mellin k (by simp)

private theorem height_pos (k : ℕ) : 0 < saddleHeight k := by
  unfold saddleHeight
  positivity

private theorem height_eq (k : ℕ) : (Real.pi/2)*saddleHeight k = 2*(k:ℝ)+7 := by
  unfold saddleHeight
  field_simp

private theorem laplace_sqrt (k : ℕ) {r : ℝ} (hr : 0 < r) :
    r^(2*k+7)*Real.exp (-(Real.pi/2)*r) ≤
      saddleMass k * Real.exp (-(Real.pi/2)*(Real.sqrt r-Real.sqrt (saddleHeight k))^2) := by
  let T := saddleHeight k
  have hT : 0 < T := height_pos k
  have hsT := Real.sq_sqrt hT.le
  have hsr := Real.sq_sqrt hr.le
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (div_pos hr hT))
  rw [Real.log_sqrt (div_pos hr hT).le, Real.sqrt_div hr.le] at hlog
  have hlog2 : T*Real.log (r/T) ≤ 2*Real.sqrt T*Real.sqrt r-2*T := by
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*T by positivity)
    have hq : 2*T*(Real.sqrt r/Real.sqrt T-1) =
        2*Real.sqrt T*Real.sqrt r-2*T := by
      field_simp
      ring_nf
      rw [hsT]
      ring
    nlinarith
  have hn : ((2*k+7:ℕ):ℝ) = (Real.pi/2)*T := by
    dsimp [T]
    rw [height_eq]
    push_cast
    ring
  have he : ((2*k+7:ℕ):ℝ)*Real.log (r/T)-(Real.pi/2)*(r-T) ≤
      -(Real.pi/2)*(Real.sqrt r-Real.sqrt T)^2 := by
    rw [hn]
    have h := mul_le_mul_of_nonneg_left hlog2 Real.pi_pos.le
    nlinarith
  have hp (u : ℝ) (hu : 0 < u) : u^(2*k+7) =
      Real.exp (((2*k+7:ℕ):ℝ)*Real.log u) := by
    rw [Real.exp_nat_mul, Real.exp_log hu]
  have hid : r^(2*k+7)*Real.exp (-(Real.pi/2)*r) = saddleMass k *
      Real.exp (((2*k+7:ℕ):ℝ)*Real.log (r/T)-(Real.pi/2)*(r-T)) := by
    simp only [saddleMass, hp r hr, hp (saddleHeight k) (height_pos k)]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      Real.log_div hr.ne' hT.ne']
    congr 1
    dsimp [T]
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 he) (by unfold saddleMass; positivity)

private theorem sinh_ratio {t : ℝ} (ht : 0 < t) :
    t/Real.sinh (Real.pi/2*t) ≤ (2/Real.pi+2*t)*Real.exp (-(Real.pi/2*t)) := by
  let u := Real.pi/2*t
  have hu : 0 < u := by dsimp [u]; positivity
  have hexp := Real.add_one_le_exp (2*u)
  have haux : 2*u ≤ (1+2*u)*(1-Real.exp (-2*u)) := by
    have h := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-2*u)).le
    have hh : Real.exp (-2*u)*Real.exp (2*u)=1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hbase : t ≤ (2/Real.pi+2*t)*(1-Real.exp (-2*u))/2 := by
    apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
    have heq : Real.pi*((2/Real.pi+2*t)*(1-Real.exp (-2*u))/2) =
        (1+2*u)*(1-Real.exp (-2*u)) := by
      dsimp [u]
      field_simp
    rw [heq]
    change Real.pi*t ≤ _
    convert haux using 1
    dsimp [u]
    ring
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
  have heq : Real.exp (-u)*Real.sinh u=(1-Real.exp (-2*u))/2 := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-u)*Real.exp u=1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp (-u)*Real.exp (-u)=Real.exp (-2*u) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith
  rw [div_le_iff₀ hs]
  change t ≤ (2/Real.pi+2*t)*Real.exp (-u)*Real.sinh u
  rw [mul_assoc,heq]
  linarith

private def radius (t : ℝ) : ℝ := Real.sqrt (t^2+49/4)

private theorem radius_facts {t : ℝ} (ht : 0 ≤ t) :
    7/2 ≤ radius t ∧ t ≤ radius t ∧ radius t ≤ t+7/2 ∧ (radius t)^2=t^2+49/4 := by
  have hs := Real.sq_sqrt (show 0 ≤ t^2+49/4 by positivity)
  have hp := Real.sqrt_nonneg (t^2+49/4)
  dsimp [radius]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · exact hs

private theorem shifted_bound (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖verticalMellin k t‖ ≤ (radius t)^(2*k+7)*Real.exp (-(Real.pi/2)*t) := by
  obtain ⟨hr,hrt,hrup,hrsq⟩ := radius_facts ht.le
  have hr0 : 0 < radius t := by linarith
  have h4 : t^2+4 ≤ (radius t)^2 := by nlinarith
  have h9 : t^2+9 ≤ (radius t)^2 := by nlinarith
  have h16 : t^2+16 ≤ 2*(radius t)^2 := by nlinarith
  have hlin : 2/Real.pi+2*t ≤ 3*radius t := by
    have hh : 2/Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    linarith
  have hs := (sinh_ratio ht).trans (mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le)
  rw [show verticalMellin k t = ∫ x in Ioi (0:ℝ),
    (x:ℂ)^((4+(t:ℂ)*I)-1)*(productKernel k x:ℂ) from rfl,
    productKernel_mellin_norm k ht]
  calc _ = (t^2+49/4)^k*(t^2+4)*(t^2+9)*(t^2+16)/(32*Real.pi^3)*
      (t/Real.sinh (Real.pi/2*t)) := by ring
    _ ≤ ((radius t)^2)^k*(radius t)^2*(radius t)^2*(2*(radius t)^2)/(32*Real.pi^3)*
      (3*radius t*Real.exp (-(Real.pi/2*t))) := by rw [← hrsq]; gcongr
    _ = 6/(32*Real.pi^3)*((radius t)^(2*k+7)*Real.exp (-(Real.pi/2)*t)) := by
      rw [← pow_mul, pow_add]
      ring_nf
    _ ≤ _ := by
      apply mul_le_of_le_one_left (by positivity)
      rw [div_le_one (by positivity : 0 < 32*Real.pi^3)]
      have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hpi 3
      norm_num at hpow
      linarith


private theorem norm_zero (k : ℕ) :
    ‖verticalMellin k 0‖ = (7/2:ℝ)^(2*k)*(36/Real.pi^4) := by
  have hg : Complex.Gamma 2 = 1 := by
    norm_num
  have hp : ‖(Real.pi:ℂ)^(-(4:ℂ))‖ = (Real.pi^4)⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    norm_num
    exact zpow_ofNat Real.pi 4
  rw [vertical_eq]
  norm_num [hg, norm_mul, norm_div, norm_pow, hp]
  ring

private theorem shifted_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖verticalMellin k t‖ ≤ (radius t)^(2*k+7)*Real.exp (-(Real.pi/2)*t) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · rw [norm_zero]
    have hr : radius 0 = 7/2 := by
      obtain ⟨h,_,_,hs⟩ := radius_facts (le_refl (0:ℝ))
      nlinarith
    rw [hr]
    simp only [mul_zero, Real.exp_zero, mul_one]
    rw [pow_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hpi 4
    have hd : 36/Real.pi^4 ≤ 1 := by
      rw [div_le_one (by positivity : 0 < Real.pi^4)]
      norm_num at hp
      linarith
    exact hd.trans (by norm_num)
  · exact shifted_bound k ht

private theorem sqrt_distance {t : ℝ} (ht : 0 ≤ t) (T : ℝ) :
    (Real.sqrt (radius t)-Real.sqrt T)^2 ≥
      (Real.sqrt t-Real.sqrt T)^2/2-7/2 := by
  obtain ⟨hr,hrt,hrup,hrsq⟩ := radius_facts ht
  have h1 := Real.sq_sqrt ht
  have h2 := Real.sq_sqrt (by linarith : 0 ≤ radius t)
  have hle := Real.sqrt_le_sqrt hrt
  have hm := mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg t)
  have hd : (Real.sqrt (radius t)-Real.sqrt t)^2 ≤ 7/2 := by nlinarith
  nlinarith [sq_nonneg (2*(Real.sqrt (radius t)-Real.sqrt T)-
    (Real.sqrt t-Real.sqrt T))]

private theorem nonneg_bound (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖verticalMellin k t‖ ≤ Real.exp (7*Real.pi/2)*saddleMass k *
      Real.exp (-(Real.pi/4)*(Real.sqrt t-Real.sqrt (saddleHeight k))^2) := by
  obtain ⟨hr,hrt,hrup,hrsq⟩ := radius_facts ht
  have hp := laplace_sqrt k (show 0 < radius t by linarith)
  have hb : 0 ≤ saddleMass k := by
    unfold saddleMass
    exact mul_nonneg (pow_nonneg (height_pos k).le _) (Real.exp_pos _).le
  calc ‖verticalMellin k t‖ ≤
        (radius t)^(2*k+7)*Real.exp (-(Real.pi/2)*t) := shifted_nonneg k ht
    _ = ((radius t)^(2*k+7)*Real.exp (-(Real.pi/2)*radius t))*
        Real.exp ((Real.pi/2)*(radius t-t)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (saddleMass k*Real.exp (-(Real.pi/2)*
        (Real.sqrt (radius t)-Real.sqrt (saddleHeight k))^2))*
        Real.exp ((Real.pi/2)*(radius t-t)) := by gcongr
    _ = saddleMass k*Real.exp ((Real.pi/2)*(radius t-t) -
        (Real.pi/2)*(Real.sqrt (radius t)-Real.sqrt (saddleHeight k))^2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ saddleMass k*Real.exp (7*Real.pi/2 -
        (Real.pi/4)*(Real.sqrt t-Real.sqrt (saddleHeight k))^2) := by
      apply mul_le_mul_of_nonneg_left _ hb
      apply Real.exp_le_exp.mpr
      have hd := sqrt_distance ht (saddleHeight k)
      have h1 := mul_le_mul_of_nonneg_left hd Real.pi_pos.le
      have h2 := mul_le_mul_of_nonneg_left hrup Real.pi_pos.le
      nlinarith
    _ = _ := by
      rw [Real.exp_sub]
      simp only [neg_mul, Real.exp_neg]
      ring

private theorem vertical_neg (k : ℕ) (t : ℝ) :
    verticalMellin k (-t) = starRingEnd ℂ (verticalMellin k t) := by
  unfold verticalMellin
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have ha : (x:ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt hx)]
    exact Real.pi_ne_zero.symm
  have he : (4:ℂ)+(-t:ℝ)*I-1 = starRingEnd ℂ ((4:ℂ)+t*I-1) := by
    norm_num [map_sub, map_add, map_mul, Complex.conj_ofNat]
  change (x:ℂ)^((4:ℂ)+(-t:ℝ)*I-1)*(productKernel k x:ℂ) =
    starRingEnd ℂ ((x:ℂ)^((4:ℂ)+t*I-1)*(productKernel k x:ℂ))
  rw [he, Complex.cpow_conj _ _ ha, Complex.conj_ofReal, map_mul, Complex.conj_ofReal]

/-- A single saddle envelope controls the actual Mellin integral at every real height. -/
theorem norm_verticalMellin_le (k : ℕ) (t : ℝ) :
    ‖verticalMellin k t‖ ≤ Real.exp (7*Real.pi/2)*saddleMass k *
      Real.exp (-(Real.pi/4)*(Real.sqrt |t|-Real.sqrt (saddleHeight k))^2) := by
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using nonneg_bound k ht
  · have h := nonneg_bound k (show 0 ≤ -t by linarith)
    rw [vertical_neg, Complex.norm_conj] at h
    simpa only [abs_of_neg (lt_of_not_ge ht)] using h


private theorem continuous_vertical (k : ℕ) : Continuous (verticalMellin k) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hg : ContinuousAt (fun u : ℝ => Complex.Gamma (((4:ℂ)+u*I)/2)) t := by
    apply (Complex.continuousAt_Gamma _ _).comp
    · fun_prop
    · intro m h
      have hr := congrArg Complex.re h
      norm_num at hr
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hp : ContinuousAt (fun u : ℝ => (Real.pi:ℂ)^(-((4:ℂ)+u*I))) t :=
    (continuousAt_const_cpow (by exact_mod_cast Real.pi_ne_zero)).comp (by fun_prop)
  have he : verticalMellin k = fun u : ℝ =>
      (-1:ℂ)^k * ((4:ℂ)+u*I-1/2)^(2*k) * ((4:ℂ)+u*I)^2 *
        ((4:ℂ)+u*I-1)^2 * (Real.pi:ℂ)^(-((4:ℂ)+u*I)) *
        Complex.Gamma (((4:ℂ)+u*I)/2)^2 / 4 := funext (vertical_eq k)
  rw [he]
  fun_prop

private def majorant (k : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(Real.pi/(36*saddleHeight k))*(t-saddleHeight k)^2) +
  Real.exp (-(Real.pi/(36*saddleHeight k))*(t+saddleHeight k)^2) +
  Real.exp (-(Real.pi/16*|t|))

private theorem envelope_majorant (k : ℕ) (t : ℝ) :
    Real.exp (-(Real.pi/4)*(Real.sqrt |t|-Real.sqrt (saddleHeight k))^2) ≤ majorant k t := by
  let T := saddleHeight k
  have hT : 0 < T := height_pos k
  have hsT := Real.sq_sqrt hT.le
  have hst := Real.sq_sqrt (abs_nonneg t)
  have hqt := Real.sqrt_nonneg |t|
  have hqT := Real.sqrt_nonneg T
  by_cases hsmall : |t| ≤ 4*T
  · have hr : Real.sqrt |t| ≤ 2*Real.sqrt T := by nlinarith
    have hs : (Real.sqrt |t|+Real.sqrt T)^2 ≤ 9*T := by nlinarith
    have hid : (|t|-T)^2 =
        (Real.sqrt |t|-Real.sqrt T)^2*(Real.sqrt |t|+Real.sqrt T)^2 := by
      calc _ = ((Real.sqrt |t|)^2-(Real.sqrt T)^2)^2 := by rw [hst,hsT]
           _ = _ := by ring
    have hd : (|t|-T)^2 ≤ 9*T*(Real.sqrt |t|-Real.sqrt T)^2 := by
      rw [hid]
      nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.sqrt |t|-Real.sqrt T))]
    have he : Real.exp (-(Real.pi/4)*(Real.sqrt |t|-Real.sqrt T)^2) ≤
        Real.exp (-(Real.pi/(36*T))*(|t|-T)^2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hd Real.pi_pos.le
      apply (mul_le_mul_iff_left₀ (show 0 < 36*T by positivity)).mp
      field_simp
      nlinarith
    refine he.trans ?_
    dsimp [majorant]
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
      dsimp [T] at he ⊢
      linarith [Real.exp_pos (-(Real.pi/(36*saddleHeight k))*(t+saddleHeight k)^2),
        Real.exp_pos (-(Real.pi/16*t))]
    · rw [abs_of_neg (lt_of_not_ge ht)]
      have heq : (-t-T)^2 = (t+T)^2 := by ring
      rw [heq]
      dsimp [T]
      linarith [Real.exp_pos (-(Real.pi/(36*saddleHeight k))*(t-saddleHeight k)^2),
        Real.exp_pos (-(Real.pi/16*(-t)))]
  · have hr : 2*Real.sqrt T ≤ Real.sqrt |t| := by nlinarith
    have hd : |t|/4 ≤ (Real.sqrt |t|-Real.sqrt T)^2 := by
      nlinarith [sq_nonneg (Real.sqrt |t|-2*Real.sqrt T)]
    have he : Real.exp (-(Real.pi/4)*(Real.sqrt |t|-Real.sqrt T)^2) ≤
        Real.exp (-(Real.pi/16*|t|)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hd Real.pi_pos.le]
    refine he.trans ?_
    dsimp [majorant]
    linarith [Real.exp_pos (-(Real.pi/(36*saddleHeight k))*(t-saddleHeight k)^2),
      Real.exp_pos (-(Real.pi/(36*saddleHeight k))*(t+saddleHeight k)^2)]

private theorem integrable_majorant (k : ℕ) : Integrable (majorant k) := by
  have hg := integrable_exp_neg_mul_sq
    (show 0 < Real.pi/(36*saddleHeight k) by exact div_pos Real.pi_pos (mul_pos (by norm_num) (height_pos k)))
  have h1 := hg.comp_sub_right (saddleHeight k)
  have h2 := hg.comp_sub_right (-saddleHeight k)
  have h3 := RHTower.integrable_exp_neg_mul_abs' (show 0 < Real.pi/16 by positivity)
  convert! (h1.add h2).add h3 using 1
  all_goals first | rfl | (funext t; simp only [majorant, Pi.add_apply, sub_neg_eq_add])

private theorem integral_majorant (k : ℕ) :
    (∫ t : ℝ, majorant k t) = 12*Real.sqrt (saddleHeight k)+32/Real.pi := by
  have hg := integrable_exp_neg_mul_sq
    (show 0 < Real.pi/(36*saddleHeight k) by exact div_pos Real.pi_pos (mul_pos (by norm_num) (height_pos k)))
  have h1 := hg.comp_sub_right (saddleHeight k)
  have h2 : Integrable (fun t : ℝ => Real.exp (-(Real.pi/(36*saddleHeight k))*(t+saddleHeight k)^2)) := by
    simpa only [sub_neg_eq_add] using hg.comp_sub_right (-saddleHeight k)
  have h3 := RHTower.integrable_exp_neg_mul_abs' (show 0 < Real.pi/16 by positivity)
  have hgauss (v : ℝ) :
      (∫ t : ℝ, Real.exp (-(Real.pi/(36*saddleHeight k))*(t-v)^2)) =
        6*Real.sqrt (saddleHeight k) := by
    rw [integral_sub_right_eq_self (fun t : ℝ => Real.exp (-(Real.pi/(36*saddleHeight k))*t^2)), integral_gaussian]
    have he : Real.pi/(Real.pi/(36*saddleHeight k))=36*saddleHeight k := by field_simp
    rw [he,Real.sqrt_mul (by norm_num : (0:ℝ)≤36)]
    norm_num
  have he : (∫ t : ℝ, Real.exp (-(Real.pi/16*|t|)))=32/Real.pi := by
    have hh := integral_comp_abs (f := fun t : ℝ => Real.exp (-(Real.pi/16*t)))
    rw [hh]
    have hx := integral_exp_mul_Ioi (show -(Real.pi/16) < 0 by linarith [Real.pi_pos]) 0
    simp only [neg_mul] at hx
    rw [hx]
    field_simp
    norm_num
  unfold majorant
  have hadd := integral_add (h1.add h2) h3
  have hadd2 := integral_add h1 h2
  simp only [Pi.add_apply] at hadd hadd2
  rw [hadd, hadd2, hgauss, he]
  have hother := hgauss (-saddleHeight k)
  simp only [sub_neg_eq_add] at hother
  rw [hother]
  ring

private theorem norm_majorant (k : ℕ) (t : ℝ) :
    ‖verticalMellin k t‖ ≤ Real.exp (7*Real.pi/2)*saddleMass k*majorant k t := by
  refine (norm_verticalMellin_le k t).trans ?_
  apply mul_le_mul_of_nonneg_left (envelope_majorant k t)
  unfold saddleMass
  exact mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (pow_nonneg (height_pos k).le _) (Real.exp_pos _).le)

/-- Absolute integration of the actual vertical Mellin transform over all heights. -/
theorem integrable_verticalMellin (k : ℕ) : Integrable (verticalMellin k) := by
  exact ((integrable_majorant k).const_mul (Real.exp (7*Real.pi/2)*saddleMass k)).mono'
    (continuous_vertical k).aestronglyMeasurable (Filter.Eventually.of_forall (norm_majorant k))

/-- The full vertical norm costs only saddle mass times its square-root width. -/
theorem integral_norm_verticalMellin_le (k : ℕ) :
    (∫ t : ℝ, ‖verticalMellin k t‖) ≤
      20*Real.exp (7*Real.pi/2)*saddleMass k*Real.sqrt (saddleHeight k) := by
  have hb : 0 ≤ Real.exp (7*Real.pi/2)*saddleMass k := by
    unfold saddleMass
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (pow_nonneg (height_pos k).le _) (Real.exp_pos _).le)
  have hT : 4 ≤ saddleHeight k := by
    unfold saddleHeight
    rw [le_div_iff₀ (by positivity : 0 < Real.pi/2)]
    nlinarith [Real.pi_lt_d2, Nat.cast_nonneg (α := ℝ) k]
  have hq : 2 ≤ Real.sqrt (saddleHeight k) := by
    nlinarith [Real.sq_sqrt (height_pos k).le, Real.sqrt_nonneg (saddleHeight k)]
  have hp : 32/Real.pi ≤ 16 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  calc (∫ t : ℝ, ‖verticalMellin k t‖) ≤
      ∫ t : ℝ, Real.exp (7*Real.pi/2)*saddleMass k*majorant k t :=
        integral_mono_ae (integrable_verticalMellin k).norm
          ((integrable_majorant k).const_mul _) (Filter.Eventually.of_forall (norm_majorant k))
    _ = Real.exp (7*Real.pi/2)*saddleMass k*(12*Real.sqrt (saddleHeight k)+32/Real.pi) := by
      rw [integral_const_mul,integral_majorant]
    _ ≤ Real.exp (7*Real.pi/2)*saddleMass k*(20*Real.sqrt (saddleHeight k)) :=
      mul_le_mul_of_nonneg_left (by linarith) hb
    _ = _ := by ring

end RHTower.WeilWorkDeficitGlobalAmplitude
