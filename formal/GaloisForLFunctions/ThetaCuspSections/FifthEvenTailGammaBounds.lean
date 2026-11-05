import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Two-sided bounds for the common incomplete-gamma mass

A tangent bound for the reciprocal square root retains two further terms
of the gamma expansion, with an explicit signed cubic remainder.
-/


noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.ThetaCuspSections.FifthAtomTail

private theorem reciprocal_sqrt_tangent {q t : ℝ} (hq : 0<q) (ht : 0<t) :
 1/Real.sqrt q-(t-q)/(2*q*Real.sqrt q)≤t^(-1/2:ℝ) := by
 have hu := Real.sqrt_pos.mpr ht
 have hv := Real.sqrt_pos.mpr hq
 have hu2 := Real.sq_sqrt ht.le
 have hv2 := Real.sq_sqrt hq.le
 have hbound : 1/Real.sqrt q-
   ((Real.sqrt t)^2-(Real.sqrt q)^2)/(2*(Real.sqrt q)^2*Real.sqrt q)≤
   (Real.sqrt t)⁻¹ := by
  rw [← one_div (Real.sqrt t)]
  apply (le_div_iff₀ hu).mpr
  have h : 0≤(Real.sqrt t-Real.sqrt q)^2*(Real.sqrt t+2*Real.sqrt q) :=
   mul_nonneg (sq_nonneg _) (by positivity)
  apply (mul_le_mul_iff_right₀
   (show 0<2*(Real.sqrt q)^2*Real.sqrt q by positivity)).mp
  field_simp [hv.ne']
  nlinarith only [h]
 rw [show (-1/2:ℝ)= -(1/2) by norm_num,Real.rpow_neg ht.le,← Real.sqrt_eq_rpow]
 simpa only [hu2,hv2] using hbound


private theorem power_integrable_gamma {s q : ℝ} (hs : -1<s) (hq : 0≤q) :
 IntegrableOn (fun t : ℝ => t^s*Real.exp (-2*t)) (Ioi q) := by
 have h := integrableOn_rpow_mul_exp_neg_mul_rpow hs
   (show (1:ℝ)≤1 by rfl) (show (0:ℝ)<2 by norm_num)
 simp only [Real.rpow_one] at h
 exact h.mono_set (Ioi_subset_Ioi hq)

private theorem powerTail_zero (q : ℝ) : powerTail 0 q=Real.exp (-2*q)/2 := by
 simp only [powerTail,Real.rpow_zero,one_mul]
 have h := integral_exp_mul_Ioi (a := (-2:ℝ)) (by norm_num) q
 convert h using 1
 ring

private theorem inverse_half_tail_upper {q : ℝ} (hq : 0<q) :
 powerTail (-1/2) q≤boundary q/(2*q^2) := by
 have hi := power_integrable_gamma (s := (-1/2)) (by norm_num) hq.le
 have he := integrableOn_exp_mul_Ioi (a := (-2:ℝ)) (by norm_num) q
 have h : powerTail (-1/2) q≤
   ∫ t in Ioi q, q^(-1/2:ℝ)*Real.exp (-2*t) := by
  apply integral_mono_ae hi (he.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_le_mul_of_nonneg_right
   (Real.rpow_le_rpow_of_nonpos hq ht.le (by norm_num)) (Real.exp_pos _).le
 rw [integral_const_mul,integral_exp_mul_Ioi (a := (-2:ℝ)) (by norm_num)] at h
 have hid : q^(-1/2:ℝ)*(-Real.exp (-2*q)/(-2))=boundary q/(2*q^2) := by
  unfold boundary
  have hp : q^(3/2:ℝ)=q^2*q^(-1/2:ℝ) := by
   rw [← Real.rpow_natCast q 2,← Real.rpow_add hq]
   norm_num
  rw [hp]
  field_simp [hq.ne']
 exact h.trans_eq hid

private theorem inverse_half_tail_lower {q : ℝ} (hq : 0<q) :
 boundary q/(2*q^2)-boundary q/(8*q^3)≤powerTail (-1/2) q := by
 have hi := power_integrable_gamma (s := (-1/2)) (by norm_num) hq.le
 have he := integrableOn_exp_mul_Ioi (a := (-2:ℝ)) (by norm_num) q
 have ht := power_integrable_gamma (s := 1) (by norm_num) hq.le
 simp only [Real.rpow_one] at ht
 have hf := (he.const_mul (1/Real.sqrt q+q/(2*q*Real.sqrt q))).sub
   (ht.const_mul (1/(2*q*Real.sqrt q)))
 have h : (∫ t in Ioi q, (1/Real.sqrt q+q/(2*q*Real.sqrt q))*Real.exp (-2*t)-
   (1/(2*q*Real.sqrt q))*(t*Real.exp (-2*t)))≤powerTail (-1/2) q := by
  apply integral_mono_ae hf hi
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t htq
  dsimp only [Pi.sub_apply]
  have hh := mul_le_mul_of_nonneg_right
   (reciprocal_sqrt_tangent hq (hq.trans htq)) (Real.exp_pos (-2*t)).le
  convert hh using 1
  ring
 have hp := powerTail_recurrence (s := 1) (by norm_num) hq
 norm_num only [Real.rpow_one,show (1:ℝ)-1=0 by norm_num,powerTail_zero] at hp
 have htI : (∫ t in Ioi q, t*Real.exp (-2*t))=
   q*Real.exp (-2*q)/2+Real.exp (-2*q)/4 := by
  simp only [powerTail,Real.rpow_one] at hp
  linear_combination hp
 rw [integral_sub (he.const_mul _) (ht.const_mul _),
   integral_const_mul,integral_const_mul,integral_exp_mul_Ioi (a := (-2:ℝ)) (by norm_num),htI] at h
 have hsq := Real.sqrt_pos.mpr hq
 have hE : boundary q=q*Real.sqrt q*Real.exp (-2*q) := by
  unfold boundary
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hq,Real.rpow_one,← Real.sqrt_eq_rpow]
 have hid : (1/Real.sqrt q+q/(2*q*Real.sqrt q))*(-Real.exp (-2*q)/(-2))-
   (1/(2*q*Real.sqrt q))*(q*Real.exp (-2*q)/2+Real.exp (-2*q)/4)=
   boundary q/(2*q^2)-boundary q/(8*q^3) := by
  rw [hE]
  field_simp [hq.ne',hsq.ne']
  nlinarith only [Real.sq_sqrt hq.le]
 exact hid ▸ h

/-- Two retained integrations by parts isolate the inverse-square-root remainder. -/
theorem gammaMass_two_terms {q : ℝ} (hq : 0<q) :
 gammaMass q=1/2+3/(8*q)+(3/(16*boundary q))*powerTail (-1/2) q := by
 have h3 := powerTail_recurrence (s := 3/2) (by norm_num) hq
 have h1 := powerTail_recurrence (s := 1/2) (by norm_num) hq
 norm_num only [show (3/2:ℝ)-1=1/2 by norm_num] at h3
 norm_num only [show (1/2:ℝ)-1= -1/2 by norm_num] at h1
 have hp : q*q^(1/2:ℝ)*Real.exp (-2*q)=boundary q := by
  unfold boundary
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hq,Real.rpow_one]
 unfold gammaMass
 rw [h3,h1]
 field_simp [(boundary_pos hq).ne',hq.ne']
 dsimp only [boundary] at hp ⊢
 simp only [neg_mul] at hp ⊢
 nlinarith only [hp]

/-- A cubic lower enclosure for the normalized gamma mass. -/
theorem gammaMass_cubic_lower {q : ℝ} (hq : 0<q) :
 1/2+3/(8*q)+3/(32*q^2)-3/(128*q^3)≤gammaMass q := by
 rw [gammaMass_two_terms hq]
 have h := mul_le_mul_of_nonneg_left (inverse_half_tail_lower hq)
   (show 0≤3/(16*boundary q) by exact (div_pos (by norm_num) (mul_pos (by norm_num) (boundary_pos hq))).le)
 have he : (3/(16*boundary q))*(boundary q/(2*q^2)-boundary q/(8*q^3))=
   3/(32*q^2)-3/(128*q^3) := by
  field_simp [(boundary_pos hq).ne',hq.ne']
  ring
 rw [he] at h
 linarith only [h]

/-- A quadratic upper enclosure for the normalized gamma mass. -/
theorem gammaMass_quadratic_upper {q : ℝ} (hq : 0<q) :
 gammaMass q≤1/2+3/(8*q)+3/(32*q^2) := by
 rw [gammaMass_two_terms hq]
 have h := mul_le_mul_of_nonneg_left (inverse_half_tail_upper hq)
   (show 0≤3/(16*boundary q) by exact (div_pos (by norm_num) (mul_pos (by norm_num) (boundary_pos hq))).le)
 have he : (3/(16*boundary q))*(boundary q/(2*q^2))=3/(32*q^2) := by
  field_simp [(boundary_pos hq).ne',hq.ne']
  ring
 rw [he] at h
 linarith only [h]

end GaloisForLFunctions.ThetaCuspSections.FifthAtomTail

