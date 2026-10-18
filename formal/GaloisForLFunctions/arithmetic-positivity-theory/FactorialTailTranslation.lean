import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailWeightedMass

/-! Translation energy of the literal factorial tail, including the cutoff jump.
The arithmetic phase is estimated through its clock displacement, not by taking
derivatives across the integer joins. -/

open MeasureTheory Set
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- Squared translation displacement of the weighted actual tail. -/
def factorialTailTranslationEnergy (n : ℕ) (σ h : ℝ) : ℝ :=
  ∫ x : ℝ, (factorialWeightedTail n σ (x+h)-factorialWeightedTail n σ x)^2

theorem factorialTailTranslationEnergy_nonneg (n : ℕ) (σ h : ℝ) :
    0 ≤ factorialTailTranslationEnergy n σ h := integral_nonneg fun _ => sq_nonneg _

theorem factorialTailTranslationEnergy_measurable (n : ℕ) (σ : ℝ) :
    Measurable (factorialTailTranslationEnergy n σ) := by
  have hf := factorialWeightedTail_measurable n σ
  have hm : Measurable (fun p : ℝ×ℝ =>
      (factorialWeightedTail n σ (p.2+p.1)-factorialWeightedTail n σ p.2)^2) :=
    ((hf.comp (measurable_snd.add measurable_fst)).sub (hf.comp measurable_snd)).pow_const 2
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private theorem square_difference_le (a b : ℝ) :
    (a-b)^2 ≤ 2*a^2+2*b^2 := by nlinarith only [sq_nonneg (a+b)]

theorem factorialTailTranslation_sq_integrable (n : ℕ)
    (σ : FactorialSamplingAbscissa) (h : ℝ) :
    Integrable (fun x : ℝ =>
      (factorialWeightedTail n σ (x+h)-factorialWeightedTail n σ x)^2) := by
  have hi := factorialWeightedTail_sq_integrable n σ
  have hm := factorialWeightedTail_measurable n σ
  apply (((hi.comp_add_right h).const_mul 2).add (hi.const_mul 2)).mono'
    (((hm.comp (measurable_id.add_const h)).sub hm).pow_const 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact square_difference_le _ _

/-- Translation costs at most four times the already controlled square mass. -/
theorem factorialTailTranslationEnergy_le_mass (n : ℕ)
    (σ : FactorialSamplingAbscissa) (h : ℝ) :
    factorialTailTranslationEnergy n σ h ≤ 384/((n+1 : ℕ) : ℝ) := by
  have hi := factorialWeightedTail_sq_integrable n σ
  have hshift : (∫ x : ℝ, (factorialWeightedTail n σ (x+h))^2) =
      ∫ x : ℝ, (factorialWeightedTail n σ x)^2 :=
    integral_add_right_eq_self (fun x : ℝ => (factorialWeightedTail n σ x)^2) h
  unfold factorialTailTranslationEnergy
  calc
    _ ≤ ∫ x : ℝ, 2*(factorialWeightedTail n σ (x+h))^2+
        2*(factorialWeightedTail n σ x)^2 :=
      integral_mono (factorialTailTranslation_sq_integrable n σ h)
        (((hi.comp_add_right h).const_mul 2).add (hi.const_mul 2))
        (fun x => square_difference_le _ _)
    _ = 4*∫ x : ℝ, (factorialWeightedTail n σ x)^2 := by
      rw [integral_add ((hi.comp_add_right h).const_mul 2) (hi.const_mul 2),
        integral_const_mul,integral_const_mul,hshift]
      ring
    _ ≤ 4*(96/((n+1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (factorialWeightedTail_sq_integral_le n σ) (by norm_num)
    _ = _ := by ring

private theorem phase_shift_sq_le (n : ℕ) (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    (factorialTailPhase n (x+h)-factorialTailPhase n x)^2 ≤
      28*((n+1 : ℕ) : ℝ)*Real.exp (-x)*h := by
  have he : Real.exp (-(x+h)) = Real.exp (-x)*Real.exp (-h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh1 : Real.exp (-h) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show -h ≤ 0 by linarith)
  have hclock : |Real.exp (-(x+h))-Real.exp (-x)| ≤ Real.exp (-x)*h := by
    rw [he,abs_of_nonpos (by nlinarith only [
      mul_le_mul_of_nonneg_left hh1 (Real.exp_pos (-x)).le])]
    nlinarith only [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-h))
      (Real.exp_pos (-x)).le]
  exact (factorialTailPhase_sub_sq_le n (x+h) x).trans
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hclock (by positivity :
        0 ≤ 28*((n+1 : ℕ) : ℝ)))

private theorem amplitude_sq_le (n : ℕ) :
    (factorialTailAmplitude n)^2 ≤ 225/((n+1 : ℕ) : ℝ) := by
  have h := mul_self_le_mul_self (factorialTailAmplitude_pos n).le
    (factorialTailAmplitude_le n)
  have hs : (Real.sqrt ((n+1 : ℕ) : ℝ))^2 = ((n+1 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  simpa only [← pow_two,div_pow,hs,show (15 : ℝ)^2 = 225 by norm_num] using h

private theorem exp_increment_le {b h : ℝ}
    (hb0 : 0 ≤ b) (hb3 : b ≤ 3) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    Real.exp (b*h)-1 ≤ 3*Real.exp 3*h := by
  have hprod : Real.exp (b*h)*Real.exp (-(b*h)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(b*h)))
    (Real.exp_pos (b*h)).le
  rw [hprod] at hh
  have hbh : b*h ≤ 3 := (mul_le_mul_of_nonneg_left hh1 hb0).trans
    (by simpa using hb3)
  have he := Real.exp_le_exp.mpr hbh
  calc
    _ ≤ (b*h)*Real.exp (b*h) := by nlinarith only [hh]
    _ ≤ (3*h)*Real.exp 3 := mul_le_mul
      (mul_le_mul_of_nonneg_right hb3 hh0) he (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

private theorem weighted_tail_value (n : ℕ) (σ x : ℝ) (hx : x ≤ 0) :
    factorialWeightedTail n σ x =
      factorialTailAmplitude n*Real.exp ((σ+1)*x)*factorialTailPhase n x := by
  rw [factorialWeightedTail_eq_phase,indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)]

private theorem interior_increment_le (n : ℕ) (σ : FactorialSamplingAbscissa)
    (h : Icc (0 : ℝ) 1) (x : ℝ) (hx : x ≤ -(h : ℝ)) :
    (factorialWeightedTail n σ (x+h)-factorialWeightedTail n σ x)^2 ≤
      (4050*Real.exp 6*(h : ℝ)^2/((n+1 : ℕ) : ℝ))*Real.exp x+
        12600*(h : ℝ)*Real.exp (x/2) := by
  let b : ℝ := (σ : ℝ)+1
  let a := factorialTailAmplitude n
  have hh0 := h.2.1
  have hb0 : 0 ≤ b := by dsimp [b]; have := σ.2.1; linarith
  have hb3 : b ≤ 3 := by dsimp [b]; have := σ.2.2; linarith
  have hbmin : 3/4 ≤ b := by dsimp [b]; have := σ.2.1; linarith
  have hx0 : x ≤ 0 := by have := h.2.1; linarith
  have hxh : x+(h : ℝ) ≤ 0 := by linarith
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have ha : a^2 ≤ 225/((n+1 : ℕ) : ℝ) := amplitude_sq_le n
  have haN : a^2*((n+1 : ℕ) : ℝ) ≤ 225 := (le_div_iff₀ hN).mp ha
  have hphase : (factorialTailPhase n (x+h))^2 ≤ 1 := by
    have hp : |factorialTailPhase n (x+h)| ≤ 1 :=
      (factorialTailPhase_abs_le n (x+h)).trans (by norm_num)
    simpa only [sq_abs,one_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr hp
  have hexp0 : 0 ≤ Real.exp (b*(x+h))-Real.exp (b*x) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hb0 h.2.1]
  have hediff : Real.exp (b*(x+h))-Real.exp (b*x) ≤
      3*Real.exp 3*(h : ℝ)*Real.exp (b*x) := by
    have he : Real.exp (b*(x+h)) = Real.exp (b*x)*Real.exp (b*h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hi := mul_le_mul_of_nonneg_left
      (exp_increment_le hb0 hb3 h.2.1 h.2.2) (Real.exp_pos (b*x)).le
    nlinarith only [hi]
  have hediff2 : (Real.exp (b*(x+h))-Real.exp (b*x))^2 ≤
      (3*Real.exp 3*(h : ℝ)*Real.exp (b*x))^2 :=
    (sq_le_sq₀ hexp0 (by positivity)).mpr hediff
  have he3 : (Real.exp 3)^2 = Real.exp 6 := by
    rw [pow_two,← Real.exp_add]
    norm_num
  have hex : (Real.exp (b*x))^2 = Real.exp ((2*b)*x) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hexminus : (Real.exp (b*x))^2*Real.exp (-x) =
      Real.exp ((2*b-1)*x) := by
    rw [hex,← Real.exp_add]
    congr 1
    ring
  have hefirst : Real.exp ((2*b)*x) ≤ Real.exp x := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2*b-1) hx0]
  have hesecond : Real.exp ((2*b-1)*x) ≤ Real.exp (x/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2*b-3/2) hx0]
  have hfirst : (a*(Real.exp (b*(x+h))-Real.exp (b*x))*
      factorialTailPhase n (x+h))^2 ≤
        (2025*Real.exp 6*(h : ℝ)^2/((n+1 : ℕ) : ℝ))*Real.exp x := by
    calc
      _ = a^2*(Real.exp (b*(x+h))-Real.exp (b*x))^2*
          (factorialTailPhase n (x+h))^2 := by ring
      _ ≤ (225/((n+1 : ℕ) : ℝ))*(3*Real.exp 3*(h : ℝ)*Real.exp (b*x))^2*1 := by
        exact mul_le_mul (mul_le_mul ha hediff2 (sq_nonneg _) (by positivity))
          hphase (sq_nonneg _) (by positivity)
      _ = (2025*Real.exp 6*(h : ℝ)^2/((n+1 : ℕ) : ℝ))*Real.exp ((2*b)*x) := by
        simp only [mul_pow,he3,hex]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hefirst (by positivity)
  have hsecond : (a*Real.exp (b*x)*
      (factorialTailPhase n (x+h)-factorialTailPhase n x))^2 ≤
        6300*(h : ℝ)*Real.exp (x/2) := by
    calc
      _ = a^2*(Real.exp (b*x))^2*
          (factorialTailPhase n (x+h)-factorialTailPhase n x)^2 := by ring
      _ ≤ a^2*(Real.exp (b*x))^2*(28*((n+1 : ℕ) : ℝ)*Real.exp (-x)*(h : ℝ)) :=
        mul_le_mul_of_nonneg_left (phase_shift_sq_le n x h.2.1) (by positivity)
      _ = 28*(a^2*((n+1 : ℕ) : ℝ))*(h : ℝ)*Real.exp ((2*b-1)*x) := by
        rw [← hexminus]
        ring
      _ ≤ 28*225*(h : ℝ)*Real.exp (x/2) := by gcongr
      _ = _ := by ring
  rw [weighted_tail_value n σ (x+h) hxh,weighted_tail_value n σ x hx0]
  change (a*Real.exp (b*(x+h))*factorialTailPhase n (x+h)-
    a*Real.exp (b*x)*factorialTailPhase n x)^2 ≤ _
  have hsplit : a*Real.exp (b*(x+h))*factorialTailPhase n (x+h)-
      a*Real.exp (b*x)*factorialTailPhase n x =
      a*(Real.exp (b*(x+h))-Real.exp (b*x))*factorialTailPhase n (x+h)+
      a*Real.exp (b*x)*(factorialTailPhase n (x+h)-factorialTailPhase n x) := by ring
  rw [hsplit]
  calc
    _ ≤ 2*(a*(Real.exp (b*(x+h))-Real.exp (b*x))*factorialTailPhase n (x+h))^2+
        2*(a*Real.exp (b*x)*(factorialTailPhase n (x+h)-factorialTailPhase n x))^2 := by
      simpa only [sub_neg_eq_add,neg_sq] using square_difference_le
        (a*(Real.exp (b*(x+h))-Real.exp (b*x))*factorialTailPhase n (x+h))
        (-(a*Real.exp (b*x)*(factorialTailPhase n (x+h)-factorialTailPhase n x)))
    _ ≤ 2*((2025*Real.exp 6*(h : ℝ)^2/((n+1 : ℕ) : ℝ))*Real.exp x)+
        2*(6300*(h : ℝ)*Real.exp (x/2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
        (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = _ := by ring

private def interiorEnvelope (n : ℕ) (h x : ℝ) : ℝ :=
  (Iic (0 : ℝ)).indicator (fun y =>
    (4050*Real.exp 6*h^2/((n+1 : ℕ) : ℝ))*Real.exp y+
      12600*h*Real.exp (y/2)) x

private def boundaryEnvelope (n : ℕ) (h x : ℝ) : ℝ :=
  (Ioc (-h) 0).indicator (fun _ => 144/((n+1 : ℕ) : ℝ)) x

private theorem exp_half_integrable :
    IntegrableOn (fun x : ℝ => Real.exp (x/2)) (Iic 0) := by
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1/2) 0

private theorem exp_one_integrable :
    IntegrableOn (fun x : ℝ => Real.exp x) (Iic 0) := by
  simpa only [one_mul] using
    integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) 0

private theorem interiorEnvelope_integrable (n : ℕ) (h : ℝ) :
    Integrable (interiorEnvelope n h) :=
  IntegrableOn.integrable_indicator
    ((exp_one_integrable.const_mul _).add (exp_half_integrable.const_mul _)) measurableSet_Iic

private theorem boundaryEnvelope_integrable (n : ℕ) (h : ℝ) :
    Integrable (boundaryEnvelope n h) :=
  IntegrableOn.integrable_indicator
    (show IntegrableOn (fun _ : ℝ => 144/((n+1 : ℕ) : ℝ)) (Ioc (-h) 0) from
      integrableOn_const (by simp)) measurableSet_Ioc

private theorem translation_sq_le_envelopes (n : ℕ) (σ : FactorialSamplingAbscissa)
    (h : Icc (0 : ℝ) 1) (x : ℝ) :
    (factorialWeightedTail n σ (x+h)-factorialWeightedTail n σ x)^2 ≤
      interiorEnvelope n h x+boundaryEnvelope n h x := by
  have hh0 := h.2.1
  have hN : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by positivity
  have hzero (y : ℝ) (hy : 0 < y) : factorialWeightedTail n σ y = 0 := by
    rw [factorialWeightedTail_eq_phase,indicator_of_notMem
      (show y ∉ Iic (0 : ℝ) from not_le.mpr hy)]
  by_cases hx0 : x ≤ 0
  · rw [interiorEnvelope,indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx0)]
    by_cases hx : x ≤ -(h : ℝ)
    · rw [boundaryEnvelope,indicator_of_notMem
        (show x ∉ Ioc (-(h : ℝ)) 0 from fun hm => not_lt_of_ge hx hm.1),add_zero]
      exact interior_increment_le n σ h x hx
    · have hxmem : x ∈ Ioc (-(h : ℝ)) 0 := ⟨lt_of_not_ge hx,hx0⟩
      rw [boundaryEnvelope,indicator_of_mem hxmem,hzero (x+h) (by linarith)]
      have hsq := factorialWeightedTail_sq_le n σ x
      rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx0)] at hsq
      have he : Real.exp ((2*((σ : ℝ)+1))*x) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        apply mul_nonpos_of_nonneg_of_nonpos _ hx0
        have := σ.2.1
        linarith
      have hflat : (factorialWeightedTail n σ x)^2 ≤ 144/((n+1 : ℕ) : ℝ) :=
        hsq.trans (div_le_div_of_nonneg_right
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 144)) hN)
      have hi0 : 0 ≤ (4050*Real.exp 6*(h : ℝ)^2/((n+1 : ℕ) : ℝ))*Real.exp x+
          12600*(h : ℝ)*Real.exp (x/2) := by positivity
      nlinarith only [hflat,hi0]
  · have hxp : 0 < x := lt_of_not_ge hx0
    rw [hzero x hxp,hzero (x+h) (by linarith),interiorEnvelope,boundaryEnvelope,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx0),
      indicator_of_notMem (show x ∉ Ioc (-(h : ℝ)) 0 from fun hm => hx0 hm.2)]
    norm_num

private theorem interiorEnvelope_integral (n : ℕ) (h : ℝ) :
    (∫ x : ℝ, interiorEnvelope n h x) =
      4050*Real.exp 6*h^2/((n+1 : ℕ) : ℝ)+25200*h := by
  have h1 : (∫ x : ℝ in Iic 0, Real.exp x) = 1 := by
    simpa only [one_mul,mul_zero,Real.exp_zero,div_one] using
      integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) 0
  have h2 : (∫ x : ℝ in Iic 0, Real.exp (x/2)) = 2 := by
    have he := integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 1/2) 0
    norm_num at he
    simpa only [div_eq_mul_inv,mul_comm,one_mul] using he
  unfold interiorEnvelope
  rw [integral_indicator measurableSet_Iic,
    integral_add (exp_one_integrable.const_mul _) (exp_half_integrable.const_mul _),
    integral_const_mul,integral_const_mul,h1,h2]
  ring

private theorem boundaryEnvelope_integral (n : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    (∫ x : ℝ, boundaryEnvelope n h x) = 144*h/((n+1 : ℕ) : ℝ) := by
  unfold boundaryEnvelope
  rw [integral_indicator measurableSet_Ioc,setIntegral_const,
    Real.volume_real_Ioc_of_le (by linarith),smul_eq_mul]
  ring

/-- A fixed constant paying for phase displacement, exponential tilt, and the cutoff jump. -/
def factorialTailTranslationConstant : ℝ := 4050*Real.exp 6+25344

theorem factorialTailTranslationConstant_pos : 0 < factorialTailTranslationConstant := by
  unfold factorialTailTranslationConstant
  positivity

/-- The actual tail has a uniform linear translation budget, including its endpoint jump. -/
theorem factorialTailTranslationEnergy_le_linear (n : ℕ)
    (σ : FactorialSamplingAbscissa) (h : Icc (0 : ℝ) 1) :
    factorialTailTranslationEnergy n σ h ≤ factorialTailTranslationConstant*(h : ℝ) := by
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n+1 by omega)
  have hh0 := h.2.1
  have hh1 := h.2.2
  have hfrac : (h : ℝ)^2/((n+1 : ℕ) : ℝ) ≤ (h : ℝ) := by
    apply (div_le_iff₀ hN).mpr
    nlinarith only [mul_nonneg hh0 (sub_nonneg.mpr hh1),
      mul_nonneg hh0 (sub_nonneg.mpr hN1)]
  have hfrac1 : (h : ℝ)/((n+1 : ℕ) : ℝ) ≤ (h : ℝ) := by
    apply (div_le_iff₀ hN).mpr
    nlinarith only [mul_nonneg hh0 (sub_nonneg.mpr hN1)]
  have hfirst : 4050*Real.exp 6*(h : ℝ)^2/((n+1 : ℕ) : ℝ) ≤
      4050*Real.exp 6*(h : ℝ) := by
    calc
      _ = (4050*Real.exp 6)*((h : ℝ)^2/((n+1 : ℕ) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfrac (by positivity)
  have hboundary : 144*(h : ℝ)/((n+1 : ℕ) : ℝ) ≤ 144*(h : ℝ) := by
    calc
      _ = 144*((h : ℝ)/((n+1 : ℕ) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfrac1 (by norm_num)
  unfold factorialTailTranslationEnergy
  calc
    _ ≤ ∫ x : ℝ, interiorEnvelope n h x+boundaryEnvelope n h x :=
      integral_mono (factorialTailTranslation_sq_integrable n σ h)
        ((interiorEnvelope_integrable n h).add (boundaryEnvelope_integrable n h))
        (translation_sq_le_envelopes n σ h)
    _ = 4050*Real.exp 6*(h : ℝ)^2/((n+1 : ℕ) : ℝ)+25200*(h : ℝ)+
        144*(h : ℝ)/((n+1 : ℕ) : ℝ) := by
      rw [integral_add (interiorEnvelope_integrable n h) (boundaryEnvelope_integrable n h),
        interiorEnvelope_integral,boundaryEnvelope_integral n h hh0]
    _ ≤ 4050*Real.exp 6*(h : ℝ)+25200*(h : ℝ)+144*(h : ℝ) :=
      add_le_add (add_le_add hfirst le_rfl) hboundary
    _ = _ := by
      unfold factorialTailTranslationConstant
      ring

/-- The change from linear to mass control occurs at the arithmetic scale `1/(n+1)`. -/
theorem factorialTailTranslationEnergy_le_min (n : ℕ)
    (σ : FactorialSamplingAbscissa) (h : Icc (0 : ℝ) 1) :
    factorialTailTranslationEnergy n σ h ≤
      factorialTailTranslationConstant*min (1/((n+1 : ℕ) : ℝ)) (h : ℝ) := by
  by_cases hscale : 1/((n+1 : ℕ) : ℝ) ≤ (h : ℝ)
  · rw [min_eq_left hscale]
    have hC : 384 ≤ factorialTailTranslationConstant := by
      unfold factorialTailTranslationConstant
      have := (Real.exp_pos 6).le
      linarith
    calc
      _ ≤ 384/((n+1 : ℕ) : ℝ) := factorialTailTranslationEnergy_le_mass n σ h
      _ ≤ factorialTailTranslationConstant/((n+1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hC (by positivity)
      _ = _ := by ring
  · rw [min_eq_right (le_of_not_ge hscale)]
    exact factorialTailTranslationEnergy_le_linear n σ h

end
end GaloisForLFunctions.ArithmeticPositivityTheory
