import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheRightZeroDetectorAfterConvolutionWithTheState

/-!
# Localizing the positive prime detector

At a logarithmic cutoff T, its weight at t is at most
exp(−(1/2−κ)(T−t))/κ. Against a wave of growth exp((1/2+κ)t) the
early integral up to ηT therefore costs exp((η−1/2+κ)T).
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Absorb the linear factor of the positive logarithmic weight. -/
theorem positivePrimeDetector_le_exp {κ : ℝ} (hκ : 0 < κ) (v : ℝ) :
    positivePrimeDetector v ≤ κ⁻¹*Real.exp (-((1/2-κ)*v)) := by
  apply (positivePrimeDetector_upper v).trans
  rcases le_total 0 v with hv | hv
  · rw [max_eq_left hv,show -((1/2-κ)*v) = -v/2+κ*v by ring,Real.exp_add,mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    rw [← div_eq_inv_mul,le_div_iff₀ hκ]
    linarith only [Real.add_one_le_exp (κ*v)]
  · rw [max_eq_right hv,mul_zero]; positivity

/-- Early signed mass is bounded in absolute value without cancellation. -/
theorem early_positivePrimeDetector_mass_le {V : ℝ → ℝ} {A κ : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A)
    (hb : ∀ t : ℝ, |V t| ≤ A*Real.exp ((1/2+κ)*t)) (η T : ℝ) :
    (∫ t in Iic (η*T), |V t|*positivePrimeDetector (T-t)) ≤
      (A*κ⁻¹)*Real.exp ((η-1/2+κ)*T) := by
  let C := A*κ⁻¹*Real.exp (-((1/2-κ)*T))
  have he (t : ℝ) : (A*Real.exp ((1/2+κ)*t))*(κ⁻¹*Real.exp (-((1/2-κ)*(T-t)))) =
      C*Real.exp t := by
    calc _ = (A*κ⁻¹)*Real.exp ((1/2+κ)*t-((1/2-κ)*(T-t))) := by rw [sub_eq_add_neg,Real.exp_add]; ring
      _ = _ := by rw [show (1/2+κ)*t-((1/2-κ)*(T-t)) = -((1/2-κ)*T)+t by ring,Real.exp_add]; dsimp only [C]; ring
  have hi : IntegrableOn (fun t : ℝ => C*Real.exp t) (Iic (η*T)) := (integrableOn_exp_Iic _).const_mul C
  calc _ ≤ ∫ t in Iic (η*T), C*Real.exp t := by
         apply integral_mono_of_nonneg (Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) (positivePrimeDetector_nonneg _)) hi
         exact Eventually.of_forall fun t => (mul_le_mul (hb t) (positivePrimeDetector_le_exp hκ _)
           (positivePrimeDetector_nonneg _) (mul_nonneg hA (Real.exp_pos _).le)).trans_eq (he t)
    _ = _ := by
         rw [integral_const_mul,integral_exp_Iic]
         dsimp only [C]; rw [mul_assoc,← Real.exp_add]; congr 2; ring

/-- For an integrable real wave with a positive weight, its signed mean
bounds the difference between the two sign masses, while a dominated
complex test bounds their sum from below. -/
theorem dominated_integral_le_signed_mass {V J : ℝ → ℝ} {H : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hJ : ∀ t, 0 ≤ J t) (hJV : Integrable fun t => V t*J t)
    (hH : Integrable fun t => (V t:ℂ)*H t) (hdom : ∀ t, ‖H t‖ ≤ C*J t)
    {s : ℝ} (hs : s=1 ∨ s= -1) :
    ‖∫ t, (V t:ℂ)*H t‖ ≤ C*(2*(∫ t, max (s*V t) 0*J t)+|∫ t, V t*J t|) := by
  let f := fun t : ℝ => V t*J t
  have hpoint (t : ℝ) : |f t|+s*f t=2*(max (s*V t) 0*J t) := by
    change |V t*J t|+s*(V t*J t)=_
    rw [abs_mul,abs_of_nonneg (hJ t)]
    rcases hs with rfl | rfl <;> rcases le_total 0 (V t) with ht | ht <;>
      simp [abs_of_nonneg,abs_of_nonpos,ht,neg_nonneg.mpr,neg_nonpos.mpr]
    all_goals ring
  have he : (∫ t, |f t|)+s*(∫ t, f t)=2*(∫ t, max (s*V t) 0*J t) := by
    rw [← integral_const_mul,← integral_add hJV.abs (hJV.const_mul s),← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hpoint)
  have hCauchy : ‖∫ t, (V t:ℂ)*H t‖ ≤ C*(∫ t, |f t|) := by
    rw [← integral_const_mul]
    apply norm_integral_le_integral_norm.trans
    apply integral_mono hH.norm (hJV.abs.const_mul C)
    intro t
    change ‖(V t:ℂ)*H t‖ ≤ C*|V t*J t|
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hJ t),mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hdom t) (abs_nonneg _)
  apply hCauchy.trans (mul_le_mul_of_nonneg_left _ hC)
  change (∫ t, |f t|) ≤ 2*(∫ t, max (s*V t) 0*J t)+|∫ t, f t|
  rcases hs with rfl | rfl
  · linarith only [he,neg_le_abs (∫ t, f t)]
  · linarith only [he,le_abs_self (∫ t, f t)]

/-- Only the early weighted mass and the unweighted mass on the remaining
finite interval can contribute to a positive sign observation. -/
theorem positivePrimeDetector_sign_split {V : ℝ → ℝ} {a T s : ℝ} (hs : s=1 ∨ s= -1)
    (hJV : Integrable (fun t : ℝ => V t*positivePrimeDetector (T-t)))
    (hi : IntegrableOn (fun t : ℝ => max (s*V t) 0) (Ioc a T)) :
    (∫ t, max (s*V t) 0*positivePrimeDetector (T-t)) ≤
      (∫ t in Iic a, |V t|*positivePrimeDetector (T-t))+2*(∫ t in Ioc a T, max (s*V t) 0) := by
  let J := fun t : ℝ => positivePrimeDetector (T-t)
  let f := fun t : ℝ => |V t|*J t
  let g := fun t : ℝ => max (s*V t) 0
  have hfj : Integrable f := hJV.abs.congr (Eventually.of_forall fun t => by
    change |V t*J t|=|V t|*J t; rw [abs_mul,abs_of_nonneg (positivePrimeDetector_nonneg _)])
  have hf := hfj.indicator (measurableSet_Iic (a := a))
  have hg : Integrable ((Ioc a T).indicator g) := (integrable_indicator_iff measurableSet_Ioc).2 hi
  have hg0 (t : ℝ) : 0 ≤ g t := le_max_right _ _
  have hgb (t : ℝ) : g t ≤ |V t| := by
    apply max_le _ (abs_nonneg _)
    rcases hs with rfl | rfl <;> simp only [one_mul,neg_one_mul]
    · exact le_abs_self _
    · exact neg_le_abs _
  have h := integral_mono_of_nonneg (f := fun t : ℝ => g t*J t)
    (Eventually.of_forall fun t => mul_nonneg (hg0 t) (positivePrimeDetector_nonneg _))
    (hf.add (hg.const_mul 2)) (Eventually.of_forall fun t => by
      change g t*J t ≤ (Iic a).indicator f t+2*(Ioc a T).indicator g t
      by_cases ht : t ≤ a
      · rw [indicator_of_mem (show t ∈ Iic a from ht),indicator_of_notMem (show t ∉ Ioc a T from fun h => h.1.not_ge ht),mul_zero,add_zero]
        exact mul_le_mul_of_nonneg_right (hgb t) (positivePrimeDetector_nonneg _)
      rw [indicator_of_notMem (show t ∉ Iic a from ht),zero_add]
      by_cases hT : t ≤ T
      · rw [indicator_of_mem (show t ∈ Ioc a T from ⟨lt_of_not_ge ht,hT⟩),mul_comm (2:ℝ)]
        exact mul_le_mul_of_nonneg_left (positivePrimeDetector_le_two _) (hg0 t)
      have hz : J t=0 := le_antisymm ((positivePrimeDetector_upper _).trans_eq (by
        rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hT)),mul_zero])) (positivePrimeDetector_nonneg _)
      rw [hz,mul_zero,indicator_of_notMem (show t ∉ Ioc a T from fun h => hT h.2),mul_zero])
  change (∫ t, g t*J t) ≤ ∫ t, (Iic a).indicator f t+2*(Ioc a T).indicator g t at h
  rwa [integral_add hf (hg.const_mul 2),integral_const_mul,integral_indicator measurableSet_Iic,integral_indicator measurableSet_Ioc] at h

/-- A smaller exponential and a bounded remainder together fit below any
fixed positive multiple of a larger, growing exponential. -/
theorem eventually_absorb_detector_remainders {a b m : ℝ} (hb : 0 < b) (hab : a < b) (hm : 0 < m)
    (K L : ℝ) : ∀ᶠ T : ℝ in atTop, K+L*Real.exp (a*T) ≤ m*Real.exp (b*T) := by
  have hz {c : ℝ} (hc : c < 0) : Tendsto (fun T : ℝ => Real.exp (c*T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hc).2 tendsto_id)
  have h := (tendsto_const_nhds (x := K)).mul (hz (neg_lt_zero.2 hb))
  have h' := h.add ((tendsto_const_nhds (x := L)).mul (hz (sub_neg.2 hab)))
  simp only [mul_zero,add_zero] at h'
  filter_upwards [h'.eventually_lt_const hm] with T hT
  change K*Real.exp (-b*T)+L*Real.exp ((a-b)*T)<m at hT
  have he : (K*Real.exp (-b*T)+L*Real.exp ((a-b)*T))*Real.exp (b*T)=K+L*Real.exp (a*T) := by
    rw [add_mul,mul_assoc,mul_assoc,← Real.exp_add,← Real.exp_add]
    rw [show -b*T+b*T=0 by ring,show (a-b)*T+b*T=a*T by ring,Real.exp_zero,mul_one]
  exact he.ge.trans (mul_le_mul_of_nonneg_right hT.le (Real.exp_pos _).le)

#print axioms early_positivePrimeDetector_mass_le
#print axioms dominated_integral_le_signed_mass
end GaloisForLFunctions.ExclusionOfTheCriticalState
