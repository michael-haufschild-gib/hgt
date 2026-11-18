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

#print axioms early_positivePrimeDetector_mass_le
#print axioms dominated_integral_le_signed_mass
end GaloisForLFunctions.ExclusionOfTheCriticalState
