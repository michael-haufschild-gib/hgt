import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineEnergyGap
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalCausalEnergyTranslation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineGroundEnergy
import GaloisForLFunctions.HTGeometry.Analysis.LinearCumulativeLaplaceBound

/-!
# Linear square mass at the critical state's terminal wall

The transverse spectral gap bounds the orthogonal residual of a causal
translate. Reversing the two unit vectors preserves the residual's square
norm and exposes the original state on the terminal interval. The exact
translation-energy identity therefore gives a linear bound for its mass.
Fubini and Cauchy–Schwarz turn this into inverse-linear decay of its
positive-real Laplace transform.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry

/-- The transverse gap bounds the square mass exposed by moving the terminal wall. -/
theorem criticalState_terminal_mass_exponential_bound {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 ≤ h →
      δ * (∫ u in Ioo (-h) 0, F u ^ 2) ≤
        criticalAliasCoefficient W₀ * criticalHalfLineExponentialPair F F *
          (Real.exp (8*h)-1) := by
  obtain ⟨δ,hδ,hgap⟩ := criticalHalfLineFullEnergy_transverse_L2_gap hW ht hF
  refine ⟨δ,hδ,fun h hh => ?_⟩
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hT := hd.causalTranslate hh
  have hmass : (∫ u, F u ^ 2) = 1 := hF.2.2.2.1
  have hTmass : (∫ u, F (u+h) ^ 2) = 1 := by
    rw [integral_add_right_eq_self (fun u => F u ^ 2) h,hmass]
  let c : ℝ := ∫ u, F u * F (u+h)
  have hcross : Integrable (fun u => F u * F (u+h)) :=
    integrable_mul_of_sq_integrable hd.meas.aestronglyMeasurable
      hT.meas.aestronglyMeasurable hd.sq hT.sq
  have hG := hT.add_const_mul hd (-c)
  have hJ := hd.add_const_mul hT (-c)
  have horth : (∫ u, F u*(F (u+h)+(-c)*F u)) = 0 := by
    have he : (fun u => F u*(F (u+h)+(-c)*F u)) =
        fun u => F u*F (u+h)-c*(F u^2) := funext fun u => by ring
    rw [he,integral_sub hcross (hd.sq.const_mul c),integral_const_mul,hmass]
    change c-c*1=0
    ring
  -- Reversing the residual exposes the wall without dividing by the correlation.
  have hequal : (∫ u, (F u+(-c)*F (u+h))^2) =
      ∫ u, (F (u+h)+(-c)*F u)^2 := by
    have hcomm : (∫ u, F u * F (u+h)) = ∫ u, F (u+h) * F u := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => mul_comm _ _
    rw [criticalHalfLine_square_mass_add_const_mul hd hT,
      criticalHalfLine_square_mass_add_const_mul hT hd,hmass,hTmass]
    rw [hcomm]
  have hterminal : (∫ u in Ioo (-h) 0, F u^2) ≤
      ∫ u, (F u+(-c)*F (u+h))^2 := by
    have he : (∫ u in Ioo (-h) 0, F u^2) =
        ∫ u in Ioo (-h) 0, (F u+(-c)*F (u+h))^2 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      have hz : F (u+h)=0 := hd.support _ (by linarith only [hu.1])
      change F u ^ 2 = (F u + -c * F (u+h)) ^ 2
      rw [hz,mul_zero,add_zero]
    rw [he]
    exact setIntegral_le_integral hJ.sq (Eventually.of_forall fun u => sq_nonneg _)
  have henergy := criticalHalfLineFullEnergy_causal_ground_shear hW ht hF hd hh (-c)
  rw [criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF,zero_add] at henergy
  calc
    δ*(∫ u in Ioo (-h) 0,F u^2) ≤ δ*(∫ u,(F u+(-c)*F (u+h))^2) :=
      mul_le_mul_of_nonneg_left hterminal hδ.le
    _ = δ*(∫ u,(F (u+h)+(-c)*F u)^2) := by rw [hequal]
    _ ≤ criticalHalfLineFullEnergy W₀ (fun u => F (u+h)+(-c)*F u) := hgap hG horth
    _ = _ := by rw [henergy]; ring

private theorem exp_eight_sub_one_le {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    Real.exp (8*h)-1 ≤ (8*Real.exp 8)*h := by
  have hx := Real.add_one_le_exp (-(8*h))
  have hm := mul_le_mul_of_nonneg_right hx (Real.exp_pos (8*h)).le
  have he : Real.exp (-(8*h))*Real.exp (8*h)=1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  rw [he] at hm
  have hb : Real.exp (8*h) ≤ Real.exp 8 :=
    Real.exp_le_exp.mpr (by linarith only [h1])
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 8*h by positivity)
  nlinarith only [hm,hb']

/-- Every actual critical state has uniformly bounded average square mass at the wall. -/
theorem criticalState_terminal_square_mass_linear {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h →
      (∫ u in Ioo (-h) 0,F u^2) ≤ C*h := by
  obtain ⟨δ,hδ,hbound⟩ := criticalState_terminal_mass_exponential_bound hW ht hF
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hm : 0 ≤ criticalHalfLineExponentialPair F F := by
    rw [criticalHalfLineExponentialPair_self]
    exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  let K : ℝ := criticalAliasCoefficient W₀*criticalHalfLineExponentialPair F F/δ
  have hK : 0 ≤ K := div_nonneg (mul_nonneg ha.le hm) hδ.le
  refine ⟨1+K*(8*Real.exp 8),by positivity,fun h hh => ?_⟩
  by_cases h1 : h ≤ 1
  · have hb : (∫ u in Ioo (-h) 0,F u^2) ≤ K*(Real.exp (8*h)-1) := by
      calc
        _ ≤ (criticalAliasCoefficient W₀ * criticalHalfLineExponentialPair F F *
            (Real.exp (8*h)-1)) / δ := (le_div_iff₀ hδ).mpr (by
          simpa only [mul_comm] using hbound h hh.le)
        _ = _ := by dsimp only [K]; ring
    have he := mul_le_mul_of_nonneg_left (exp_eight_sub_one_le hh.le h1) hK
    calc
      (∫ u in Ioo (-h) 0,F u^2) ≤ K*(Real.exp (8*h)-1) := hb
      _ ≤ K*((8*Real.exp 8)*h) := he
      _ ≤ (1+K*(8*Real.exp 8))*h := by nlinarith only [hh]
  · have hsmall : (∫ u in Ioo (-h) 0,F u^2) ≤ 1 := by
      have hb := setIntegral_le_integral (s := Ioo (-h) 0) hd.sq
        (Eventually.of_forall fun u => sq_nonneg (F u))
      rwa [hF.2.2.2.1] at hb
    have hlarge : 1 ≤ (1+K*(8*Real.exp 8))*h := by
      have hp : 0 ≤ K*(8*Real.exp 8) := by positivity
      nlinarith only [hp,hh,not_le.mp h1]
    exact hsmall.trans hlarge

/-- The same constant controls terminal square mass and positive-real Laplace decay. -/
theorem criticalState_wall_and_laplace_bounds {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ C : ℝ, 0 < C ∧
      (∀ h : ℝ, 0 < h → (∫ u in Ioo (-h) 0, F u ^ 2) ≤ C*h) ∧
      (∀ t : ℝ, 0 < t → ‖negativeHalfLineLaplace (cx F) (t : ℂ)‖ ≤ Real.sqrt C/t) := by
  obtain ⟨C, hC, hbound⟩ := criticalState_terminal_square_mass_linear hW ht hF
  refine ⟨C, hC, hbound, fun t ht => ?_⟩
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  rw [negativeHalfLineLaplace_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have he : (fun u => F u * Real.exp (t*u)) =
      (Iio 0).indicator (fun u => F u * Real.exp (t*u)) := by
    funext u
    by_cases hu : u < 0
    · rw [indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu)]
    · rw [indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu),
        hd.support u (le_of_not_gt hu), zero_mul]
  calc
    _ = |∫ u in Iio 0, F u * Real.exp (t*u)| := by
      congr 1
      conv_lhs => rw [he, integral_indicator measurableSet_Iio]
    _ ≤ _ := abs_integral_exp_mul_Iio_le_of_terminal_square_mass hd.meas hd.sq.restrict
      hC.le hbound ht

/-- Either RH holds, or its critical state obeys both boundary and transform bounds. -/
theorem riemannHypothesis_or_criticalState_wall_and_laplace_bounds :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∃ C : ℝ, 0 < C ∧
        (∀ h : ℝ, 0 < h → (∫ u in Ioo (-h) 0, F u ^ 2) ≤ C*h) ∧
        (∀ t : ℝ, 0 < t → ‖negativeHalfLineLaplace (cx F) (t : ℂ)‖ ≤ Real.sqrt C/t) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀, F, hW, ht, hF, criticalState_wall_and_laplace_bounds hW ht hF⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
