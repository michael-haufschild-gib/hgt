import GaloisForLFunctions.ExceptionalLayerTheory.IntegerCancellationOnMiddleDivisorIntervals
import GaloisForLFunctions.ExceptionalLayerTheory.TheCompletedCofactorRowRetainsThePrimeError
import GaloisForLFunctions.BiScaleUncertainty.CenteredRamanujanVarianceAndAbelCofactorCancellation
import GaloisForLFunctions.RHTower.DivisorHyperbolaAbelBound
import GaloisForLFunctions.RHTower.SelbergSymmetryCore

/-!
# A power saving in the complete divisor error

The centered modular ramps differ from centered reciprocal fractional
parts by a harmonic term. The smooth hyperbola boundary is logarithmic.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem divisor_defect_eq (N : ℕ) :
    completeDivisorError N+2*Real.eulerMascheroniConstant*N =
      divisorHyperbolaSmoothRemainder N+2*centeredDivisorHyperbola N := by
  rw [divisorHyperbolaSmooth_add_centered,←floorSummatory_chebyshevPsi]
  unfold completeDivisorError floorSummatory
  simp only [sum_sub_distrib,chebyshevPsi_eq_psi]

private theorem hyperbola_ramps (N : ℕ) :
    2*centeredDivisorHyperbola N =
      2*(∑ d ∈ Icc 1 (Nat.sqrt N), centeredQuotient N d 1)+((harmonic (Nat.sqrt N) : ℚ) : ℝ) := by
  have eq (d : ℕ) (hd : d ∈ Icc 1 (Nat.sqrt N)) :
      2*HTGeometry.centeredModularRamp d N=2*centeredQuotient N d 1+(d : ℝ)⁻¹ := by
    have h := (mem_Icc.mp hd).1
    have h₀ : (d : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt h
    rw [HTGeometry.centeredModularRamp,centeredQuotient,Nat.cast_one,div_one,
      GaloisForLFunctions.BiScaleUncertainty.int_fract_natCast_div_eq_mod_div h]
    field_simp; ring
  rw [centeredDivisorHyperbola,mul_sum,sum_congr rfl eq,sum_add_distrib,←mul_sum,sum_inv_Icc_eq_ratCast_harmonic]

/-- Uniform pointwise power saving after removing the full linear divisor mean. -/
theorem complete_divisor_error_power :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, |completeDivisorError n+2*Real.eulerMascheroniConstant*n| ≤
      C*(n : ℝ)^(99/200 : ℝ) := by
  obtain ⟨K,hK,h⟩ := sum_centered_quotient_to_sqrt
  refine ⟨200*(9+2*K),by positivity,?_⟩
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [completeDivisorError,Real.zero_rpow (by norm_num : (99/200 : ℝ)≠0)]
  let J := 1+Real.log n
  let P := (n : ℝ)^(49/100 : ℝ)
  let s := Nat.sqrt n
  let H := ((harmonic s : ℚ) : ℝ)
  let F := ∑ d ∈ Icc 1 s, centeredQuotient n d 1
  have hn₁ : (1 : ℝ)≤n := by exact_mod_cast hn
  have hn₀ := zero_lt_one.trans_le hn₁
  have hJ : 1≤J := le_add_of_nonneg_right (Real.log_natCast_nonneg _)
  have hP : 1≤P := Real.one_le_rpow hn₁ (by norm_num)
  have hJ' := le_mul_of_one_le_right (zero_le_one.trans hJ) hP
  have hH : |H|≤J := by
    have hs := Nat.le_sqrt.mpr (by simpa using hn : 1*1≤n)
    have hh : 0≤H := by
      dsimp only [H]; rw [←sum_inv_Icc_eq_ratCast_harmonic]
      exact sum_nonneg fun d _ => inv_nonneg.mpr (Nat.cast_nonneg d)
    rw [abs_of_nonneg hh]
    exact (harmonic_le_one_add_log s).trans (add_le_add_left (Real.log_le_log
      (by exact_mod_cast hs : (0 : ℝ) < s) (by exact_mod_cast Nat.sqrt_le_self n)) 1)
  have hS : |divisorHyperbolaSmoothRemainder n|≤8*J := by
    apply (abs_divisorHyperbolaSmoothRemainder_le hn).trans
    have hl := Real.log_le_log (by positivity : (0 : ℝ)<(n : ℝ)+1)
      (show (n : ℝ)+1≤2*n by linarith only [hn₁])
    rw [Real.log_mul (by norm_num) hn₀.ne'] at hl
    dsimp [J]
    linarith only [hl,Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2),Real.log_natCast_nonneg n]
  have hF : |2*F|≤2*(K*J*P) := by
    rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
    exact mul_le_mul_of_nonneg_left (h hn) (by norm_num)
  have hmain : |completeDivisorError n+2*Real.eulerMascheroniConstant*n|≤(9+2*K)*(J*P) := by
    rw [divisor_defect_eq,hyperbola_ramps]
    apply (abs_add_le _ _).trans ((add_le_add hS ((abs_add_le _ _).trans (add_le_add hF hH))).trans _)
    linarith only [hJ']
  let e : ℝ := 1/200
  have he : 0<e := by norm_num [e]
  have hlog : J≤200*(n : ℝ)^e := by
    have ht := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn₀ e)
    rw [Real.log_rpow hn₀] at ht
    dsimp [e,J] at ht ⊢; linarith only [ht]
  have hp : (n : ℝ)^e*P=(n : ℝ)^(99/200 : ℝ) := by
    dsimp only [P]; rw [←Real.rpow_add hn₀]; norm_num [e]
  apply hmain.trans
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlog (zero_le_one.trans hP))
    (show 0≤9+2*K by positivity)
  rw [←hp]; linarith only [hh]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
