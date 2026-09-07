import GaloisForLFunctions.HTGeometry.PolynomialODEEvenSeamJets
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenSeamDeterminant
import GaloisForLFunctions.RHTower.ThetaCuspEvenFourCompensation

/-! # Literal complete theta seam jets through derivative twelve -/
namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- Every required even derivative of the complete source is its exact modular seam polynomial. -/
theorem thetaCuspFullSource_even_seamJet_eq_polynomial (k : Fin 7) :
    iteratedDeriv (2*k.val) thetaCuspFullSource 0 =
      thetaCuspSelfDualThetaMass * HTGeometry.modularThetaEvenSeamSourcePolynomial k
        (thetaCuspSelfDualModularScale^2) := by
  have h := thetaCuspFullSource_seamJet_eq_formalJet (2*k.val)
  rw [HTGeometry.eval_modularThetaODESourceJet_even_seam] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul]
  rw [h]
  congr 1
  fin_cases k <;> norm_num [HTGeometry.modularThetaEvenSeamSourcePolynomial]

/-- All seven reflected signed seam moments retain the literal infinite source. -/
theorem thetaCuspNativeEvenMoment_zero_eq_polynomial (k : Fin 7) :
    (-1 : ℝ)^k.val*thetaCuspNativeReflectionJet (2*k.val) 0 =
      thetaCuspSelfDualThetaMass^2 * HTGeometry.modularThetaEvenSeamMomentPolynomial k
        (thetaCuspSelfDualModularScale^2) := by
  have h0 := thetaCuspFullSource_even_seamJet_eq_polynomial (0 : Fin 7)
  have h2 := thetaCuspFullSource_even_seamJet_eq_polynomial (1 : Fin 7)
  have h4 := thetaCuspFullSource_even_seamJet_eq_polynomial (2 : Fin 7)
  have h6 := thetaCuspFullSource_even_seamJet_eq_polynomial (3 : Fin 7)
  have h8 := thetaCuspFullSource_even_seamJet_eq_polynomial (4 : Fin 7)
  have h10 := thetaCuspFullSource_even_seamJet_eq_polynomial (5 : Fin 7)
  have h12 := thetaCuspFullSource_even_seamJet_eq_polynomial (6 : Fin 7)
  norm_num at h0 h2 h4 h6 h8 h10 h12
  have h1 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 1) (by norm_num : Odd 1)
  have h3 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 3) (by norm_num : Odd 3)
  have h5 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 5) (by norm_num : Odd 5)
  have h7 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 7) (by norm_num : Odd 7)
  have h9 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 9) (by norm_num : Odd 9)
  have h11 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 11) (by norm_num : Odd 11)
  fin_cases k <;>
    norm_num [thetaCuspNativeReflectionJet_eq, Finset.sum_range_succ, Nat.choose,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      HTGeometry.modularThetaEvenSeamSourcePolynomial, HTGeometry.modularThetaEvenSeamMomentPolynomial] <;> ring

end
end RHTower
