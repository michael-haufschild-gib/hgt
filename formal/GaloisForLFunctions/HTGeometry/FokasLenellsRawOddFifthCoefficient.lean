import GaloisForLFunctions.HTGeometry.FokasLenellsRawOddCoefficientParity
import GaloisForLFunctions.HTGeometry.FokasLenellsRawQuinticMoments

/-!
# Evaluated genuine fifth scattering coefficient for odd profiles

All nonlinear terms cancel in the whole-line symmetrization. Both lower
endpoint corrections vanish for odd data, so the surviving spatial first
moment is the coefficient of the actual scattering matrix.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Both oriented fifth endpoints combine into the actual full-line fifth integrand. -/
theorem rawFifthEndpoint_difference (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    rawFifthEndpoint q k v false-rawFifthEndpoint q k v true = ∫ x : ℝ, rawFifthIntegrand q k v x := by
  have hh := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (b := (0 : ℝ))
    (rawFifthIntegrand_integrable q k v).integrableOn (rawFifthIntegrand_integrable q k v).integrableOn
  unfold rawFifthEndpoint rawOrientedFifthIntegrand
  simp only [Bool.false_eq_true,↓reduceIte,integral_neg,integral_comp_neg_Ioi,neg_zero,sub_neg_eq_add]
  simpa only [add_comm] using hh

/-- The actual fifth integrand has an evaluated full-line lower component on odd projected data. -/
theorem integral_rawFifthIntegrand_oddInitialPart_lower (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, (rawFifthIntegrand (oddInitialPart q) 0 (1,0) x).2) =
      4*I*∫ x : ℝ, (x : ℂ)*oddInitialPart q x := by
  have hi : Integrable (fun x : ℝ => (rawFifthIntegrand (oddInitialPart q) 0 (1,0) x).2) :=
    (rawFifthIntegrand_integrable (oddInitialPart q) 0 (1,0)).snd
  have hs := integral_add hi hi.comp_neg
  have he : (fun x : ℝ => (rawFifthIntegrand (oddInitialPart q) 0 (1,0) x).2+
      (rawFifthIntegrand (oddInitialPart q) 0 (1,0) (-x)).2) =
      fun x : ℝ => (I/12)*((oddInitialPart q x)^(4 : ℕ)*deriv (oddInitialPart q) x)-
        (4*I)*((x : ℂ)^(2 : ℕ)*deriv (oddInitialPart q) x) := by
    funext x
    rw [rawFifthIntegrand_oddInitialPart_symmetrization]
    ring
  change (∫ x : ℝ, (rawFifthIntegrand (oddInitialPart q) 0 (1,0) x).2+
    (rawFifthIntegrand (oddInitialPart q) 0 (1,0) (-x)).2) = _ at hs
  rw [he,integral_sub ((integrable_quartic_derivative (oddInitialPart q)).const_mul _)
    ((integrable_coordinate_sq_derivative (oddInitialPart q)).const_mul _),
    integral_const_mul,integral_const_mul,integral_quartic_derivative,
    integral_coordinate_sq_derivative,
    integral_neg_eq_self (fun x : ℝ => (rawFifthIntegrand (oddInitialPart q) 0 (1,0) x).2) volume] at hs
  linear_combination -(1/2 : ℂ)*hs

/-- No lower endpoint cross-products survive for odd data. -/
theorem rawScatteringFifthCoefficient_oddInitialPart_lower_integral (q : SchwartzMap ℝ ℂ) :
    rawScatteringFifthCoefficient (oddInitialPart q) 1 0 =
      ∫ x : ℝ, (rawFifthIntegrand (oddInitialPart q) 0 (1,0) x).2 := by
  have hh := congrArg Prod.snd (rawFifthEndpoint_difference (oddInitialPart q) 0 (1,0))
  simp only [Prod.snd_sub,snd_integral (rawFifthIntegrand_integrable (oddInitialPart q) 0 (1,0))] at hh
  simp only [rawScatteringFifthCoefficient,rawScatteringFifthRemainder,
    rawFirstCoefficientMatrix_oddInitialPart,rawQuadraticEndpointMatrix_oddInitialPart,
    Complex.ofReal_zero,zero_smul,zero_pow (by omega : 2 ≠ 0),
    zero_pow (by omega : 3 ≠ 0),zero_pow (by omega : 4 ≠ 0),zero_pow (by omega : 5 ≠ 0),
    zero_mul,mul_zero,add_zero,sub_zero]
  simpa [rawQuinticEndpointMatrix,Matrix.adjugate_fin_two,sub_eq_add_neg] using hh

/-- The actual fifth reflection coefficient on the entire odd subspace is the linear spatial first moment. -/
theorem rawScatteringFifthCoefficient_oddInitialPart_lower (q : SchwartzMap ℝ ℂ) :
    rawScatteringFifthCoefficient (oddInitialPart q) 1 0 = 4*I*∫ x : ℝ, (x : ℂ)*q x := by
  rw [rawScatteringFifthCoefficient_oddInitialPart_lower_integral,
    integral_rawFifthIntegrand_oddInitialPart_lower,integral_coordinate_oddInitialPart]

/-- Odd projections of Schwartz derivatives have an exact fifth coefficient determined by mass. -/
theorem rawScatteringFifthCoefficient_oddDerivative_lower (q : SchwartzMap ℝ ℂ) :
    rawScatteringFifthCoefficient (oddInitialPart (SchwartzMap.derivCLM ℂ ℂ q)) 1 0 =
      -4*I*∫ x : ℝ, q x := by
  rw [rawScatteringFifthCoefficient_oddInitialPart_lower]
  simp only [SchwartzMap.derivCLM_apply,integral_coordinate_derivative]
  ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
