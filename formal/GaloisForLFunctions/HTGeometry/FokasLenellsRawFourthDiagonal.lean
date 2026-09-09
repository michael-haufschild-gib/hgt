import GaloisForLFunctions.HTGeometry.FokasLenellsRawScatteringFifth

/-!
# Fourth order contributes only to transmission

The actual third primitive is off diagonal at zero frequency. Consequently
the fourth integrand and both fourth endpoint coefficients are diagonal.
The true fourth scattering coefficient has no reflection entries.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem rawThirdSlope_zero_diagonal (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (rawThirdSlope q 0 (1,0) x).1 = 0 ∧ (rawThirdSlope q 0 (0,1) x).2 = 0 := by
  have h1 := (ContinuousLinearMap.fst ℂ ℂ ℂ).intervalIntegral_comp_comm
    ((rawThirdIntegrand_integrable q 0 (1,0)).intervalIntegrable (a := 0) (b := x))
  have h2 := (ContinuousLinearMap.snd ℂ ℂ ℂ).intervalIntegral_comp_comm
    ((rawThirdIntegrand_integrable q 0 (0,1)).intervalIntegrable (a := 0) (b := x))
  change (∫ s in (0 : ℝ)..x, (rawThirdIntegrand q 0 (1,0) s).1) = (rawThirdSlope q 0 (1,0) x).1 at h1
  change (∫ s in (0 : ℝ)..x, (rawThirdIntegrand q 0 (0,1) s).2) = (rawThirdSlope q 0 (0,1) x).2 at h2
  simp only [(rawThirdIntegrand_zero_diagonal q _).1,intervalIntegral.integral_zero] at h1
  simp only [(rawThirdIntegrand_zero_diagonal q _).2,intervalIntegral.integral_zero] at h2
  exact ⟨h1.symm,h2.symm⟩

/-- Multiplying the actual odd coefficients by the odd kernels makes the next coefficient diagonal. -/
theorem rawFourthIntegrand_zero_offdiagonal (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (rawFourthIntegrand q 0 (1,0) x).2 = 0 ∧ (rawFourthIntegrand q 0 (0,1) x).1 = 0 := by
  simp only [rawFourthIntegrand,Complex.ofReal_zero,zero_smul,add_zero,rawSolutionSlope_zero,
    rawLinearCoefficient,rawLinearPrimitive,rawDividedOperator_apply,rawCubicOperator_zero_apply,
    Prod.snd_add,Prod.fst_add,Prod.snd_sub,Prod.fst_sub,
    (rawThirdSlope_zero_diagonal q x).1,(rawThirdSlope_zero_diagonal q x).2,
    mul_zero,sub_self,add_zero,and_self]

theorem rawQuarticEndpointMatrix_offdiagonal (q : SchwartzMap ℝ ℂ) (left : Bool) :
    rawQuarticEndpointMatrix q left 1 0 = 0 ∧ rawQuarticEndpointMatrix q left 0 1 = 0 := by
  have hi := (rawOrientedFourthIntegrand_integrable q 0 (1,0) left).integrableOn (s := Set.Ioi 0)
  have hj := (rawOrientedFourthIntegrand_integrable q 0 (0,1) left).integrableOn (s := Set.Ioi 0)
  change (∫ x in Set.Ioi (0 : ℝ), rawOrientedFourthIntegrand q 0 (1,0) left x).2 = 0 ∧
    (∫ x in Set.Ioi (0 : ℝ), rawOrientedFourthIntegrand q 0 (0,1) left x).1 = 0
  rw [snd_integral hi,fst_integral hj]
  cases left <;> simp only [rawOrientedFourthIntegrand,Bool.false_eq_true,↓reduceIte,Prod.fst_neg,Prod.snd_neg,
    (rawFourthIntegrand_zero_offdiagonal q _).1,(rawFourthIntegrand_zero_offdiagonal q _).2,
    neg_zero,integral_zero,and_self]

/-- Fourth order contributes to neither actual reflection channel. -/
theorem rawScatteringFourthCoefficient_offdiagonal (q : SchwartzMap ℝ ℂ) :
    rawScatteringFourthCoefficient q 1 0 = 0 ∧ rawScatteringFourthCoefficient q 0 1 = 0 := by
  simp [rawScatteringFourthCoefficient,rawQuadraticEndpointMatrix_eq,rawFirstCoefficientMatrix,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
    (rawQuarticEndpointMatrix_offdiagonal q false).1,(rawQuarticEndpointMatrix_offdiagonal q false).2,
    (rawQuarticEndpointMatrix_offdiagonal q true).1,(rawQuarticEndpointMatrix_offdiagonal q true).2,
    (rawCubicEndpointMatrix_zero_diagonal q false).1,(rawCubicEndpointMatrix_zero_diagonal q false).2,
    (rawCubicEndpointMatrix_zero_diagonal q true).1,(rawCubicEndpointMatrix_zero_diagonal q true).2]

/-- Exact reflection expansion through fifth order, with the cubic obstruction evaluated. -/
theorem rawReflection_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    rawScatteringMatrix q k 1 0 = (k : ℂ)^3*(2*compatibilityMoment q)+
      (k : ℂ)^5*rawScatteringFifthRemainder q k 1 0 := by
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) (rawScatteringMatrix_fifth_factor q k)
  simpa only [Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_ne (by omega : (1 : Fin 2) ≠ 0),
    rawScatteringQuadraticCoefficient_lower,rawScatteringCubicCoefficient_lower,
    (rawScatteringFourthCoefficient_offdiagonal q).1,smul_zero,zero_add,add_zero,smul_eq_mul,mul_zero] using hh

/-- The reverse channel has the opposite cubic obstruction and its own controlled fifth remainder. -/
theorem rawReverseReflection_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    rawScatteringMatrix q k 0 1 = (k : ℂ)^3*(-2*compatibilityMoment q)+
      (k : ℂ)^5*rawScatteringFifthRemainder q k 0 1 := by
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) (rawScatteringMatrix_fifth_factor q k)
  simpa only [Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_ne (by omega : (0 : Fin 2) ≠ 1),
    rawScatteringQuadraticCoefficient_upper,rawScatteringCubicCoefficient_upper,
    (rawScatteringFourthCoefficient_offdiagonal q).2,smul_zero,zero_add,add_zero,smul_eq_mul,mul_zero] using hh

end
end GaloisForLFunctions.HTGeometry.FokasLenells
