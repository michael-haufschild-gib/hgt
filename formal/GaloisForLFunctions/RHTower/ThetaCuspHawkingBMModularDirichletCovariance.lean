import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalChartTestSeparation

/-!
The actual Möbius Jacobian preserves the full hyperbolic Dirichlet pairing.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

private theorem real_linear_complex_expand (A : ℂ →L[ℝ] ℂ) (w : ℂ) :
    A w = (w.re:ℂ)*A 1+(w.im:ℂ)*A Complex.I := by
  have he : w = w.re • (1:ℂ)+w.im • Complex.I := by
    simpa only [Complex.real_smul,mul_one] using w.re_add_im.symm
  calc
    A w = A (w.re • (1:ℂ)+w.im • Complex.I) := congrArg A he
    _ = _ := by
      rw [A.map_add,A.map_smul,A.map_smul]
      simp only [Complex.real_smul]

/-- The two real derivative directions retain their complete complex energy
pairing under a complex scalar Jacobian, with exactly its squared norm factor. -/
theorem complex_gradient_pairing_scale (A B : ℂ →L[ℝ] ℂ) (c : ℂ) :
    conj (A c)*B c+conj (A (c*Complex.I))*B (c*Complex.I) =
      (Complex.normSq c:ℂ)*(conj (A 1)*B 1+conj (A Complex.I)*B Complex.I) := by
  rw [real_linear_complex_expand A c,real_linear_complex_expand B c,
    real_linear_complex_expand A (c*Complex.I),real_linear_complex_expand B (c*Complex.I)]
  simp only [Complex.mul_I_re,Complex.mul_I_im,Complex.ofReal_neg,map_add,map_mul,
    map_neg,Complex.conj_ofReal,Complex.normSq_apply,Complex.ofReal_add,Complex.ofReal_mul]
  ring

/-- The derivative of the actual pullback is the full chain rule for the modular
Möbius map in the original chart. -/
theorem chart_fderiv_modular_pullback (A : SL(2,ℤ)) (f : UpperHalfPlane → ℂ)
    (hf : ChartSmooth f) (z : UpperHalfPlane) :
    fderiv ℝ ((fun w : UpperHalfPlane => f (A • w)) ∘ ofComplex) (z:ℂ) =
      (fderiv ℝ (f ∘ ofComplex) ((A • z:UpperHalfPlane):ℂ)).comp
        (UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z:ℂ)) := by
  have hd : HasFDerivAt (fun w : ℂ => ((A • ofComplex w : UpperHalfPlane):ℂ))
      (UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z:ℂ)) (z:ℂ) :=
    (UpperHalfPlane.hasStrictFDerivAt_smul (A : GL (Fin 2) ℝ) z).hasFDerivAt
  have hh := ((hf (A • z)).differentiableAt (by simp)).hasFDerivAt
  have hh' : HasFDerivAt (f ∘ ofComplex)
      (fderiv ℝ (f ∘ ofComplex) ((A • z:UpperHalfPlane):ℂ))
        ((A • ofComplex (z:ℂ):UpperHalfPlane):ℂ) := by
    simpa only [ofComplex_apply] using hh
  have hc := hh'.comp (z:ℂ) hd
  simpa only [Function.comp_def,ofComplex_apply] using hc.fderiv

/-- The original special-linear Möbius differential is multiplication by its
actual reciprocal-square denominator, with no arbitrary frame normalization. -/
theorem modular_chart_jacobian (A : SL(2,ℤ)) (z : UpperHalfPlane) (v : ℂ) :
    UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z:ℂ) v =
      (1/(denom A z)^(2 : ℕ))*v := by
  simp [UpperHalfPlane.smulFDeriv,UpperHalfPlane.σ,mul_comm]

/-- The actual complex Dirichlet pairing of the two hyperbolic-frame derivatives. -/
def frameEnergy (f h : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑ i : Fin 2, conj (weightedDeriv (direction i) f z)*weightedDeriv (direction i) h z

private theorem frameEnergy_chart (f h : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    frameEnergy f h z = (z.im:ℂ)^(2 : ℕ) *
      (conj (fderiv ℝ (f ∘ ofComplex) (z:ℂ) 1)*fderiv ℝ (h ∘ ofComplex) (z:ℂ) 1+
       conj (fderiv ℝ (f ∘ ofComplex) (z:ℂ) Complex.I)*fderiv ℝ (h ∘ ofComplex) (z:ℂ) Complex.I) := by
  simp only [frameEnergy,Fin.sum_univ_two,direction,Matrix.cons_val_zero,Matrix.cons_val_one,
    weightedDeriv,map_mul,Complex.conj_ofReal]
  ring

/-- Modular pullback preserves the complete hyperbolic gradient pairing pointwise. -/
theorem frameEnergy_modular_pullback (A : SL(2,ℤ)) (f h : UpperHalfPlane → ℂ)
    (hf : ChartSmooth f) (hh : ChartSmooth h) (z : UpperHalfPlane) :
    frameEnergy (fun w => f (A • w)) (fun w => h (A • w)) z = frameEnergy f h (A • z) := by
  rw [frameEnergy_chart,frameEnergy_chart,chart_fderiv_modular_pullback A f hf,
    chart_fderiv_modular_pullback A h hh]
  simp only [ContinuousLinearMap.comp_apply,modular_chart_jacobian,mul_one]
  rw [complex_gradient_pairing_scale,← mul_assoc]
  congr 1
  rw [ModularGroup.im_smul_eq_div_normSq,Complex.ofReal_div,div_pow,
    Complex.normSq_div,Complex.normSq_one,map_pow]
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow]
  ring

end
end RHTower.D4BMModularCore
