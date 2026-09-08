import GaloisForLFunctions.HTGeometry.L2CauchyHolomorphy

/-! Almost-everywhere representative changes preserve the actual frequency-dependent L² class. -/
open MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
variable {A : Type*} [MeasurableSpace A]

/-- Changing representatives almost everywhere leaves the canonical L² class unchanged. -/
theorem l2Family_congr_ae (μ : Measure A) (F G : ℂ → A → ℂ) (z : ℂ)
    (h : F z =ᵐ[μ] G z) : l2Family μ F z = l2Family μ G z := by
  classical
  by_cases hF : MemLp (F z) 2 μ
  · have hG := hF.ae_eq h
    rw [l2Family_eq_toLp μ F z hF,l2Family_eq_toLp μ G z hG]
    exact Lp.ext (hF.coeFn_toLp.trans (h.trans hG.coeFn_toLp.symm))
  · have hG : ¬MemLp (G z) 2 μ := fun hg => hF (hg.ae_eq h.symm)
    simp only [l2Family,dif_neg hF,dif_neg hG]

/-- Scalar multiplication commutes with taking the actual L² class of an admitted representative. -/
theorem l2Family_smul (μ : Measure A) (F G : ℂ → A → ℂ) (z c : ℂ)
    (hF : MemLp (F z) 2 μ) (h : ∀ a, G z a = c • F z a) :
    l2Family μ G z = c • l2Family μ F z := by
  have he : G z = c • F z := funext h
  have hG : MemLp (G z) 2 μ := by rw [he]; exact hF.const_smul c
  rw [l2Family_eq_toLp μ G z hG,l2Family_eq_toLp μ F z hF]
  simpa only [he] using MemLp.toLp_const_smul c hF

end
end GaloisForLFunctions.HTGeometry
