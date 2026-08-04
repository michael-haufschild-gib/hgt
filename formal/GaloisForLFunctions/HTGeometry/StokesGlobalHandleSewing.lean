import GaloisForLFunctions.HTGeometry.StokesGlobalPuiseuxWittLaw

namespace GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

noncomputable section

variable {p : ℕ}
variable {n m K N : Fin (p + 1) → ℕ}

/-- Adding one handle subtracts exactly two from the coefficient of the sole common-rank
channel. -/
theorem globalRankCoefficient_succ_genus (genus : ℕ)
    (d : LocalData p n m K N) :
    globalRankCoefficient (genus + 1) d =
      globalRankCoefficient genus d - 2 := by
  simp only [globalRankCoefficient, fusionCoefficient]
  push_cast
  ring

/-- Sewing two punctured curves away from marked points adds their local defect sums and subtracts
two from the resulting common-rank coefficient. -/
theorem scalarRankCoefficient_sewing
    (genus₁ genus₂ punctures₁ punctures₂ : ℕ)
    (localDefect₁ localDefect₂ : ℝ) :
    fusionCoefficient (genus₁ + genus₂) (punctures₁ + punctures₂) -
        (localDefect₁ + localDefect₂) =
      (fusionCoefficient genus₁ punctures₁ - localDefect₁) +
        (fusionCoefficient genus₂ punctures₂ - localDefect₂) - 2 := by
  simp only [fusionCoefficient]
  push_cast
  ring

end

end GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt
