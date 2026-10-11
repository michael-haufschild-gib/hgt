import GaloisForLFunctions.RHTower.PaperDeningerMateProfile

/-! # Literal framed source/dual curvature and the Gamma boundary

The normalized matrix is built from the existing composition curvatures, with
their canonical left gains removed. Its upper-right entry is the bounded mate
profile; at degree six it recovers the actual ordered Gamma boundary coefficient.
-/

namespace RHTower
noncomputable section

def paperDeningerNormalizedFrame (s : ℂ) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (paperDeningerMateEnergy s j)⁻¹ •
    (deningerHalfDensityMateGain 2 s • deningerFramedCompositionCurvature
      (deningerOneSidedFramedTransport (fun k => (deningerHalfDensityMateGain k s)⁻¹)) 2 (j + 2) -
    (deningerHalfDensityMateGain 2 s)⁻¹ • deningerFramedCompositionCurvature
      (deningerOneSidedFramedTransport (fun k => deningerHalfDensityMateGain k s)) 2 (j + 2))

theorem paperDeningerNormalizedFrame_eq (s : ℂ) (j : ℕ) :
    paperDeningerNormalizedFrame s j = !![0, paperDeningerMateWeight s j; 0, 0] := by
  have hm := deningerHalfDensityMateGain_mul (by norm_num : 0 < 2) (by omega : 0 < j + 2) s
  have hmi : (deningerHalfDensityMateGain (2 * (j + 2)) s)⁻¹ =
      (deningerHalfDensityMateGain 2 s)⁻¹ * (deningerHalfDensityMateGain (j + 2) s)⁻¹ := by
    rw [hm, mul_inv]
  have hg (k : ℕ) : deningerHalfDensityMateGain k s ≠ 0 :=
    (deningerHalfDensityMateGain_pos k s).ne'
  rw [paperDeningerNormalizedFrame, deningerOneSidedFramedCurvature_eq _ _ _ hmi,
    deningerOneSidedFramedCurvature_eq _ _ _ hm]
  rw [paperDeningerMateWeight,
    ← deningerHalfDensityMateGain_sub_inv_eq_mateCurvature (by omega : 0 < j + 2) s]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Matrix.smul_apply]
  field_simp [hg, (paperDeningerMateEnergy_pos s j).ne']
  ring

@[simp] theorem paperDeningerNormalizedFrame_entry (s : ℂ) (j : ℕ) :
    paperDeningerNormalizedFrame s j 0 1 = paperDeningerMateWeight s j := by
  rw [paperDeningerNormalizedFrame_eq]
  rfl

theorem paperDeningerNormalizedFrame_sq (s : ℂ) (j : ℕ) :
    paperDeningerNormalizedFrame s j ^ 2 = 0 := by
  rw [paperDeningerNormalizedFrame_eq, pow_two]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem paperDeningerNormalizedFrame_trace (s : ℂ) (j : ℕ) :
    Matrix.trace (paperDeningerNormalizedFrame s j) = 0 := by
  rw [paperDeningerNormalizedFrame_eq]
  simp [Matrix.trace, Fin.sum_univ_succ]

theorem paperDeningerNormalizedFrame_eq_zero_iff (s : ℂ) (j : ℕ) :
    paperDeningerNormalizedFrame s j = 0 ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
    simp only [paperDeningerNormalizedFrame_entry, Matrix.zero_apply] at he
    rw [paperDeningerMateWeight, div_eq_zero_iff] at he
    exact (deningerTensorSquareRadialMateCurvature_eq_zero_iff _ _ (by omega)).mp
      (he.resolve_right (ne_of_gt (paperDeningerMateEnergy_pos s j)))
  · intro h
    rw [paperDeningerNormalizedFrame_eq, paperDeningerMateWeight_critical s h]
    ext i k
    fin_cases i <;> fin_cases k <;> rfl

/-- Positive calibration and reciprocal-gain energy recover the literal Gamma boundary. -/
theorem paperDeningerNormalizedFrame_Gamma (r : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r =
      ((deningerCalderonWittBaseGammaMateCalibration * paperDeningerMateEnergy (r.1 : ℂ) 4 : ℝ) : ℂ) *
        (paperDeningerNormalizedFrame (r.1 : ℂ) 4 0 1 : ℂ) := by
  rw [deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_framedCurvaturePolarization,
    deningerOneSidedReducedCurvature_dual_sub_source (by norm_num : 0 < 6),
    paperDeningerNormalizedFrame_entry, ← Complex.ofReal_mul]
  congr 1
  rw [paperDeningerMateWeight]
  have he : paperDeningerMateEnergy (r.1 : ℂ) 4 ≠ 0 :=
    (paperDeningerMateEnergy_pos _ _).ne'
  field_simp

end
end RHTower
