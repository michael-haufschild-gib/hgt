import GaloisForLFunctions.OrderSixMetaplecticTheory.TheFractionalTraceIsASumOverTheProjectiveLineModuloTheSquare

/-!
# The cusp `0` of the fractional trace reads low points of low points

Conjugating the fractional translations by `S` turns them into lower ones: `T_tS = S A_qL(−t)A_q⁻¹`
(`fracShift_mul_sO`). For `q ∤ t` the Hecke-at-`q` identity `A_qL(−t) = M_{−t}A_q⁻¹T(−β_{−t})`
(`M_{−t} = [[q, 3β_{−t}], [−3t, δ_{−t}]]`) gives

`Θ(T_tSy) = (−3t/q)₃ Θ(A_q⁻¹T(−β_{−t})A_q⁻¹y)`   (`theta_fracShift_sO`),

so that (`fracSum_sO`)

`G_Θ(Sy) = Θ(y)² + Σ_{t ≢ 0} χ(−9t²) Θ^{(−β_{−t})}(A_q⁻¹y) Θ^{(−β_t)}(A_q⁻¹y)`:

products of low points of low points, at height `v/N(q)`, whose phases `χ(−9t²)` sum to zero.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem fracShift_zero : P.fracShift 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [fracShift, complexTranslation]

theorem contraction_mul_dilation : P.contraction * P.dilation = 1 := by
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, PrimaryPrime.contraction, complexDiagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, hr0]

theorem dilation_fracShift (t : O) :
    P.dilation * P.fracShift t = complexMatrix (transThree t) * P.dilation := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fracShift, complexTranslation, PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, transThree,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ringComplex_three]
  rw [← hr]
  field_simp

/-- `T_{3t/q} = A_q⁻¹T(t)A_q`. -/
theorem fracShift_eq (t : O) :
    P.fracShift t = P.contraction * complexMatrix (transThree t) * P.dilation := by
  rw [mul_assoc, ← P.dilation_fracShift, ← mul_assoc, P.contraction_mul_dilation, one_mul]

/-- `T(t)S = S L(−t)` in `SL₂(O)`. -/
theorem transThree_mul_sO (t : O) :
    ((transThree t : levelThree) : SL(2, O)) * sO = sO * ((lowerThree (-t) : levelThree) : SL(2, O)) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [transThree, lowerThree, coe_sO, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- `T_tS = S A_qL(−t)A_q⁻¹`. -/
theorem fracShift_mul_sO (t : O) :
    P.fracShift t * integralComplexMatrix sO =
      integralComplexMatrix sO * (P.dilation * complexMatrix (lowerThree (-t)) * P.contraction) := by
  have h1 : complexMatrix (transThree t) * integralComplexMatrix sO =
      integralComplexMatrix sO * complexMatrix (lowerThree (-t)) := by
    rw [complexMatrix_eq, complexMatrix_eq, ← map_mul, ← map_mul, transThree_mul_sO]
  rw [P.fracShift_eq, mul_assoc, P.dilation_S, ← mul_assoc, mul_assoc P.contraction, h1, ← mul_assoc,
    P.contraction_S, mul_assoc, mul_assoc, mul_assoc]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
