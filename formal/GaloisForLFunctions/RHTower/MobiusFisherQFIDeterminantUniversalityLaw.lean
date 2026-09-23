import GaloisForLFunctions.RHTower.MobiusCriticalFisherConnectionInertia
import GaloisForLFunctions.RHTower.MobiusCriticalFisherDoubledParityClock

open Complex Filter
open scoped ComplexOrder InnerProductSpace Matrix Topology

namespace RHTower

noncomputable section

/-! The finite doubled-clock QFI and the completed infinite pointed-Fisher compression are
different realizations of one squarefree Möbius projective-energy coordinate. -/

/-- The determinant of the completed squarefree Möbius pointed-Fisher compression is the
negative half-square of its projective Fisher energy. -/
theorem det_squarefreeMobiusCritical_pointedFisherConnectionCompression
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (GaloisForLFunctions.HTGeometry.pointedFisherConnectionCompression
      (infiniteMobiusSignedWeightLp sigma hsigma)
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma)).det =
      -(1 / 2 : ℂ) *
        (squarefreeMobiusCriticalProjectiveFisherEnergy sigma : ℂ) ^ (2 : ℕ) := by
  rw [GaloisForLFunctions.HTGeometry.det_pointedFisherConnectionCompression_eq_neg_half_projectiveEnergy_sq]
  congr 2
  unfold _root_.HTGeometry.projectiveGramTangentEnergy
  rw [norm_infiniteMobiusSignedWeightLp_sq hsigma,
    norm_infiniteMobiusCriticalFisherTangentLp_sq hsigma,
    inner_infiniteMobiusSignedWeightLp_fisherTangent_eq_zero hsigma,
    norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  norm_num

/-- Finite doubled-clock erased QFI reconstructs the determinant of the completed infinite
pointed-Fisher compression by the universal negative half-square transform. -/
theorem tendsto_negHalfSq_finiteMobiusDoubledErasedQFI_to_connectionDet
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Tendsto (fun N : ℕ =>
      -(1 / 2 : ℂ) * (finiteMobiusDoubledErasedQFI sigma N : ℂ) ^ (2 : ℕ))
      atTop
      (nhds
        (GaloisForLFunctions.HTGeometry.pointedFisherConnectionCompression
          (infiniteMobiusSignedWeightLp sigma hsigma)
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma)).det) := by
  have hqfi : Tendsto (fun N : ℕ => (finiteMobiusDoubledErasedQFI sigma N : ℂ))
      atTop (nhds (squarefreeMobiusCriticalProjectiveFisherEnergy sigma : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_finiteMobiusDoubledErasedQFI hsigma)
  rw [det_squarefreeMobiusCritical_pointedFisherConnectionCompression hsigma]
  exact (tendsto_const_nhds.mul (hqfi.pow 2))

/-- The squarefree Möbius pointed-Fisher determinant has universal critical boundary value
`-8`, while every interior compression remains Hermitian, nonsingular, and mixed-signature. -/
theorem squarefreeMobiusCritical_fisherQFIDeterminantUniversality :
    Tendsto (fun sigma : ℝ =>
      if hsigma : 1 < sigma then
        (GaloisForLFunctions.HTGeometry.pointedFisherConnectionCompression
          (infiniteMobiusSignedWeightLp sigma hsigma)
          (infiniteMobiusCriticalFisherTangentLp sigma hsigma)).det
      else 0)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (-8 : ℂ)) ∧
    ∀ {sigma : ℝ} (hsigma : 1 < sigma),
      let M := GaloisForLFunctions.HTGeometry.pointedFisherConnectionCompression
        (infiniteMobiusSignedWeightLp sigma hsigma)
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
      M.IsHermitian ∧ M.det ≠ 0 ∧
        ¬ M.PosSemidef ∧ ¬ (-M).PosSemidef ∧
        Tendsto (fun N : ℕ =>
          -(1 / 2 : ℂ) * (finiteMobiusDoubledErasedQFI sigma N : ℂ) ^ (2 : ℕ))
          atTop (nhds M.det) := by
  constructor
  · have henergy : Tendsto (fun sigma : ℝ =>
        (squarefreeMobiusCriticalProjectiveFisherEnergy sigma : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (4 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_squarefreeMobiusCriticalProjectiveFisherEnergy
    have hdet : Tendsto (fun sigma : ℝ =>
        -(1 / 2 : ℂ) *
          (squarefreeMobiusCriticalProjectiveFisherEnergy sigma : ℂ) ^ (2 : ℕ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (-8 : ℂ)) := by
      convert tendsto_const_nhds.mul (henergy.pow 2) using 1
      norm_num
    apply hdet.congr'
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    have hgt : 1 < sigma := hsigma
    rw [dif_pos hgt,
      det_squarefreeMobiusCritical_pointedFisherConnectionCompression hgt]
  · intro sigma hsigma
    let M := GaloisForLFunctions.HTGeometry.pointedFisherConnectionCompression
      (infiniteMobiusSignedWeightLp sigma hsigma)
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
    have hmixed :=
      squarefreeMobiusCritical_pointedFisherConnectionCompression_exact_mixed_signature hsigma
    exact ⟨hmixed.1, hmixed.2.1, hmixed.2.2.1, hmixed.2.2.2,
      tendsto_negHalfSq_finiteMobiusDoubledErasedQFI_to_connectionDet hsigma⟩

end

end RHTower
