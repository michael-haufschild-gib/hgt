import GaloisForLFunctions.HTGeometry.SchattenCubicExponentialContraction
import GaloisForLFunctions.HTGeometry.PencilSufficiencyLaw
import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicSchattenMass

open NormedSpace

namespace RHTower

noncomputable section

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A restricted unitary obtained by exponentiating a self-adjoint generator whose Hardy seam is
Hilbert--Schmidt. -/
structure RestrictedSelfAdjointExponentialDatum (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  restricted : RestrictedUnitaryDatum H
  generator : H →L[ℂ] H
  generator_adjoint : ContinuousLinearMap.adjoint generator = generator
  unitary_eq_exp : restricted.unitary = exp (Complex.I • generator)
  generatorForwardSeam_isHilbertSchmidt :
    ((1 - restricted.projection) * generator * restricted.projection).IsHilbertSchmidt

private theorem RestrictedSelfAdjointExponentialDatum.generatorBackwardSeam_isHilbertSchmidt
    (E : RestrictedSelfAdjointExponentialDatum H) :
    (E.restricted.projection * E.generator * (1 - E.restricted.projection)).IsHilbertSchmidt := by
  have h := E.generatorForwardSeam_isHilbertSchmidt.adjoint
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint.map_sub,
    ContinuousLinearMap.adjoint_one, E.restricted.projection_adjoint,
    E.generator_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc] using h

private theorem RestrictedSelfAdjointExponentialDatum.generatorCommutator_isHilbertSchmidt
    (E : RestrictedSelfAdjointExponentialDatum H) :
    (E.restricted.projection * E.generator -
      E.generator * E.restricted.projection).IsHilbertSchmidt := by
  let A := (1 - E.restricted.projection) * E.generator * E.restricted.projection
  let B := E.restricted.projection * E.generator * (1 - E.restricted.projection)
  have hPP : E.restricted.projection * E.restricted.projection =
      E.restricted.projection := E.restricted.projection_idempotent
  have hcomm : E.restricted.projection * E.generator -
      E.generator * E.restricted.projection = B - A := by
    simp only [A, B]
    noncomm_ring [hPP]
  rw [hcomm]
  exact E.generatorBackwardSeam_isHilbertSchmidt.sub
    E.generatorForwardSeam_isHilbertSchmidt

/-- A self-adjoint generator's commutator has two adjoint off-diagonal blocks, so its exact cubic
Schatten energy is twice either oriented seam energy. -/
theorem RestrictedSelfAdjointExponentialDatum.schattenNorm_generatorCommutator_three_rpow_eq
    (E : RestrictedSelfAdjointExponentialDatum H) :
    schattenNorm 3
        (E.restricted.projection * E.generator -
          E.generator * E.restricted.projection) ^ (3 : ℝ) =
      2 * schattenNorm 3
        ((1 - E.restricted.projection) * E.generator * E.restricted.projection) ^ (3 : ℝ) := by
  let P := E.restricted.projection
  let A := (1 - P) * E.generator * P
  let B := P * E.generator * (1 - P)
  let C := P * E.generator - E.generator * P
  have hPP : P * P = P := E.restricted.projection_idempotent
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    E.restricted.projection_adjoint
  have hMadj : ContinuousLinearMap.adjoint E.generator = E.generator :=
    E.generator_adjoint
  have hBadj : B = ContinuousLinearMap.adjoint A := by
    simp only [A, B, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_one,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    rw [hPadj, hMadj]
  have hC : C = B - A := by
    simp only [C, A, B]
    noncomm_ring [hPP]
  have henergy : star C * C = star A * A + star B * B := by
    have hPQ : P * (1 - P) = 0 := by noncomm_ring [hPP]
    have hQP : (1 - P) * P = 0 := by noncomm_ring [hPP]
    have hBA : star B * A = 0 := by
      change ContinuousLinearMap.adjoint B * A = 0
      rw [hBadj, ContinuousLinearMap.adjoint_adjoint]
      calc
        A * A = (1 - P) * E.generator * (P * (1 - P)) * E.generator * P := by
          simp only [A, mul_assoc]
        _ = 0 := by rw [hPQ]; simp
    have hAB : star A * B = 0 := by
      change ContinuousLinearMap.adjoint A * B = 0
      rw [← hBadj]
      calc
        B * B = P * E.generator * ((1 - P) * P) * E.generator * (1 - P) := by
          simp only [B, mul_assoc]
        _ = 0 := by rw [hQP]; simp
    change ContinuousLinearMap.adjoint C * C =
      ContinuousLinearMap.adjoint A * A + ContinuousLinearMap.adjoint B * B
    rw [hC, ContinuousLinearMap.adjoint.map_sub]
    change (star B - star A) * (B - A) = star A * A + star B * B
    noncomm_ring [hBA, hAB]
  have hAP : A * P = A := by
    simp only [A]
    noncomm_ring [hPP]
  have hBQ : B * (1 - P) = B := by
    simp only [B]
    noncomm_ring [hPP]
  have horth := absOp_complementary_right_support A B P
    E.restricted.projection_idempotent E.restricted.projection_adjoint hAP hBQ
  have hAHS : A.IsHilbertSchmidt := E.generatorForwardSeam_isHilbertSchmidt
  have hBHS : B.IsHilbertSchmidt := by rw [hBadj]; exact hAHS.adjoint
  have hCHS : C.IsHilbertSchmidt := by rw [hC]; exact hBHS.sub hAHS
  have hmass := schattenNorm_three_rpow_eq_add C A B hCHS hAHS hBHS
    henergy horth.1 horth.2
  rw [hBadj, schattenNorm_adjoint] at hmass
  simpa only [C, A, two_mul] using hmass

/-- Exact nonlinear-to-additive reduction `(RUCRI.4f)`: exponentiation does not amplify the
Schatten-three commutator, and the self-adjoint generator has two equal chiral seams. -/
theorem RestrictedSelfAdjointExponentialDatum.traceNorm_cubicDefect_le_generatorSeam
    (E : RestrictedSelfAdjointExponentialDatum H) :
    traceNorm H (restrictedProjectionCubicDefect
        E.restricted.conjugateProjection E.restricted.projection) ≤
      2 * schattenNorm 3
        ((1 - E.restricted.projection) * E.generator * E.restricted.projection) ^ (3 : ℝ) := by
  classical
  by_cases hH : Nontrivial H
  · letI : Nontrivial H := hH
    let P := E.restricted.projection
    let M := E.generator
    let X : H →L[ℂ] H := Complex.I • M
    let C : H →L[ℂ] H := P * M - M * P
    have hMadj : ContinuousLinearMap.adjoint M = M := by
      simpa only [M] using E.generator_adjoint
    have hMstar : star M = M := hMadj
    have hX : X ∈ skewAdjoint (H →L[ℂ] H) := by
      rw [skewAdjoint.mem_iff]
      change star (Complex.I • M) = -(Complex.I • M)
      rw [star_smul, hMstar]
      simp
    have hCX : P * X - X * P = Complex.I • C := by
      simp only [X, C, mul_smul_comm, smul_mul_assoc, smul_sub]
    have hCthree : MemSchattenClass 3 C :=
      ((memSchattenClass_two_iff_isHilbertSchmidt C).2
        E.generatorCommutator_isHilbertSchmidt).mono (by norm_num) (by norm_num)
    have hCXthree : MemSchattenClass 3 (P * X - X * P) := by
      rw [hCX]
      exact memSchattenClass_smul Complex.I hCthree
    have hKcpt : IsCompactOperator
        (P * exp X - exp X * P : H →L[ℂ] H) := by
      have hu : exp X = E.restricted.unitary := by
        simpa only [X, M] using E.unitary_eq_exp.symm
      rw [hu]
      exact E.restricted.commutator_isHilbertSchmidt.isCompactOperator
    have hcontract := schattenNorm_three_commutator_exp_le P X hX hCXthree hKcpt
    have hu : exp X = E.restricted.unitary := by
      simpa only [X, M] using E.unitary_eq_exp.symm
    rw [hu, hCX, schattenNorm_smul (by norm_num) Complex.I C] at hcontract
    simp only [Complex.norm_I, one_mul] at hcontract
    rw [E.restricted.traceNorm_cubicDefect_eq_schattenNorm_commutator_three_rpow]
    calc
      schattenNorm 3 (P * E.restricted.unitary - E.restricted.unitary * P) ^ (3 : ℝ) ≤
          schattenNorm 3 C ^ (3 : ℝ) :=
        Real.rpow_le_rpow (schattenNorm_nonneg 3 _ ) hcontract (by norm_num)
      _ = _ := by
        simpa only [P, M, C] using
          E.schattenNorm_generatorCommutator_three_rpow_eq
  · haveI : Subsingleton H := not_nontrivial_iff_subsingleton.mp hH
    have hzero (T : H →L[ℂ] H) : T = 0 := Subsingleton.elim _ _
    rw [hzero (restrictedProjectionCubicDefect
        E.restricted.conjugateProjection E.restricted.projection),
      hzero ((1 - E.restricted.projection) * E.generator * E.restricted.projection)]
    simp only [traceNorm, schattenNorm, approxNumber_zero_op,
      Real.zero_rpow (by norm_num : (3 : ℝ) ≠ 0), tsum_zero,
      Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0), mul_zero, le_rfl]

end

end RHTower

