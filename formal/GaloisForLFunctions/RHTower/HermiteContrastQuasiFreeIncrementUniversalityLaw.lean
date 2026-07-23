import GaloisForLFunctions.RHTower.HermiteContrastLp
import GaloisForLFunctions.RHTower.LadderLimitSecular
import GaloisForLFunctions.RHTower.HermiteEvenSlaterPluckerConnector

/-!
# Hermite contrast/quasi-free increment universality

The constrained-prolate weights occur independently as the mass coordinates of the limiting
secular ladder and as occupations of the Hermite-even Slater--Pluecker block.  This module proves
that the contrast energy at rung `k` recovers the next occupation exactly.  Consequently one
contrast norm determines the next-rank increments of the quasi-free mean, variance, and Fano
margin.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

/-- Quasi-free mean of the first `m` constrained-prolate occupations at step-four energies. -/
def constrainedProlateHermiteQuasiFreeMean (m : ℕ) : ℝ :=
  quasiFreeSpectralMean (hermiteEvenRealGramCoordinates m)
    (fun j => (hermiteEvenStepFourDegree j : ℝ))
    (fun j => constrainedProlateHermiteWeight (j : ℕ))

/-- Quasi-free variance of the first `m` constrained-prolate occupations. -/
def constrainedProlateHermiteQuasiFreeVariance (m : ℕ) : ℝ :=
  quasiFreeSpectralVariance (hermiteEvenRealGramCoordinates m)
    (fun j => (hermiteEvenStepFourDegree j : ℝ))
    (fun j => constrainedProlateHermiteWeight (j : ℕ))

/-- Quasi-free Fano margin of the first `m` constrained-prolate occupations. -/
def constrainedProlateHermiteQuasiFreeFanoMargin (m : ℕ) : ℝ :=
  quasiFreeSpectralFanoMargin (hermiteEvenRealGramCoordinates m)
    (fun j => (hermiteEvenStepFourDegree j : ℝ))
    (fun j => constrainedProlateHermiteWeight (j : ℕ))

/-- The complement of normalized contrast energy is exactly the next occupation divided by the
accumulated mass. -/
theorem constrainedProlateHermiteWeight_eq_accumulatedMass_mul_one_sub_energy (k : ℕ) :
    constrainedProlateHermiteWeight (k + 1) =
      constrainedProlateHermiteWeightSum (k + 1) *
        (1 - (‖hermiteContrastLp k‖ ^ 2 * constrainedProlateHermiteWeight (k + 1)) /
          (Real.sqrt 2 * constrainedProlateHermiteWeightSum (k + 1) ^ 2)) := by
  have hE :
      (‖hermiteContrastLp k‖ ^ 2 * constrainedProlateHermiteWeight (k + 1)) /
          (Real.sqrt 2 * constrainedProlateHermiteWeightSum (k + 1) ^ 2) =
        constrainedProlateHermiteTheta k := by
    have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have hweight : constrainedProlateHermiteWeight (k + 1) ≠ 0 :=
      (constrainedProlateHermiteWeight_pos (k + 1)).ne'
    have hsum : constrainedProlateHermiteWeightSum (k + 1) ≠ 0 :=
      (constrainedProlateHermiteWeightSum_pos (k + 1)).ne'
    rw [norm_sq_hermiteContrastLp_eq, constrainedProlateHermiteTheta]
    field_simp
  rw [hE, constrainedProlateHermiteTheta, constrainedProlateHermiteWeightSum_succ]
  have hQ : constrainedProlateHermiteWeightSum k +
      constrainedProlateHermiteWeight (k + 1) ≠ 0 :=
    (add_pos (constrainedProlateHermiteWeightSum_pos k)
      (constrainedProlateHermiteWeight_pos (k + 1))).ne'
  field_simp [hQ]
  ring

/-- Adding rank `m` contributes its occupation times its step-four energy. -/
theorem constrainedProlateHermiteQuasiFreeMean_succ_sub (m : ℕ) :
    constrainedProlateHermiteQuasiFreeMean (m + 1) -
        constrainedProlateHermiteQuasiFreeMean m =
      constrainedProlateHermiteWeight m * (4 * m : ℝ) := by
  rw [constrainedProlateHermiteQuasiFreeMean,
    constrainedProlateHermiteQuasiFreeMean,
    quasiFreeSpectralMean_hermiteEvenRealGramCoordinates,
    quasiFreeSpectralMean_hermiteEvenRealGramCoordinates]
  rw [Fin.sum_univ_castSucc]
  simp [hermiteEvenStepFourDegree]

/-- Adding rank `m` contributes the Bernoulli variance of its occupied step-four mode. -/
theorem constrainedProlateHermiteQuasiFreeVariance_succ_sub (m : ℕ) :
    constrainedProlateHermiteQuasiFreeVariance (m + 1) -
        constrainedProlateHermiteQuasiFreeVariance m =
      constrainedProlateHermiteWeight m *
        (1 - constrainedProlateHermiteWeight m) * (4 * m : ℝ) ^ 2 := by
  rw [constrainedProlateHermiteQuasiFreeVariance,
    constrainedProlateHermiteQuasiFreeVariance,
    quasiFreeSpectralVariance_hermiteEvenRealGramCoordinates,
    quasiFreeSpectralVariance_hermiteEvenRealGramCoordinates]
  rw [Fin.sum_univ_castSucc]
  simp [hermiteEvenStepFourDegree]

/-- Adding rank `m` contributes its exact one-mode Fano margin. -/
theorem constrainedProlateHermiteQuasiFreeFanoMargin_succ_sub (m : ℕ) :
    constrainedProlateHermiteQuasiFreeFanoMargin (m + 1) -
        constrainedProlateHermiteQuasiFreeFanoMargin m =
      constrainedProlateHermiteWeight m *
        ((4 * m : ℝ) - (1 - constrainedProlateHermiteWeight m) * (4 * m : ℝ) ^ 2) := by
  rw [constrainedProlateHermiteQuasiFreeFanoMargin,
    constrainedProlateHermiteQuasiFreeFanoMargin,
    quasiFreeSpectralFanoMargin_hermiteEvenRealGramCoordinates,
    quasiFreeSpectralFanoMargin_hermiteEvenRealGramCoordinates]
  rw [Fin.sum_univ_castSucc]
  simp [hermiteEvenStepFourDegree]

/-- **Contrast/quasi-free increment universality.**  A single normalized contrast norm and the
accumulated mass determine all three next-rank quasi-free increments. -/
theorem hermiteContrastSecularEnergy_quasiFreeIncrementUniversality (k : ℕ) :
    let Q := constrainedProlateHermiteWeightSum (k + 1)
    let E := (‖hermiteContrastLp k‖ ^ 2 * constrainedProlateHermiteWeight (k + 1)) /
      (Real.sqrt 2 * constrainedProlateHermiteWeightSum (k + 1) ^ 2)
    let d : ℝ := 4 * (k + 1)
    constrainedProlateHermiteQuasiFreeMean (k + 2) -
          constrainedProlateHermiteQuasiFreeMean (k + 1) = Q * (1 - E) * d ∧
      constrainedProlateHermiteQuasiFreeVariance (k + 2) -
          constrainedProlateHermiteQuasiFreeVariance (k + 1) =
        Q * (1 - E) * (1 - Q * (1 - E)) * d ^ 2 ∧
      constrainedProlateHermiteQuasiFreeFanoMargin (k + 2) -
          constrainedProlateHermiteQuasiFreeFanoMargin (k + 1) =
        Q * (1 - E) * (d - (1 - Q * (1 - E)) * d ^ 2) := by
  dsimp only
  set E : ℝ := (‖hermiteContrastLp k‖ ^ 2 * constrainedProlateHermiteWeight (k + 1)) /
    (Real.sqrt 2 * constrainedProlateHermiteWeightSum (k + 1) ^ 2) with hE
  have hw : constrainedProlateHermiteWeight (k + 1) =
      constrainedProlateHermiteWeightSum (k + 1) * (1 - E) := by
    simpa [hE] using
      constrainedProlateHermiteWeight_eq_accumulatedMass_mul_one_sub_energy k
  constructor
  · rw [constrainedProlateHermiteQuasiFreeMean_succ_sub]
    simp only [hw]
    norm_num [Nat.cast_add, Nat.cast_one]
  constructor
  · rw [constrainedProlateHermiteQuasiFreeVariance_succ_sub]
    simp only [hw]
    norm_num [Nat.cast_add, Nat.cast_one]
  · rw [constrainedProlateHermiteQuasiFreeFanoMargin_succ_sub]
    simp only [hw]
    norm_num [Nat.cast_add, Nat.cast_one]

end

end RHTower
