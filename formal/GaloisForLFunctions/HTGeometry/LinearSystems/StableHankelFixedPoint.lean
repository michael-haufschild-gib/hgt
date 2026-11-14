import GaloisForLFunctions.HTGeometry.LinearSystems.StableHankelPerturbation

/-!
# Certified Picard iteration for exponential Hankel feedback

Dividing a stable Hankel packet by one plus its explicit modal norm budget
makes feedback strictly contractive for every choice of poles and residues.
The forced feedback equation has a unique half-line `L²` solution. Picard
iteration converges from every initial state with an explicit geometric
error bound, independent of an observation window.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The sum of the individual modal operator norms. -/
def stableHankelBudget {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ) : ℝ :=
  ∑ j, ‖residue j‖ / (2 * Real.exp (logRate j))

theorem stableHankelBudget_nonneg {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ) :
    0 ≤ stableHankelBudget logRate residue := by
  unfold stableHankelBudget
  exact Finset.sum_nonneg fun j _ => div_nonneg (norm_nonneg _) (by positivity)

/-- Normalization gives strict contraction even when residues are large or poles coincide. -/
def stableHankelContraction {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ) :
    HalfLineLaplaceL2 →L[ℂ] HalfLineLaplaceL2 :=
  (((1 + stableHankelBudget logRate residue)⁻¹ : ℝ) : ℂ) •
    stableHankelPacket logRate residue

/-- Explicit contraction ratio, always strictly below one. -/
def stableHankelRatio {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ) : ℝ≥0 :=
  ⟨stableHankelBudget logRate residue / (1 + stableHankelBudget logRate residue),
    div_nonneg (stableHankelBudget_nonneg _ _) (by positivity)⟩

theorem stableHankelRatio_lt_one {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ) :
    stableHankelRatio logRate residue < 1 := by
  apply NNReal.coe_lt_one.mp
  change stableHankelBudget logRate residue / (1 + stableHankelBudget logRate residue) < 1
  have hB := stableHankelBudget_nonneg logRate residue
  apply (div_lt_one (by linarith : 0 < 1 + stableHankelBudget logRate residue)).mpr
  linarith

theorem norm_stableHankelContraction_le {n : ℕ} (logRate : Fin n → ℝ)
    (residue : Fin n → ℂ) :
    ‖stableHankelContraction logRate residue‖ ≤ stableHankelRatio logRate residue := by
  have hpos : 0 ≤ (1 + stableHankelBudget logRate residue)⁻¹ :=
    inv_nonneg.mpr (add_nonneg zero_le_one (stableHankelBudget_nonneg _ _))
  change ‖stableHankelContraction logRate residue‖ ≤
    stableHankelBudget logRate residue / (1 + stableHankelBudget logRate residue)
  rw [stableHankelContraction, norm_smul, Complex.norm_real, Real.norm_of_nonneg hpos]
  calc
    _ ≤ (1 + stableHankelBudget logRate residue)⁻¹ * stableHankelBudget logRate residue :=
      mul_le_mul_of_nonneg_left (norm_stableHankelPacket_le _ _) hpos
    _ = _ := by ring

/-- One feedback step with prescribed forcing. -/
def hankelPicardStep {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ)
    (forcing u : HalfLineLaplaceL2) : HalfLineLaplaceL2 :=
  forcing + stableHankelContraction logRate residue u

theorem contractingWith_hankelPicardStep {n : ℕ} (logRate : Fin n → ℝ)
    (residue : Fin n → ℂ) (forcing : HalfLineLaplaceL2) :
    ContractingWith (stableHankelRatio logRate residue) (hankelPicardStep logRate residue forcing) := by
  refine ⟨stableHankelRatio_lt_one _ _, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [hankelPicardStep, dist_add_left, dist_eq_norm, ← map_sub]
  exact ((stableHankelContraction logRate residue).le_opNorm (x - y)).trans
    (mul_le_mul_of_nonneg_right (norm_stableHankelContraction_le _ _) (norm_nonneg _))

/-- The uniquely determined forced feedback response. -/
def hankelFixedPoint {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ)
    (forcing : HalfLineLaplaceL2) : HalfLineLaplaceL2 :=
  ContractingWith.fixedPoint (hankelPicardStep logRate residue forcing)
    (contractingWith_hankelPicardStep logRate residue forcing)

theorem hankelFixedPoint_eq {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ)
    (forcing : HalfLineLaplaceL2) :
    hankelFixedPoint logRate residue forcing = forcing +
      stableHankelContraction logRate residue (hankelFixedPoint logRate residue forcing) :=
  (contractingWith_hankelPicardStep logRate residue forcing).fixedPoint_isFixedPt.symm

/-- Well-posed feedback follows from the proved modal budget, without a smallness premise. -/
theorem existsUnique_hankelFeedback {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ)
    (forcing : HalfLineLaplaceL2) :
    ∃! u : HalfLineLaplaceL2, u = forcing + stableHankelContraction logRate residue u := by
  refine ⟨hankelFixedPoint logRate residue forcing, hankelFixedPoint_eq _ _ _, ?_⟩
  intro u hu
  exact (contractingWith_hankelPicardStep logRate residue forcing).fixedPoint_unique hu.symm

/-- Every starting state converges to the same feedback response. -/
theorem tendsto_hankelPicard {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ)
    (forcing u : HalfLineLaplaceL2) :
    Tendsto (fun k => (hankelPicardStep logRate residue forcing)^[k] u) atTop
      (𝓝 (hankelFixedPoint logRate residue forcing)) :=
  (contractingWith_hankelPicardStep logRate residue forcing).tendsto_iterate_fixedPoint u

/-- A residual-based error certificate after any number of iterations. -/
theorem hankelPicard_error_le {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ)
    (forcing u : HalfLineLaplaceL2) (k : ℕ) :
    ‖(hankelPicardStep logRate residue forcing)^[k] u - hankelFixedPoint logRate residue forcing‖ ≤
      ‖u - hankelPicardStep logRate residue forcing u‖ *
        (stableHankelRatio logRate residue : ℝ) ^ k / (1 - stableHankelRatio logRate residue) := by
  simpa only [dist_eq_norm] using
    (contractingWith_hankelPicardStep logRate residue forcing).apriori_dist_iterate_fixedPoint_le u k

/-- Starting at zero bounds the error entirely by forcing size and the modal budget. -/
theorem hankelPicard_zero_error_le {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ)
    (forcing : HalfLineLaplaceL2) (k : ℕ) :
    ‖(hankelPicardStep logRate residue forcing)^[k] 0 - hankelFixedPoint logRate residue forcing‖ ≤
      (1 + stableHankelBudget logRate residue) * ‖forcing‖ *
        (stableHankelRatio logRate residue : ℝ) ^ k := by
  have hpos : 0 < 1 + stableHankelBudget logRate residue := by
    linarith [stableHankelBudget_nonneg logRate residue]
  have hden : 1 - (stableHankelRatio logRate residue : ℝ) =
      (1 + stableHankelBudget logRate residue)⁻¹ := by
    change 1 - stableHankelBudget logRate residue /
      (1 + stableHankelBudget logRate residue) = _
    field_simp [hpos.ne']
    ring
  have h := hankelPicard_error_le logRate residue forcing 0 k
  simpa only [hankelPicardStep, map_zero, add_zero, zero_sub, norm_neg, hden,
    div_inv_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- The feedback response has a uniform forcing-to-solution bound. -/
theorem norm_hankelFixedPoint_le {n : ℕ} (logRate : Fin n → ℝ) (residue : Fin n → ℂ)
    (forcing : HalfLineLaplaceL2) :
    ‖hankelFixedPoint logRate residue forcing‖ ≤
      (1 + stableHankelBudget logRate residue) * ‖forcing‖ := by
  simpa using hankelPicard_zero_error_le logRate residue forcing 0

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.stableHankelBudget_nonneg
#print axioms GaloisForLFunctions.HTGeometry.stableHankelRatio_lt_one
#print axioms GaloisForLFunctions.HTGeometry.norm_stableHankelContraction_le
#print axioms GaloisForLFunctions.HTGeometry.contractingWith_hankelPicardStep
#print axioms GaloisForLFunctions.HTGeometry.hankelFixedPoint_eq
#print axioms GaloisForLFunctions.HTGeometry.existsUnique_hankelFeedback
#print axioms GaloisForLFunctions.HTGeometry.tendsto_hankelPicard
#print axioms GaloisForLFunctions.HTGeometry.hankelPicard_error_le
#print axioms GaloisForLFunctions.HTGeometry.hankelPicard_zero_error_le
#print axioms GaloisForLFunctions.HTGeometry.norm_hankelFixedPoint_le
