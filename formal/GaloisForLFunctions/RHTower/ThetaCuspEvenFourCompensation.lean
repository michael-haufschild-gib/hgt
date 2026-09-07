import GaloisForLFunctions.RHTower.ThetaCuspNativeEvenHead
import GaloisForLFunctions.HTGeometry.HankelSuccessorSchurStrict

/-!
# Source-selected rank-four compensation at the seam and on the cofinal tail

A fixed coefficient, defined solely from the literal seam Schur coordinate, gives
strictness near the seam. The complete-source Gaussian limit gives strictness past
a finite center. Global positivity still requires a comparison on the compact gap.
-/
open Filter Topology Matrix
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

/-- The native twelfth-entry Schur coordinate, using the actual even head inverse. -/
def thetaCuspNativeEvenFourSchur (x : ℝ) : ℝ :=
  finiteHankelSuccessorSchur (fun k => (-1 : ℝ)^k*thetaCuspNativeReflectionJet (2*k) x) 3

/-- Fixed source-selected positive coefficient; it has no aperture or sample dependence. -/
def thetaCuspNativeEvenCompensationCoefficient : ℝ :=
  (|thetaCuspNativeEvenFourSchur 0| + thetaCuspFullSource 0^2) / thetaCuspFullSource 0^2

/-- The exact corrected source matrix is strict precisely when its one remaining scalar is. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_iff
    {x : ℝ} (hx : 0 ≤ x) (C : ℝ) :
    (thetaCuspNativeEvenFourCompensated C x).PosDef ↔
      0 < thetaCuspNativeEvenFourSchur x + C*thetaCuspCenterCompensationSource x := by
  let m (k : ℕ) := (-1 : ℝ)^k*thetaCuspNativeReflectionJet (2*k) x
  let mC (k : ℕ) := m k + if k = 6 then C*thetaCuspCenterCompensationSource x else 0
  have hhead : finiteHankelMatrix mC 3 = thetaCuspNativeEvenHead x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [finiteHankelMatrix, thetaCuspNativeEvenHead, mC, m]
  have hfour : thetaCuspNativeEvenFourCompensated C x = finiteHankelMatrix mC 4 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [thetaCuspNativeEvenFourCompensated, finiteHankelMatrix, mC, m]
  have hS : finiteHankelSuccessorSchur mC 3 =
      thetaCuspNativeEvenFourSchur x + C*thetaCuspCenterCompensationSource x := by
    unfold finiteHankelSuccessorSchur
    rw [hhead]
    norm_num [thetaCuspNativeEvenFourSchur, finiteHankelSuccessorSchur, mC,
      Fin.sum_univ_succ, thetaCuspNativeEvenHead, m]
    ring
  have hp : (finiteHankelMatrix mC 3).PosDef := by
    rw [hhead]
    exact thetaCuspNativeEvenHead_posDef hx
  rw [hfour, finiteHankelMatrix_succ_posDef_iff_schur_pos hp, hS]

/-- The canonical coefficient is strictly positive without an unproved seam sign premise. -/
theorem thetaCuspNativeEvenCompensationCoefficient_pos :
    0 < thetaCuspNativeEvenCompensationCoefficient := by
  unfold thetaCuspNativeEvenCompensationCoefficient
  have hp := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
  exact div_pos (add_pos_of_nonneg_of_pos (abs_nonneg _) hp) hp

/-- Exact seam reserve supplied by the literal source-selected coefficient. -/
theorem thetaCuspNativeEvenFourCompensated_zero_posDef :
    (thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient 0).PosDef := by
  rw [thetaCuspNativeEvenFourCompensated_posDef_iff le_rfl]
  have hp := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
  have he : thetaCuspNativeEvenCompensationCoefficient*thetaCuspCenterCompensationSource 0 =
      3*|thetaCuspNativeEvenFourSchur 0|+3*thetaCuspFullSource 0^2 := by
    unfold thetaCuspNativeEvenCompensationCoefficient thetaCuspCenterCompensationSource
    simp only [mul_zero, zero_mul, add_zero]
    field_simp [(thetaCuspFullSource_pos_all 0).ne']
  rw [he]
  nlinarith [neg_le_abs (thetaCuspNativeEvenFourSchur 0), abs_nonneg (thetaCuspNativeEvenFourSchur 0)]

/-- Every entry of the corrected source matrix depends continuously on the center. -/
theorem continuous_thetaCuspNativeEvenFourCompensated (C : ℝ) :
    Continuous (thetaCuspNativeEvenFourCompensated C) := by
  have hΦ : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  have hd : Continuous (deriv thetaCuspFullSource) :=
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
  have hj := continuous_thetaCuspNativeReflectionJet
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold thetaCuspNativeEvenFourCompensated thetaCuspCenterCompensationSource
  split_ifs <;> fun_prop

/-- A nontrivial source interval at the seam is repaired unconditionally. -/
theorem exists_thetaCuspNativeEvenFourCompensated_posDef_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ →
      (thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient x).PosDef := by
  have hHerm (x : ℝ) :
      (thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient x).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspNativeEvenFourCompensated, add_comm, and_comm]
  have ht (i j : Fin 4) : Tendsto
      (fun x => thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient x i j)
      (𝓝 0) (𝓝 (thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient 0 i j)) := by
    have hM := continuous_thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient
    have hc : Continuous (fun x =>
        thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient x i j) := by
      fun_prop
    exact hc.continuousAt.tendsto
  have he := posDef_eventually_of_tendsto thetaCuspNativeEvenFourCompensated_zero_posDef
    (Filter.Eventually.of_forall hHerm) ht
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ, hδ, fun x hx => hb (by simpa [Real.dist_eq] using hx)⟩

/-- One fixed literal coefficient covers the seam and a cofinal ray; the remaining gap is compact. -/
theorem exists_thetaCuspNativeEvenFourCompensated_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ x : ℝ, 0 ≤ x → (x < δ ∨ R ≤ x) →
      (thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient x).PosDef := by
  obtain ⟨δ, hδ, hnear⟩ := exists_thetaCuspNativeEvenFourCompensated_posDef_near_zero
  obtain ⟨R, _, htail⟩ := exists_thetaCuspNativeEvenFourCompensated_posDef_tail
    thetaCuspNativeEvenCompensationCoefficient
  refine ⟨δ, max R δ, hδ, le_max_right _ _, fun x hx h => ?_⟩
  rcases h with h | h
  · exact hnear x (by simpa [abs_of_nonneg hx] using h)
  · exact htail x ((le_max_left _ _).trans h)

end
end RHTower
