import GaloisForLFunctions.BiScaleUncertainty.DivisorGridRunGeometry
import GaloisForLFunctions.BiScaleUncertainty.FiniteGridTraceStability

/-!
# Longest-run stability of arbitrary divisor traces

The actual masked successor on complex ℓ² is a contraction and is nilpotent at
the arithmetic longest-run length. Its sine numerical-radius bound gives the
physical Dirichlet coercivity of every actual real union datum and closed range.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

def divisorGridShift (d : ℕ) (D : Set ℕ) : SequenceData ℂ →L[ℂ] SequenceData ℂ :=
  sequenceMask ℂ (divisorGridActive d D) * sequenceLeftShift ℂ *
    sequenceMask ℂ (divisorGridActive d D)

theorem divisorGridShift_apply (d : ℕ) (D : Set ℕ) (v : SequenceData ℂ) (k : ℕ) :
    divisorGridShift d D v k =
      if divisorGridActive d D k ∧ divisorGridActive d D (k + 1) then v (k + 1) else 0 := by
  simp only [divisorGridShift, mul_apply_eq_comp, sequenceMask_apply, sequenceLeftShift_apply]
  split_ifs <;> simp_all

theorem norm_divisorGridShift_le (d : ℕ) (D : Set ℕ) : ‖divisorGridShift d D‖ ≤ 1 := by
  have hm := norm_sequenceMask_le ℂ (divisorGridActive d D)
  have hl := norm_sequenceLeftShift_le ℂ
  have hml : ‖sequenceMask ℂ (divisorGridActive d D) * sequenceLeftShift ℂ‖ ≤ 1 := by
    apply (norm_mul_le _ _).trans
    simpa only [one_mul] using mul_le_mul hm hl (norm_nonneg _) zero_le_one
  apply (norm_mul_le _ _).trans
  simpa only [one_mul] using mul_le_mul hml hm (norm_nonneg _) zero_le_one

/-- A missing node anywhere along a successor path kills its iterated coefficient. -/
theorem divisorGridShift_pow_zero_of_gap (d : ℕ) (D : Set ℕ) (n : ℕ)
    (hn : 0 < n) (v : SequenceData ℂ) (k i : ℕ) (hi : i ≤ n)
    (hg : ¬ divisorGridActive d D (k + i)) : (divisorGridShift d D ^ n) v k = 0 := by
  induction n generalizing k i with
  | zero => omega
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, divisorGridShift_apply]
      split_ifs with hk
      · by_cases hn0 : n = 0
        · have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with hi0 | hi1
          · exact False.elim (hg (by simpa [hi0] using hk.1))
          · exact False.elim (hg (by simpa [hi1] using hk.2))
        · have hip : 0 < i := by
            by_contra h
            have hi0 : i = 0 := by omega
            exact hg (by simpa [hi0] using hk.1)
          apply ih (by omega) (k + 1) (i - 1) (by omega)
          simpa [show k + 1 + (i - 1) = k + i by omega] using hg
      · rfl

theorem divisorGridShift_nilpotent (d : ℕ) (D : Set ℕ)
    (hb : divisorGridBoundedRuns d D) :
    divisorGridShift d D ^ divisorGridRunLength d D = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext k
  obtain ⟨i, hi, hg⟩ := divisorGridRunLength_gap d D hb k
  exact divisorGridShift_pow_zero_of_gap d D _ (divisorGridRunLength_pos d D hb) v k i hi hg

def divisorGridSineFactor (d : ℕ) (D : Set ℕ) : ℝ :=
  Real.cos (Real.pi / ((divisorGridRunLength d D : ℝ) + 1))

theorem divisorGridSineFactor_eq_chain (d : ℕ) (D : Set ℕ)
    (hb : divisorGridBoundedRuns d D) :
    divisorGridSineFactor d D = chainSineFactor (divisorGridRunLength d D - 1) := by
  have hp := divisorGridRunLength_pos d D hb
  unfold divisorGridSineFactor chainSineFactor
  rw [Nat.cast_sub (by omega : 1 ≤ divisorGridRunLength d D), Nat.cast_one]
  congr 2
  ring

theorem divisorGridSineFactor_nonneg (d : ℕ) (D : Set ℕ)
    (hb : divisorGridBoundedRuns d D) :
    0 ≤ divisorGridSineFactor d D := by
  rw [divisorGridSineFactor_eq_chain d D hb]
  exact chainSineFactor_nonneg _

theorem divisorGridSineFactor_lt_one (d : ℕ) (D : Set ℕ)
    (hb : divisorGridBoundedRuns d D) :
    divisorGridSineFactor d D < 1 := by
  rw [divisorGridSineFactor_eq_chain d D hb]
  exact chainSineFactor_lt_one _

theorem divisorGrid_adjacent_bound (d : ℕ) (D : Set ℕ)
    (hb : divisorGridBoundedRuns d D) (v : DivisorGridData d D) :
    |∑' k, v.1 k * v.1 (k + 1)| ≤ divisorGridSineFactor d D * ‖v‖ ^ 2 := by
  let z := complexTraceData v.1
  have hs : HasSum (fun k => v.1 k * v.1 (k + 1))
      (inner ℂ (divisorGridShift d D z) z).re := by
    apply (Complex.reCLM.hasSum (lp.hasSum_inner (divisorGridShift d D z) z)).congr_fun
    intro k
    by_cases hk : divisorGridActive d D k
    · by_cases hk1 : divisorGridActive d D (k + 1)
      · simp [z, divisorGridShift_apply, hk, hk1, complexTraceData_apply, RCLike.inner_apply]
      · simp [z, divisorGridShift_apply, hk1, divisorGridData_off d D v hk1]
    · simp [z, divisorGridShift_apply, hk, divisorGridData_off d D v hk]
  rw [hs.tsum_eq]
  apply (Complex.abs_re_le_norm _).trans
  change ‖inner ℂ (divisorGridShift d D z) z‖ ≤ divisorGridSineFactor d D * ‖v.1‖^2
  have h := RHTower.norm_inner_nilpotent_contraction_le_sine
    (divisorGridShift d D) (norm_divisorGridShift_le d D) (divisorGridRunLength d D)
    (divisorGridShift_nilpotent d D hb) z
  simpa only [divisorGridSineFactor, z, norm_complexTraceData] using h

/-- Sharp-factor bounds for every actual arbitrary-family union datum. -/
theorem divisorGridExtension_stability (d : ℕ) (D : Set ℕ)
    (hb : divisorGridBoundedRuns d D) (v : DivisorGridData d D) :
    (2 - 2 * divisorGridSineFactor d D) * ‖v‖ ^ 2 ≤ ‖divisorGridExtension d D v‖ ^ 2 ∧
      ‖divisorGridExtension d D v‖ ^ 2 ≤ (2 + 2 * divisorGridSineFactor d D) * ‖v‖ ^ 2 := by
  rw [divisorGridExtension_energy]
  have h := abs_le.mp (divisorGrid_adjacent_bound d D hb v)
  constructor <;> nlinarith only [h.1, h.2]

/-- Arbitrary ambient data produce a certified interpolant by explicit masking. -/
theorem divisorGrid_masked_extension_stability (d : ℕ) (D : Set ℕ)
    (hb : divisorGridBoundedRuns d D) (v : TraceData) :
    (2 - 2 * divisorGridSineFactor d D) *
        (∑' k, if divisorGridActive d D k then (v k)^2 else 0) ≤
      ‖divisorGridExtension d D (divisorGridData d D v)‖^2 ∧
      ‖divisorGridExtension d D (divisorGridData d D v)‖^2 ≤
        (2 + 2 * divisorGridSineFactor d D) *
          (∑' k, if divisorGridActive d D k then (v k)^2 else 0) := by
  have hm : ‖divisorGridData d D v‖^2 =
      ∑' k, if divisorGridActive d D k then (v k)^2 else 0 := by
    rw [divisorGridExtension_mass]
    congr 1
    funext k
    rw [divisorGridData_apply]
    split_ifs <;> simp
  simpa only [hm] using divisorGridExtension_stability d D hb (divisorGridData d D v)

theorem divisorGridExtension_antilipschitz (d : ℕ) (D : Set ℕ)
    (hb : divisorGridBoundedRuns d D) :
    AntilipschitzWith
      ⟨(Real.sqrt (2 - 2 * divisorGridSineFactor d D))⁻¹, by positivity⟩
      (divisorGridExtension d D) := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro v
  have ha : 0 < 2 - 2 * divisorGridSineFactor d D := by
    linarith only [divisorGridSineFactor_lt_one d D hb]
  have hp : 0 < Real.sqrt (2 - 2 * divisorGridSineFactor d D) := Real.sqrt_pos.mpr ha
  have hs := Real.sq_sqrt ha.le
  have hb := (divisorGridExtension_stability d D hb v).1
  have hh : Real.sqrt (2 - 2 * divisorGridSineFactor d D) * ‖v‖ ≤
      ‖divisorGridExtension d D v‖ := by
    have hsq : (Real.sqrt (2 - 2 * divisorGridSineFactor d D) * ‖v‖)^2 ≤
        ‖divisorGridExtension d D v‖^2 := by
      rw [mul_pow, hs]
      exact hb
    exact (sq_le_sq₀ (mul_nonneg hp.le (norm_nonneg v)) (norm_nonneg _)).mp hsq
  change ‖v‖ ≤ (Real.sqrt (2 - 2 * divisorGridSineFactor d D))⁻¹ * _
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hh)

theorem isClosed_range_divisorGridExtension (d : ℕ) (D : Set ℕ)
    (hb : divisorGridBoundedRuns d D) :
    IsClosed (Set.range (divisorGridExtension d D)) :=
  (divisorGridExtension_antilipschitz d D hb).isClosed_range
    (divisorGridExtension d D).uniformContinuous

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
