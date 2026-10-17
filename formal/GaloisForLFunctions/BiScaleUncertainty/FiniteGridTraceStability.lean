import GaloisForLFunctions.BiScaleUncertainty.FiniteGridTraceData
import GaloisForLFunctions.BiScaleUncertainty.TriangularGramSineBound

/-!
# Longest-run stability of finite divisor traces

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

def complexTraceData (v : TraceData) : SequenceData ℂ :=
  ⟨fun k => (v k : ℂ), (lp.memℓp v).mono' (fun k => by simp)⟩

theorem complexTraceData_apply (v : TraceData) (k : ℕ) :
    complexTraceData v k = (v k : ℂ) := rfl

theorem norm_complexTraceData (v : TraceData) : ‖complexTraceData v‖ = ‖v‖ := by
  apply le_antisymm
  · exact lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      (fun k => by simp [complexTraceData_apply])
  · exact lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      (fun k => by simp [complexTraceData_apply])

def finiteGridShift (d : ℕ) (D : Finset ℕ) : SequenceData ℂ →L[ℂ] SequenceData ℂ :=
  sequenceMask ℂ (finiteGridActive d D) * sequenceLeftShift ℂ *
    sequenceMask ℂ (finiteGridActive d D)

theorem finiteGridShift_apply (d : ℕ) (D : Finset ℕ) (v : SequenceData ℂ) (k : ℕ) :
    finiteGridShift d D v k =
      if finiteGridActive d D k ∧ finiteGridActive d D (k + 1) then v (k + 1) else 0 := by
  simp only [finiteGridShift, mul_apply_eq_comp, sequenceMask_apply, sequenceLeftShift_apply]
  split_ifs <;> simp_all

theorem norm_finiteGridShift_le (d : ℕ) (D : Finset ℕ) : ‖finiteGridShift d D‖ ≤ 1 := by
  have hm := norm_sequenceMask_le ℂ (finiteGridActive d D)
  have hl := norm_sequenceLeftShift_le ℂ
  have hml : ‖sequenceMask ℂ (finiteGridActive d D) * sequenceLeftShift ℂ‖ ≤ 1 := by
    apply (norm_mul_le _ _).trans
    simpa only [one_mul] using mul_le_mul hm hl (norm_nonneg _) zero_le_one
  apply (norm_mul_le _ _).trans
  simpa only [one_mul] using mul_le_mul hml hm (norm_nonneg _) zero_le_one

/-- A missing node anywhere along a successor path kills its iterated coefficient. -/
theorem finiteGridShift_pow_zero_of_gap (d : ℕ) (D : Finset ℕ) (n : ℕ)
    (hn : 0 < n) (v : SequenceData ℂ) (k i : ℕ) (hi : i ≤ n)
    (hg : ¬ finiteGridActive d D (k + i)) : (finiteGridShift d D ^ n) v k = 0 := by
  induction n generalizing k i with
  | zero => omega
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, finiteGridShift_apply]
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

theorem finiteGridShift_nilpotent (d : ℕ) (D : Finset ℕ) :
    finiteGridShift d D ^ finiteGridRunLength d D = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext k
  obtain ⟨i, hi, hg⟩ := finiteGridRunLength_gap d D k
  exact finiteGridShift_pow_zero_of_gap d D _ (finiteGridRunLength_pos d D) v k i hi hg

def finiteGridSineFactor (d : ℕ) (D : Finset ℕ) : ℝ :=
  Real.cos (Real.pi / ((finiteGridRunLength d D : ℝ) + 1))

theorem finiteGridSineFactor_eq_chain (d : ℕ) (D : Finset ℕ) :
    finiteGridSineFactor d D = chainSineFactor (finiteGridRunLength d D - 1) := by
  have hp := finiteGridRunLength_pos d D
  unfold finiteGridSineFactor chainSineFactor
  rw [Nat.cast_sub (by omega : 1 ≤ finiteGridRunLength d D), Nat.cast_one]
  congr 2
  ring

theorem finiteGridSineFactor_nonneg (d : ℕ) (D : Finset ℕ) :
    0 ≤ finiteGridSineFactor d D := by
  rw [finiteGridSineFactor_eq_chain]
  exact chainSineFactor_nonneg _

theorem finiteGridSineFactor_lt_one (d : ℕ) (D : Finset ℕ) :
    finiteGridSineFactor d D < 1 := by
  rw [finiteGridSineFactor_eq_chain]
  exact chainSineFactor_lt_one _

theorem finiteGrid_adjacent_bound (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D) :
    |∑' k, v.1 k * v.1 (k + 1)| ≤ finiteGridSineFactor d D * ‖v‖ ^ 2 := by
  let z := complexTraceData v.1
  have hs : HasSum (fun k => v.1 k * v.1 (k + 1))
      (inner ℂ (finiteGridShift d D z) z).re := by
    apply (Complex.reCLM.hasSum (lp.hasSum_inner (finiteGridShift d D z) z)).congr_fun
    intro k
    by_cases hk : finiteGridActive d D k
    · by_cases hk1 : finiteGridActive d D (k + 1)
      · simp [z, finiteGridShift_apply, hk, hk1, complexTraceData_apply, RCLike.inner_apply]
      · simp [z, finiteGridShift_apply, hk1, finiteGridData_off d D v hk1]
    · simp [z, finiteGridShift_apply, hk, finiteGridData_off d D v hk]
  rw [hs.tsum_eq]
  apply (Complex.abs_re_le_norm _).trans
  change ‖inner ℂ (finiteGridShift d D z) z‖ ≤ finiteGridSineFactor d D * ‖v.1‖^2
  have h := RHTower.norm_inner_nilpotent_contraction_le_sine
    (finiteGridShift d D) (norm_finiteGridShift_le d D) (finiteGridRunLength d D)
    (finiteGridShift_nilpotent d D) z
  simpa only [finiteGridSineFactor, z, norm_complexTraceData] using h

/-- Unconditional sharp-factor bounds for every actual finite-family union datum. -/
theorem finiteGridExtension_stability (d : ℕ) (D : Finset ℕ) (v : FiniteGridData d D) :
    (2 - 2 * finiteGridSineFactor d D) * ‖v‖ ^ 2 ≤ ‖finiteGridExtension d D v‖ ^ 2 ∧
      ‖finiteGridExtension d D v‖ ^ 2 ≤ (2 + 2 * finiteGridSineFactor d D) * ‖v‖ ^ 2 := by
  rw [finiteGridExtension_energy]
  have h := abs_le.mp (finiteGrid_adjacent_bound d D v)
  constructor <;> nlinarith only [h.1, h.2]

/-- Arbitrary ambient data produce a certified interpolant by explicit masking. -/
theorem finiteGrid_masked_extension_stability (d : ℕ) (D : Finset ℕ) (v : TraceData) :
    (2 - 2 * finiteGridSineFactor d D) *
        (∑' k, if finiteGridActive d D k then (v k)^2 else 0) ≤
      ‖finiteGridExtension d D (finiteGridData d D v)‖^2 ∧
      ‖finiteGridExtension d D (finiteGridData d D v)‖^2 ≤
        (2 + 2 * finiteGridSineFactor d D) *
          (∑' k, if finiteGridActive d D k then (v k)^2 else 0) := by
  have hm : ‖finiteGridData d D v‖^2 =
      ∑' k, if finiteGridActive d D k then (v k)^2 else 0 := by
    rw [finiteGridExtension_mass]
    congr 1
    funext k
    rw [finiteGridData_apply]
    split_ifs <;> simp
  simpa only [hm] using finiteGridExtension_stability d D (finiteGridData d D v)

theorem finiteGridExtension_antilipschitz (d : ℕ) (D : Finset ℕ) :
    AntilipschitzWith
      ⟨(Real.sqrt (2 - 2 * finiteGridSineFactor d D))⁻¹, by positivity⟩
      (finiteGridExtension d D) := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro v
  have ha : 0 < 2 - 2 * finiteGridSineFactor d D := by
    linarith only [finiteGridSineFactor_lt_one d D]
  have hp : 0 < Real.sqrt (2 - 2 * finiteGridSineFactor d D) := Real.sqrt_pos.mpr ha
  have hs := Real.sq_sqrt ha.le
  have hb := (finiteGridExtension_stability d D v).1
  have hh : Real.sqrt (2 - 2 * finiteGridSineFactor d D) * ‖v‖ ≤
      ‖finiteGridExtension d D v‖ := by
    have hsq : (Real.sqrt (2 - 2 * finiteGridSineFactor d D) * ‖v‖)^2 ≤
        ‖finiteGridExtension d D v‖^2 := by
      rw [mul_pow, hs]
      exact hb
    exact (sq_le_sq₀ (mul_nonneg hp.le (norm_nonneg v)) (norm_nonneg _)).mp hsq
  change ‖v‖ ≤ (Real.sqrt (2 - 2 * finiteGridSineFactor d D))⁻¹ * _
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hh)

theorem finiteGridExtension_injective (d : ℕ) (D : Finset ℕ) :
    Function.Injective (finiteGridExtension d D) :=
  (finiteGridExtension_antilipschitz d D).injective

theorem isClosed_range_finiteGridExtension (d : ℕ) (D : Finset ℕ) :
    IsClosed (Set.range (finiteGridExtension d D)) :=
  (finiteGridExtension_antilipschitz d D).isClosed_range
    (finiteGridExtension d D).uniformContinuous

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
